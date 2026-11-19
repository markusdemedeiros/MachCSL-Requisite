#!/usr/bin/env python3
"""Compare complete string proofs with pinned original proofs under the Lean cap.

Uses prebuilt imports; this is neither a full build nor a whole-build benchmark.
The report records single focused checks, including every experimental import's
source hash. Production clients and earlier benchmark reports are not modified.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
ARTIFACTS = Path(".lake/whole-function/strings")
DEFAULT_REF = "818a8b6a6d38d128130fa0aa7e0c0505d6850feb"


def digest(data):
    return hashlib.sha256(data).hexdigest()


def source_closure(module):
    """Follow local imports; report experiment hashes and original-proof imports."""
    visited, hashes, forbidden = set(), {}, []

    def visit(name):
        if name in visited:
            return
        visited.add(name)
        path = ROOT / (name.replace(".", "/") + ".lean")
        if not path.exists():
            return
        if name in ["Xv6.ProofStrlen", "Xv6.ProofStrncpy"]:
            forbidden.append(name)
        data = path.read_bytes()
        if name.startswith("Experiments."):
            hashes[str(path.relative_to(ROOT))] = digest(data)
        for imp in re.findall(r"^import\s+(\S+)", data.decode(), re.M):
            visit(imp)

    visit(module)
    return hashes, forbidden


def check(label, source, output=None, source_root=None):
    command = ["bash", "Experiments/check.sh"]
    if source_root:
        command.append("--root=" + str(source_root))
    if output:
        (ROOT / output).parent.mkdir(parents=True, exist_ok=True)
        command += ["-o", str(output)]
    command.append(str(source))
    before = (ROOT / source).read_bytes()
    log = ARTIFACTS / (label + ".log")
    with (ROOT / log).open("w") as stream:
        result = subprocess.run(command, cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT)
    text = (ROOT / log).read_text()
    runtime = re.search(r"Service runtime: ([0-9.]+)s", text)
    cpu = re.search(r"CPU time consumed: ([0-9.]+)s", text)
    memory = re.search(r"Memory peak: ([0-9.]+)([KMGT])", text)
    changed = before != (ROOT / source).read_bytes()
    sample = {"command": command, "source_sha256": digest(before), "log": str(log),
              "exit_code": result.returncode or int(changed),
              "source_changed_during_check": changed,
              "runtime_seconds": float(runtime[1]) if runtime else None,
              "cpu_seconds": float(cpu[1]) if cpu else None,
              "peak_MiB": float(memory[1]) * 1024 ** ("KMGT".index(memory[2]) - 1)
              if memory else None}
    print(f"{label}: {'PASS' if not sample['exit_code'] else 'FAIL'}; "
          f"{sample['runtime_seconds']} s, {sample['peak_MiB']} MiB", flush=True)
    if sample["exit_code"]:
        print(text[-5000:], flush=True)
    return sample


def audit_source(name, helpers, original=False):
    lower, spec = name.lower(), name.upper()
    module = "Upstream" + name if original else "Experiments.WholeFunction." + name + "Complete"
    theorem = f"Xv6.{lower}_proof" if original else f"Xv6.WholeFunction.{name}.compiled_{lower}"
    axioms_file = ARTIFACTS / (lower + ("-baseline" if original else "-current") + "-axioms.txt")
    text = f'''import {module}
import Lean.Util.CollectAxioms

example : Xv6.{spec} := {theorem}

open Lean in
run_cmd do
  let axs ← collectAxioms ``{theorem}
  IO.FS.writeFile "{axioms_file}"
    (String.intercalate "\\n" (axs.toList.map toString) ++ "\\n")
  if axs.contains ``sorryAx then throwError "{theorem}: contains sorryAx"
'''
    if not original:
        forbidden = ", ".join(json.dumps("Xv6." + h) for h in helpers)
        text += f'''  let baseline := (← IO.FS.readFile "{ARTIFACTS / (lower + '-baseline-axioms.txt')}").splitOn "\\n"
  let extra := axs.filter fun ax => !baseline.contains ax.toString
  unless extra.isEmpty do throwError "Axioms beyond original {spec}: {{extra}}"
  let env ← getEnv
  let forbidden : Array String := #[{forbidden}]
  for name in forbidden do
    if env.contains name.toName then
      throwError "Old production proof declaration in import closure: {{name}}"
'''
    text += f'  logInfo m!"{theorem}: exact {spec} type; {{axs.size}} axioms checked."\n\n#check {theorem}\n'
    return text


def run_function(name, revision, reuse, baseline_only):
    lower = name.lower()
    source = subprocess.check_output(["git", "show", revision + ":Xv6/Proof" + name + ".lean"], cwd=ROOT)
    helpers = re.findall(r"^(?:private )?(?:noncomputable )?(?:theorem|def|abbrev|structure)\s+(\w+)",
                         source.decode(), re.M)
    assert lower + "_proof" in helpers
    baseline_source = ARTIFACTS / ("Upstream" + name + ".lean")
    baseline_audit = ARTIFACTS / (name + "BaselineAudit.lean")
    current_audit = ARTIFACTS / (name + "CurrentAudit.lean")
    (ROOT / baseline_source).write_bytes(source)
    (ROOT / baseline_audit).write_text(audit_source(name, helpers, original=True))
    (ROOT / current_audit).write_text(audit_source(name, helpers))
    baseline_result = ROOT / ARTIFACTS / (lower + "-baseline.json")
    baseline_axioms = ROOT / ARTIFACTS / (lower + "-baseline-axioms.txt")
    key = {"revision": revision, "source_sha256": digest(source),
           "audit_sha256": digest((ROOT / baseline_audit).read_bytes())}
    baseline = json.loads(baseline_result.read_text()) if reuse and baseline_result.exists() else None
    if not (baseline and baseline.get("status") == "PASS" and baseline.get("key") == key
            and baseline_axioms.exists()
            and baseline.get("axioms_sha256") == digest(baseline_axioms.read_bytes())):
        baseline = {"key": key, "checks": [], "status": "FAIL"}
        for label, path, output, source_root in [
            (lower + "-baseline", baseline_source,
             Path(".lake/build/lib/lean/Upstream" + name + ".olean"), ARTIFACTS),
            (lower + "-baseline-audit", baseline_audit, None, None)]:
            sample = check(label, path, output, source_root)
            baseline["checks"].append(sample)
            if sample["exit_code"]:
                baseline_result.write_text(json.dumps(baseline, indent=2) + "\n")
                return {"status": "FAIL", "baseline": baseline}
        baseline.update(status="PASS", axioms_sha256=digest(baseline_axioms.read_bytes()))
        baseline_result.write_text(json.dumps(baseline, indent=2) + "\n")
    entry = {"status": "BASELINE_ONLY" if baseline_only else "FAIL", "baseline": baseline,
             "public_type": "Xv6." + name.upper(),
             "compiled_theorem": f"Xv6.WholeFunction.{name}.compiled_{lower}", "checks": []}
    if baseline_only:
        return entry
    module = "Experiments.WholeFunction." + name + "Complete"
    hashes, forbidden = source_closure(module)
    entry.update(experiment_dependency_source_hashes=hashes, forbidden_proof_imports=forbidden)
    if forbidden:
        return entry
    complete = Path(module.replace(".", "/") + ".lean")
    for label, path, output in [
        (lower + "-complete", complete, Path(".lake/build/lib/lean") / complete.with_suffix(".olean")),
        (lower + "-current-audit", current_audit, None)]:
        sample = check(label, path, output)
        entry["checks"].append(sample)
        if sample["exit_code"]:
            break
    entry["sources_unchanged_across_check"] = hashes == source_closure(module)[0]
    current_axioms = ROOT / ARTIFACTS / (lower + "-current-axioms.txt")
    if current_axioms.exists() and len(entry["checks"]) == 2:
        old, new = set(baseline_axioms.read_text().splitlines()), set(current_axioms.read_text().splitlines())
        entry["axioms"] = {"baseline_count": len(old), "current_count": len(new),
                           "added": sorted(new - old), "removed": sorted(old - new),
                           "baseline": sorted(old), "current": sorted(new)}
    if len(entry["checks"]) == 2 and all(not s["exit_code"] for s in entry["checks"]) and entry["sources_unchanged_across_check"]:
        entry.update(status="PASS", old_proof_declarations_absent=helpers)
    return entry


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline-ref", default=DEFAULT_REF)
    parser.add_argument("--functions", nargs="+", choices=["Strlen", "Strncpy"], default=["Strlen", "Strncpy"])
    parser.add_argument("--reuse-baseline", action="store_true", help="reuse a successful matching baseline source/audit/axiom snapshot")
    parser.add_argument("--baseline-only", action="store_true", help="capture upstream evidence while new proofs are being edited")
    parser.add_argument("--output", type=Path, help="new report path; preserve earlier checkpoints")
    args = parser.parse_args()
    path = ROOT / args.output if args.output else HERE / "string-integration.json"
    if args.output and path.exists():
        parser.error("--output must name a new report; existing evidence is preserved")
    revision = subprocess.check_output(["git", "rev-parse", "--verify", args.baseline_ref + "^{commit}"], cwd=ROOT, text=True).strip()
    (ROOT / ARTIFACTS).mkdir(parents=True, exist_ok=True)
    report = json.loads(path.read_text()) if path.exists() else {
        "scope": "Single capped checks with prebuilt imports; no whole-build speedup or source-length savings claim.",
        "reproduce": "python3 Experiments/WholeFunction/audit-strings.py",
        "functions": {}}
    failed = False
    for name in args.functions:
        entry = run_function(name, revision, args.reuse_baseline, args.baseline_only)
        report["functions"][name] = entry
        path.write_text(json.dumps(report, indent=2) + "\n")
        failed |= entry["status"] == "FAIL"
    raise SystemExit(int(failed))


if __name__ == "__main__":
    main()
