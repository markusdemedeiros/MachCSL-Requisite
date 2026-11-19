#!/usr/bin/env python3
"""Reconstruct the pinned COPYOUT baseline and audit the current linked proof.

Requires the normal prebuilt dependencies (see Experiments/README.md).
Every Lean invocation uses Experiments/check.sh; this is not a full build.
Artifacts and logs are written under .lake/whole-function.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
ARTIFACTS = Path(".lake/whole-function")
DEFAULT_REF = "818a8b6a6d38d128130fa0aa7e0c0505d6850feb"
BASELINE_AUDIT = r'''import UpstreamCopyout
import Lean.Util.CollectAxioms

example : Xv6.WALKADDR → Xv6.VMFAULT → Xv6.WALK_NOALLOC → Xv6.MEMMOVE → Xv6.COPYOUT :=
  Xv6.copyout_proof

open Lean in
run_cmd do
  let axioms ← collectAxioms ``Xv6.copyout_proof
  IO.FS.writeFile ".lake/whole-function/upstream-copyout-axioms.txt"
    (String.intercalate "\n" (axioms.toList.map toString) ++ "\n")
  logInfo m!"Original COPYOUT public type checked; {axioms.size} axiom dependencies saved."

#check Xv6.copyout_proof
'''
PRODUCTION_AUDIT = r'''import Xv6.LinkCopyout
import Lean.Util.CollectAxioms

example : Xv6.WALKADDR → Xv6.VMFAULT → Xv6.WALK_NOALLOC → Xv6.MEMMOVE → Xv6.COPYOUT :=
  Xv6.WholeFunction.Copyout.compiled_copyout
example : Xv6.WALKADDR → Xv6.VMFAULT → Xv6.WALK_NOALLOC → Xv6.MEMMOVE → Xv6.COPYOUT :=
  Xv6.copyout_proof
example : Xv6.WALKADDR → Xv6.VMFAULT → Xv6.WALK_NOALLOC → Xv6.MEMMOVE → Xv6.COPYOUT :=
  Xv6.Copyout
example : Xv6.COPYOUT := Xv6.CopyoutClosed

open Lean in
run_cmd do
  let baseline := (← IO.FS.readFile ".lake/whole-function/upstream-copyout-axioms.txt").splitOn "\n"
  for decl in #[``Xv6.WholeFunction.Copyout.compiled_copyout, ``Xv6.copyout_proof, ``Xv6.Copyout] do
    let axs ← collectAxioms decl
    let extra := axs.filter fun a => !baseline.contains a.toString
    unless extra.isEmpty do throwError "{decl}: axioms beyond original proof {extra}"
    if axs.contains ``sorryAx then throwError "{decl}: sorryAx"
    logInfo m!"{decl}: exact public type checked; {axs.size} axioms, all in original proof."
  let axs ← collectAxioms ``Xv6.copyout_proof
  IO.FS.writeFile ".lake/whole-function/production-copyout-axioms.txt"
    (String.intercalate "\n" (axs.toList.map toString) ++ "\n")
  let env ← getEnv
  let removedHelpers : Array String := #[@HELPERS@]
  for helper in removedHelpers do
    if env.contains (Name.str `Xv6 helper) then
      throwError "Old ProofCopyout helper remains in production import closure: {helper}"
  logInfo m!"All {removedHelpers.size} old ProofCopyout helpers absent from production import closure."

#check Xv6.WholeFunction.Copyout.compiled_copyout
#check Xv6.copyout_proof
#check Xv6.Copyout
#check Xv6.CopyoutClosed
'''


def prepare(ref):
    revision = subprocess.check_output(
        ["git", "rev-parse", "--verify", ref + "^{commit}"], cwd=ROOT, text=True).strip()
    source = subprocess.check_output(
        ["git", "show", revision + ":Xv6/ProofCopyout.lean"], cwd=ROOT)
    helpers = re.findall(
        r"^(?:private )?(?:noncomputable )?(?:theorem|def|abbrev|structure)\s+(\w+)",
        source.decode(), re.M)
    helpers.remove("copyout_proof")
    directory = ROOT / ARTIFACTS
    directory.mkdir(parents=True, exist_ok=True)
    (directory / "UpstreamCopyout.lean").write_bytes(source)
    (directory / "upstream-copyout-revision.txt").write_text(revision + "\n")
    (directory / "CopyoutOriginalAudit.lean").write_text(BASELINE_AUDIT)
    (directory / "CopyoutIntegrationAudit.lean").write_text(PRODUCTION_AUDIT.replace(
        "@HELPERS@", ", ".join(json.dumps(name) for name in helpers)))
    return {"status": "FAIL", "baseline_revision": revision,
            "baseline_sha256": hashlib.sha256(source).hexdigest(), "checks": []}


def check(report, label, *arguments):
    log = ARTIFACTS / (label + ".log")
    command = ["bash", "Experiments/check.sh", *arguments]
    with (ROOT / log).open("w") as output:
        result = subprocess.run(command, cwd=ROOT, stdout=output, stderr=subprocess.STDOUT)
    report["checks"].append({"command": command, "exit_code": result.returncode,
                             "log": str(log)})
    if result.returncode:
        raise RuntimeError(f"{label} failed; see {log}")
    print(f"PASS {label}: {log}", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline-ref", default=DEFAULT_REF,
                        help="explicit revision containing the original proof")
    parser.add_argument("--prepare-only", action="store_true",
                        help="reconstruct sources without invoking Lean")
    args = parser.parse_args()
    report = prepare(args.baseline_ref)
    if args.prepare_only:
        print(f"Prepared audit sources from {report['baseline_revision']}")
        return
    output = ROOT / ".lake/build/lib/lean"
    output.mkdir(parents=True, exist_ok=True)
    try:
        check(report, "upstream-copyout", "--root=" + str(ARTIFACTS),
              "-o", str(output / "UpstreamCopyout.olean"),
              str(ARTIFACTS / "UpstreamCopyout.lean"))
        check(report, "upstream-copyout-audit", str(ARTIFACTS / "CopyoutOriginalAudit.lean"))
        for module in ["Experiments/WholeFunction/CopyoutComplete",
                       "Xv6/ProofCopyout", "Xv6/LinkCopyout"]:
            target = output / (module + ".olean")
            target.parent.mkdir(parents=True, exist_ok=True)
            check(report, "integration-" + module.split("/")[-1],
                  "-o", str(target), module + ".lean")
        check(report, "copyout-integration-audit", str(ARTIFACTS / "CopyoutIntegrationAudit.lean"))
        old = set((ROOT / ARTIFACTS / "upstream-copyout-axioms.txt").read_text().splitlines())
        new = set((ROOT / ARTIFACTS / "production-copyout-axioms.txt").read_text().splitlines())
        report["axioms"] = {"baseline_count": len(old), "production_count": len(new),
                            "added": sorted(new - old), "removed": sorted(old - new)}
        report["status"] = "PASS"
    finally:
        (ROOT / ARTIFACTS / "audit-copyout-result.json").write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
