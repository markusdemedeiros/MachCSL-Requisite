#!/usr/bin/env python3
"""Recheck the prototype in dependency order, with one capped Lean worker.

Imports outside this experiment reuse the existing build. This measures a
focused compiler check, not a clean xv6 build or a whole-build speedup.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
PREFIX = "Experiments.WholeFunction."


def ordered_sources():
    sources = {p.stem: p for p in HERE.glob("*.lean")}
    ordered, visiting, visited = [], set(), set()

    def visit(name):
        if name in visited:
            return
        if name in visiting:
            raise RuntimeError(f"cyclic experiment imports: {name}")
        visiting.add(name)
        for imp in re.findall(r"^import\s+(\S+)", sources[name].read_text(), re.M):
            if imp.startswith(PREFIX):
                dependency = imp.removeprefix(PREFIX)
                if dependency not in sources:
                    raise RuntimeError(f"missing experiment source: {imp}")
                visit(dependency)
        visiting.remove(name)
        visited.add(name)
        ordered.append(sources[name])

    for name in sorted(sources):
        visit(name)
    return ordered


def check(source, label, output):
    log_path = ROOT / ".lake/whole-function" / f"suite-{label}.log"
    log_path.parent.mkdir(parents=True, exist_ok=True)
    output.parent.mkdir(parents=True, exist_ok=True)
    source_before = source.read_bytes()
    start = time.monotonic()
    with log_path.open("w") as log_file:
        result = subprocess.run(
            ["bash", "Experiments/check.sh", "-o", str(output),
             str(source.relative_to(ROOT))], cwd=ROOT, stdout=log_file, stderr=log_file,
            check=False)
    elapsed = time.monotonic() - start
    log = log_path.read_text()
    incomplete = "declaration uses 'sorry'" in log or "sorryAx" in log
    runtime = re.search(r"Service runtime:\s*([^\n]+)", log)
    memory = re.search(r"Memory peak:\s*([0-9.]+)([KMGT])", log)
    peak = None if memory is None else float(memory[1]) * 1024 ** "KMGT".index(memory[2]) / 1024
    data = source.read_bytes()
    source_changed = source_before != data
    sample = {
        "source": str(source.relative_to(ROOT)),
        "exit_code": result.returncode or int(incomplete or source_changed),
        "incomplete_proof_detected": incomplete,
        "source_changed_during_check": source_changed,
        "elapsed_seconds_including_lock": round(elapsed, 3),
        "service_runtime": runtime[1].strip() if runtime else None,
        "peak_mib": peak, "physical_lines": len(data.splitlines()),
        "sha256": hashlib.sha256(data).hexdigest(),
        "log": str(log_path.relative_to(ROOT)),
    }
    print(f"{source.name}: {'PASS' if sample['exit_code'] == 0 else 'FAIL'}, "
          f"{sample['service_runtime']}, {peak} MiB", flush=True)
    if sample["exit_code"]:
        print(log[-6000:], flush=True)
    return sample


def source_imports(source):
    text = source.read_text()
    comment = r"/-(?:(?!/-|-/)[\s\S])*-/"
    while re.search(comment, text):
        text = re.sub(comment, "", text)
    text = re.sub(r"--[^\n]*", "", text)
    return [module for line in re.findall(
        r"^\s*(?:public\s+)?import\s+([^\n]+)", text, re.M) for module in line.split()]


def selected_sources(targets, changed, root=ROOT):
    """Visit prerequisites only; never discover downstream clients to compile."""
    graph, sources, hashes, visiting, ordered = {}, {}, {}, [], []
    local_namespaces = {"Experiments", "MachCSL", "Xv6", "Requisiteness"}

    def visit(module, required=False):
        if not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*", module):
            raise ValueError(f"invalid module name: {module}")
        if module in visiting:
            raise ValueError("cyclic local imports: " + " -> ".join(visiting + [module]))
        if module in graph:
            return
        source = root.joinpath(*module.split(".")).with_suffix(".lean")
        if not source.exists():
            if required or module.split(".")[0] in local_namespaces:
                raise ValueError(f"missing local source: {module}")
            return  # Dependency supplied by a Lean/Lake package.
        visiting.append(module)
        sources[module] = source
        hashes[module] = hashlib.sha256(source.read_bytes()).hexdigest()
        graph[module] = source_imports(source)
        for dependency in graph[module]:
            visit(dependency)
        visiting.pop()
        ordered.append(module)

    for target in targets:
        visit(target, required=True)
    missing = set(changed) - graph.keys()
    if missing:
        raise ValueError(f"changed roots absent from target dependency closure: {sorted(missing)}")
    affected = set(changed)
    for module in ordered:
        if any(dependency in affected for dependency in graph[module]):
            affected.add(module)
    selected = [module for module in ordered if module in affected]
    # Additional production prerequisites must be named explicitly, never swept
    # into a broad xv6 build as a side effect of selecting a client.
    forbidden = [module for module in selected if module not in targets and not
                 module.startswith((PREFIX, "Experiments.SolverSurvey."))]
    if forbidden:
        raise ValueError("affected prerequisites outside the focused namespaces; "
                         f"name them explicitly in --targets: {forbidden}")
    return selected, graph, sources, hashes


def check_selected(args):
    selected, graph, sources, hashes = selected_sources(args.targets, args.changed)
    output = args.output.resolve()
    if output.exists():
        raise ValueError(f"refusing to overwrite an existing report: {output}")
    snapshots = {module: {"source": str(source.relative_to(ROOT)),
                         "sha256": hashes[module], "imports": graph[module]}
                 for module, source in sources.items()}
    samples = []
    label_prefix = "selected-" + hashlib.sha256(str(output).encode()).hexdigest()[:12] + "-"
    for module in selected:
        if args.list_only:
            print(module)
            continue
        olean = ROOT.joinpath(".lake/build/lib/lean", *module.split(".")).with_suffix(".olean")
        samples.append(dict(check(sources[module], label_prefix + module, olean), module=module))
        if samples[-1]["exit_code"]:
            break
    changed_sources = [module for module, source in sources.items()
                       if not source.exists() or hashlib.sha256(source.read_bytes()).hexdigest() != hashes[module]]
    for sample in samples:
        sample["source_changed_after_check"] = sample["module"] in changed_sources
        if sample["source_changed_after_check"]:
            sample["exit_code"] = sample["exit_code"] or 1
    report = {
        "scope": "Selected affected prerequisites only; cached external imports; no downstream build",
        "list_only": args.list_only, "targets": args.targets, "changed_roots": args.changed,
        "selected_modules_in_dependency_order": selected,
        "cached_local_modules": sorted(set(sources) - set(selected)),
        "source_graph": snapshots, "source_changes_during_run": changed_sources,
        "memory_limit_gib": 4, "lean_workers": 1, "samples": samples,
        "passed": None if args.list_only else not changed_sources and len(samples) == len(selected)
                  and all(sample["exit_code"] == 0 for sample in samples),
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    with output.open("x") as stream:
        stream.write(json.dumps(report, indent=2) + "\n")
    return int(bool(changed_sources) or any(sample["exit_code"] for sample in samples))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline", action="store_true",
                        help="also check original ProofCopyin and ProofCopyout from --baseline-ref")
    parser.add_argument("--baseline-ref", default="HEAD",
                        help="git revision containing the historical production proof (default: HEAD)")
    parser.add_argument("--resume", action="store_true",
                        help="reuse the unchanged successful prefix of the previous results")
    parser.add_argument("--targets", nargs="+", help="explicit module roots for selected dependency refresh")
    parser.add_argument("--changed", nargs="+", help="changed module roots within the target closure")
    parser.add_argument("--output", type=Path, help="new, separate JSON report path for selected mode")
    parser.add_argument("--list-only", action="store_true", help="write the selected plan without invoking Lean")
    args = parser.parse_args()
    if args.targets or args.changed or args.output or args.list_only:
        if not (args.targets and args.changed and args.output):
            parser.error("selected mode requires --targets, --changed, and a separate --output")
        if args.resume or args.baseline:
            parser.error("selected mode cannot be combined with --resume or --baseline")
        try:
            return check_selected(args)
        except (ValueError, OSError) as error:
            parser.error(str(error))
    previous = []
    if args.resume and (HERE / "results.json").exists():
        previous = json.loads((HERE / "results.json").read_text())["samples"]
    samples = []
    for index, source in enumerate(ordered_sources()):
        output = ROOT / ".lake/build/lib/lean/Experiments/WholeFunction" / f"{source.stem}.olean"
        old = previous[index] if index < len(previous) else None
        if (old and old["exit_code"] == 0 and old["source"] == str(source.relative_to(ROOT)) and
                old["sha256"] == hashlib.sha256(source.read_bytes()).hexdigest() and output.exists()):
            samples.append(dict(old, reused_prior_check=True))
            print(f"{source.name}: REUSE unchanged successful check", flush=True)
        else:
            previous = []  # Any changed dependency invalidates subsequent cached samples.
            samples.append(check(source, source.stem, output))
        if samples[-1]["exit_code"]:
            break
    # Compare with an explicit git source, never label the working-tree wrapper
    # as the unchanged historical proof.
    reference_revision = subprocess.check_output(
        ["git", "rev-parse", args.baseline_ref], cwd=ROOT, text=True).strip()
    integrations, references = {}, {}
    for name in ("Copyin", "Copyout"):
        lower = name.lower()
        relative = f"Xv6/Proof{name}.lean"
        reference = subprocess.check_output(
            ["git", "show", f"{reference_revision}:{relative}"], cwd=ROOT)
        production_source = ROOT / relative
        production = production_source.read_bytes()
        links_compiler = (
            f"import Experiments.WholeFunction.{name}Complete".encode() in production and
            re.search(rf"theorem\s+{lower}_proof\b".encode(), production) is not None and
            f"WholeFunction.{name}.compiled_{lower}".encode() in production)
        production_check = None
        if links_compiler and all(s["exit_code"] == 0 for s in samples):
            production_check = check(production_source, f"production-{lower}",
                ROOT / f".lake/whole-function/integration/Proof{name}.olean")
        integrated = links_compiler and production_check is not None and production_check["exit_code"] == 0
        baseline = None
        if args.baseline and all(s["exit_code"] == 0 for s in samples):
            historical = ROOT / f".lake/whole-function/reference/Proof{name}.lean"
            historical.parent.mkdir(parents=True, exist_ok=True)
            historical.write_bytes(reference)
            baseline = check(historical, f"reference-{lower}",
                             ROOT / f".lake/whole-function/reference/Proof{name}.olean")
        integrations[lower] = dict(source=relative, links_compiler=links_compiler,
            checked=integrated, check=production_check,
            wrapper_lines_removed=len(reference.splitlines()) - len(production.splitlines()) if integrated else 0)
        references[lower] = dict(git_revision=reference_revision, git_source=relative,
            sha256=hashlib.sha256(reference).hexdigest(), physical_lines=len(reference.splitlines()), check=baseline)
    for sample in samples:
        current = (ROOT / sample["source"]).read_bytes()
        sample["source_changed_after_check"] = hashlib.sha256(current).hexdigest() != sample["sha256"]
        if sample["source_changed_after_check"]:
            sample["exit_code"] = sample["exit_code"] or 1
    report = {
        "scope": "Focused checks with cached external imports; not a whole-build benchmark",
        "git_head": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        "production_proofs_replaced": sum(int(x["checked"]) for x in integrations.values()),
        "production_wrapper_lines_removed": sum(x["wrapper_lines_removed"] for x in integrations.values()),
        "production_integrations": integrations,
        "references": references,
        "memory_limit_gib": 4, "lean_workers": 1,
        "samples": samples,
    }
    (HERE / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    extra_checks = [x["check"] for x in integrations.values()] + [x["check"] for x in references.values()]
    return int(any(s["exit_code"] for s in samples) or
               any(x is not None and x["exit_code"] != 0 for x in extra_checks))



if __name__ == "__main__":
    raise SystemExit(main())
