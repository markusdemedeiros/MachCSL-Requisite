#!/usr/bin/env python3
"""Freshen the focused experiment and compare it with the requisiteness commit.
All checks are serial, single-worker and capped at 4 GiB. Other imports remain
cached; these numbers are not whole-xv6 build measurements.
"""
import hashlib
import json
from pathlib import Path
import re
import statistics
import subprocess

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / ".lake/focused-experiments"
BASE = "c2a08aa60"
DECLS = {
    "Xv6.DinodeEnc": ["Xv6.dinodeBytes_" + n for n in ["type", "major", "minor", "nlink", "size", "addrs"]],
    "Xv6.DirentEnc": ["Xv6.direntBytes_inum", "Xv6.direntBytes_name"],
    "Xv6.DinodeSlot": ["Xv6.dislot_bytes"],
}
MODULES = ["Experiments.Layout", "Experiments.LayoutResources", *DECLS,
           "Experiments.LayoutChecks", "Requisiteness.Axioms", "Requisiteness.Coherence",
           "Xv6.IupdateSteps", "Xv6.DirlookupParts", "Xv6.IlockBlk"]


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def seconds(value):
    return sum(float(n) * {"ms": .001, "s": 1, "min": 60, "h": 3600}[unit]
               for n, unit in re.findall(r"([\d.]+)(ms|min|s|h)", value))


def run(path, tag, module=None):
    args = ["bash", "Experiments/check.sh"]
    if module:
        output = ROOT / ".lake/build/lib/lean" / Path(*module.split(".")).with_suffix(".olean")
        output.parent.mkdir(parents=True, exist_ok=True)
        temporary = output.with_suffix(".checking.olean")
        args += ["-o", str(temporary)]
    log = OUT / (tag + ".log")
    print("checking " + tag, flush=True)
    with log.open("w") as stream:
        result = subprocess.run(args + [str(path)], cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT)
    text = log.read_text()
    if result.returncode:
        if module:
            temporary.unlink(missing_ok=True)
        raise SystemExit(text[-5000:])
    if module:
        temporary.replace(output)
    memory = re.search(r"Memory peak:\s*([\d.]+)([KMG])", text)
    return {"wall_s": seconds(re.search(r"Service runtime:\s*(.+)", text)[1]),
            "cpu_s": seconds(re.search(r"CPU time consumed:\s*(.+)", text)[1]),
            "peak_mib": float(memory[1]) * {"K": 1 / 1024, "M": 1, "G": 1024}[memory[2]],
            "log": str(log.relative_to(ROOT))}, text


def statement(raw, name):
    start = raw.index("theorem " + name.rsplit(".", 1)[-1] + " ")
    return raw[start:raw.index(":= by", start)]


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    paths = {m: ROOT / Path(*m.split(".")).with_suffix(".lean") for m in MODULES}
    hashes = {m: digest(p.read_bytes()) for m, p in paths.items()}
    validation = []
    for m, path in paths.items():
        metrics, _ = run(path, m, m)
        validation.append({"module": m, "sha256": hashes[m], "metrics": metrics})
    comparisons = []
    for m, names in DECLS.items():
        original = subprocess.check_output(["git", "show", f"{BASE}:{paths[m].relative_to(ROOT)}"], cwd=ROOT)
        current = paths[m].read_bytes()
        for name in names:
            assert statement(original.decode(), name) == statement(current.decode(), name), name
        sources, samples, axioms = {}, {}, {}
        for kind, raw in (("original", original), ("current", current)):
            sources[kind] = OUT / f"{m}-{kind}.lean"
            sources[kind].write_bytes(raw + ("\n" + "\n".join(f"#print axioms {n}" for n in names)).encode())
            samples[kind] = []
        for i in range(3):
            for kind in (("original", "current") if i % 2 == 0 else ("current", "original")):
                metrics, text = run(sources[kind], f"{m}-{kind}-{i}")
                samples[kind].append(metrics)
                axioms[kind] = {n: sorted(a.strip() for a in aa.split(",") if a.strip())
                                for n, aa in re.findall(r"'([^']+)' depends on axioms:\s*\[(.*?)\]", text, re.S)}
                assert set(axioms[kind]) == set(names)
        for name in names:
            assert not set(axioms["current"][name]) - set(axioms["original"][name]), name
        medians = {k: {v: statistics.median(s[v] for s in ss) for v in ["wall_s", "cpu_s", "peak_mib"]}
                   for k, ss in samples.items()}
        comparisons.append({"module": m, "statements_unchanged": names, "axioms": axioms,
                            "source_sha256": {"original": digest(original), "current": digest(current)},
                            "lines": {"original": len(original.splitlines()), "current": len(current.splitlines())},
                            "samples": samples, "median": medians})
        print(json.dumps({"module": m, "median": medians}), flush=True)
    assert all(digest(paths[m].read_bytes()) == h for m, h in hashes.items()), "sources changed"
    report = {"baseline": BASE, "scope": __doc__, "lean_threads": 1,
              "wrapper_sha256": digest((ROOT / "Experiments/check.sh").read_bytes()),
              "validation": validation, "comparisons": comparisons}
    (ROOT / "Experiments/results.json").write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
