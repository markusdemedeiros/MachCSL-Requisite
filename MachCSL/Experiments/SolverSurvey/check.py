#!/usr/bin/env python3
"""Check all retained solver clients, serialized and memory capped.

Run setup.sh first. Dependencies outside SolverSurvey reuse compiled imports.
Performance comparisons are separate; this is a source-hashed correctness run.
"""
import hashlib
import json
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PREFIX = 'Experiments.SolverSurvey.'


def main():
    sources = {p.stem: p for p in HERE.glob('*.lean')}
    ordered, active, done = [], set(), set()

    def visit(name):
        if name in done:
            return
        if name in active:
            raise RuntimeError(f'cyclic import: {name}')
        active.add(name)
        for module in re.findall(r'^import\s+(\S+)', sources[name].read_text(), re.M):
            if module.startswith(PREFIX):
                visit(module.removeprefix(PREFIX))
        active.remove(name)
        done.add(name)
        ordered.append(sources[name])

    for name in sorted(sources):
        visit(name)
    samples = []
    for source in ordered:
        before = source.read_bytes()
        log = ROOT / '.lake/solver-survey' / f'suite-{source.stem}.log'
        output = ROOT / '.lake/build/lib/lean/Experiments/SolverSurvey' / f'{source.stem}.olean'
        log.parent.mkdir(parents=True, exist_ok=True)
        output.parent.mkdir(parents=True, exist_ok=True)
        with log.open('w') as stream:
            run = subprocess.run(['bash', 'Experiments/check.sh', '-o', str(output),
                                  str(source.relative_to(ROOT))], cwd=ROOT,
                                 stdout=stream, stderr=subprocess.STDOUT)
        text = log.read_text()
        sample = dict(source=str(source.relative_to(ROOT)),
                      sha256=hashlib.sha256(before).hexdigest(),
                      exit_code=run.returncode, log=str(log.relative_to(ROOT)),
                      source_changed=before != source.read_bytes(),
                      incomplete="declaration uses 'sorry'" in text)
        for label, key in [('Service runtime', 'service_runtime'), ('Memory peak', 'peak')]:
            match = re.search(label + r':\s*([^\n]+)', text)
            sample[key] = match[1] if match else None
        samples.append(sample)
        print(json.dumps(sample), flush=True)
        if run.returncode or sample['source_changed'] or sample['incomplete']:
            break
    for sample in samples:
        sample['hash_matches_after_suite'] = hashlib.sha256(
            (ROOT / sample['source']).read_bytes()).hexdigest() == sample['sha256']
    passed = len(samples) == len(ordered) and all(
        not x['exit_code'] and not x['source_changed'] and not x['incomplete'] and
        x['hash_matches_after_suite'] for x in samples)
    (HERE / 'check-results.json').write_text(json.dumps(dict(
        scope='Focused correctness checks with cached external imports; not build benchmarks',
        passed=passed, workers=1, memory_limit_gib=4, samples=samples), indent=2) + '\n')
    return 0 if passed else 1


if __name__ == '__main__':
    raise SystemExit(main())
