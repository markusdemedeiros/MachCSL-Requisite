#!/usr/bin/env python3
"""Reproduce the isolated affine experiment with the shared capped Lean checker.

This checks seven Affine modules, not xv6 or the integrated STRLEN client.
Enumeration is the default discovery backend; --compare-z3 also measures Z3.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compare-z3', action='store_true')
    parser.add_argument('--output', type=Path, default=HERE / 'AffineResults.json')
    args = parser.parse_args()
    spec = importlib.util.spec_from_file_location('focused_checker', HERE / 'check.py')
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    samples = []

    def check(name):
        source = HERE / f'{name}.lean'
        sample = checker.check(source, 'affine-final-' + name,
            ROOT / f'.lake/build/lib/lean/Experiments/WholeFunction/{name}.olean')
        samples.append(sample)
        if sample['exit_code']:
            raise RuntimeError(f'{name} failed; no successful report emitted')

    check('AffineCore')
    check('AffineSamples')
    discovery_path = ROOT / '.lake/whole-function/affine-discovery-final.json'
    command = ['python3', str(HERE / 'affine-synthesize.py'), '--log',
               str(ROOT / samples[-1]['log']), '--report', str(discovery_path)]
    if args.compare_z3:
        command.append('--compare')
    subprocess.run(command, cwd=ROOT, check=True)
    for name in ['AffineCandidates', 'AffineReplay', 'AffineClient', 'AffineTransport', 'AffineRejects']:
        check(name)
    for sample in samples:
        if hashlib.sha256((ROOT / sample['source']).read_bytes()).hexdigest() != sample['sha256']:
            raise RuntimeError('checked source changed: ' + sample['source'])
    discovery = json.loads(discovery_path.read_text())
    # Queries and solver responses remain in the separately reproducible raw
    # discovery report; the committed result retains their exact hashes.
    for name in ['query', 'response']:
        value = discovery.pop(name)
        discovery[name + '_sha256'] = None if value is None else hashlib.sha256(value.encode()).hexdigest()
    report = dict(
        scope='Isolated actual-STRLEN affine discovery, universal replay, memory consumer and negative checks; no full xv6 build',
        passed=True, memory_limit_gib=4, lean_workers=1,
        solver_limits=dict(address_space_mib=512, z3_memory_mib=256, query_timeout_ms=3000),
        discovered_register_relations=3, handwritten_scan_formulas_as_discovery_input=0,
        supplied_semantics=['ABI anchor entry.a0', 'first scan index 1', 'nonzero-byte backedge advances index by 1'],
        not_inferred=['buffer ownership and contents', 'C-string termination', 'index bounds', 'return-value range bound'],
        checked_obligations=['actual prefix initiation', 'actual prefix induction step',
            'actual byte-load Enabled condition', 'finite CFG certificate filtering',
            'wrong initial index', 'wrong stride annotation', 'incorrect nonmodular address claim',
            'removed loop row', 'removed empty-string suffix'],
        axiom_boundary=['propext', 'Classical.choice', 'Quot.sound'],
        performance_limit='Sampling and module timings are cached-import standalone checks. Discovery timings compare identical finite grammars and data; neither is a whole-build measurement.',
        discovery=discovery, discovery_report=str(discovery_path.relative_to(ROOT)), samples=samples,
        reproduction='python3 Experiments/WholeFunction/affine-check.py --compare-z3')
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print('Affine experiment PASS:', args.output, flush=True)


if __name__ == '__main__':
    main()
