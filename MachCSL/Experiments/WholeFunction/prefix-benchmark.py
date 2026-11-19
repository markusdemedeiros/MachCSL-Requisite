#!/usr/bin/env python3
"""Interleaved actual STRNCPY client checks of closed metadata and lookup reuse.

Each check uses the serialized memory-capped wrapper. The candidate engine is
restored and rebuilt even on failure. This is not a whole-build benchmark.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import statistics
import subprocess

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
ENGINE = HERE / 'MemoryPrefix.lean'
CLIENT = HERE / 'StrncpyCopy.lean'
ARTIFACTS = ROOT / '.lake/whole-function/prefix-benchmark'


def digest(data):
    return hashlib.sha256(data).hexdigest()


def check(label, source, output=None):
    command = ['bash', 'Experiments/check.sh']
    if output:
        command += ['-o', str(output.relative_to(ROOT))]
    command.append(str(source.relative_to(ROOT)))
    log = ARTIFACTS / (label + '.log')
    with log.open('w') as stream:
        result = subprocess.run(command, cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT)
    text = log.read_text()
    runtime = re.search(r'Service runtime: ([0-9.]+)s', text)
    memory = re.search(r'Memory peak: ([0-9.]+)([KMGT])', text)
    sample = {'command': command, 'exit_code': result.returncode,
              'log': str(log.relative_to(ROOT)), 'log_sha256': digest(log.read_bytes()),
              'service_seconds': float(runtime[1]) if runtime else None,
              'peak_MiB': float(memory[1]) * 1024 ** ('KMGT'.index(memory[2]) - 1) if memory else None}
    print(label, 'PASS' if not result.returncode else 'FAIL', sample['service_seconds'], flush=True)
    if result.returncode:
        raise RuntimeError(f'{label} failed: {log}')
    return sample


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=HERE / 'prefix-cache-results.json')
    parser.add_argument('--baseline-engine', type=Path,
                        default=ROOT / '.lake/whole-function/prefix-cache-baseline/MemoryPrefix.lean')
    args = parser.parse_args()
    if args.output.exists():
        raise RuntimeError('Use a fresh --output path to preserve prior evidence')
    original = args.baseline_engine.read_bytes()
    candidate = ENGINE.read_bytes()
    client = CLIENT.read_bytes()
    ARTIFACTS.mkdir(parents=True, exist_ok=True)
    for label, data in [('original', original), ('candidate', candidate), ('client', client)]:
        (ARTIFACTS / (label + '.lean.txt')).write_bytes(data)
    spec = importlib.util.spec_from_file_location('focused_suite', HERE / 'check.py')
    suite = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(suite)
    _, _, sources, _ = suite.selected_sources(
        ['Experiments.WholeFunction.StrncpyModel'], ['Experiments.WholeFunction.StrncpyModel'])
    fixed = {}
    for module, source in sources.items():
        fixed[str(source.relative_to(ROOT))] = digest(source.read_bytes())
        olean = ROOT.joinpath('.lake/build/lib/lean', *module.split('.')).with_suffix('.olean')
        if not olean.exists():
            raise RuntimeError(f'Missing cached prerequisite: {olean}')
        fixed[str(olean.relative_to(ROOT))] = digest(olean.read_bytes())
    axioms = ARTIFACTS / 'current-axioms.txt'
    audit = f'''\nopen Lean in
run_cmd do
  let mut lines : List String := []
  for decl in #[``Xv6.WholeFunction.Strncpy.initial_good, ``Xv6.WholeFunction.Strncpy.copy_good] do
    let axs ← collectAxioms decl
    if axs.contains ``sorryAx then throwError "incomplete prefix client"
    lines := lines ++ axs.toList.map toString
  IO.FS.writeFile "{axioms.relative_to(ROOT)}" (String.intercalate "\\n" lines)
'''
    clients = {}
    for variant in ['original', 'closed_uncached', 'cached']:
        lines = client.decode().splitlines(True)
        if variant != 'original':
            last = max(i for i, line in enumerate(lines) if line.startswith('import ')) + 1
            lines.insert(last, '\nset_option symbolicPrefix.cache ' +
                         ('true' if variant == 'cached' else 'false') + '\n')
        path = ARTIFACTS / (variant + '.lean')
        path.write_text(''.join(lines) + audit)
        clients[variant] = path
    report = {'status': 'RUNNING', 'scope': 'Same actual STRNCPY prefix/semantic proofs; cached fixed imports; no whole-build claim.',
              'original_engine_source': original.decode(), 'candidate_engine_source': candidate.decode(),
              'original_engine_sha256': digest(original), 'candidate_engine_sha256': digest(candidate),
              'client_sha256': digest(client), 'fixed_inputs': fixed,
              'samples': [], 'engine_checks': []}
    active = None
    baseline_axioms = None
    try:
        orders = [('original', 'cached', 'closed_uncached'),
                  ('closed_uncached', 'cached', 'original'),
                  ('cached', 'closed_uncached', 'original')]
        for round_index, order in enumerate(orders):
            for variant in order:
                desired = 'original' if variant == 'original' else 'candidate'
                if active != desired:
                    ENGINE.write_bytes(original if desired == 'original' else candidate)
                    report['engine_checks'].append(check(f'engine-{round_index}-{variant}', ENGINE,
                        ROOT / '.lake/build/lib/lean/Experiments/WholeFunction/MemoryPrefix.olean'))
                    active = desired
                sample = check(f'client-{round_index}-{variant}', clients[variant])
                current = sorted(set(axioms.read_text().splitlines()))
                if baseline_axioms is None:
                    baseline_axioms = current
                if current != baseline_axioms:
                    raise RuntimeError(f'{variant}: axiom dependencies changed')
                sample.update(round=round_index, variant=variant, axioms=current)
                report['samples'].append(sample)
                args.output.write_text(json.dumps(report, indent=2) + '\n')
        changed = [path for path, sha in fixed.items() if digest((ROOT/path).read_bytes()) != sha]
        report['fixed_inputs_changed'] = changed
        if changed or CLIENT.read_bytes() != client:
            raise RuntimeError('Client or fixed prerequisites changed during benchmark')
        report['medians'] = {variant: statistics.median(s['service_seconds'] for s in report['samples']
                                                       if s['variant'] == variant) for variant in clients}
        report['status'] = 'PASS'
    finally:
        ENGINE.write_bytes(candidate)
        report['restored_candidate_check'] = check('restored-candidate', ENGINE,
            ROOT / '.lake/build/lib/lean/Experiments/WholeFunction/MemoryPrefix.olean')
        args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report.get('medians', {})), flush=True)


if __name__ == '__main__':
    main()
