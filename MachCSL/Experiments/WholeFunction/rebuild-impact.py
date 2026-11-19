#!/usr/bin/env python3
"""Read sources/timing manifests only; estimate serial cached-import rebuild work.

Run after check.py finishes. No Lean or Lake commands are executed. Missing or
source-mismatched measurements are excluded and explicitly reported.
"""
import argparse
from collections import defaultdict
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
ROOTS = ['Xv6.ProofCopyin', 'Xv6.ProofCopyout']


def sha(data):
    return hashlib.sha256(data).hexdigest()


def imports(text):
    # Remove nested Lean comments before recognizing module headers.
    text = re.sub(r'--[^\n]*', '', text)
    while re.search(r'/\*(?:(?!/\*|\*/)[\s\S])*\*/', text):
        text = re.sub(r'/\*(?:(?!/\*|\*/)[\s\S])*\*/', '', text)
    return [m for line in re.findall(r'^\s*(?:public\s+)?import\s+([^\n]+)', text, re.M)
            for m in line.split()]


def reachable(graph, starts):
    seen, stack = set(), list(starts)
    while stack:
        node = stack.pop()
        if node not in seen:
            seen.add(node)
            stack.extend(graph.get(node, []))
    return seen


def reverse(graph):
    out = defaultdict(list)
    for node, deps in graph.items():
        for dep in deps:
            out[dep].append(node)
    return out


def seconds(value):
    if not value:
        return None
    units = {'h': 3600, 'min': 60, 's': 1, 'ms': .001, 'us': .000001}
    parts = re.findall(r'([0-9.]+)\s*(min|ms|us|h|s)', value)
    return sum(float(n) * units[u] for n, u in parts) if parts else None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline-ref', default='818a8b6a6d38d128130fa0aa7e0c0505d6850feb')
    parser.add_argument('--output', type=Path, default=HERE / 'rebuild-impact.json',
                        help='Write a separate path for post-extraction comparisons; preserve the baseline JSON.')
    args = parser.parse_args()
    paths = {'.'.join(p.relative_to(ROOT).with_suffix('').parts): p
             for directory in ['Experiments', 'MachCSL', 'Xv6']
             for p in (ROOT / directory).rglob('*.lean')}
    data = {m: p.read_bytes() for m, p in paths.items()}
    graph = {m: imports(b.decode()) for m, b in data.items()}
    hashes = {m: sha(b) for m, b in data.items()}
    ref = subprocess.check_output(['git', 'rev-parse', args.baseline_ref], cwd=ROOT, text=True).strip()
    reports, candidates, historical = {}, defaultdict(list), {}
    for relative in ['Experiments/WholeFunction/results.json', 'Experiments/SolverSurvey/check-results.json']:
        path = ROOT / relative
        obj = json.loads(path.read_text())
        reports[relative] = {'sha256': sha(path.read_bytes()), 'scope': obj.get('scope')}
        samples = obj.get('samples', [])[:]
        integrations = obj.get('production_integrations', {})
        if 'production_integration' in obj:
            integrations = {'copyin': obj['production_integration']}
        samples += [x['check'] for x in integrations.values() if x.get('check')]
        refs = obj.get('references', {})
        if 'reference_copyin' in obj:
            refs = {'copyin': obj['reference_copyin']}
        for k, v in refs.items():
            if v.get('git_revision') == ref:
                historical[k] = v
        for sample in samples:
            module = sample['source'].removesuffix('.lean').replace('/', '.')
            candidates[module].append(dict(sample, timing_manifest=relative))
    timing = {}
    for module in paths:
        choices = candidates.get(module, [])
        valid = [s for s in choices if s.get('sha256') == hashes[module]
                 and s.get('exit_code') == 0
                 and not any(s.get(k) for k in ['incomplete', 'incomplete_proof_detected',
                     'source_changed', 'source_changed_during_check', 'source_changed_after_check'])
                 and seconds(s.get('service_runtime')) is not None]
        if valid:
            s = valid[-1]
            timing[module] = {'seconds': seconds(s['service_runtime']), 'sha256': s['sha256'],
                'manifest': s['timing_manifest'], 'log': s.get('log'), 'peak_mib': s.get('peak_mib'),
                'reported_peak': s.get('peak')}
    def summarize(nodes):
        nodes = sorted(nodes)
        measured = [m for m in nodes if m in timing]
        missing = []
        for m in nodes:
            if m not in timing:
                entries = candidates.get(m, [])
                reason = 'no measurement' if not entries else 'measurement failed, incomplete, source changed, or hash mismatch'
                missing.append({'module': m, 'reason': reason,
                    'available_measurement_hashes': [s.get('sha256') for s in entries]})
        return {'module_count': len(nodes), 'modules': nodes,
                'measured_module_count': len(measured),
                'measured_service_seconds_sum': round(sum(timing[m]['seconds'] for m in measured), 6),
                'complete_measurement_coverage': not missing, 'missing_timings': missing}
    closures = {r: reachable(graph, [r]) for r in ROOTS}
    experiment_closures = {r: {m for m in c if m.startswith('Experiments.')} for r, c in closures.items()}
    union = set.union(*experiment_closures.values()) | set(ROOTS)
    roots = {}
    for root, exp in experiment_closures.items():
        family = root.removeprefix('Xv6.Proof')
        groups = defaultdict(set)
        for m in exp:
            leaf = m.rsplit('.', 1)[-1]
            if m.startswith('Experiments.SolverSurvey.'):
                category = 'solver_survey'
            elif leaf.startswith(family):
                category = 'function_specific'
            elif leaf.startswith(('Copyin', 'Copyout')):
                category = 'cross_function_specific_reuse'
            elif m.startswith('Experiments.WholeFunction.') and (leaf.startswith('Copy') or leaf == 'BinaryCopy'):
                category = 'shared_copy_family_support'
            elif m.startswith('Experiments.WholeFunction.'):
                category = 'shared_kernel_backend'
            else:
                category = 'other_experiment_support'
            groups[category].add(m)
        roots[root] = {'support': summarize(exp), 'support_plus_production_wrapper': summarize(exp | {root}),
            'partition': {k: summarize(v) for k, v in sorted(groups.items())},
            'nonexperiment_imports_cached': sorted(closures[root] - exp - {root})}
        other = next(r for r in ROOTS if r != root)
        roots[root]['additional_modules_if_other_proof_support_cached'] = summarize(
            (exp - experiment_closures[other]) | {root})
    old_graph = dict(graph)
    old_sources = {}
    for root in ROOTS:
        relative = str(paths[root].relative_to(ROOT))
        old = subprocess.check_output(['git', 'show', f'{ref}:{relative}'], cwd=ROOT)
        old_graph[root] = imports(old.decode())
        old_sources[root] = {'git_revision': ref, 'source': relative, 'sha256': sha(old), 'imports': old_graph[root]}
    rev = reverse(graph)
    changes = {}
    for changed in ['Experiments.WholeFunction.CopyoutInvariant',
                    'Experiments.WholeFunction.CopyoutBlockFacts',
                    'Experiments.WholeFunction.KernelReg',
                    'Experiments.WholeFunction.CopyinInvariant', 'Xv6.ProofCopyout']:
        invalid = reachable(rev, [changed])
        affected = invalid & union
        changes[changed] = {'measured_copy_proof_rebuild_subset': summarize(affected),
            'per_root': {r: summarize(invalid & (exp | {r})) for r, exp in experiment_closures.items()},
            'repository_source_consumers': sorted(invalid & set(paths)),
            'production_consumers': sorted(m for m in invalid if m.startswith(('Xv6.', 'MachCSL.'))),
            'outside_measured_copy_closures': sorted((invalid & set(paths)) - union)}
    baselines = {}
    for family in ['Copyin', 'Copyout']:
        root = 'Xv6.Proof' + family
        relative = '.lake/whole-function/' + family.lower() + '-production-integration.json'
        path = ROOT / relative
        record = json.loads(path.read_text()) if path.exists() else {}
        recorded_sha = record.get('baseline_source_sha256', record.get('baseline_sha256'))
        sample = record.get('baseline', {})
        valid = (record.get('baseline_revision') == ref
                 and recorded_sha == old_sources[root]['sha256'])
        runtime = sample.get('runtime_seconds', sample.get('service_seconds'))
        old_invalid = reachable(reverse(old_graph), [root])
        baselines[root] = {'source': old_sources[root], 'sample': sample or None,
            'timing_manifest': relative, 'manifest_sha256': sha(path.read_bytes()) if path.exists() else None,
            'validated_service_seconds': runtime if valid else None,
            'source_hash_and_revision_valid': valid,
            'source_consumers': sorted(old_invalid & set(paths)),
            'production_consumers': sorted(m for m in old_invalid if m.startswith(('Xv6.', 'MachCSL.'))),
            'note': 'Earlier capped standalone cached-import measurement, not a paired run. Historical graph comparison substitutes both old copy proof imports into the current source graph; not a full historical checkout. Downstream consumer costs are unmeasured.'}
    relevant = union | set.union(*(set(x['repository_source_consumers']) for x in changes.values()))
    report = {'method': 'Read-only source-import graph and hash-matched per-module service runtime sums; each distinct module counted once.',
        'limitations': ['Sums estimate serial source elaboration with cached imports, not an observed clean or Lake incremental build.',
            'Cached external imports, Lake scheduling/artifact costs, and Z3 setup are excluded; service runtime excludes waiting for the shared lock.',
            'Module source hashes are checked. Historical timing manifests do not record transitive import artifact hashes; separate suite measurements are estimates, not one clean-build trace.',
            'Import closure conservatively invalidates all source dependents; no claim of semantic minimality.',
            'Shared copy-family support includes domain adapters and binary image data. Shared kernel backend includes test-named modules actually imported; classification is by role, not elimination of proof obligations.',
            'A module may be shared by both functions yet still be function-specific; cross-function support is reported separately.',
            'Missing/invalid timings are not zero-cost modules. Compare totals only where measurement coverage is complete.'],
        'timing_manifests': reports, 'roots': roots, 'distinct_union_with_wrappers': summarize(union),
        'shared_imported_support': summarize(set.intersection(*experiment_closures.values())),
        'incremental_changes': changes, 'historical_monolithic_proofs': baselines,
        'timings': {m: timing[m] for m in sorted(union) if m in timing},
        'source_graph': {m: {'source': str(paths[m].relative_to(ROOT)), 'sha256': hashes[m], 'imports': graph[m]}
                         for m in sorted(relevant) if m in paths},
        'source_graph_sha256': sha(json.dumps({m: [hashes[m], graph[m]] for m in sorted(relevant) if m in paths}, sort_keys=True).encode()),
        'sources_unchanged_during_analysis': all(paths[m].read_bytes() == data[m] for m in relevant if m in paths)}
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    for r, info in roots.items():
        s = info['support_plus_production_wrapper']
        print(r, s['module_count'], s['measured_service_seconds_sum'], 'missing',len(s['missing_timings']))
    print('union', report['distinct_union_with_wrappers']['measured_service_seconds_sum'])
    for m, v in changes.items():
        s = v['measured_copy_proof_rebuild_subset']; print('change',m,s['module_count'],s['measured_service_seconds_sum'],'missing',len(s['missing_timings']))

if __name__ == '__main__':
    main()
