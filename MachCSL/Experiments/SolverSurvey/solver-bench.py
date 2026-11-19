#!/usr/bin/env python3
"""Serialized, capped cold/reuse/slicing/replay experiments; no lake build.

The six obligations are isolated shapes from CopyLemmas, PlatformFacts,
ProofFlags2perm, Instr and Pte. Repetition and irrelevant multiplication premises
are controlled synthetic stressors, not a claim about their frequency in xv6.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / '.lake/solver-survey'
FAMILIES = [
    ('page_down', '(x : BitVec 64)',
     'x &&& 0xFFFFFFFFFFFFF000#64 = (x >>> 12) <<< 12'),
    ('page_same8', '(x : BitVec 64) (aligned : BitVec.extractLsb\' 0 3 x = 0#3)',
     '(x &&& (~~~4095#64 &&& ~~~0#64) == (x + 8#64 - 1#64) &&& (~~~4095#64 &&& ~~~0#64)) = true'),
    ('flags_shift', '(x : BitVec 64)',
     '(BitVec.signExtend 64 (BitVec.extractLsb\' 0 32 x <<< 3) &&& 8#64) = if x.getLsbD 0 then 8#64 else 0#64'),
    ('flags_branch', '(x : BitVec 64)',
     '(x &&& 2#64 = 0#64) ↔ x.getLsbD 1 = false'),
    ('even_add', '(x y : BitVec 64) (hx : x.getLsbD 0 = false) (hy : y.getLsbD 0 = false)',
     '(x + y).getLsbD 0 = false'),
    ('pte_ppn', '(ppn : BitVec 44) (flags : BitVec 8)',
     'BitVec.extractLsb\' 10 44 (0#10 ++ ppn ++ 0#2 ++ flags) = ppn'),
]


def source(mode, repeats=1, noise=False, disk=None):
    text = 'import Experiments.SolverSurvey.SolverCache\nimport Std.Tactic.BVDecide\nset_option maxHeartbeats 4000000\n'
    if mode == 'noslice':
        text += 'set_option solver_bv.slice false\n'
    if disk is not None:
        text += f'set_option solver_bv.diskCache {json.dumps(str(disk))}\n'
        text += 'set_option solver_bv.cache false\n'
    tactic = 'bv_decide' if mode == 'baseline' else 'solver_bv'
    for i in range(repeats):
        for name, params, claim in FAMILIES:
            if noise:
                params += ' (noise other : BitVec 32) (unused : noise * other = 7#32)'
            text += f'theorem {name}_{i} {params} : {claim} := by {tactic}\n'
    if mode != 'baseline':
        text += '#solver_stats\n'
    return text


def run(label, text, expected_success=True, expected_message=None):
    src = OUT / f'{label}.lean'
    src.write_text(text)
    start = time.monotonic()
    result = subprocess.run(['bash', 'Experiments/check.sh', str(src)], cwd=ROOT,
                            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    elapsed = time.monotonic() - start
    (OUT / f'{label}.log').write_text(result.stdout)
    def field(pattern):
        match = re.search(pattern, result.stdout, re.DOTALL if "statistics" in pattern else 0)
        return match.group(1) if match else None
    record = dict(label=label, source_sha256=hashlib.sha256(text.encode()).hexdigest(),
                  success=result.returncode == 0,
                  expected_success=expected_success, elapsed_with_queue=round(elapsed, 3),
                  runtime=field(r'Service runtime: (.*)'),
                  cpu=field(r'CPU time consumed: (.*)'),
                  memory=field(r'Memory peak: (.*)'),
                  stats=field(r'solver_bv statistics.*?: (\{[^}]*\})'))
    print(json.dumps(record), flush=True)
    if record['success'] != expected_success or (expected_message and expected_message not in result.stdout):
        print(result.stdout, flush=True)
        raise RuntimeError(f'unexpected result: {label}')
    return record


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--rounds', type=int, default=2)
    parser.add_argument('--quick', action='store_true')
    args = parser.parse_args()
    OUT.mkdir(parents=True, exist_ok=True)
    results = []
    for turn in range(args.rounds):
        modes = ['baseline', 'cached', 'noslice'] if turn % 2 == 0 else ['noslice', 'cached', 'baseline']
        for case, repeats, noise in [('cold', 1, False), ('repeated', 4, False), ('noise_stress', 2, True)]:
            if args.quick and case != 'cold':
                continue
            for mode in modes:
                results.append(run(f'{case}-{mode}-{turn}', source(mode, repeats, noise)))
    disk = OUT / f'certs-{time.time_ns()}'
    results.append(run('disk-cold', source('cached', disk=disk)))
    results.append(run('disk-warm', source('cached', disk=disk)))
    certificates = sorted(disk.glob('*.lrat'))
    if not certificates:
        raise RuntimeError('disk test wrote no certificates')
    certificate = certificates[0]
    saved = certificate.read_bytes()
    certificate.write_text('this is not an LRAT certificate\n')
    results.append(run('disk-corrupt', source('cached', disk=disk), False, 'invalid LRAT'))
    certificate.write_bytes(saved)
    certificate.write_text('999999 0 0\n')
    results.append(run('disk-invalid-proof', source('cached', disk=disk), False, 'certificate could not be verified'))
    certificate.write_bytes(saved)
    key = certificate.with_suffix('.key')
    key.write_text('different reflected formula')
    results.append(run('disk-wrong-key', source('cached', disk=disk), False, 'disk cache key mismatch'))
    imported = '''import Experiments.SolverSurvey.SolverChecks
example (renamed : BitVec 64) :
    renamed &&& 0xFFFFFFFFFFFFF000#64 = (renamed >>> 12) <<< 12 := by solver_bv
#solver_stats
'''
    results.append(run('imported-cache', imported))
    (OUT / 'results.json').write_text(json.dumps(results, indent=2) + '\n')

if __name__ == '__main__':
    main()
