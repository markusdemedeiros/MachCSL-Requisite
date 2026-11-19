#!/usr/bin/env python3
"""Untrusted discovery from Lean-generated observations; output requires Lean replay.

Z3 and enumeration search exactly the same affine grammar and training rows.
This does not execute instructions or import existing register invariants.
"""
import argparse
import fcntl
import hashlib
import itertools
import json
import re
import resource
import subprocess
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
MODULUS = 2 ** 64
Z3_HASH = 'bbea82f99718e57d939db27db7a6e3afb2dfdee4bd11dd0858e5cfefbdf80fa1'
ANCHOR = range(-1, 2)
COUNTER = range(-2, 3)
OFFSET = range(-4, 5)


def matches(rule, observation, register):
    a, b, c = rule
    return (a * observation['base'] + b * observation['iteration'] + c) % MODULUS == observation['registers'][register]


def enumerate_candidates(observations):
    return {r: [list(rule) for rule in itertools.product(ANCHOR, COUNTER, OFFSET)
                if all(matches(rule, s, r) for s in observations)] for r in range(32)}


def z3_candidates(observations):
    solver = ROOT / '.lake/solver-python/bin/z3'
    if hashlib.sha256(solver.read_bytes()).hexdigest() != Z3_HASH:
        raise RuntimeError('pinned Z3 executable changed')
    lines = ['(set-option :timeout 3000)', '(set-option :memory_max_size 256)', '(set-logic QF_LIA)']
    for r in range(32):
        lines += [f'(declare-const a{r} Int)', f'(declare-const b{r} Int)',
                  f'(declare-const c{r} Int)', f'(declare-const h{r} Bool)',
                  f'(assert (and (<= -1 a{r}) (<= a{r} 1) (<= -2 b{r}) (<= b{r} 2) (<= -4 c{r}) (<= c{r} 4)))']
        for s in observations:
            expression = f'(mod (+ (* a{r} {s["base"]}) (* b{r} {s["iteration"]}) c{r}) {MODULUS})'
            lines.append(f'(assert (=> h{r} (= {expression} {s["registers"][r]})))')
    # Independent candidate families; maximizing coverage asks for every
    # register admitting a candidate, not a hand-selected list of roles.
    lines += ['(maximize (+ ' + ' '.join(f'(ite h{r} 1 0)' for r in range(32)) + '))', '(check-sat)']
    names = ' '.join(f'h{r} a{r} b{r} c{r}' for r in range(32))
    lines.append(f'(get-value ({names}))')
    query = '\n'.join(lines) + '\n'
    result = subprocess.run([str(solver), '-in', '-smt2'], input=query, text=True,
                            capture_output=True, timeout=5, check=True)
    if not result.stdout.startswith('sat\n'):
        raise RuntimeError('solver did not finish candidate search: ' + result.stdout)
    values = {}
    for name, value in re.findall(r'\(([habc]\d+)\s+(true|false|-?\d+|\(-\s+\d+\))\)', result.stdout):
        values[name] = value if value in ['true', 'false'] else int(value.replace('(', '').replace(')', '').replace(' ', ''))
    candidates = {}
    for r in range(32):
        if values.get(f'h{r}') == 'true':
            rule = [values[f'a{r}'], values[f'b{r}'], values[f'c{r}']]
            if not all(matches(rule, s, r) for s in observations):
                raise RuntimeError('model failed independent sample validation')
            candidates[r] = rule
    return candidates, query, result.stdout


def main():
    # This cap covers this driver and inherited Z3 children, independently of
    # the capped Lean wrapper. No solver call or compilation runs in parallel.
    resource.setrlimit(resource.RLIMIT_AS, (512 * 1024 ** 2, 512 * 1024 ** 2))
    resource.setrlimit(resource.RLIMIT_CPU, (20, 20))
    lock = (ROOT / '.lake/focused-experiments.lock').open('a')
    fcntl.flock(lock, fcntl.LOCK_EX)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--log', type=Path, default=ROOT / '.lake/whole-function/affine-samples.log')
    parser.add_argument('--report', type=Path, default=ROOT / '.lake/whole-function/affine-discovery.json')
    parser.add_argument('--backend', choices=['enumeration', 'z3'], default='enumeration')
    parser.add_argument('--compare', action='store_true', help='also measure the comparative Z3 backend')
    args = parser.parse_args()
    samples = []
    for line in args.log.read_text().splitlines():
        if line.startswith('AFFINE_SAMPLES '):
            samples.extend(json.loads(line.removeprefix('AFFINE_SAMPLES ')))
    if len(samples) != 24:
        raise RuntimeError(f'expected 24 actual-prefix observations, got {len(samples)}')
    training = [s for s in samples if s['iteration'] <= 2 and s['base'] < 2 ** 63]
    holdout = [s for s in samples if s not in training]
    started = time.perf_counter()
    enumerated = enumerate_candidates(training)
    enum_seconds = time.perf_counter() - started
    expected = {r: rules[0] for r, rules in enumerated.items() if len(rules) == 1}
    if any(len(rules) > 1 for rules in enumerated.values()):
        raise RuntimeError('ambiguous training data; refusing arbitrary candidate selection')
    candidates, query, response, z3_seconds = expected, None, None, None
    if args.backend == 'z3' or args.compare:
        started = time.perf_counter()
        discovered, query, response = z3_candidates(training)
        z3_seconds = time.perf_counter() - started
        if discovered != expected:
            raise RuntimeError('solver and exhaustive grammar enumeration disagree')
        if args.backend == 'z3':
            candidates = discovered
    if not all(matches(rule, s, r) for r, rule in candidates.items() for s in holdout):
        raise RuntimeError('held-out actual-prefix observations rejected candidate')
    source = '/- Generated by affine-synthesize.py; untrusted until AffineReplay checks it. -/\n'
    source += 'import Experiments.WholeFunction.AffineCore\n\nnamespace Xv6.WholeFunction.Affine\n\n'
    source += 'def inferred : List Rule := [\n'
    source += ',\n'.join(f'  ⟨{r}#5, {a}, {b}, {c}⟩' for r, (a,b,c) in sorted(candidates.items()))
    source += ']\n\nend Xv6.WholeFunction.Affine\n'
    output = ROOT / 'Experiments/WholeFunction/AffineCandidates.lean'
    if not output.exists() or output.read_text() != source:
        output.write_text(source)
    report = dict(scope='Untrusted candidate discovery; finite samples are not a proof',
                  grammar=dict(anchor=list(ANCHOR), counter=list(COUNTER), offset=list(OFFSET), modulus=MODULUS),
                  backend=args.backend, training_count=len(training), holdout_count=len(holdout), candidates=candidates,
                  enumeration_seconds=enum_seconds, z3_seconds=z3_seconds,
                  solver_sha256=Z3_HASH, query=query, response=response,
                  driver_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  samples_sha256=hashlib.sha256(args.log.read_bytes()).hexdigest(),
                  generated_sha256=hashlib.sha256(output.read_bytes()).hexdigest())
    args.report.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: report[k] for k in ['candidates','training_count','holdout_count','enumeration_seconds','z3_seconds']}, indent=2))


if __name__ == '__main__':
    main()
