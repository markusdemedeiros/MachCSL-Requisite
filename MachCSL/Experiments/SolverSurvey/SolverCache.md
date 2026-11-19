# Cached CaDiCaL/LRAT prototype

`SolverCache.lean` adds `solver_bv` around Lean 4.34.1's existing CaDiCaL/LRAT
backend. It is supplemental infrastructure for repeated obligations, not a new
SMT theory or evidence of an end-to-end xv6 speedup. The installed bundled
CaDiCaL version was 2.1.2. The earlier archived cache concerned decoded
instructions; this prototype caches reflected UNSAT proofs.

The pipeline drops context declarations disconnected from the conclusion,
runs Lean's standard proof-producing BV normalization/reflection, then looks up
the complete closed reflected formula in a hash map. Exact expression equality
is checked after hashing. New formulas use the existing AIG/CNF bitblaster,
external CaDiCaL, and LRAT checker. Checked auxiliary theorems are exported in
`.olean` files, so renamed instances can reuse a proof across modules without
rerunning the external solver or native certificate checker.

The dependency closure precomputes each declaration's dependencies and stops at
a fixed point. The existing bitblaster supplies AIG sharing; this code does not
claim a new DAG optimizer or width-reduction procedure. A synchronous environment
extension makes preceding theorem results available, which can block parallel
elaboration. Measurements here deliberately use the project's serialized checks.

## Trust and failure behavior

CaDiCaL is untrusted. As with the repository's existing `bv_decide`, native
execution of the verified LRAT checker introduces a closed Boolean-equation
axiom asserting `verifyBVExpr formula certificate = true`. This is **not** a
kernel-reduced LRAT checker. Final reflection and cache reuse are kernel checked
relative to that existing native-checker boundary.

`SolverChecks.lean` checks the actual types of collected axioms: only the three
standard axioms and closed `verifyBVExpr ... = true` equations are accepted.
The renamed page-mask proof has exactly the original proof's axiom set.
The tests also exercise 32/64-bit formulas, retained necessary assumptions, wrong
masks, missing assumptions, and disconnected contradictory hypotheses.

Slicing deliberately weakens the goal. It can fail when the only way to prove a
goal is a contradiction involving entirely unrelated variables. Use
`set_option solver_bv.slice false in solver_bv` for that case. A cache miss is
normal; a malformed or mismatched disk entry fails closed and is not silently
replaced. Disk replay rechecks the LRAT certificate, and a full manifest match is
required; a filename hash alone never authorizes reuse. Both malformed LRAT and
valid LRAT syntax with an invalid proof were rejected. The prototype's disk
writes assume serialized runs, as used by `Experiments/check.sh`.

## Measurements

Run `python3 Experiments/SolverSurvey/solver-bench.py --rounds 2` after compiling
`SolverCache.lean` and `SolverChecks.lean` with `Experiments/check.sh` and `-o`
paths under `.lake/build/lib/lean/Experiments/SolverSurvey/`. The script itself
uses only the capped serialized check runner. Detailed results and source hashes
are in `solver-bench-results.json`; generated inputs/logs are under
`.lake/solver-survey/`.

The six isolated obligation shapes come from `CopyLemmas.co_pgdown_toNat`,
`PlatformFacts.page_mask_same8`, `ProofFlags2perm`'s shift/mask and branch facts,
`Instr.add_lsb0`, and the normalized PPN extraction in `Pte.ppn_of_mkPte`.
Five need SAT certificates; the PPN extraction normalizes directly. Repetition
and the disconnected 32-bit multiplication premise are synthetic stressors;
these measurements do not assert their frequency in real proof contexts.

Service-runtime medians in seconds over two interleaved runs, excluding lock wait:

| Workload | Existing bv_decide | Cache and slicing | Cache, no slicing |
| --- | ---: | ---: | ---: |
| Six distinct obligations, cold | 1.556 | 1.583 | 1.638 |
| Same six obligations repeated four times | 3.054 | 2.110 | 2.077 |
| Six twice, with disconnected multiplication premise | 2.467 | 1.790 | 2.066 |

The repeated case used five external calls and fifteen theorem-cache hits.
The noisy case removed 36 declarations; slicing contributes a measurable benefit
beyond caching. Peak memory across timing workloads was 168–248 MiB. No resource
cap was approached. CPU time is also retained in the JSON; wall-time reductions
do not imply identical reductions in total CPU work.

A fresh-process disk test changed five external calls into five checked LRAT
replays: 1.561 seconds cold, 1.242 seconds warm. Importing a cached theorem from
`SolverChecks.olean` took 1.081 seconds with one theorem hit and zero external
calls. Cold single-use goals have no demonstrated benefit, so this is not a
reason to replace every existing `bv_decide` call. Domain-aware normalization and
mixed BV/Nat reasoning remain separate work.
