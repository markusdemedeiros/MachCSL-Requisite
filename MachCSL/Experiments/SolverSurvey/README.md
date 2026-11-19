# Solver experiments

The objective is to make xv6 proofs express the algorithm and its invariants,
with routine arithmetic, collection observations, and register execution handled
by checked automation. Source length alone is not the acceptance criterion.

`audit.py` surveys both production trees. Its counts identify candidate patterns;
they are lexical counts, not timing or proof-coverage measurements. The ranked
angles and existing mechanisms to improve upon are in `report.json`.

## Arithmetic context selection

`SmtSlice.lean` provides `smt_omega` for Nat/Int arithmetic and `bv_smt` for
mixed BitVec/Nat obligations. Z3 selects an unsatisfiable core. Lean's ordinary
`omega` then proves the goal using those hypotheses. The SMT encoding, Z3, and
its answer are **not trusted**; a bad answer cannot bypass replay.

Install the pinned isolated binary with `bash Experiments/SolverSurvey/setup.sh`.
The path is configurable through `smtSlice.solver`. Solver timeout is bounded;
the shared check wrapper additionally caps the entire process group at 4 GiB.
`SmtSliceChecks.lean` checks core selection; `SmtSliceRejects.lean` checks false
claims, deliberately lying solver answers, and tool failure. `ArithmeticClients`
proves actual copy-family arithmetic statements without invoking their old proofs.

First production-client evidence is frozen in `benchmark-initial.json`:

| grep epilogue variant | Seconds | Peak MiB |
|---|---:|---:|
| Original, with 13 manual clearing directives | 16.866 | 478.2 |
| Original solver, clearing directives removed | 26.973 | 1,019.1 |
| SMT selection, clearing directives removed | 19.188 | 449.2 |

These are single samples, including solver IPC and kernel replay. The measured
improvement is resilience to accumulated irrelevant facts. The already tuned
original remains faster. Strncpy, scheduler and uvmcopy trials passed unchanged
statements and axiom audits, but did not establish a speed improvement. Reproduce
with `python3 Experiments/SolverSurvey/benchmark.py --cases grep --rounds 3`.

`SmtLearn.lean` additionally abstracts the selected Nat/Int atoms and proves a
universal lemma in an empty local context. This isolates arithmetic proof
reconstruction from large program expressions. Theorems are indexed by a
canonical arithmetic goal, checked on reuse, and available through imported
`.olean` files. `SmtLearnChecks` and `SmtLearnImport` test renamed terms, missing
premises, changed constants, and replay with no SMT executable. This is a
separate experiment: the first unindexed lookup regressed, and learning the
entire mixed page-phase proof timed out at the normal heartbeat limit.

The learned version is now used in `Xv6/UkGrepLoopFrame.lean`'s epilogue, removing
the 13 manually scheduled clearing directives. Three interleaved samples are
recorded in `benchmark-learn.json`: tuned-original median 15.998 seconds versus
17.447 seconds without manual clearing, with the same theorem/axioms and peak
memory 434.5 versus 421.5 MiB. This accepts about 9% extra local checking time for
context-growth robustness and simpler proof maintenance. It is not a speedup
over the already hand-tuned proof, and is not a recommendation to replace every
`omega` call. Source builds of this module require the pinned Z3 tool above.

## Other engines

* `SolverCache.lean`: external CaDiCaL with checked LRAT, exact-formula theorem
  reuse, optional certificate-file replay, and context slicing. This retains
  Lean `bv_decide`'s existing native-checker trust boundary; it does not claim
  kernel reduction of LRAT. `solver-bench.py` compares cold/repeated/noisy cases
  and checks corrupt certificates and cache-key mismatches.
* `Collections.lean`: valid-index observation proofs for list updates and
  splice identities, using a restricted theorem vocabulary. Seven exact existing
  production statements pass without depending on their old result proofs.
  This improves clarity; the current general solver is slower than bespoke
  proof bodies, so a blanket conversion is not justified.
* `MapOverlay.lean`: lookup-certified finite-map overlays transport submaps and
  domains and reconstruct the complete filesystem byte/cache invariant.
  `MapOverlayChecks` re-proves the actual `byteRange_log_update` spatial contract:
  invariant opening, ghost updates, fractions and masks remain unchanged;
  reconstruction becomes one `cache_splice` application. Exact-type, dependency
  and axiom audits pass, together with wrong-address, wrong-priority and overrun
  rejection checks. The audited client took 3.247 seconds; an isolated upstream
  client took 2.596 seconds. No speed improvement is established.
* `ImageWriteLaws.lean`: two checked state-transition laws connect actual fault
  and source-slice write effects to COPYOUT's semantic trace. They remain
  standalone experiments; the integrated COPYOUT proof does not import them.
* `Block*.lean`: actual binary-derived block outputs checked against semantic
  register/argument postconditions, using the SAT and mixed arithmetic engines.
  The fast fixed-width ABI layer and more expensive Nat-indexed phase layer are
  measured separately. These are independent checks, not additional assumptions
  supplied to the integrated COPYIN proof.

The recommended block experiment is `BlockBridge`: prove the complete
fixed-width `PageABI`, then translate masks/counts at the Nat boundary once.
Its exact original phase claim costs 2.490 + 3.201 = 5.691 seconds across the
machine/bridge modules, versus 25.397 seconds for direct mixed reasoning
(`BlockPhase`). These are single cached-import module samples, not a comparison
against all handwritten code or a whole xv6 build. `BlockAudit` checks the
actual-binary composition and bans dependence on the old copy-specific proof
chain. `BlockRejects` exercises wrong page size, a missing mask premise, and a
wrong physical-source offset.

Run Lean checks only through `bash Experiments/check.sh FILE.lean`, with cached
imports and one serialized worker. Full xv6 builds are not needed for these
experiments. The completed COPYIN compiler and its production integration have
a separate report in `../WholeFunction/results.json`.

The focused correctness run and source hashes are recorded in `check-results.json`. The promoted grep epilogue and its four unchanged
consumers also pass (`production-checks.json`); its original axiom set is
unchanged. Run `python3 Experiments/SolverSurvey/check.py` to refresh the focused
checks. The collection and block engines remain experimental. COPYOUT now uses the arithmetic engine inside its complete binary-derived block
contracts. Its full proof and public production wrapper are checked separately
by the WholeFunction suite. The map-overlay client demonstrates the same
semantic-boundary approach on an actual filesystem invariant update.
