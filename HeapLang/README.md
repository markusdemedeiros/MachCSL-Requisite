# Req

A Lean formalization of semantic requisiteness for HeapLang, using the unchanged
[Iris-Lean](https://github.com/leanprover-community/iris-lean) dependency.
Uses Lean 4.35.0 and Iris-Lean `v4.35.0`; exact dependency revisions are recorded
in `lake-manifest.json`.

Run from the `HeapLang/` directory:

```sh
lake build
lake env lean tests/Axioms.lean
```

Import `Req` to use the library.

## Results

- `Req.HeapLang.wp_requisiteness`: operational adequacy in a state implies
  semantic `WP` from ownership of that state. Supports concurrency and all
  HeapLang operations, including prophecy creation and nested resolution.
- `Req.HeapLang.wp_requisiteness_nopre`: adequacy in every state gives `WP`
  with no resource precondition.
- `Req.HeapLang.wp_requisiteness_nofork`: for sequential executions, returns
  ownership of the final local state and a postcondition about both value and state.

The concurrent results require the usual HeapLang ghost resources and a ghost map
for thread expressions (`GhostMapG GF Nat Exp H` for a lawful finite-map type `H`).
The sequential theorem does not require the thread ghost map.

## Proof organization

[Req/Requisiteness.lean](Req/Requisiteness.lean) defines `StateSimulation`, an
observation-aware version of the paper's `StateUpd` condition, and proves the
generic concurrent and sequential requisiteness theorems. The concurrent proof
uses a shared invariant, thread tokens, and Löb induction. Both proofs use semantic
WP lifting directly; neither invokes the upstream completeness theorem.

[Req/HeapLang.lean](Req/HeapLang.lean) supplies the HeapLang instance. Its
`ownState` predicate owns every heap entry, including tombstones, and a prophecy
token with an existentially hidden prediction list for each allocated prophecy.
Agreement with the physical interpretation provides the information needed for
step matching. `base_update` covers every base reduction; evaluation-context
lifting then establishes `heapLangStateSimulation`.

The implementation uses empty-mask updates for state simulation and a timeless
local ownership predicate. The local prophecy predictions are existentially
hidden rather than indexed by a common observation trace as in the Rocq source.
The physical interpretation still tracks and consumes the exact observation trace.

[tests/Axioms.lean](tests/Axioms.lean) checks the transitive axioms of the generic
results, HeapLang step simulation, and public endpoints. Only `propext`,
`Classical.choice`, and `Quot.sound` are permitted. There are no `sorry` proofs or
new axioms.

## References and attribution

The proof follows §10 and Appendix B of
[Completeness of Iris-Based Program Logics](https://iris-project.org/pdfs/2026-icfp-completeness.pdf)
and the accompanying
[Rocq development](https://gitlab.mpi-sws.org/johannes/iris-completeness/-/tree/0a0dd8ae249069eb2b4b78774649d0cd0b5c7b0c/theories/framework/requisite).
The adapted proof modules retain the source attribution and BSD 3-Clause terms
in [LICENSE.iris-completeness](LICENSE.iris-completeness).

A prose explanation is in [requisiteness-heaplang.md](requisiteness-heaplang.md).
