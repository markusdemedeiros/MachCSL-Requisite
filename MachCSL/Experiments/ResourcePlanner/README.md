Resource planner pilot
======================

This experiment infers byte-window access paths and linear closing wands from
ordinary Iris entailments. Clients do not name prefix/tail residual predicates.
It does not synthesize program invariants or prove callee contracts.

`Actual.lean` checks two real ownership boundaries using resource definitions,
without importing their existing proofs:

* `writei_kernel_boundary` uses `WiArgs` and `wiSrc`, exposes source/destination
  windows, and restores the PID share, arbitrary frame, original source and
  modified destination for arbitrary same-length returned bytes. This covers
  the kernel-source branch; user-memory fault semantics remain outside this
  pilot.
* `readi_hold_window` has the original `ReadiDefs.rd_hold_win` statement,
  including its extent fact and buffer-hold restoration. The generic planner
  obtains bounds from pure fields inside `bufHold0`, without an extra client
  length assumption. Leading pure conclusions are solved from those facts;
  no separate client extent helper or internal hold-window wrapper remains.

`Rules.lean` proves generic read/write windows using existing split/join laws.
`Planner.lean` matches request atoms to source atoms and emits Iris applications
of those rules. It preserves arbitrary read `DFrac` values; writes require full
ownership. Returned ownership and all closing wands are used linearly. Bounds,
lengths, fractions and final resource reconstruction are checked by Lean.

Two planners solve the same finite injective assignment problem:
`resource_read`/`resource_write` use augmenting paths; their `_smt` counterparts
ask Z3 for an assignment. Z3 is an untrusted subprocess with a query timeout,
inside the existing memory-capped, serialized Lean wrapper. Its answer is
checked against candidate routes and then replayed. Solver output never
provides a proof, resource or permission.

`Checks.lean` tests competing source choices, a bottleneck requiring an
alternative assignment, reordered context/return resources, symbolic offsets,
insufficient bounds/fractions, changed return length, resource duplication and
a deliberately corrupt solver answer. Rejection examples with a fallback
assumption require both tactics to fail before using that assumption.

Current limits are explicit: one window per source atom, syntactic/definitional
address matching, no map-resource planning, no fraction splitting, and no
split-tree planning across an already partitioned buffer. A valid adjacent
split is proved manually after asserting that both planners reject it. Thus
this version does not establish an advantage for an external solver over
ordinary matching.

Run every Lean check through `Experiments/check.sh` with a namespace-correct
output path. The focused benchmark is:

    python3 Experiments/ResourcePlanner/benchmark.py --rounds 3 --output NEW.json

It rotates manual, deterministic and Z3 variants with identical theorem
headers/imports. The manual baseline uses the same window replay rules: this
isolates routing overhead, not the original hand-split Readi proof. Source and
compiled-import closure hashes are checked around each run, axiom arrays must
agree, and service runtime excludes shared-lock waiting and hashing. Shared
rule/planner compilation and complete xv6 rebuilds are excluded. Existing
reports are never overwritten.

Final validation and measurement
-------------------------------

`correctness-final.json` records the checked sources and logs, including the
independent exact-original-contract check with the original minimal instances.
The earlier failed audit is retained; it exposed an accidental `LogG` argument
from sharing Writei's section instance environment. Readi now has its own
minimal section. The checked public clients use only `propext`,
`Classical.choice`, and `Quot.sound`.

The final three-round rotated comparison (`benchmark-final.json`) accepted all
nine samples, with unchanged source/artifact hashes and equal axiom sets:

| Variant | Median service time |
| --- | ---: |
| Manual routing with shared window rules | 2.573 s |
| Deterministic inferred routing | 2.849 s |
| Z3 inferred routing | 2.786 s |

The result demonstrates reduced client routing code, not a performance gain.
The small difference between the two planners is not evidence of a substantive
SMT advantage. Individual samples are in the report. The initial comparison
and its source snapshots remain in `benchmark-initial.json` and
`baseline-source/`; they predate automatic leading-pure conclusions.

To refresh only this pilot's checked modules (after creating the output
directory), run each command through the shared wrapper:

    mkdir -p .lake/build/lib/lean/Experiments/ResourcePlanner
    for name in Rules Planner Actual Checks; do
      bash Experiments/check.sh \
        -o ".lake/build/lib/lean/Experiments/ResourcePlanner/$name.olean" \
        "Experiments/ResourcePlanner/$name.lean"
    done

The solver executable is `.lake/solver-python/bin/z3`; both its hash and the
full source/compiled-import closure are recorded in the benchmark. Production
Writei/Readi files were not modified, and `wiSrcRest` has not been removed from
production: its user-memory fault branch is outside this pilot.
