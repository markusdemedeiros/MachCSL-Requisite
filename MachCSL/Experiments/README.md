# Focused layout experiments

Base: `c2a08aa60` (Make MachCSL weakest precondition requisite).
The previous experimental branch is archived as
`archive/requisiteness-experiments-20261118` at `c545be9b4`.
All subsequent simulator, block, loop, sequence and accessor-framework changes
were removed from this branch before starting this experiment. The fifteen
reverted production modules were rechecked, and old experimental oleans were
moved out of the import path. The core MachCSL and requisiteness sources are
unchanged from the base.

The fresh targets are serialized inode/directory records and the inode's
byte-to-field ownership view. Existing encoders, lookup/length laws and codec
equivalences remain authoritative. These tools automate layout reasoning;
they introduce neither another machine interpreter nor another WP theorem.

## Kept

* `Layout.layout_lookup`: deterministic field routing followed by observation
  rewriting. Explicit laws describe opaque fields; byte arithmetic is not
  unfolded. Arithmetic side conditions run without error recovery, so an
  unproved bound rejects the rewrite. A second rewrite pass applies the field
  law after its index has been normalized.
* `LayoutResources.layout_resources`: normalize concatenation, split byte
  ownership using the existing rule, normalize addresses, and apply the supplied
  codec equivalences. Alignment hypotheses and ownership fractions remain
  explicit. This handles both directions of the inode ownership conversion
  without manually calculating each intermediate address.
* `LayoutChecks`: ELF reads survive arbitrary prefix relocation, including
  unsuccessful out-of-bounds reads; a word field composes with a variable-sized
  prefix and tail at an arbitrary fraction. Wrong offsets, missing alignment
  and changing the ownership fraction are rejected. Axiom guards reject proof
  holes and assumptions beyond the existing codec inputs.

The original `Requisiteness/Axioms.lean` and `Coherence.lean` checks are retained
and pass. The large earlier experiment suites remain only on the archive branch.

## Compared and rejected

A first field-lookup implementation used restricted `grind`. It checked, but
raised the inode encoding module's paired median from 2.542 to 4.545 seconds
(79%). That implementation is not retained. Deterministic rewriting avoids
that search cost. Reordering the deterministic rewrite preferences also gave
no encouraging result in a single exploratory check and was not adopted.

## Measurements against the clean base

Three interleaved checks per version, one Lean worker, cached external imports:

| Module | Base median | Retained median | Production lines removed |
|---|---:|---:|---:|
| DinodeEnc | 2.492 s | 2.796 s | 22 |
| DirentEnc | 3.565 s | 3.489 s | 4 |
| DinodeSlot | 4.468 s | 4.197 s | 32 |
| Total of medians | 10.525 s | 10.482 s | 58 |

The aggregate is effectively unchanged; the inode lookup module is still 12%
slower, while its ownership conversion module is 6% faster. This is not a
whole-build speedup. Compiling the two helpers costs another 3.635 seconds
with cached imports. Their 40 Lean lines replace 58 production lines;
55 new test lines make the overall Lean change **+37 lines**. The Python runner,
documentation and raw measurements are counted separately from Lean code.

All eleven targeted modules passed, including three consumers and both base
requisiteness regressions. All nine replaced theorem statements and exact axiom
sets are unchanged. Native bitvector assumptions already present in the codecs
are inherited, not silently treated as standard axioms. The measured run peaked
at 353.8 MiB; every Lean job was capped at 4 GiB. Source lints passed. The source
hashes and raw samples are in [results.json](results.json).

Run `python3 Experiments/measure.py` to freshen the selected modules, audit the
statements/assumptions, and repeat the paired comparison. Run individual checks
through `bash Experiments/check.sh File.lean`. No full xv6 rebuild is required.

Use the lookup tool when layout maintenance or a new observation proof warrants
it; the remaining cost does not justify converting every short handwritten
lookup. The stronger result is the small spatial normalizer: it removes repeated
address and ownership reconstruction directly from record proofs. New layouts
can supply their existing codec laws without defining another accessor algebra.

## Whole-function experiment

`WholeFunction/CopyinComplete.lean` and `CopyoutComplete.lean` prove the unchanged public contracts:

```lean
compiled_copyin (WA : WALKADDR) (VF : VMFAULT) (MM : MEMMOVE) : COPYIN
compiled_copyout (WA : WALKADDR) (VF : VMFAULT) (W : WALK_NOALLOC) (MM : MEMMOVE) : COPYOUT
```

`Xv6/ProofCopyin.lean` now exports `copyin_proof` through this theorem. The
proof covers the actual binary, including zero length, page crossings, successful
and failed faults, partial copies, saved registers, return, and hart migration.
It imports no production `ProofCopyin` proof and assumes no additional body,
loop-invariant, or execution-certificate premise. Its semantic parameters are
exactly the three existing public callee contracts.

`Xv6/ProofCopyout.lean` likewise exports the complete compiled theorem. It
preserves the source buffer's fraction, the exact written image, the writable
prefix at the returned table, and the entry-table failure witness. Its page
permission check fuses the actual nonallocating WALK call with the following
PTE load, then restores page-table ownership. The load is explicitly accounted
for; it is not skipped by the register interpreter. `CopyoutChecks` checks
instruction coverage and rejects incorrect stack sizes and permission masks.

COPYOUT makes reuse concrete: both functions use `KernelDispatch` for actual
instruction/call composition. COPYOUT's public export now uses
`CopyoutRegistryClient`: `KernelCallRegistry` supplies the finite callee registry,
and `KernelCallSites` derives call-row, jump and return evidence from the actual
binary. `Residual` provides generic prefix advancement
and endpoint extraction; COPYOUT instantiates it. `FrameCompiler` generates
COPYOUT's save/restore plans from a register layout, retaining its arbitrary
padding word. Semantic joins and ownership adapters remain explicit. COPYOUT's
seven binary-prefix certificates and arithmetic ABI lemmas use standard Lean
axioms; Z3 selects arithmetic premises and `omega` reconstructs their proofs.

The proof separates algorithm reasoning from generated execution:

* `CopyEffects`/`CopyContracts` describe page extensions, fault zeroing, copied
  prefixes and permissions using actual `UPtd`/`UMem` definitions.
  `CopyinInvariant` states the algorithm's cursor, remaining-length, page and
  failure facts. These are explicit semantic invariants, not automatically
  inferred properties of arbitrary programs.
* `BinaryCopy` certifies the real decoded instruction tables. `KernelSymbolic`
  evaluates their register/control operations with symbolic inputs, checking
  branch cases and rejecting unsupported instructions or exhausted fuel.
  `CopyinPrefix` and `CopyinHeaderPrefix` derive execution into semantic cutpoints;
  unbounded loop composition is handled separately by the guarded CFG rule.
* `CopyCallRegistry` connects the public WALKADDR/VMFAULT/MEMMOVE contracts to
  local effects and ownership. `CopyinCallClosure` proves that each real call
  return reestablishes the algorithm invariant. `KernelFull` and `KernelDispatch`
  provide instruction/call WP composition uniformly, without handwritten
  `ci_page`/`ci_move`/`ci_iter` spatial execution adapters.
* `StackValueWp`, `StackReturn`, `CopyinEntry` and `CopyinBoundary` check the
  complete prologue, epilogue and public entry/exit interface. `CopyinComplete`
  discharges all remaining pure obligations and exports `COPYIN`.

Requisiteness is a **separate checked route**, not the implementation of this
completed compiler. `RequisiteObstruction` proves that exact `ownState` cannot
coexist with the production resource invariant. `RequisiteFootprint` instead
imports operational reasoning through a footprint simulation that borrows the
existing resource interpretation; `RequisiteHart` and `RequisiteExample`
exercise its register-update and migration bookkeeping. The completed COPYIN
compiler uses existing Sail-derived kernel WP rules. Its axiom audit allows
only the inherited instruction/backend axioms, including their existing native
bitvector axioms; the new pure call-closure proof uses standard Lean axioms.

The main evaluation criteria are the unchanged contract, explicit semantic
invariants, readable proof boundaries, reusable execution machinery, checked
solver certificates, and measured checking costs. Source counts are descriptive:
removing the old production body does not mean the compiler and its support code
are free. `family-audit.py` records possible reuse across the copy/page family;
further opportunities beyond COPYOUT are not demonstrated savings for other functions.
Its `--clients --output NEW_REPORT.json` mode compares explicit instruction
steps, spatial tactics, interrupt transport and byte-ownership accessors with
the pinned original proofs. These are lexical authoring-pattern counts over
the complete function-prefix file cohorts, excluding audit modules and shared
engines; they measure neither proof effort nor net code savings.

Run `python3 Experiments/WholeFunction/check.py --baseline` to recheck all modules
in dependency order and record source hashes, runtimes and memory in
`WholeFunction/results.json`. The harness also checks the current production
wrappers, detects whether they use the compiled theorems, and compares their sources with
an explicit git revision (`--baseline-ref`, default `HEAD`). With `--baseline`,
it extracts and checks both historical proofs separately. All Lean jobs use the
serialized 4 GiB, single-worker wrapper and cached external imports. After an
interrupted run, `--resume` reuses only the unchanged successful source prefix.

For a shared-engine edit, `check.py --targets MODULE ... --changed MODULE ...
--output NEW_REPORT.json` refreshes only affected prerequisites of the named
targets, in dependency order across both experiment namespaces. `--list-only`
records the plan without invoking Lean. Affected production prerequisites must
be named explicitly; downstream xv6 callers are not automatically rebuilt.
This mode preserves the default frozen report and rejects source changes during
the run.

Run `python3 Experiments/WholeFunction/audit-copyout.py` to reproduce the
COPYOUT integration audit. It reconstructs the original proof from pinned
revision `818a8b6a6d38d128130fa0aa7e0c0505d6850feb` (override with
`--baseline-ref`), checks it under the same cap, and derives its axiom set anew.
It then checks the current complete theorem, production wrapper and link,
verifies their exact public types and axiom subset, and rejects old proof helpers
in the production import closure. Existing compiled dependencies are required;
the dependency-ordered check above prepares them. Sources, logs and
`audit-copyout-result.json` are saved under `.lake/whole-function`.
The recorded integration measurements are in
[`WholeFunction/copyout-integration.json`](WholeFunction/copyout-integration.json).
That report records the current registry migration and dependency source hashes;
`WholeFunction/copyout-integration-initial.json` preserves the earlier checkpoint.

These are focused checks, **not a clean xv6 build benchmark**. A faster cached
wrapper check does not establish lower total build time: rebuilding the compiler
and function certificates must also be counted. Regression checks cover missing
CFG targets, invalid instruction addresses, wrong source slices, NUL/length
violations, exact-state ownership conflicts, and the completed public theorem.

The source-import audit in `WholeFunction/rebuild-impact.json` counts supporting
modules rather than only wrappers. At the first complete COPYOUT checkpoint,
hash-matched standalone service-time sums were 157.327 seconds for COPYIN's
42 support modules plus wrapper and 217.012 seconds for COPYOUT's 60 support
modules plus wrapper; their distinct union cost 249.192 seconds. Historical
monolithic checks cost 20.633 and 24.367 seconds with their original dependencies
cached. These are serial estimates from separate module checks, not observed
clean builds. They show no rebuild-speed win for the present architecture.
Changing just COPYOUT's invariant invalidates nine measured nodes (23.854 seconds);
31 production consumers outside that measured closure have additional unpriced
cost. `rebuild-impact.py` regenerates the import graph and rejects stale source
hashes when pricing modules. The baseline exposed an avoidable dependency
from COPYOUT's arithmetic bridge into COPYIN's invariant. `CopyArithmetic` now
holds the shared word/count lemmas; changes to `CopyinInvariant` no longer
invalidate COPYOUT. Both production exports now use finite witnessed registries.
Their seven callsites are derived by `checked_callsite` from actual decoder
lookups; obsolete target dispatch and manually reconstructed call entries were
removed. Wrong PCs, targets, return addresses and enabled witnesses are rejected.

`WholeFunction/bundle-results.json` records a controlled packaging experiment:
the same 20 COPYOUT modules checked separately in 66.080 seconds and together in
33.906 seconds. Import-only controls explain the saving. A larger frozen bundle
checked all 55 supporting modules and the complete theorem in 107.584 seconds,
peaking at 938 MiB, versus a source-hash-matched separate-check estimate of
197.338 seconds. Both retain exactly the same 37 instruction-rule axioms.
`bundle_benchmark.py` reproduces these bounded experiments without changing
modular authoring. Bundling trades repeated import cost for coarser invalidation;
it is not enabled for production builds and does not establish a speedup over
the original monolithic proof.

`MemoryModel`/`MemoryActions`/`MemoryCompiler` extend the existing compiler with
resource-aware byte loads and stores, reusing `byteBuf_acc`/`byteBuf_upd`.
`MemoryChecks` exercises actual instruction correspondence, fractional reads,
rejected fractional stores, bounds/address rejection, low-byte updates and
preservation of other buffers. Complete `Strlen.compiled_strlen : STRLEN` and
`Strncpy.compiled_strncpy : STRNCPY` clients have checked with the unchanged
public contracts and no original proof imports. STRNCPY exercises both copying
and zero filling, retaining the original fractional source and exact destination
postcondition. Both production string exports remain unchanged.

The first direct-plan clients are preserved in `StrlenDirectPlanBaseline.json`
and `StrncpyDirectPlanBaseline.json`. They demonstrate backend reuse, not net
concision: STRNCPY initially required 1124 client lines versus the original 672.
`FrameContract` now proves the common two-slot `ra`/`s0` save/restore once for
arbitrary instruction addresses; each client supplies its actual decoder
certificates. Its pure laws use only standard axioms and its spatial importers
add none beyond the existing frame rules. The shared-frame STRNCPY checkpoint
and its refreshed dependency checks are recorded in `string-integration.json`:
the complete public theorem has 37 axioms, a subset of the original 38.

Run `python3 Experiments/WholeFunction/audit-strings.py` to reconstruct pinned
original proofs and audit exact public contracts, axiom subsets, old-proof
independence, and transitive source hashes. `--reuse-baseline` reuses only a
hash-validated original checkpoint. Original cached checks took 4.828 seconds
for STRLEN and 12.195 seconds for STRNCPY. The new STRNCPY final module took
2.423 seconds with its supporting modules cached; this is not a full proof-build
speed comparison.

`MemoryPrefix` now derives register execution directly from decoded rows between
three STRLEN and four STRNCPY semantic cutpoints. Byte operations and loop facts
remain explicit. SUBW/ADDW use the shared register semantics; the separate scalar
backend has been removed. `scalar-regression.json` records the preceding
100-module regression, including both production copy proofs and their links.

`RegisterEffects` derives register write masks from the same decoded body rows.
`MemoryFrame` preserves the complementary registers and stack cells through
register and byte steps; `FrameEffects` discharges the saved-register ABI on
return. Both string clients now keep algorithm facts separate from these frame
facts. Unsupported instructions and understated masks fail closed. ABI
acceptance alone does not imply a function-specific unchanged-a0 requirement;
the checks include a constructive counterexample to that implication.
`client-authoring-effects.json` measures 487 STRLEN and 815 STRNCPY client lines,
excluding audits and shared engines, versus the original 289 and 672. This is
clearer separation and less client bookkeeping, not net source compression.

`prefix-cache-results.json` compares identical actual STRNCPY proof obligations
over three interleaved rounds with fixed dependency sources and compiled imports.
Caching closed, kernel-checked row lookup and decoder evidence reduced median
check time from 15.157 to 12.744 seconds (15.9%). The candidate with caching
disabled took 15.122 seconds. Execution states, cutpoints and postconditions are
not cached. Imported-cache tests reject changed binary tables and false
postconditions; the cache adds no axiom dependencies. This is a local improvement
over the experimental compiler, not a speedup over upstream xv6.

`copyout-prefix-summary.json` records reuse of this frontend in COPYOUT: four
client modules shrink from 834 to 589 lines, removing eight handwritten
instruction records and four composite result-state summaries. Walk, fault,
permission and memmove return paths now generate prefixes into semantic
invariants. Setup, header and page argument summaries remain explicit.
The Blocks module takes 12.214 seconds versus 5.588 before this migration;
the benefit is reduced proof plumbing, not faster checking.
`copyout-prefix-production.json` checks the refreshed complete theorem,
production export and link. No full xv6 rebuild was run.

The focused wrapper requires the service's main process to have exited normally
with status zero. Merely seeing systemd's `Result=success` is insufficient:
an explicitly stopped Lean process can also produce that service result.
`python3 Experiments/check-wrapper-test.py` checks normal, killed, missing and
conflicting termination records with mocked services; it starts no compiler.

The COPYIN migration is now complete as well. `copyin-prefix-production.json`
checks the unchanged public contract and production link after removing the old
`CopyinBlocks`/`CopyinBlockFacts` backend. Actual-row prefixes establish semantic
page, call and return facts directly. The affected authoring layer shrank from
872 to 631 lines; its 13 focused checks took 48.938 seconds. This is a maintenance
improvement, not a demonstrated build-speed gain. `final-block-compatibility.json`
refreshes the retained solver experiments against the new COPYIN invariant.

`AffineResults.json` and `StrlenAffineComparison.json` record the completed
invariant-discovery experiment and its full experimental STRLEN consumer. Three
handwritten scan register equations are replaced by a generated relation table;
actual-row entry, backedge and memory-address proofs certify it universally.
Samples and solver models supply candidates only. Enumeration and Z3 found the
same relations, but enumeration took about 2.5 milliseconds versus Z3's 1.1
seconds, so enumeration is the default. This small grammar does not demonstrate
an SMT advantage. The complete STRLEN contract remains unchanged, with 37
inherited axioms. New shared machinery exceeds the nine client lines removed.

`FrameDeriveResults.json` records a separate, complete static-frame experiment:
five actual layouts, including sparse slots and mixed instruction widths, with
arbitrary scratch values, exact save/restore and ABI checks. All 109 generated
declarations also passed independent kernel replay. Derivation/checking costs
101.745 seconds for the five fixtures; replay plus padding tests costs 9.345
seconds. It remains experimental because this cost is substantial and conditional
save/restore paths are unsupported. Existing frame clients were not migrated.

The resource planner's actual Writei/Readi ownership boundaries, exact original
Readi contract audit, failure tests, and manual/deterministic/Z3 comparisons are
documented in `ResourcePlanner/README.md`. These are ownership-boundary proofs,
not replacements for the complete filesystem functions. They preserve symbolic
read fractions and require full write ownership; returned resources reconstruct
the original frame through checked linear closing wands.
