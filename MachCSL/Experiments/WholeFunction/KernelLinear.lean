import Experiments.WholeFunction.KernelStackGraph

/-! Finite binary-row composition. This uses the same mixed-action semantics
and production transfer proof as the CFG engine, but returns a completed trace
certificate so value-sensitive pure trace theorems can discharge the exit.
-/
namespace Xv6.WholeFunction.Linear
open Iris Iris.BI Iris.ProgramLogic MachCSL

inductive RowRun (slots : Nat) : List Binary.Row → Stack.State → Stack.State → Prop
  | nil (s : Stack.State) : RowRun slots [] s s
  | cons {rows : List Binary.Row} {s t u : Stack.State}
      (row : Binary.Row) (a : {a : MixedAction // row.code = a.code}) (cpu : CPU)
      (decode : MixedAction.decode slots row.code = some a)
      (pc : s.pc = row.pc) (step : a.val.Next row.rvc cpu s t)
      (tail : RowRun slots rows t u) : RowRun slots (row :: rows) s u

/-- Pure local safety for every possible successor, including fresh stack
values and each possible migration hart. No spatial WP premise occurs here. -/
def Safe (slots : Nat) : List Binary.Row → Stack.State → Prop
  | [], _ => True
  | row :: rows, s => ∃ a : {a : MixedAction // row.code = a.code},
      MixedAction.decode slots row.code = some a ∧ s.pc = row.pc ∧
        a.val.Enabled s ∧ ∀ cpu t, a.val.Next row.rvc cpu s t → Safe slots rows t

/-- Discharge linear safety with one invariant and per-operation pure laws.
Contiguity supplies all internal PC checks; instructions must really advance
to their row's next PC. Branches require the CFG engine instead. -/
theorem safe_of_invariant (slots : Nat) (rows : List Binary.Row)
    (inv : Stack.State → Prop) (start finish : BitVec 64)
    (contiguous : Binary.contiguous start finish rows = true)
    (laws : ∀ row ∈ rows, ∃ a : {a : MixedAction // row.code = a.code},
      MixedAction.decode slots row.code = some a ∧
      (∀ s, inv s → s.pc = row.pc → a.val.Enabled s) ∧
      (∀ cpu s t, inv s → s.pc = row.pc → a.val.Next row.rvc cpu s t →
        inv t ∧ t.pc = row.next))
    (s : Stack.State) (entry : inv s) (pc : s.pc = start) : Safe slots rows s := by
  induction rows generalizing start s with
  | nil => trivial
  | cons row rows ih =>
    have hc : start = row.pc ∧ Binary.contiguous row.next finish rows = true := by
      simpa only [Binary.contiguous, Bool.and_eq_true, beq_iff_eq] using contiguous
    obtain ⟨a, hd, he, hs⟩ := laws row List.mem_cons_self
    have hp : s.pc = row.pc := pc.trans hc.1
    refine ⟨a, hd, hp, he s entry hp, ?_⟩
    intro cpu t hn
    obtain ⟨ht, hpc⟩ := hs cpu s t entry hp hn
    exact ih row.next hc.2 (fun r hr => laws r (List.mem_cons_of_mem row hr)) t ht hpc

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
variable [CurCtx] [KernelGeom] [KernelImage GF]

/-- Checked finite binary execution returns a complete operational trace to
its spatial continuation. Thus a pure theorem about RowRun can directly
establish the caller's exact register/cell postcondition. -/
theorem wp_rows (slots : Nat) (rows : List Binary.Row) (cpu : CPU) (s : Stack.State)
    (safe : Safe slots rows s) :
    mixedOwn (GF := GF) cpu s ∗ wpNext s.ctx.sie s.ctx.proc cpu (fun cpu' => iprop(
      ∀ t, ⌜RowRun slots rows s t⌝ -∗ mixedOwn cpu' t -∗ wpLoop cpu'))
      ⊢ wpLoop cpu := by
  induction rows generalizing cpu s with
  | nil =>
    iintro ⟨Hstate, Hexit⟩
    ihave Hexit := wpNext_self _ _ cpu _ $$ Hexit
    iapply Hexit $$ %s %(RowRun.nil s) Hstate
  | cons row rows ih =>
    obtain ⟨a, hd, hp, enabled, safeTail⟩ := safe
    unfold mixedOwn regOwn Stack.State.machine
    iintro ⟨⟨⟨#HT, HK, HPC⟩, HF⟩, Hexit⟩
    ihave #HI := row.instr (GF := GF) $$ HT
    rw [← hp, a.property]
    iapply a.val.sound row.rvc cpu s enabled $$ [$HI $HK $HPC $HF Hexit]
    inext
    iapply wpNext_intro_pin
    iintro %cpu' %hpin %t %hn HK HPC HF
    have indices := a.val.indices row.rvc cpu' s t hn
    iapply ih cpu' t (safeTail cpu' t hn) $$ [HT HK HPC HF Hexit]
    isplitl [HK HPC HF]
    · unfold mixedOwn regOwn Stack.State.machine
      iframe HT HK HPC HF
    · rw [indices.1, indices.2]
      iapply wpNext_intro_pin
      iintro %cpu'' %hpin' %u %hr Hstate
      ihave Hexit := wpNext_at _ _ cpu cpu'' _ (fun h => (hpin' h).trans (hpin h)) $$ Hexit
      dsimp only [mixedOwn, regOwn, Stack.State.machine]
      iapply Hexit $$ %u %(RowRun.cons row a cpu' hd hp hn hr) Hstate

end Xv6.WholeFunction.Linear

open Lean in
run_cmd do
  let baseline ← collectAxioms ``Xv6.WholeFunction.MixedAction.sound
  for decl in #[``Xv6.WholeFunction.Linear.safe_of_invariant, ``Xv6.WholeFunction.Linear.wp_rows] do
    let axioms ← collectAxioms decl
    let extra := axioms.filter fun a => !baseline.contains a
    unless extra.isEmpty do throwError "{decl}: new axioms {extra}"
    if axioms.contains ``sorryAx then throwError "{decl}: contains sorryAx"
  logInfo "Linear composition adds no axioms beyond the checked mixed backend."
