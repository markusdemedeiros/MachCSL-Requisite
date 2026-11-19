import Experiments.WholeFunction.CopyinHeaderPrefix

/-! Entry and loop-header facts are established directly by checked symbolic
prefixes over the actual binary. There are no handwritten register summaries. -/
namespace Xv6.WholeFunction.Copyin
open MachCSL LeanRV64D
set_option maxHeartbeats 0

theorem initial_common (i : Inputs) : Common i (initialBody i) := by
  constructor
  · exact .refl _
  · simp [initialBody, Experiments.WholeFunction.Copy.initial]
  · rfl
  · simp [initialBody, StackValues.prologueResult, KCtx.sp, KCtx.setReg_regs, KCtx.push_regs, RegMap.set_apply]
  · simp [initialBody, StackValues.prologueResult, KCtx.setReg_regs, KCtx.push_regs, RegMap.set_apply]
  · rfl
  · intro _; exact ⟨rfl, rfl⟩


/-- The nine actual setup instructions establish the semantic loop header. -/
theorem setup_prefix (i : Inputs) (valid : Valid i) (positive : 0 < i.old.length) :
    Symbolic.Prefix Binary.copyin.rows (fun pc => pc == 0x800016e2#64)
      ⟨(initialBody i).machine.ctx, 0x800016a6#64⟩
      (fun r => Header i (atResult (initialBody i) r)) := by
  symbolic_prefix 9
  refine ⟨?_, rfl, ?_, ?_, Or.inl rfl, ?_⟩
  · apply common_result (initial_common i)
    · rfl
    · simp only [KCtx.setReg_regs, RegMap.set_apply, BitVec.reduceEq, ↓reduceIte]
    · simp only [KCtx.setReg_regs, RegMap.set_apply, BitVec.reduceEq, ↓reduceIte]
  · simpa only [atResult, initialBody, Experiments.WholeFunction.Copy.initial,
      List.length_nil] using positive
  · simpa only [atResult, initialBody, Experiments.WholeFunction.Copy.initial,
      List.length_nil, Nat.add_zero] using i.src.isLt
  · constructor
    all_goals simp [atResult, initialBody, StackValues.prologueResult,
      Experiments.WholeFunction.Copy.initial, KCtx.setReg_regs, KCtx.push_regs,
      RegMap.set_apply, Inputs.src, Inputs.dst, Inputs.size, valid.root, valid.length]

/-- Nonempty public inputs enter the complete body invariant without any
assumption about temporary registers, page mappings or a precomputed result. -/
theorem initial_good (i : Inputs) (valid : Valid i) (positive : 0 < i.old.length) :
    Good i (initialBody i) := by
  obtain ⟨result, certificate, ready⟩ := setup_prefix i valid positive
  apply good_prefix (i := i) (s := initialBody i) (t := atResult (initialBody i) result)
    rfl rfl
  · simpa only [atResult, Stack.State.machine, initialBody, StackValues.prologueResult] using certificate
  · exact header_prefix_good ready

end Xv6.WholeFunction.Copyin

open Lean in
run_cmd do
  for decl in #[``Xv6.WholeFunction.Copyin.header_prefix,
      ``Xv6.WholeFunction.Copyin.header_prefix_good,
      ``Xv6.WholeFunction.Copyin.setup_prefix,
      ``Xv6.WholeFunction.Copyin.initial_good] do
    let extra := (← collectAxioms decl).filter fun a =>
      !(#[``propext, ``Classical.choice, ``Quot.sound]).contains a
    unless extra.isEmpty do throwError "{decl}: nonstandard axioms {extra}"
  logInfo "Actual COPYIN setup/header prefixes use standard axioms only."
