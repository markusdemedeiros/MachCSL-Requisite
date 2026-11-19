import Experiments.WholeFunction.FrameEffects
import Experiments.WholeFunction.MemoryFrameChecks
import Experiments.WholeFunction.StrncpyFrameDefs

namespace Xv6.WholeFunction.FrameEffects.Checks
open MachCSL LeanRV64D

noncomputable def strncpyBody := Memory.bodyRows Binary.strncpy.rows
  (Binary.strncpy_000 :: StrncpyFrame.saveRows ++ StrncpyFrame.returnRows)

theorem actual_strncpy_mask :
    deriveRowWrites Memory.decodeWrites strncpyBody = some 0x1f800#32 := by binary_rfl

theorem strlen_accepted : Accepts FrameContract.layout 0xe400#32 := by decide
theorem strncpy_accepted : Accepts FrameContract.layout 0x1f800#32 := by decide

/-- The generic ABI bridge consumes the actual client's body-entry context. -/
theorem actual_strncpy_return (entry current : KCtx)
    (frame : CtxFrame 0x1f800#32 (StrncpyFrame.initialMachine entry).ctx current) :
    calleeSaved entry.regs (StrncpyFrame.returnResult entry current).ctx.regs :=
  return_calleeSaved (layout := StrncpyFrame.layout) (by decide) frame

theorem actual_strncpy_a0 (entry current : KCtx)
    (frame : CtxFrame 0x1f800#32 (StrncpyFrame.initialMachine entry).ctx current) :
    current.regs 10#5 = entry.regs 10#5 :=
  body_lookup (layout := StrncpyFrame.layout) frame 10#5 (by decide) (by decide) (by decide)

/-- A new write to unrestored s1 must invalidate the ABI coverage certificate. -/
theorem rejects_unrestored_s1 :
    ¬ Accepts FrameContract.layout (RegMask.union 0x1f800#32 (RegMask.singleton 9#5)) := by decide

theorem rejects_body_sp_write :
    ¬ Accepts FrameContract.layout (RegMask.union 0xe400#32 (RegMask.singleton 2#5)) := by decide

def missingFramePointer : FrameCompiler.Layout := {
  slots := 0, saved := [], popImm := 0, pushImm := 0,
  popOffset := by decide, pushOffset := by decide }

/-- Even an empty body cannot excuse an un-restored frame-pointer prologue. -/
theorem rejects_missing_fp_restore : ¬ Accepts missingFramePointer RegMask.empty := by decide

/-- a0 is caller-saved: ABI coverage alone must not imply STRNCPY's additional
unchanged-a0 contract. A permitted a0 write supplies a concrete counterexample. -/
theorem a0_needs_separate_preservation (entry : KCtx) :
    ∃ current, CtxFrame (RegMask.union 0x1f800#32 (RegMask.singleton 10#5))
      (initialContext FrameContract.layout entry) current ∧
      current.regs 10#5 ≠ entry.regs 10#5 := by
  refine ⟨(initialContext FrameContract.layout entry).setReg 10#5 (entry.regs 10#5 + 1#64), ?_, ?_⟩
  · exact (CtxFrame.of_set _ _ _).weaken (by decide)
  · simp only [KCtx.setReg_regs, RegMap.set_apply, ↓reduceIte]
    bv_omega

end Xv6.WholeFunction.FrameEffects.Checks

open Lean in
run_cmd do
  for decl in #[``Xv6.WholeFunction.FrameEffects.Checks.actual_strncpy_mask,
      ``Xv6.WholeFunction.FrameEffects.Checks.actual_strncpy_return,
      ``Xv6.WholeFunction.FrameEffects.Checks.a0_needs_separate_preservation] do
    let extra := (← collectAxioms decl).filter fun a =>
      !(#[``propext, ``Classical.choice, ``Quot.sound]).contains a
    unless extra.isEmpty do throwError "Frame-effect checks added axioms: {extra}"
  logInfo "Actual ABI masks checked; unrestored callee registers, sp writes and missing frame restoration rejected."
