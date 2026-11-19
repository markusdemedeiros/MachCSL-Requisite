import Experiments.WholeFunction.RegisterEffects
import Experiments.WholeFunction.StrlenBinary

/-! Effect certificates for actual binary rows, plus refusal of incomplete
masks and unsupported rows. No claim that this selected list is a whole CFG. -/
namespace Xv6.WholeFunction.RegisterEffectsChecks
open MachCSL LeanRV64D

noncomputable def rows : List Binary.Row :=
  [Binary.strlen_006, Binary.strlen_00e, Binary.strlen_012,
    Binary.strlen_014, Binary.strlen_01c]

/-- Include prologue s0 conservatively rather than assuming a body-PC region. -/
theorem actual_mask : deriveRowWrites decodeRegWrites rows = some 0xA500#32 := by binary_rfl

theorem actual_row_preserves (row : Binary.Row) (member : row ∈ rows)
    (action : RegAction) (decoded : row.code = action.code) (cpu : CPU) (s : RegState) :
    (action.run row.rvc cpu s).ctx = s.ctx.withRegs (action.run row.rvc cpu s).ctx.regs ∧
    (action.run row.rvc cpu s).ctx.regs 9#5 = s.ctx.regs 9#5 := by
  have framed := row_run_frame actual_mask row member action decoded cpu s
  exact ⟨framed.shape, framed.lookup 9#5 (by decide)⟩

/-- The actual a3 write cannot be removed from the certificate. -/
theorem reject_missing_destination :
    deriveRowWrites decodeRegWrites rows ≠ some 0x8500#32 := by
  rw [actual_mask]
  decide

/-- The known byte-load row is rejected by the register-only classifier even
when surrounded by valid register rows; it is never silently ignored. -/
theorem reject_memory_row :
    deriveRowWrites decodeRegWrites [Binary.strlen_00e, Binary.strlen_008, Binary.strlen_01c] =
      none := by binary_rfl

theorem reject_linked_call : decodeRegWrites (.JAL (4#21, .Regidx 1#5)) = none := rfl

/-- Replacing a caller-temporary destination with s1 requires a different mask. -/
theorem reject_callee_clobber :
    ¬ (RegAction.addi 1#12 9#5 10#5 (by decide)).writes.Subset (RegMask.singleton 15#5) := by
  decide

/-- TP-dependent source values do not weaken preservation of other registers. -/
theorem tp_read_frame (cpu : CPU) (s : RegState) :
    CtxFrame (RegMask.singleton 15#5) s.ctx
      ((RegAction.addi 0#12 15#5 4#5 (by decide)).run false cpu s).ctx :=
  RegAction.run_frame (.addi 0#12 15#5 4#5 (by decide)) false cpu s

end Xv6.WholeFunction.RegisterEffectsChecks

open Lean in
run_cmd do
  for name in #[``Xv6.WholeFunction.RegisterEffectsChecks.actual_mask,
      ``Xv6.WholeFunction.RegisterEffectsChecks.actual_row_preserves,
      ``Xv6.WholeFunction.RegisterEffectsChecks.reject_missing_destination,
      ``Xv6.WholeFunction.RegisterEffectsChecks.reject_memory_row,
      ``Xv6.WholeFunction.RegisterEffectsChecks.reject_linked_call,
      ``Xv6.WholeFunction.RegisterEffectsChecks.reject_callee_clobber,
      ``Xv6.WholeFunction.RegisterEffectsChecks.tp_read_frame] do
    let extra := (← collectAxioms name).filter fun a =>
      !(#[``propext, ``Classical.choice, ``Quot.sound]).contains a
    unless extra.isEmpty do throwError "{name}: unexpected axioms {extra}"
  logInfo "Actual-row effects and mutation rejections: standard axioms only."
