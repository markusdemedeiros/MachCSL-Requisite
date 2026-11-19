import Experiments.WholeFunction.MemoryFrame
import Experiments.WholeFunction.StrlenFrameDefs
import Experiments.WholeFunction.StrncpyFrameDefs

/-! Full actual non-frame string tables exercise the mask frontend at the
ordinary checker recursion limit. Expected constants below are test oracles,
not mask inputs supplied to the generator. -/
namespace Xv6.WholeFunction.RegisterEffectsFrontendChecks
open MachCSL LeanRV64D

noncomputable def strlenRows : List Binary.Row :=
  Memory.bodyRows Binary.strlen.rows
    (Binary.strlen_000 :: StrlenFrame.saveRows ++ StrlenFrame.returnRows)
noncomputable def strncpyRows : List Binary.Row :=
  Memory.bodyRows Binary.strncpy.rows
    (Binary.strncpy_000 :: StrncpyFrame.saveRows ++ StrncpyFrame.returnRows)

noncomputable def strlenEffects : RowEffects Memory.decodeWrites strlenRows := by derive_effects
noncomputable def strncpyEffects : RowEffects Memory.decodeWrites strncpyRows := by derive_effects

theorem strlen_value : strlenEffects.writes = 0xe400#32 := rfl
theorem strncpy_value : strncpyEffects.writes = 0x1f800#32 := rfl

theorem strlen_checked : deriveRowWrites Memory.decodeWrites strlenRows = some strlenEffects.writes :=
  strlenEffects.checked

theorem strncpy_checked : deriveRowWrites Memory.decodeWrites strncpyRows = some strncpyEffects.writes :=
  strncpyEffects.checked

/-- A byte instruction cannot acquire an empty mask through a register-only
classifier. Failure must occur inside the tactic, not deferred kernel checking. -/
example : True := by
  fail_if_success
    have bad : RowEffects decodeRegWrites [Binary.strlen_008] := by derive_effects
  trivial

/-- A whole function's unhandled stack instructions also reject derivation. -/
example : True := by
  fail_if_success
    have bad : RowEffects Memory.decodeWrites Binary.strlen.rows := by derive_effects
  trivial

/-- Closed masks are inferred without a prescribed hexadecimal result. -/
noncomputable def prologueWrite : RowEffects decodeRegWrites [Binary.strlen_006] := by derive_effects

theorem prologue_value : prologueWrite.writes = RegMask.singleton 8#5 := by decide

/-- Open input data is intentionally outside this closed-row frontend. -/
example (rows : List Binary.Row) : True := by
  fail_if_success
    have bad : RowEffects Memory.decodeWrites rows := by derive_effects
  trivial

end Xv6.WholeFunction.RegisterEffectsFrontendChecks

open Lean in
run_cmd do
  for name in #[``Xv6.WholeFunction.RegisterEffectsFrontendChecks.strlenEffects,
      ``Xv6.WholeFunction.RegisterEffectsFrontendChecks.strncpyEffects,
      ``Xv6.WholeFunction.RegisterEffectsFrontendChecks.strlen_checked,
      ``Xv6.WholeFunction.RegisterEffectsFrontendChecks.strncpy_checked,
      ``Xv6.WholeFunction.RegisterEffectsFrontendChecks.prologueWrite] do
    let extra := (← collectAxioms name).filter fun a =>
      !(#[``propext, ``Classical.choice, ``Quot.sound]).contains a
    unless extra.isEmpty do throwError "{name}: unexpected axioms {extra}"
  logInfo "Derived actual string masks: compact literals, kernel replay, no native axioms."
