import Experiments.WholeFunction.CopyoutCallRegistry
import Experiments.WholeFunction.CopyoutBlocks
import Experiments.WholeFunction.CopyoutFrame

/-! Actual-binary coverage and rejection checks. The one non-stack load is
consumed by the resource-aware WALK summary, not treated as an ordinary step. -/
namespace Xv6.WholeFunction.Copyout.Checks
open MachCSL LeanRV64D
set_option maxHeartbeats 0

/-- Every unsupported mixed row is either one of the four actual calls or
precisely the PTE load handled by CopyCall.walk_load. -/
theorem externally_handled_rows :
    (Binary.copyout.rows.filter fun row =>
      !(MixedAction.decode 14 row.code).isSome).map Binary.Row.pc =
      [0x80001604#64, 0x80001622#64, 0x80001632#64, 0x80001640#64, 0x80001644#64] := by
  binary_rfl

theorem registered_targets :
    Binary.copyout.rows.filterMap (fun row => (LinkedJump.decode row.code).map
      (fun a => row.pc + a.val.imm.signExtend 64)) =
      [KA.«memmove», KA.«walkaddr», KA.«vmfault», KA.«walk»] := by
  binary_rfl

/-- The PTE load cannot be smuggled through the resource-free register engine. -/
example : findMixed 14 0x80001644#64 Binary.copyout.rows = none := by binary_rfl

/-- A frame annotation with the wrong size rejects the actual stack push. -/
example : MixedAction.decode 12 Binary.copyout_002.code = none := by binary_rfl

/-- Clearing the permission mask changes the decoded program. -/
example : Binary.copyout_084.code ≠ (RegAction.andi 0#12 15#5 15#5 (by decide)).code := by
  intro h
  have code : Binary.copyout_084.code = (RegAction.andi 4#12 15#5 15#5 (by decide)).code := by binary_rfl
  rw [code] at h
  cases h

/-- Swapping the read and write permission bits also changes the program. -/
example : Binary.copyout_084.code ≠ (RegAction.andi 2#12 15#5 15#5 (by decide)).code := by
  intro h
  have code : Binary.copyout_084.code = (RegAction.andi 4#12 15#5 15#5 (by decide)).code := by binary_rfl
  rw [code] at h
  cases h

end Xv6.WholeFunction.Copyout.Checks
