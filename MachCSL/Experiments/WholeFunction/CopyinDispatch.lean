import Experiments.WholeFunction.CopyCallRegistry
import Experiments.WholeFunction.KernelDispatch
import Experiments.WholeFunction.BinaryCopy

/-! COPYIN binary coverage and its shared epilogue cutpoint. Call readiness,
return effects and spatial dispatch are supplied by CopyinRegistryClient. -/
namespace Xv6.WholeFunction.Copyin
open MachCSL

def readLength (s : State) : Nat := (s.machine.ctx.regs 12#5).toNat

def BodyExit (s : State) : Prop := s.machine.pc = 0x80001704#64

end Xv6.WholeFunction.Copyin

namespace Xv6.WholeFunction.Copyin
open MachCSL

/- All sixty-seven actual copyin instructions are classified. This is code
coverage, not a proof that each symbolic state's arguments are ready. -/
set_option maxHeartbeats 0 in
theorem all_rows_classified : Binary.copyin.rows.all (fun row =>
    (MixedAction.decode 12 row.code).isSome || (LinkedJump.decode row.code).isSome) = true := by
  binary_rfl

set_option maxHeartbeats 0 in
theorem ordinary_rows_count :
    (Binary.copyin.rows.filter (fun row => (MixedAction.decode 12 row.code).isSome)).length = 64 := by
  binary_rfl

/- The decoded call registry consists exactly of the three public callees. -/
set_option maxHeartbeats 0 in
theorem registered_targets :
    Binary.copyin.rows.filterMap (fun row => (LinkedJump.decode row.code).map
      (fun a => row.pc + a.val.imm.signExtend 64)) =
      [KA.«memmove», KA.«walkaddr», KA.«vmfault»] := by
  binary_rfl

end Xv6.WholeFunction.Copyin

