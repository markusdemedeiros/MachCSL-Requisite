import Experiments.WholeFunction.FrameDeriveFrontend
import Experiments.WholeFunction.FrameDeriveFixtures
import Lean.Util.CollectAxioms

namespace Xv6.WholeFunction.FrameDerive.Checks
open MachCSL Fixtures
set_option maxHeartbeats 0

noncomputable def strncpy : Certificate strncpyPush strncpySaveRows strncpyReturnRows := by derive_frame

example : strncpy.layout.slots = 2 := rfl
example : strncpy.saved = [(0, 1#5), (1, 8#5)] := rfl

noncomputable def copyin : Certificate copyinPush copyinSaveRows copyinReturnRows := by derive_frame
noncomputable def copyout : Certificate copyoutPush copyoutSaveRows copyoutReturnRows := by derive_frame
noncomputable def consoleread : Certificate consolereadPush consolereadSaveRows consolereadReturnRows := by derive_frame
noncomputable def kexec : Certificate kexecPush kexecSaveRows kexecReturnRows := by derive_frame

example : copyin.layout.slots = 12 := rfl
example : copyout.layout.slots = 14 := rfl
example : consoleread.layout.slots = 12 := rfl
example : consoleread.saved.map Prod.fst = [0,1,2,3,4,5,7,8] := rfl
example : kexec.layout.slots = 68 := rfl
example : kexec.saved.map Prod.fst = [0,1,2,3] := rfl
example : kexec.savePlan.map (fun row => row.2.1) = [false,false,false,false,true] := rfl
example : kexec.returnPlan.map (fun row => row.2.1) = [false,false,false,false,false,true] := rfl

/-- A missing RA save cannot masquerade as a complete frame. -/
example : True := by
  fail_if_success
    have bad : Certificate strncpyPush (strncpySaveRows.drop 1) strncpyReturnRows := by derive_frame
  trivial

/-- A restore from the wrong frame size is rejected. -/
example : True := by
  fail_if_success
    have bad : Certificate copyinPush copyinSaveRows strncpyReturnRows := by derive_frame
  trivial

/-- Conditional entry instructions do not become static save actions. -/
example : True := by
  fail_if_success
    have bad : Certificate copyinPush (Binary.copyin_000 :: copyinSaveRows) copyinReturnRows := by derive_frame
  trivial

/-- Actual rows in a discontinuous order cannot produce a safety proof. -/
example : True := by
  fail_if_success
    have bad : Certificate strncpyPush
      [Binary.strncpy_004, Binary.strncpy_002, Binary.strncpy_006] strncpyReturnRows := by derive_frame
  trivial

/-- ABI coverage must include every callee-saved body destination. -/
example : FrameEffects.Accepts strncpy.layout (RegMask.singleton 10#5) := by decide
example : ¬ FrameEffects.Accepts strncpy.layout (RegMask.singleton 9#5) := by decide
example : ¬ FrameEffects.Accepts copyout.layout (RegMask.singleton 2#5) := by decide
example : ¬ FrameEffects.Accepts consoleread.layout (RegMask.singleton 21#5) := by decide

end Xv6.WholeFunction.FrameDerive.Checks

open Lean in
run_cmd do
  let baseline ← collectAxioms ``Xv6.WholeFunction.FrameCompiler.wp_push_plan
  for name in #[``Xv6.WholeFunction.FrameDerive.save_run,
      ``Xv6.WholeFunction.FrameDerive.return_run,
      ``Xv6.WholeFunction.FrameDerive.return_abi,
      ``Xv6.WholeFunction.FrameDerive.wp_save,
      ``Xv6.WholeFunction.FrameDerive.wp_return,
      ``Xv6.WholeFunction.FrameDerive.Checks.strncpy,
      ``Xv6.WholeFunction.FrameDerive.Checks.copyin,
      ``Xv6.WholeFunction.FrameDerive.Checks.copyout,
      ``Xv6.WholeFunction.FrameDerive.Checks.consoleread,
      ``Xv6.WholeFunction.FrameDerive.Checks.kexec] do
    let axioms ← collectAxioms name
    let extra := axioms.filter fun ax => !baseline.contains ax
    unless extra.isEmpty do throwError "{name}: additional axioms {extra}"
    if axioms.contains ``sorryAx then throwError "{name}: contains sorryAx"
  logInfo "Derived static frames, sparse padding, mixed widths and ABI rejection checks: no new axioms."

