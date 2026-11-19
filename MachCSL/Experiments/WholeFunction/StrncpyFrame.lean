import Experiments.WholeFunction.StrncpyFrameDefs
import Experiments.WholeFunction.FrameContract

namespace Xv6.WholeFunction.StrncpyFrame
open Iris Iris.BI Iris.ProgramLogic MachCSL LeanRV64D FrameCompiler
set_option linter.unusedSimpArgs false

set_option maxHeartbeats 0 in
theorem save_binary : compileRows 2 saveRows = savePlan.map some := by binary_rfl
set_option maxHeartbeats 0 in
theorem return_binary : compileRows 2 returnRows = returnPlan.map some := by binary_rfl

theorem result_a0 (entry current : KCtx) :
    (returnResult entry current).ctx.regs 10#5 = current.regs 10#5 :=
  FrameContract.result_a0 entry current

theorem result_base (entry base : KCtx) (R : RegMap) (available : 2 ≤ base.avail) :
    (returnResult entry ((base.pushed 2).withRegs R)).ctx =
      base.withRegs (returnResult entry ((base.pushed 2).withRegs R)).ctx.regs :=
  FrameContract.result_base entry base R available

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
variable [CurCtx] [KernelGeom] [KernelImage GF]

theorem wp_prologue (cpu : CPU) (entry : KCtx) (available : 2 ≤ entry.avail) :
    kernelText (GF := GF) ∗ kctx cpu entry ∗ pcIs cpu 0x80000e26#64 ∗
      wpNext entry.sie entry.proc cpu (fun cpu' => iprop(
        mixedOwn cpu' (initialMachine entry) -∗ wpLoop cpu'))
      ⊢ wpLoop cpu := by
  have pc : Binary.strncpy_000.pc = 0x80000e26#64 := by binary_rfl
  have hn : Binary.strncpy_000.next = 0x80000e28#64 := by binary_rfl
  have rule := FrameContract.wp_prologue (GF := GF) Binary.strncpy_000 saveRows
    (by binary_rfl) (by rw [hn]; exact save_binary) cpu entry available
  rw [pc, hn] at rule
  exact rule

theorem wp_return (entry current : KCtx) (cpu : CPU) (sp : current.sp = entry.sp - 16#64) :
    mixedOwn (GF := GF) cpu ⟨current, 0x80000e64#64, frameCells entry⟩ ∗
      wpNext current.sie current.proc cpu (fun cpu' => iprop(
        mixedOwn cpu' (returnResult entry current) -∗ wpLoop cpu')) ⊢ wpLoop cpu :=
  FrameContract.wp_return returnRows 0x80000e64#64 return_binary entry current cpu sp

end Xv6.WholeFunction.StrncpyFrame
