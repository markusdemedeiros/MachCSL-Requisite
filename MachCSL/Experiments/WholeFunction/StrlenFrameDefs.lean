import Experiments.WholeFunction.FrameCompiler
import Experiments.WholeFunction.StrlenBinary

/-! STRLEN's exact two-cell frame and actual save/restore sequences. -/
namespace Xv6.WholeFunction.StrlenFrame
open Iris Iris.BI Iris.ProgramLogic MachCSL LeanRV64D FrameCompiler
set_option linter.unusedSimpArgs false

def layout : Layout := {
  slots := 2
  saved := [⟨1, by decide⟩, ⟨8, by decide⟩]
  popImm := 16#12
  pushImm := 4080#12
  popOffset := by decide
  pushOffset := by decide }

def frameCells (entry : KCtx) : List Stack.Cell := layout.frameCells entry []

def initialMachine (entry : KCtx) : Stack.State :=
  ⟨(entry.push 2).setReg 8#5 entry.sp, 0x80000eaa#64, frameCells entry⟩

def returnResult (entry current : KCtx) : Stack.State :=
  ⟨(layout.restore entry current).pop 2, jumpPc (entry.regs 1#5), []⟩

noncomputable def saveRows : List Binary.Row := Binary.strlen.rows.drop 1 |>.take 3
noncomputable def returnRows : List Binary.Row := Binary.strlen.rows.drop 12 |>.take 4

def savePlan : Plan := layout.savePlan 0x80000ea4#64
def returnPlan : Plan := layout.returnPlan 0x80000ec2#64

end Xv6.WholeFunction.StrlenFrame
