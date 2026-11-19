import Experiments.WholeFunction.FrameCompiler

/-! Copyout's frame is one layout descriptor: thirteen saved registers plus
one untouched padding cell. Both complete binary frame sequences are compiled
by the shared frame engine. No production ProofCopyout theorem is imported. -/
namespace Xv6.WholeFunction.CopyoutFrame
open Iris Iris.BI Iris.ProgramLogic MachCSL LeanRV64D FrameCompiler
set_option linter.unusedSimpArgs false

def layout : Layout := {
  slots := 14
  saved := [⟨1, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩,
    ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩,
    ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩]
  popImm := 112#12
  pushImm := 3984#12
  popOffset := by decide
  pushOffset := by decide }

def frameCells (entry : KCtx) (padding : BitVec 64) : List Stack.Cell :=
  layout.frameCells entry [padding]

def Frame (entry : KCtx) (cells : List Stack.Cell) : Prop :=
  ∃ padding, cells = frameCells entry padding

def initialMachine (entry : KCtx) (cells : List Stack.Cell) : Stack.State :=
  ⟨(entry.push 14).setReg 8#5 entry.sp, 0x800015e2#64, cells⟩

def returnResult (entry current : KCtx) : Stack.State :=
  ⟨(layout.restore entry current).pop 14, jumpPc (entry.regs 1#5), []⟩

noncomputable def saveRows : List Binary.Row := Binary.copyout.rows.drop 2 |>.take 14
noncomputable def returnRows : List Binary.Row := Binary.copyout.rows.drop 66 |>.take 15

def savePlan : Plan := layout.savePlan 0x800015c6#64
def returnPlan : Plan := layout.returnPlan 0x80001662#64

end Xv6.WholeFunction.CopyoutFrame
