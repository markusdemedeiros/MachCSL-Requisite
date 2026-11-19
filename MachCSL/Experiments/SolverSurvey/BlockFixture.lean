import Experiments.WholeFunction.CopyinInvariant
import Experiments.WholeFunction.MemoryPrefix

/-! Independent historical solver benchmark oracle. The explicit page/move
contexts below are test fixture costs, not production proof deletion savings.
The page oracle is checked against the real binary by the current generic
symbolic-prefix frontend; no old handwritten runUntil script is retained. -/
namespace Experiments.SolverSurvey.Block.Fixture
open Xv6.WholeFunction MachCSL LeanRV64D

def pageCandidate (k : KCtx) : BitVec 64 :=
  (k.regs 19#5 - k.regs 18#5) + k.regs 22#5

def pageBranch (k : KCtx) : Bool := bcond .BGEU (k.regs 20#5) (pageCandidate k)

def pagePrefix (k : KCtx) : KCtx :=
  (k.setReg 9#5 (k.regs 19#5 - k.regs 18#5)).setReg 9#5 (pageCandidate k)

def pageSelected (k : KCtx) : KCtx :=
  if pageBranch k then pagePrefix k
  else (pagePrefix k).setReg 9#5 (0#64 + k.regs 20#5)

def pageTail (k : KCtx) : KCtx :=
  let k1 := k.setReg 11#5 (k.regs 18#5 - k.regs 19#5)
  let k2 := k1.setReg 12#5 ((k1.regs 9#5 + 0#64).extractLsb' 0 32 |>.signExtend 64)
  let k3 := k2.setReg 11#5 (k2.regs 11#5 + k2.regs 10#5)
  k3.setReg 10#5 (0#64 + k3.regs 21#5)

def pageResult (k : KCtx) : RegState := ⟨pageTail (pageSelected k), 0x800016d0#64⟩

def movedCtx (k : KCtx) : KCtx :=
  ((k.setReg 20#5 (k.regs 20#5 - k.regs 9#5)).setReg 21#5
    (k.regs 21#5 + k.regs 9#5)).setReg 18#5 (k.regs 19#5 + k.regs 22#5)

def moveDone (k : KCtx) : Bool := bcond .BEQ ((movedCtx k).regs 20#5) 0#64

def bodyCuts (pc : BitVec 64) : Bool := pc == 0x800016d0#64

set_option maxHeartbeats 0 in
theorem page_certificate (k : KCtx) :
    Symbolic.Certificate Binary.copyin.rows bodyCuts
      ⟨k, 0x800016b8#64⟩ ⟨pageResult k, .cut⟩ := by
  have result : Symbolic.Prefix Binary.copyin.rows bodyCuts
      ⟨k, 0x800016b8#64⟩ (fun r => r = pageResult k) := by
    symbolic_prefix 9
    all_goals simp_all [pageResult, pageTail, pageSelected, pagePrefix, pageBranch,
      pageCandidate, KCtx.setReg_regs, RegMap.set_apply]
  obtain ⟨r, cert, rfl⟩ := result
  exact cert

end Experiments.SolverSurvey.Block.Fixture
