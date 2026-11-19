import Experiments.WholeFunction.MemoryPrefix
import Experiments.WholeFunction.BinaryCopy

/-! Register prefixes are generated from the actual COPYOUT rows. The PTE load
is handled by the WALK/LD call adapter; its return enters at 1646. -/
namespace Xv6.WholeFunction.Copyout
open MachCSL LeanRV64D
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

def bodyCuts (pc : BitVec 64) : Bool :=
  pc == 0x80001622#64 || pc == 0x80001632#64 || pc == 0x80001640#64 ||
  pc == 0x80001604#64 || pc == 0x80001662#64

def setupCtx (k : KCtx) : KCtx :=
  let k1 := ((((k.setReg 23#5 (0#64 + k.regs 10#5)).setReg 27#5 (0#64 + k.regs 11#5)).setReg
    20#5 (0#64 + k.regs 12#5)).setReg 22#5 (0#64 + k.regs 13#5)).setReg
      21#5 (0#64 + k.regs 14#5)
  let k2 := (k1.setReg 26#5 ((0xfffff#20 ++ 0#12).signExtend 64)).setReg 25#5 (0#64 + -1#64)
  let k3 := k2.setReg 25#5 (k2.regs 25#5 >>> 26)
  k3.setReg 24#5 ((1#20 ++ 0#12).signExtend 64)

def setupResult (k : KCtx) : RegState := ⟨setupCtx k, 0x80001616#64⟩

def setupCut (pc : BitVec 64) : Bool := pc == 0x80001616#64

def headerPrefix (k : KCtx) : KCtx := k.setReg 9#5 (k.regs 20#5 &&& k.regs 26#5)

def tooHigh (k : KCtx) : Bool := bcond .BLTU (k.regs 25#5) ((headerPrefix k).regs 9#5)

def headerResult (k : KCtx) : RegState :=
  let p := headerPrefix k
  if tooHigh k then ⟨p.setReg 10#5 (0#64 + -1#64), 0x80001662#64⟩ else
    ⟨(p.setReg 11#5 (0#64 + p.regs 9#5)).setReg 10#5 (0#64 + p.regs 23#5), 0x80001622#64⟩

def savePhysical (k : KCtx) : KCtx := k.setReg 19#5 (0#64 + k.regs 10#5)

def nonzero (k : KCtx) : Bool := bcond .BNE (k.regs 10#5) 0#64

def zero (k : KCtx) : Bool := bcond .BEQ (k.regs 10#5) 0#64

def walkArgs (k : KCtx) : KCtx :=
  ((k.setReg 12#5 0#64).setReg 11#5 (0#64 + k.regs 9#5)).setReg 10#5 (0#64 + k.regs 23#5)

def faultArgs (k : KCtx) : KCtx :=
  (((k.setReg 13#5 0#64).setReg 12#5 (0#64 + k.regs 9#5)).setReg
    11#5 (0#64 + k.regs 27#5)).setReg 10#5 (0#64 + k.regs 23#5)

def pageCandidate (k : KCtx) : BitVec 64 := (k.regs 9#5 - k.regs 20#5) + k.regs 24#5

def pageBranch (k : KCtx) : Bool := bcond .BGEU (k.regs 21#5) (pageCandidate k)

def pagePrefix (k : KCtx) : KCtx :=
  (k.setReg 18#5 (k.regs 9#5 - k.regs 20#5)).setReg 18#5 (pageCandidate k)

def pageSelected (k : KCtx) : KCtx :=
  if pageBranch k then pagePrefix k else (pagePrefix k).setReg 18#5 (0#64 + k.regs 21#5)

def moveArgs (k : KCtx) : KCtx :=
  let k1 := k.setReg 10#5 (k.regs 20#5 - k.regs 9#5)
  let k2 := k1.setReg 12#5 ((k1.regs 18#5 + 0#64).extractLsb' 0 32 |>.signExtend 64)
  let k3 := k2.setReg 11#5 (0#64 + k2.regs 22#5)
  k3.setReg 10#5 (k3.regs 10#5 + k3.regs 19#5)

def pageResult (k : KCtx) : RegState := ⟨moveArgs (pageSelected k), 0x80001604#64⟩

def permissionCtx (k : KCtx) : KCtx := k.setReg 15#5 (k.regs 15#5 &&& 4#64)

def readonly (k : KCtx) : Bool := bcond .BEQ ((permissionCtx k).regs 15#5) 0#64

def movedCtx (k : KCtx) : KCtx :=
  ((k.setReg 21#5 (k.regs 21#5 - k.regs 18#5)).setReg 22#5
    (k.regs 22#5 + k.regs 18#5)).setReg 20#5 (k.regs 9#5 + k.regs 24#5)

def moveDone (k : KCtx) : Bool := bcond .BEQ ((movedCtx k).regs 21#5) 0#64

theorem setup_certificate (k : KCtx) :
    Symbolic.Certificate Binary.copyout.rows setupCut
      ⟨k, 0x800015e2#64⟩ ⟨setupResult k, .cut⟩ := by
  suffices h : Symbolic.Prefix Binary.copyout.rows setupCut
      ⟨k, 0x800015e2#64⟩ (fun r => r = setupResult k) from by
    obtain ⟨_, cert, rfl⟩ := h
    exact cert
  symbolic_prefix 10
  all_goals simp_all only [setupResult, setupCtx,
    KCtx.setReg_regs, RegMap.set_apply, BitVec.reduceEq, Bool.false_eq_true,
    ↓reduceIte, BitVec.zero_add, BitVec.add_zero,
    show BitVec.signExtend 64 0#12 = 0#64 from rfl]
  all_goals rfl

theorem header_certificate (k : KCtx) :
    Symbolic.Certificate Binary.copyout.rows bodyCuts
      ⟨k, 0x80001616#64⟩ ⟨headerResult k, .cut⟩ := by
  suffices h : Symbolic.Prefix Binary.copyout.rows bodyCuts
      ⟨k, 0x80001616#64⟩ (fun r => r = headerResult k) from by
    obtain ⟨_, cert, rfl⟩ := h
    exact cert
  symbolic_prefix 5
  all_goals simp_all only [headerResult, tooHigh, headerPrefix,
    KCtx.setReg_regs, RegMap.set_apply, BitVec.reduceEq, Bool.false_eq_true,
    ↓reduceIte, BitVec.zero_add, BitVec.add_zero,
    show BitVec.signExtend 64 0#12 = 0#64 from rfl]
  all_goals rfl

theorem page_certificate (k : KCtx) :
    Symbolic.Certificate Binary.copyout.rows bodyCuts
      ⟨k, 0x8000164a#64⟩ ⟨pageResult k, .cut⟩ := by
  suffices h : Symbolic.Prefix Binary.copyout.rows bodyCuts
      ⟨k, 0x8000164a#64⟩ (fun r => r = pageResult k) from by
    obtain ⟨_, cert, rfl⟩ := h
    exact cert
  symbolic_prefix 10
  all_goals simp_all only [pageResult, moveArgs, pageSelected, pagePrefix, pageBranch, pageCandidate,
    KCtx.setReg_regs, RegMap.set_apply, BitVec.reduceEq, Bool.false_eq_true,
    ↓reduceIte, BitVec.zero_add, BitVec.add_zero,
    show BitVec.signExtend 64 0#12 = 0#64 from rfl]
  all_goals rfl

end Xv6.WholeFunction.Copyout
