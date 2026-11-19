import Experiments.WholeFunction.StrncpyFrame
import Experiments.WholeFunction.StrncpyFacts
import Experiments.WholeFunction.MemoryFrame
import Experiments.WholeFunction.FrameEffects

namespace Xv6.WholeFunction.Strncpy
open Iris Iris.BI Iris.ProgramLogic MachCSL LeanRV64D
open StrncpyFacts

structure Inputs where
  entry : KCtx
  old : List (BitVec 8)
  source : List (BitVec 8)
  n : Nat
  fraction : DFrac

def Inputs.dst (i : Inputs) : BitVec 64 := i.entry.regs 10#5
def Inputs.src (i : Inputs) : BitVec 64 := i.entry.regs 11#5
def Inputs.dstBuffer (i : Inputs) (bytes : List (BitVec 8)) : Memory.Buffer :=
  ⟨i.dst, DFrac.own 1, bytes⟩
def Inputs.srcBuffer (i : Inputs) : Memory.Buffer := ⟨i.src, i.fraction, i.source⟩
def Inputs.buffers (i : Inputs) (bytes : List (BitVec 8)) : List Memory.Buffer :=
  [i.dstBuffer bytes, i.srcBuffer]

structure Valid (i : Inputs) : Prop where
  arg : i.entry.regs 12#5 = BitVec.ofNat 64 i.n
  bound : i.n < 2 ^ 31
  dstLength : i.old.length = i.n
  srcLength : i.n ≤ i.source.length

structure CopyData (i : Inputs) (dst : List (BitVec 8)) (j : Nat) : Prop where
  bound : j ≤ i.n
  nonzero : ∀ x, x < j → i.source[x]? ≠ some 0#8
  content : dst = copied i.source i.old j

structure Written (i : Inputs) (dst : List (BitVec 8)) (j : Nat) (b : BitVec 8) : Prop where
  bound : j < i.n
  nonzero : ∀ x, x < j → i.source[x]? ≠ some 0#8
  lookup : i.source[j]? = some b
  content : dst = copied i.source i.old (j + 1)

structure PadData (i : Inputs) (dst : List (BitVec 8)) (k j : Nat) : Prop where
  nulBound : k < i.n
  lower : k + 1 ≤ j
  bound : j ≤ i.n
  nonzero : ∀ x, x < k → i.source[x]? ≠ some 0#8
  nul : i.source[k]? = some 0#8
  content : dst = padded i.source i.old k j

def copyRegs (i : Inputs) (ctx : KCtx) (j : Nat) : Prop :=
  ctx.regs 11#5 = i.src + BitVec.ofNat 64 j ∧ ctx.regs 12#5 = BitVec.ofNat 64 (i.n - j)

def post (i : Inputs) (dst : List (BitVec 8)) : Prop :=
  dst.length = i.n ∧ ((i.n = 0 ∧ dst = i.old) ∨ (0 < i.n ∧ Xv6.sncPost i.source dst i.n))

theorem CopyData.length {i : Inputs} {dst : List (BitVec 8)} {j : Nat}
    (h : CopyData i dst j) (v : Valid i) : dst.length = i.n := by
  have := h.bound
  have := v.dstLength
  have := v.srcLength
  rw [h.content, copied_length _ _ _ (by omega) (by omega), v.dstLength]

theorem CopyData.finish {i : Inputs} {dst : List (BitVec 8)}
    (h : CopyData i dst i.n) (v : Valid i) : post i dst := by
  refine ⟨h.length v, ?_⟩
  by_cases hz : i.n = 0
  · exact Or.inl ⟨hz, by rw [h.content, hz, copied_zero]⟩
  · exact Or.inr ⟨by omega, h.content ▸ copied_post i.source i.old i.n v.srcLength h.nonzero⟩

theorem Written.more {i : Inputs} {dst : List (BitVec 8)} {j : Nat} {b : BitVec 8}
    (h : Written i dst j b) (nonzero : b ≠ 0#8) : CopyData i dst (j + 1) := by
  refine ⟨by have := h.bound; omega, ?_, h.content⟩
  intro x hx
  by_cases eq : x = j
  · subst x; rw [h.lookup]; simpa using nonzero
  · exact h.nonzero x (by omega)

theorem Written.pad {i : Inputs} {dst : List (BitVec 8)} {j : Nat}
    (h : Written i dst j 0#8) : PadData i dst j (j + 1) :=
  ⟨h.bound, Nat.le_refl _, by have := h.bound; omega, h.nonzero, h.lookup,
    h.content.trans (copied_nul i.source i.old j h.lookup)⟩

theorem PadData.length {i : Inputs} {dst : List (BitVec 8)} {k j : Nat}
    (data : PadData i dst k j) (valid : Valid i) : dst.length = i.n := by
  have hk := data.nulBound
  have hl := data.lower
  have hj := data.bound
  have hs := valid.srcLength
  have hd := valid.dstLength
  rw [data.content, padded_length _ _ _ _ (by omega) (by omega) (by omega), hd]

theorem PadData.finished {i : Inputs} {dst : List (BitVec 8)} {k : Nat}
    (data : PadData i dst k i.n) (valid : Valid i) : post i dst := by
  have hk := data.nulBound
  refine ⟨data.length valid, Or.inr ⟨by omega, ?_⟩⟩
  rw [data.content]
  exact padded_post i.source i.old k i.n data.nulBound data.nonzero data.nul

inductive Control (i : Inputs) (s : Stack.State) (dst : List (BitVec 8)) : Prop
  | read (pc : s.pc = 0x80000e40#64) (j : Nat) (data : CopyData i dst j) (active : j < i.n)
      (regs : copyRegs i s.ctx j) (cursor : s.ctx.regs 15#5 = i.dst + BitVec.ofNat 64 (j + 1))
      (nextCount : s.ctx.regs 13#5 = BitVec.ofNat 64 (i.n - (j + 1)))
      (padCount : s.ctx.regs 16#5 = BitVec.ofNat 64 (i.n - (j + 1)))
  | write (pc : s.pc = 0x80000e44#64) (j : Nat) (data : CopyData i dst j) (active : j < i.n)
      (regs : copyRegs i s.ctx j) (cursor : s.ctx.regs 15#5 = i.dst + BitVec.ofNat 64 (j + 1))
      (nextCount : s.ctx.regs 13#5 = BitVec.ofNat 64 (i.n - (j + 1)))
      (padCount : s.ctx.regs 16#5 = BitVec.ofNat 64 (i.n - (j + 1)))
      (b : BitVec 8) (lookup : i.source[j]? = some b) (value : s.ctx.regs 14#5 = b.setWidth 64)
  | padWrite (pc : s.pc = 0x80000e58#64) (k j : Nat) (data : PadData i dst k j) (active : j < i.n)
      (endValue : (s.ctx.regs 15#5).extractLsb' 0 32 = (i.dst + BitVec.ofNat 64 i.n).extractLsb' 0 32)
      (cursor : s.ctx.regs 14#5 = i.dst + BitVec.ofNat 64 (j + 1))
  | done (pc : s.pc = 0x80000e64#64) (result : post i dst)

structure Common (i : Inputs) (s : Memory.State) (dst : List (BitVec 8)) : Prop where
  buffers : s.buffers = i.buffers dst

structure GoodAt (i : Inputs) (s : Memory.State) (dst : List (BitVec 8)) : Prop extends Common i s dst where
  control : Control i s.machine dst

noncomputable def bodyRows : List Binary.Row := Memory.bodyRows Binary.strncpy.rows
  (Binary.strncpy_000 :: StrncpyFrame.saveRows ++ StrncpyFrame.returnRows)

noncomputable def effects : RowEffects Memory.decodeWrites bodyRows := by derive_effects

noncomputable abbrev writes : RegMask := effects.writes

theorem writes_checked : deriveRowWrites Memory.decodeWrites bodyRows = some writes := effects.checked

theorem frame_accepted : FrameEffects.Accepts StrncpyFrame.layout writes := by decide

def Endpoint (i : Inputs) (s : Memory.State) : Prop := ∃ dst, GoodAt i s dst
abbrev Good (i : Inputs) := Memory.ResidualGood bodyRows (Endpoint i)

def bodyCuts (pc : BitVec 64) : Bool :=
  pc == 0x80000e40#64 || pc == 0x80000e44#64 || pc == 0x80000e58#64 || pc == 0x80000e64#64

def atResult (s : Memory.State) (r : RegState) : Memory.State :=
  ⟨⟨r.ctx, r.pc, s.machine.cells⟩, s.buffers⟩

theorem Common.result {i : Inputs} {s : Memory.State} {dst : List (BitVec 8)}
    (h : Common i s dst) (r : RegState) :
    Common i (atResult s r) dst := ⟨h.buffers⟩

def initial (i : Inputs) : Memory.State := ⟨StrncpyFrame.initialMachine i.entry, i.buffers i.old⟩
def Exit (s : Memory.State) : Prop := s.machine.pc = 0x80000e64#64

set_option maxHeartbeats 0 in
theorem endpoint_terminal (i : Inputs) (s : Memory.State) (h : Endpoint i s) :
    findReg s.machine.pc bodyRows = none := by
  obtain ⟨dst, h⟩ := h
  cases h.control with
  | _ pc => rw [pc]; binary_rfl

set_option maxHeartbeats 0 in
theorem good_done {i : Inputs} {s : Memory.State} (h : Good i s) (exit : Exit s) :
    ∃ dst, Common i s dst ∧ post i dst := by
  have terminal : findReg s.machine.pc bodyRows = none := by rw [exit]; binary_rfl
  obtain ⟨dst, h⟩ := Residual.endpoint_of_no_decode h terminal
  refine ⟨dst, h.toCommon, ?_⟩
  cases h.control with
  | done _ result => exact result
  | _ pc => simp_all [Exit]

end Xv6.WholeFunction.Strncpy
