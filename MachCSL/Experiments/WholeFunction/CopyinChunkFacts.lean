import Experiments.WholeFunction.CopyinInvariant
import Experiments.WholeFunction.CopyArithmetic

/-! Arithmetic for the actual page-ready copyin block. The branch compares
the remaining length with the unsigned page remainder; ADDIW sign extension
is harmless because a chunk has at most 4096 bytes. No execution theorem or
production ProofCopyin declaration is assumed here. -/
namespace Xv6.WholeFunction.Copyin
open MachCSL LeanRV64D

theorem page_nowrap (a d : Nat)
    (pageBound : (a + d) / 4096 * 4096 < 2 ^ 38) :
    a + d < 2 ^ 64 := by
  have hm := Nat.mod_lt (a + d) (by decide : 0 < 4096)
  omega

theorem page_remaining (a d : Nat) (nowrap : a + d < 2 ^ 64) :
    BitVec.ofNat 64 ((a + d) / 4096 * 4096) - BitVec.ofNat 64 (a + d) + 4096#64 =
      BitVec.ofNat 64 (4096 - (a + d) % 4096) := by
  rw [BitVec.sub_eq_add_neg, BitVec.add_assoc]
  exact co_n_val3 (a + d) nowrap

theorem source_offset (a d : Nat) (nowrap : a + d < 2 ^ 64) :
    BitVec.ofNat 64 (a + d) - BitVec.ofNat 64 ((a + d) / 4096 * 4096) =
      BitVec.ofNat 64 ((a + d) % 4096) := by
  rw [co_ofNat_sub (a + d) ((a + d) / 4096 * 4096) (by omega) nowrap]
  congr 1
  omega

/-- BGEU takes the page-remainder arm, including the equality case. -/
theorem selected_chunk (a d len : Nat) (len64 : len < 2 ^ 64) :
    (if bcond bop.BGEU (BitVec.ofNat 64 (len - d))
        (BitVec.ofNat 64 (4096 - (a + d) % 4096))
      then BitVec.ofNat 64 (4096 - (a + d) % 4096)
      else BitVec.ofNat 64 (len - d)) = BitVec.ofNat 64 (chunkSize a d len) := by
  have hm := Nat.mod_lt (a + d) (by decide : 0 < 4096)
  by_cases h : 4096 - (a + d) % 4096 ≤ len - d
  · rw [co_bgeu_ge (len - d) (4096 - (a + d) % 4096) (by omega) (by omega) h]
    rw [chunkSize, Nat.min_eq_left h]
  · rw [co_bgeu_lt (len - d) (4096 - (a + d) % 4096) (by omega) (by omega) (by omega)]
    rw [chunkSize, Nat.min_eq_right (by omega)]

/-- A small nonnegative word keeps its value under sext.w. The mask and
extension facts are proved inside the kernel, without native reflection. -/
theorem sextw_small_checked (x : BitVec 64) (small : x.toNat < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.extractLsb' 0 32 x) = x :=
  MachCSL.CopyArithmetic.sextw_small_checked x small

theorem chunk_sextw (a d len : Nat) (more : d < len) :
    BitVec.signExtend 64 (BitVec.extractLsb' 0 32
      (BitVec.ofNat 64 (chunkSize a d len))) =
      BitVec.ofNat 64 (chunkSize a d len) := by
  apply sextw_small_checked
  obtain ⟨_, _, _, hsmall, _⟩ := chunk_facts a d len more
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact hsmall

theorem loop_page_remaining (i : Inputs) (d : Nat) (R : RegMap)
    (regs : LoopRegs i d R)
    (page : R 19#5 = BitVec.ofNat 64 ((i.src.toNat + d) / 4096 * 4096))
    (pageBound : (i.src.toNat + d) / 4096 * 4096 < 2 ^ 38) :
    R 19#5 - R 18#5 + R 22#5 =
      BitVec.ofNat 64 (4096 - (i.src.toNat + d) % 4096) := by
  rw [page, regs.src, regs.pageSize]
  exact page_remaining i.src.toNat d (page_nowrap _ _ pageBound)

theorem loop_selected_chunk (i : Inputs) (d : Nat) (R : RegMap)
    (regs : LoopRegs i d R)
    (page : R 19#5 = BitVec.ofNat 64 ((i.src.toNat + d) / 4096 * 4096))
    (pageBound : (i.src.toNat + d) / 4096 * 4096 < 2 ^ 38)
    (len64 : i.old.length < 2 ^ 64) :
    (if bcond bop.BGEU (R 20#5) (R 19#5 - R 18#5 + R 22#5)
      then R 19#5 - R 18#5 + R 22#5 else R 20#5) =
      BitVec.ofNat 64 (chunkSize i.src.toNat d i.old.length) := by
  rw [loop_page_remaining i d R regs page pageBound, regs.remaining]
  exact selected_chunk i.src.toNat d i.old.length len64

theorem loop_source_offset (i : Inputs) (d : Nat) (R : RegMap)
    (regs : LoopRegs i d R)
    (page : R 19#5 = BitVec.ofNat 64 ((i.src.toNat + d) / 4096 * 4096))
    (pageBound : (i.src.toNat + d) / 4096 * 4096 < 2 ^ 38) :
    R 18#5 - R 19#5 = BitVec.ofNat 64 ((i.src.toNat + d) % 4096) := by
  rw [regs.src, page]
  exact source_offset i.src.toNat d (page_nowrap _ _ pageBound)

theorem loop_physical_source (i : Inputs) (d : Nat) (R : RegMap) (w : BitVec 64)
    (regs : LoopRegs i d R)
    (page : R 19#5 = BitVec.ofNat 64 ((i.src.toNat + d) / 4096 * 4096))
    (pageBound : (i.src.toNat + d) / 4096 * 4096 < 2 ^ 38)
    (physical : R 10#5 = pte2pa w) :
    (R 18#5 - R 19#5) + R 10#5 =
      pte2pa w + BitVec.ofNat 64 ((i.src.toNat + d) % 4096) := by
  rw [loop_source_offset i d R regs page pageBound, physical, BitVec.add_comm]

end Xv6.WholeFunction.Copyin

/-- info: 'Xv6.WholeFunction.Copyin.chunk_sextw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Xv6.WholeFunction.Copyin.chunk_sextw
