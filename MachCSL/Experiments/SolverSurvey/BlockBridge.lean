import Experiments.SolverSurvey.BlockMachine
import Experiments.WholeFunction.CopyArithmetic

/-! Keep machine VCs in bitvectors; cross the Nat boundary once per phase.
Imported arithmetic consists of universal page-mask and count-selection laws.
No prior copyin page/chunk/register proof is used. -/
namespace Experiments.SolverSurvey.Block
open Fixture
open Xv6 Xv6.WholeFunction.Copyin MachCSL LeanRV64D
set_option smtSlice.trace true

theorem page_bits_nat (a : Nat) (bounded : a < 2 ^ 64) :
    BitVec.ofNat 64 a &&& 0xFFFFFFFFFFFFF000#64 = BitVec.ofNat 64 (a / 4096 * 4096) ∧
    BitVec.ofNat 64 a &&& 4095#64 = BitVec.ofNat 64 (a % 4096) := by
  constructor
  · apply BitVec.eq_of_toNat_eq
    rw [co_pgdown_toNat]
    bv_smt
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bounded]
    have mask : a &&& 4095 = a % 4096 := Nat.and_two_pow_sub_one_eq_mod a 12
    simpa only [Nat.reducePow, Nat.reduceMod, mask] using
      (Nat.mod_eq_of_lt (show a % 4096 < 2 ^ 64 by omega)).symm

theorem abi_count_nat (a d len : Nat) (len64 : len < 2 ^ 64) :
    (if (BitVec.ofNat 64 (len - d)).ult (4096#64 - BitVec.ofNat 64 ((a + d) % 4096))
      then BitVec.ofNat 64 (len - d)
      else 4096#64 - BitVec.ofNat 64 ((a + d) % 4096)) =
      BitVec.ofNat 64 (chunkSize a d len) := by
  simpa only [chunkSize] using MachCSL.CopyArithmetic.abi_count_nat a d len len64

/-- Same exact natural-indexed postcondition as the full direct VCs, using
one machine ABI certificate and two shared representation-boundary laws. -/
theorem page_chunk_values_bridge (i : Inputs) (d : Nat) (k : KCtx) (w : BitVec 64)
    (regs : LoopRegs i d k.regs)
    (page : k.regs 19#5 = BitVec.ofNat 64 ((i.src.toNat + d) / 4096 * 4096))
    (pageBound : (i.src.toNat + d) / 4096 * 4096 < 2 ^ 38)
    (physical : k.regs 10#5 = pte2pa w) (more : d < i.old.length)
    (len64 : i.old.length < 2 ^ 64) :
    (pageResult k).ctx.regs 9#5 = BitVec.ofNat 64 (chunkSize i.src.toNat d i.old.length) ∧
    (pageResult k).ctx.regs 10#5 = i.dst + BitVec.ofNat 64 d ∧
    (pageResult k).ctx.regs 11#5 = pte2pa w + BitVec.ofNat 64 ((i.src.toNat + d) % 4096) ∧
    (pageResult k).ctx.regs 12#5 = BitVec.ofNat 64 (chunkSize i.src.toNat d i.old.length) := by
  have bounded : i.src.toNat + d < 2 ^ 64 := by smt_omega
  obtain ⟨mask, offset⟩ := page_bits_nat (i.src.toNat + d) bounded
  have actualMask : k.regs 19#5 = k.regs 18#5 &&& 0xFFFFFFFFFFFFF000#64 := by
    rw [regs.src, mask, page]
  have abi := page_machine k actualMask regs.pageSize
  simpa only [PageABI, regs.src, offset, regs.remaining,
    abi_count_nat i.src.toNat d i.old.length len64, regs.dst, physical] using abi

end Experiments.SolverSurvey.Block
