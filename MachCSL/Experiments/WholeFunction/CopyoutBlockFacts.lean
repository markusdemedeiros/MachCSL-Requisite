import Experiments.WholeFunction.CopyoutBlocks
import Experiments.WholeFunction.CopyArithmetic
import Experiments.WholeFunction.CopyinPure

/-! Semantic ABI obligations for copyout. Register normalization produces
pure VCs; Z3 selects premises and omega reconstructs kernel proofs. The
universal checked small-word conversion is shared with copyin. -/
namespace Xv6.WholeFunction.Copyout
open MachCSL LeanRV64D
open MachCSL.CopyArithmetic

theorem setup_values (k : KCtx) :
    (setupCtx k).regs 20#5 = k.regs 12#5 ∧
    (setupCtx k).regs 21#5 = k.regs 14#5 ∧
    (setupCtx k).regs 22#5 = k.regs 13#5 ∧
    (setupCtx k).regs 23#5 = k.regs 10#5 ∧
    (setupCtx k).regs 24#5 = 4096#64 ∧
    (setupCtx k).regs 25#5 = 0x3fffffffff#64 ∧
    (setupCtx k).regs 26#5 = 0xfffffffffffff000#64 ∧
    (setupCtx k).regs 27#5 = k.regs 11#5 := by
  simp only [setupCtx, KCtx.setReg_regs, RegMap.set_apply, BitVec.reduceEq,
    ↓reduceIte, BitVec.zero_add,
    show (0xfffff#20 ++ 0#12).signExtend 64 = 0xfffffffffffff000#64 by decide,
    show (-1#64 : BitVec 64) >>> 26 = 0x3fffffffff#64 by decide,
    show (1#20 ++ 0#12).signExtend 64 = 4096#64 by decide, and_self]

theorem setup_sp (k : KCtx) : (setupCtx k).regs 2#5 = k.regs 2#5 := by
  simp only [setupCtx, KCtx.setReg_regs, RegMap.set_apply, BitVec.reduceEq, ↓reduceIte]

theorem setup_context (k : KCtx) : setupCtx k = k.withRegs (setupCtx k).regs := rfl

def chosenCount (k : KCtx) : BitVec 64 :=
  if pageBranch k then pageCandidate k else k.regs 21#5

macro "out_normalize" : tactic =>
  `(tactic| simp_all only [pageResult, moveArgs, pageSelected, pagePrefix,
    chosenCount, KCtx.setReg_regs, RegMap.set_apply, BitVec.reduceEq,
    Bool.false_eq_true, ↓reduceIte, BitVec.zero_add, BitVec.add_zero])

theorem page_chunk_values (k : KCtx) (a d len : Nat) (source physical : BitVec 64)
    (cursor : k.regs 20#5 = BitVec.ofNat 64 (a + d))
    (page : k.regs 9#5 = BitVec.ofNat 64 ((a + d) / 4096 * 4096))
    (pageSize : k.regs 24#5 = 4096#64)
    (remaining : k.regs 21#5 = BitVec.ofNat 64 (len - d))
    (src : k.regs 22#5 = source) (phys : k.regs 19#5 = physical)
    (pageBound : (a + d) / 4096 * 4096 < 2 ^ 38)
    (more : d < len) (len64 : len < 2 ^ 64) :
    (pageResult k).ctx.regs 18#5 = BitVec.ofNat 64 (Copyin.chunkSize a d len) ∧
    (pageResult k).ctx.regs 10#5 = physical + BitVec.ofNat 64 ((a + d) % 4096) ∧
    (pageResult k).ctx.regs 11#5 = source ∧
    (pageResult k).ctx.regs 12#5 = BitVec.ofNat 64 (Copyin.chunkSize a d len) := by
  have bounded : a + d < 2 ^ 64 := by smt_omega
  have room : pageCandidate k = 4096#64 - BitVec.ofNat 64 ((a + d) % 4096) := by
    unfold pageCandidate
    rw [cursor, page, pageSize]
    bv_smt
  have count : chosenCount k = BitVec.ofNat 64 (Copyin.chunkSize a d len) := by
    unfold chosenCount pageBranch
    rw [remaining, room]
    have hn := abi_count_nat a d len len64
    cases h : (BitVec.ofNat 64 (len - d)).ult (4096#64 - BitVec.ofNat 64 ((a + d) % 4096)) <;>
      simpa only [Copyin.chunkSize, bcond, h, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] using hn
  have small : (BitVec.ofNat 64 (Copyin.chunkSize a d len)).toNat < 2 ^ 31 := by
    have bound := (Copyin.chunk_facts a d len more).2.2.2.1
    bv_smt
  have word := MachCSL.CopyArithmetic.sextw_small_checked (BitVec.ofNat 64 (Copyin.chunkSize a d len)) small
  have offset : k.regs 20#5 - k.regs 9#5 = BitVec.ofNat 64 ((a + d) % 4096) := by
    rw [cursor, page]
    bv_smt
  cases h : pageBranch k <;> out_normalize <;>
    simp only [BitVec.add_comm, and_true, true_and]

theorem page_preserves (k : KCtx) (r : BitVec 5)
    (h18 : r ≠ 18#5) (h10 : r ≠ 10#5) (h11 : r ≠ 11#5) (h12 : r ≠ 12#5) :
    (pageResult k).ctx.regs r = k.regs r := by
  cases h : pageBranch k <;> out_normalize

theorem page_context (k : KCtx) :
    (pageResult k).ctx = k.withRegs (pageResult k).ctx.regs := by
  cases h : pageBranch k <;>
    simp only [pageResult, moveArgs, pageSelected, pagePrefix, h, Bool.false_eq_true,
      ↓reduceIte, KCtx.setReg, KCtx.withRegs]

theorem header_preserves (k : KCtx) (r : BitVec 5)
    (h9 : r ≠ 9#5) (h10 : r ≠ 10#5) (h11 : r ≠ 11#5) :
    (headerResult k).ctx.regs r = k.regs r := by
  cases h : tooHigh k <;>
    simp only [headerResult, headerPrefix, h, Bool.false_eq_true, ↓reduceIte,
      KCtx.setReg_regs, RegMap.set_apply, h9, h10, h11, ↓reduceIte]

theorem header_context (k : KCtx) :
    (headerResult k).ctx = k.withRegs (headerResult k).ctx.regs := by
  cases h : tooHigh k <;>
    simp only [headerResult, headerPrefix, h, Bool.false_eq_true, ↓reduceIte,
      KCtx.setReg, KCtx.withRegs]

theorem header_values (k : KCtx) (good : tooHigh k = false) :
    (headerResult k).ctx.regs 9#5 = k.regs 20#5 &&& k.regs 26#5 ∧
    (headerResult k).ctx.regs 10#5 = k.regs 23#5 ∧
    (headerResult k).ctx.regs 11#5 = k.regs 20#5 &&& k.regs 26#5 := by
  simp only [headerResult, headerPrefix, good, Bool.false_eq_true, ↓reduceIte,
    KCtx.setReg_regs, RegMap.set_apply, BitVec.reduceEq, ↓reduceIte, BitVec.zero_add, and_self]

theorem header_failure (k : KCtx) (high : tooHigh k = true) :
    (headerResult k).pc = 0x80001662#64 ∧
    (headerResult k).ctx.regs 10#5 = -1#64 ∧
    (headerResult k).ctx.regs 9#5 = k.regs 20#5 &&& k.regs 26#5 := by
  simp only [headerResult, headerPrefix, high, ↓reduceIte,
    KCtx.setReg_regs, RegMap.set_apply, BitVec.reduceEq, ↓reduceIte, BitVec.zero_add, and_self]

theorem tooHigh_iff (k : KCtx) (a d : Nat)
    (cursor : k.regs 20#5 = BitVec.ofNat 64 (a + d))
    (mask : k.regs 26#5 = 0xfffffffffffff000#64)
    (maximum : k.regs 25#5 = 0x3fffffffff#64)
    (bounded : a + d < 2 ^ 64) : tooHigh k = true ↔ 2 ^ 38 ≤ a + d := by
  simp only [tooHigh, headerPrefix, KCtx.setReg_regs, RegMap.set_apply,
    BitVec.reduceEq, ↓reduceIte, cursor, mask, maximum, Copyin.rounded_source a d bounded,
    bcond, BitVec.ult, decide_eq_true_eq]
  bv_smt

theorem permission_preserves (k : KCtx) (r : BitVec 5) (h : r ≠ 15#5) :
    (permissionCtx k).regs r = k.regs r := by
  simp only [permissionCtx, KCtx.setReg_regs, RegMap.set_apply, h, ↓reduceIte]
theorem permission_context (k : KCtx) :
    permissionCtx k = k.withRegs (permissionCtx k).regs := rfl
theorem readonly_iff (k : KCtx) : readonly k = true ↔ k.regs 15#5 &&& 4#64 = 0#64 := by
  simp only [readonly, permissionCtx, KCtx.setReg_regs, RegMap.set_apply,
    BitVec.reduceEq, ↓reduceIte, bcond, beq_iff_eq]

theorem walkArgs_values (k : KCtx) :
    (walkArgs k).regs 10#5 = k.regs 23#5 ∧
    (walkArgs k).regs 11#5 = k.regs 9#5 ∧ (walkArgs k).regs 12#5 = 0#64 := by
  simp only [walkArgs, KCtx.setReg_regs, RegMap.set_apply, BitVec.reduceEq,
    ↓reduceIte, BitVec.zero_add, and_self]
theorem faultArgs_values (k : KCtx) :
    (faultArgs k).regs 10#5 = k.regs 23#5 ∧
    (faultArgs k).regs 11#5 = k.regs 27#5 ∧
    (faultArgs k).regs 12#5 = k.regs 9#5 ∧ (faultArgs k).regs 13#5 = 0#64 := by
  simp only [faultArgs, KCtx.setReg_regs, RegMap.set_apply, BitVec.reduceEq,
    ↓reduceIte, BitVec.zero_add, and_self]
theorem savedPhysical_value (k : KCtx) : (savePhysical k).regs 19#5 = k.regs 10#5 := by
  simp only [savePhysical, KCtx.setReg_regs, RegMap.set_apply, BitVec.reduceEq,
    ↓reduceIte, BitVec.zero_add]

theorem faultArgs_preserves (k : KCtx) (r : BitVec 5)
    (h10 : r ≠ 10#5) (h11 : r ≠ 11#5) (h12 : r ≠ 12#5) (h13 : r ≠ 13#5) :
    (faultArgs k).regs r = k.regs r := by
  simp only [faultArgs, KCtx.setReg_regs, RegMap.set_apply,
    h10, h11, h12, h13, ↓reduceIte]
theorem walkArgs_preserves (k : KCtx) (r : BitVec 5)
    (h10 : r ≠ 10#5) (h11 : r ≠ 11#5) (h12 : r ≠ 12#5) :
    (walkArgs k).regs r = k.regs r := by
  simp only [walkArgs, KCtx.setReg_regs, RegMap.set_apply, h10, h11, h12, ↓reduceIte]
theorem savedPhysical_preserves (k : KCtx) (r : BitVec 5) (h : r ≠ 19#5) :
    (savePhysical k).regs r = k.regs r := by
  simp only [savePhysical, KCtx.setReg_regs, RegMap.set_apply, h, ↓reduceIte]

theorem walkArgs_context (k : KCtx) : walkArgs k = k.withRegs (walkArgs k).regs := rfl
theorem faultArgs_context (k : KCtx) : faultArgs k = k.withRegs (faultArgs k).regs := rfl
theorem savedPhysical_context (k : KCtx) : savePhysical k = k.withRegs (savePhysical k).regs := rfl
theorem movedCtx_context (k : KCtx) : movedCtx k = k.withRegs (movedCtx k).regs := rfl
theorem movedCtx_preserves (k : KCtx) (r : BitVec 5)
    (h20 : r ≠ 20#5) (h21 : r ≠ 21#5) (h22 : r ≠ 22#5) :
    (movedCtx k).regs r = k.regs r := by
  simp only [movedCtx, KCtx.setReg_regs, RegMap.set_apply, h20, h21, h22, ↓reduceIte]

theorem move_remaining (k : KCtx) (d n len : Nat)
    (remaining : k.regs 21#5 = BitVec.ofNat 64 (len - d))
    (count : k.regs 18#5 = BitVec.ofNat 64 n)
    (bound : d + n ≤ len) (len64 : len < 2 ^ 64) :
    (movedCtx k).regs 21#5 = BitVec.ofNat 64 (len - (d + n)) := by
  simp only [movedCtx, KCtx.setReg_regs, RegMap.set_apply, BitVec.reduceEq, ↓reduceIte]
  bv_smt

theorem moveDone_iff (k : KCtx) (d n len : Nat)
    (remaining : k.regs 21#5 = BitVec.ofNat 64 (len - d))
    (count : k.regs 18#5 = BitVec.ofNat 64 n)
    (bound : d + n ≤ len) (len64 : len < 2 ^ 64) :
    moveDone k = true ↔ d + n = len := by
  simp only [moveDone, movedCtx, KCtx.setReg_regs, RegMap.set_apply,
    BitVec.reduceEq, ↓reduceIte, bcond, beq_iff_eq]
  bv_smt

theorem zero_iff (k : KCtx) : zero k = true ↔ k.regs 10#5 = 0#64 := by
  simp only [zero, bcond, beq_iff_eq]
theorem nonzero_iff (k : KCtx) : nonzero k = true ↔ k.regs 10#5 ≠ 0#64 := by
  simp only [nonzero, bcond, bne_iff_ne]

open Lean in
run_cmd do
  for decl in #[``page_chunk_values, ``move_remaining, ``moveDone_iff, ``tooHigh_iff, ``setup_values,
      ``setup_certificate, ``header_certificate,
      ``page_certificate] do
    let axioms ← collectAxioms decl
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "{decl}: non-kernel arithmetic dependency {axioms}"
  logInfo "Copyout: three binary certificates, MAXVA comparison, and arithmetic ABI facts use only standard kernel axioms."

end Xv6.WholeFunction.Copyout
