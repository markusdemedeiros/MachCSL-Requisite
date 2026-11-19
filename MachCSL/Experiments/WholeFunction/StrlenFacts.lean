import MachCSL.CallConv

/-! Pure STRLEN facts. These proofs have no dependency on ProofStrlen or its
iteration rules; they describe the actual byte and SUBW arithmetic. -/
namespace Xv6.WholeFunction.Strlen
open Iris Iris.BI Iris.ProgramLogic MachCSL LeanRV64D
set_option linter.unusedSimpArgs false

theorem subw_len (s : BitVec 64) (n : Nat) (hn : n < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.extractLsb' 0 32 (s + BitVec.ofNat 64 n) - BitVec.extractLsb' 0 32 s) =
      BitVec.ofNat 64 n := by
  have h32 : BitVec.extractLsb' 0 32 (s + BitVec.ofNat 64 n) - BitVec.extractLsb' 0 32 s = BitVec.ofNat 32 n := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.extractLsb'_toNat, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.shiftRight_zero, Nat.reducePow]
    omega
  rw [h32]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_signExtend]
  have hmsb : (BitVec.ofNat 32 n).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat, Nat.reducePow]; rw [Nat.mod_eq_of_lt (by omega)]
    simp; omega
  rw [hmsb]
  simp only [Bool.false_eq_true, ite_false, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow, Nat.add_zero]
  rw [Nat.mod_eq_of_lt (by omega : n < 4294967296), Nat.mod_eq_of_lt (by omega : n < 18446744073709551616)]

def cstrAt (bs : List (BitVec 8)) (n : Nat) : Prop :=
  (∀ j, j < n → ∃ b, bs[j]? = some b ∧ b ≠ 0#8) ∧ bs[n]? = some 0#8

theorem cstrAt_len {bs : List (BitVec 8)} {n : Nat} (h : cstrAt bs n) : n < bs.length :=
  (List.getElem?_eq_some_iff.mp h.2).1

/-- The buffer under `cstr a dq s` is a C string of length `s.length`. -/
theorem cstrAt_of_nonul (s : List (BitVec 8)) (h : nonul s) : cstrAt (s ++ [0#8]) s.length := by
  constructor
  · intro j hj
    refine ⟨s[j]'hj, ?_, h _ (List.getElem_mem hj)⟩
    rw [List.getElem?_append_left hj]
    simp
  · rw [List.getElem?_append_right (Nat.le_refl _)]
    simp


theorem cstrAt_read {bs : List (BitVec 8)} {n i : Nat} (h : cstrAt bs n) (hi : i ≤ n) :
    ∃ b, bs[i]? = some b ∧ (b = 0#8 ↔ i = n) := by
  by_cases eq : i = n
  · subst i; exact ⟨0#8, h.2, by simp⟩
  · obtain ⟨b, hb, nonzero⟩ := h.1 i (by omega)
    exact ⟨b, hb, by simp [nonzero, eq]⟩

theorem cstrAt_zero {bs : List (BitVec 8)} {n i : Nat} (h : cstrAt bs n)
    (hi : i ≤ n) {b : BitVec 8} (hb : bs[i]? = some b) : b = 0#8 ↔ i = n := by
  obtain ⟨b', hb', hz⟩ := cstrAt_read h hi
  have : b = b' := Option.some.inj (hb.symm.trans hb')
  subst b'; exact hz

theorem byte_zero (b : BitVec 8) : b.setWidth 64 = 0#64 ↔ b = 0#8 := by
  constructor
  · intro h; have := congrArg (BitVec.setWidth 8) h; simpa using this
  · intro h; subst b; rfl

end Xv6.WholeFunction.Strlen
