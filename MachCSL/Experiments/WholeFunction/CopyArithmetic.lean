import MachCSL.Compat
import Experiments.SolverSurvey.SmtSlice

/-! Shared arithmetic at machine-word/page boundaries. This module imports
no binary, register-state model, function invariant, or copy specification.
External SMT search is replayed by omega; both results have kernel proofs. -/
namespace MachCSL.CopyArithmetic

theorem sextw_small_checked (x : BitVec 64) (small : x.toNat < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.extractLsb' 0 32 x) = x := by
  have low : (BitVec.extractLsb' 0 32 x).toNat = x.toNat := by
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
    exact Nat.mod_eq_of_lt (by omega)
  have sign : (BitVec.extractLsb' 0 32 x).msb = false := by
    apply BitVec.msb_eq_false_iff_two_mul_lt.mpr
    rw [low]
    omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false sign]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, low, Nat.mod_eq_of_lt x.isLt]

theorem abi_count_nat (a d len : Nat) (len64 : len < 2 ^ 64) :
    (if (BitVec.ofNat 64 (len - d)).ult (4096#64 - BitVec.ofNat 64 ((a + d) % 4096))
      then BitVec.ofNat 64 (len - d)
      else 4096#64 - BitVec.ofNat 64 ((a + d) % 4096)) =
      BitVec.ofNat 64 (min (4096 - (a + d) % 4096) (len - d)) := by
  rw [Nat.min_def]
  split <;> split <;>
    simp only [BitVec.ult, decide_eq_true_eq, decide_eq_false_iff_not] at * <;> bv_smt

open Lean in
run_cmd do
  for decl in #[``sextw_small_checked, ``abi_count_nat] do
    let axioms ← collectAxioms decl
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "{decl}: unexpected non-kernel arithmetic axiom {axioms}"

end MachCSL.CopyArithmetic
