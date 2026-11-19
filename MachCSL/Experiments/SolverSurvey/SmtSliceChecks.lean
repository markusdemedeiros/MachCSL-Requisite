import Experiments.SolverSurvey.SmtSlice

open Experiments.SmtSlice
set_option smtSlice.trace true

theorem selected_bound (x y a b c d : Nat)
    (_hdead : a - b = c - d) (hxy : x ≤ y) (hy : y < 100) : x < 100 := by
  smt_omega

theorem selected_sub (x y a b c d : Nat)
    (_hdead : a - b = c - d) (hxy : x ≤ y) : y - x + x = y := by
  smt_omega

theorem selected_mod (x a b c d : Nat)
    (_hdead : a - b = c - d) : x / 4096 * 4096 + x % 4096 = x := by
  smt_omega

theorem selected_bv (x y junk : BitVec 64) (h : x.toNat + 8 < 2^64)
    (_hdead : junk + y = x) : (x + 8#64).toNat = x.toNat + 8 := by
  bv_smt

example (x : Nat) : x = x := by
  fail_if_success have : x < x := by smt_omega
  rfl

open Lean in
run_cmd do
  for decl in #[``selected_bound, ``selected_sub, ``selected_mod, ``selected_bv] do
    let axioms ← collectAxioms decl
    unless axioms.all (#[``propext, ``Quot.sound, ``Classical.choice].contains ·) do
      throwError "Unexpected axioms: {axioms}"

