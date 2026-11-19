import Experiments.SolverSurvey.SmtLearn

open Experiments.SmtSlice
set_option smtSlice.trace true

theorem learn_first (x y : Nat) (h : x = y - 112) (hy : 112 ≤ y) : x + 112 = y := by
  smt_learn

-- A different expression and irrelevant context reuse the same checked lemma.
theorem learn_renamed (f : Nat → Nat) (a b c d : Nat)
    (_dead : a - b = c - d) (h : f a = f b - 112) (hb : 112 ≤ f b) :
    f a + 112 = f b := by
  run_tac unless (← tryLearned) do throwError "Expected reuse across renamed arithmetic atoms"

theorem learn_wrong (x y : Nat) (h : x = y - 112) : x = y - 112 := by
  fail_if_success have : x + 112 = y := by smt_learn
  exact h

theorem learn_other_width (x y : Nat) (h : x = y - 96) (hy : 96 ≤ y) : x + 96 = y := by
  smt_learn

open Lean in
run_cmd do
  for decl in #[``learn_first, ``learn_renamed, ``learn_wrong, ``learn_other_width] do
    let axs ← collectAxioms decl
    unless axs.all (#[``propext, ``Quot.sound, ``Classical.choice].contains ·) do
      throwError "Unexpected axioms: {axs}"
