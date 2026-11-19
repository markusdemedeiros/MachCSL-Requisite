import Experiments.SolverSurvey.SmtLearnChecks

open Experiments.SmtSlice

-- An imported checked arithmetic lemma works without any SMT executable.
set_option smtSlice.solver "/no/such/solver" in
theorem imported_arithmetic (f : Nat → Nat) (x y : Nat)
    (h : f x = f y - 112) (bound : 112 ≤ f y) : f x + 112 = f y := by
  run_tac unless (← tryLearned) do throwError "Expected an imported checked lemma"

example (x y : Nat) (h : x = y - 112) : x = y - 112 := by
  fail_if_success
    have : x + 112 = y := by
      run_tac unless (← tryLearned) do throwError "No matching checked lemma"
  exact h

open Lean in
run_cmd do
  let axs ← collectAxioms ``imported_arithmetic
  unless axs.all (#[``propext, ``Quot.sound, ``Classical.choice].contains ·) do
    throwError "Unexpected axioms: {axs}"
