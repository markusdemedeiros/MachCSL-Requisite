import Experiments.SolverSurvey.SmtSlice

open Experiments.SmtSlice

-- An external oracle may lie. Its core is only a hint for an ordinary proof.
set_option smtSlice.solver "Experiments/SolverSurvey/lying-solver.py" in
example (x : Nat) (h : x > 0) : x > 0 := by
  fail_if_success have : x = 0 := by smt_omega
  exact h

-- A valid core for another context must not be accepted through stale state.
set_option smtSlice.solver "Experiments/SolverSurvey/lying-solver.py" in
example (x : Nat) (h : x ≤ 4) : x ≤ 4 := by
  fail_if_success have : x = 4 := by smt_omega
  exact h

-- An unavailable tool fails instead of silently bypassing the obligation.
set_option smtSlice.solver "/no/such/solver" in
example (x : Nat) : x = x := by
  fail_if_success have : x < x := by smt_omega
  rfl

-- Nonlinear and unsupported reasoning never becomes an assumption.
example (x y : Nat) : x = x := by
  fail_if_success have : x * y = 100 := by smt_omega
  rfl
