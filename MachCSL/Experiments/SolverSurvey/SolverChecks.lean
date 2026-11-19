import Experiments.SolverSurvey.SolverCache
import Lean.Util.CollectAxioms

namespace Experiments.SolverSurvey

theorem page_mask (x : BitVec 64) :
    x &&& 0xFFFFFFFFFFFFF000#64 = (x >>> 12) <<< 12 := by solver_bv

/-- Same reflected formula, with a renamed input and disconnected hypotheses. -/
theorem page_mask_shared (address noise : BitVec 64) (irrelevant : noise + 1#64 = 17#64) :
    address &&& 0xFFFFFFFFFFFFF000#64 = (address >>> 12) <<< 12 := by solver_bv

/-- A changed mask is a different formula; a stale certificate cannot prove it. -/
example : True := by
  fail_if_success
    have bad (x : BitVec 64) : x &&& 0xFFFFFFFFFFFFE000#64 = (x >>> 12) <<< 12 := by solver_bv
  trivial

/-- Required premises survive dependency-based hypothesis slicing. -/
theorem even_add (x y noise : BitVec 64) (hx : x.getLsbD 0 = false)
    (hy : y.getLsbD 0 = false) (unused : noise = 19#64) :
    (x + y).getLsbD 0 = false := by solver_bv

/-- Width changes produce independent reflected keys. -/
theorem page_mask32 (x : BitVec 32) :
    x &&& 0xFFFFF000#32 = (x >>> 12) <<< 12 := by solver_bv

/-- An indispensable arithmetic premise cannot be silently omitted. -/
example : True := by
  fail_if_success
    have bad (x y : BitVec 64) (hx : x.getLsbD 0 = false) :
        (x + y).getLsbD 0 = false := by solver_bv
  trivial

/-- Disconnected contradictions require opting out of dependency slicing. -/
example (noise : BitVec 8) (impossible : noise ≠ noise) : False := by
  fail_if_success solver_bv
  set_option solver_bv.slice false in solver_bv

#solver_stats

open Lean Elab Command in
run_cmd do
  let original ← liftCoreM <| collectAxioms ``page_mask
  let reused ← liftCoreM <| collectAxioms ``page_mask_shared
  unless original == reused do throwError "reused formula acquired additional axioms"
  let arithmetic ← liftCoreM <| collectAxioms ``even_add
  let width ← liftCoreM <| collectAxioms ``page_mask32
  for name in original ++ arithmetic ++ width do
    unless name == ``propext || name == ``Classical.choice || name == ``Quot.sound do
      let type := (← getEnv).find? name |>.map Lean.ConstantInfo.type
      let some type := type | throwError "missing axiom {name}"
      let args := type.getAppArgs
      unless type.isAppOfArity ``Eq 3 && args[0]! == Lean.mkConst ``Bool &&
          args[1]!.isAppOfArity ``Std.Tactic.BVDecide.Reflect.verifyBVExpr 2 &&
          args[2]! == Lean.mkConst ``Bool.true && !type.hasFVar && !type.hasMVar do
        throwError "unexpected solver assumption type: {name}: {type}"
  logInfo m!"page-mask certificate reused with identical axiom set ({original.size} axioms)"

#print axioms even_add
end Experiments.SolverSurvey
