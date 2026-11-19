import Experiments.SolverSurvey.SmtSlice

/-! Learn reusable arithmetic lemmas from solver-selected cores.

Only Nat/Int atoms are abstracted. The resulting universally quantified lemma
is proved by `omega` in an empty local context, then checked and stored in the
environment. Later goals instantiate that lemma using local assumptions. A
cache hit needs neither external search nor arithmetic proof reconstruction.
-/
namespace Experiments.SmtSlice
open Lean Meta Elab Tactic

initialize learned : SimplePersistentEnvExtension (String × Name) (Std.HashMap String (Array Name)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun state (key, name) => state.insert key ((state.getD key #[]).push name)
    addImportedFn := fun states => states.foldl (fun acc entries => entries.foldl
      (fun acc (key, name) => acc.insert key ((acc.getD key #[]).push name)) acc) {}
    asyncMode := .sync }

def tryLearned : TacticM Bool := withMainContext do
  let goal ← getMainGoal
  let target ← goal.getType
  let (key, _) ← (proposition (← instantiateMVars target)).run {}
  for name in ((learned.getState (← getEnv)).getD key #[]).reverse do
    let saved ← saveState
    let messages ← Core.getMessageLog
    try
      let thm ← mkConstWithFreshMVarLevels name
      let (args, _, conclusion) ← forallMetaTelescopeReducing (← inferType thm)
      unless ← isDefEq conclusion target do throwError "different conclusion"
      for arg in args do
        if (← instantiateMVars arg).hasMVar then
          let ty ← instantiateMVars (← inferType arg)
          if ← isProp ty then
            let premise ← mkFreshExprSyntheticOpaqueMVar ty
            replaceMainGoal [premise.mvarId!]
            withoutRecover <| evalTactic (← `(tactic| assumption))
            setGoals [goal]
            unless ← isDefEq arg (← instantiateMVars premise) do throwError "premise mismatch"
      let proof ← instantiateMVars (mkAppN thm args)
      if proof.hasMVar then throwError "undetermined arithmetic atom"
      goal.assign proof
      replaceMainGoal []
      if smtSlice.trace.get (← getOptions) then logInfo "smt_learn: reused checked arithmetic lemma"
      return true
    catch _ =>
      saved.restore
      Core.setMessageLog messages
  return false

def proveGeneralization (kept : Array FVarId) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let hypotheses ← kept.mapM fun id => do instantiateMVars (← inferType (mkFVar id))
  let (key, enc) ← (proposition target).run {}
  let mut enc := enc
  for h in hypotheses do
    let (_, next) ← (proposition h).run enc
    enc := next
  let atoms := enc.atoms.map Prod.fst
  let types ← atoms.mapM fun e => do inferType e
  let decls := types.mapIdx fun i ty => (Name.mkSimple s!"a{i}", ty)
  let statement ← withLocalDeclsDND decls fun vars => do
    let abstractAtoms (e : Expr) := e.replace fun t =>
      match atoms.findIdx? (· == t) with
      | some i => some vars[i]!
      | none => none
    let mut body := abstractAtoms target
    for h in hypotheses.reverse do body ← mkArrow (abstractAtoms h) body
    mkForallFVars vars body
  if statement.hasFVar || statement.hasMVar then
    throwError "smt_learn: arithmetic abstraction left external dependencies"
  let obligation ← mkFreshExprMVarAt {} #[] statement .syntheticOpaque
  replaceMainGoal [obligation.mvarId!]
  withoutRecover <| Term.withoutErrToSorry <|
    evalTactic (← `(tactic| (repeat intro) <;> omega))
  unless (← getGoals).isEmpty do throwError "smt_learn: generalized replay left goals"
  setGoals [goal]
  let proof ← instantiateMVars obligation
  if proof.hasSorry || proof.hasMVar then throwError "smt_learn: incomplete generalized proof"
  let thm ← mkAuxTheorem statement proof
  let .const name _ := thm | throwError "smt_learn: expected a theorem constant"
  let application := mkAppN thm (atoms ++ kept.map mkFVar)
  unless ← isDefEq (← inferType application) target do throwError "smt_learn: instantiation mismatch"
  goal.assign application
  replaceMainGoal []
  modifyEnv fun env => learned.addEntry env (key, name)
  if smtSlice.trace.get (← getOptions) then
    logInfo m!"smt_learn: learned lemma with {atoms.size} atoms, {kept.size} premises"

elab "smt_learn" : tactic => do
  if ← tryLearned then return
  let kept ← selectCore
  let saved ← saveState
  let messages ← Core.getMessageLog
  try proveGeneralization kept
  catch err =>
    saved.restore
    Core.setMessageLog messages
    if smtSlice.trace.get (← getOptions) then
      logInfo m!"smt_learn: generalization unavailable: {err.toMessageData}"
    -- Some encodings include dependent Lean terms. Ordinary core replay still
    -- checks them; failing to generalize is never permission to assume them.
    let dropped ← withMainContext do
      let mut dropped := #[]
      for decl in ← getLCtx do
        if (← isProp decl.type) && !kept.contains decl.fvarId then
          dropped := dropped.push decl.fvarId
      return dropped
    replaceMainGoal [← (← getMainGoal).tryClearMany dropped]
    withoutRecover <| evalTactic (← `(tactic| omega))

macro "bv_smt_learn" : tactic =>
  `(tactic| ((try simp (config := { implicitDefEqProofs := false }) only [bitvec_to_nat] at *) <;> smt_learn))

end Experiments.SmtSlice
