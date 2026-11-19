import Lean.Elab.Tactic.BVDecide
import Lean.Util.CollectFVars

/-! A certificate cache around Lean's existing external CaDiCaL/LRAT backend.
The key is the complete closed reflected formula, not a textual goal or hash
alone. Cached UNSAT theorems are kernel-checked when reused and persisted in
olean files. Optional disk LRAT replay reruns the standard verified checker.

Trust is exactly the existing bv_decide native-checker boundary: CaDiCaL is
untrusted, but native evaluation of verifyBVExpr introduces its usual audited
closed Boolean equation axiom. This does not claim fully kernel-reduced LRAT.
-/
namespace Experiments.SolverSurvey
open Lean Meta Elab Tactic Meta.Tactic.BVDecide

register_option solver_bv.diskCache : String := {
  defValue := "", descr := "Optional directory for checked LRAT replay; empty disables disk cache" }
register_option solver_bv.slice : Bool := {
  defValue := true, descr := "Drop proposition hypotheses disconnected from the target before normalization" }
register_option solver_bv.cache : Bool := {
  defValue := true, descr := "Reuse closed reflected UNSAT theorems from this module and imported modules" }

initialize certificateCache : SimplePersistentEnvExtension (Expr × Name) (Std.HashMap Expr Name) ←
  registerSimplePersistentEnvExtension {
    asyncMode := .sync
    addEntryFn := fun state (key, name) => state.insert key name
    addImportedFn := fun states => states.foldl (fun state entries =>
      entries.foldl (fun state (key, name) => state.insert key name) state) {} }

structure SolverStats where
  checked : Nat := 0
  theoremHits : Nat := 0
  diskHits : Nat := 0
  externalCalls : Nat := 0
  sliced : Nat := 0
  deriving Repr, Inhabited

initialize stats : IO.Ref SolverStats ← IO.mkRef {}

/-- Discard only assumptions disconnected from the conclusion and the retained
assumptions. This weakens the goal; it cannot invent a proof. Closed assumptions
are retained. Incomplete slicing can be disabled when an unrelated contradiction
is intentionally needed. -/
def sliceGoal (g : MVarId) : MetaM MVarId := g.withContext do
  unless solver_bv.slice.get (← getOptions) do return g
  let mut relevant := (collectFVars {} (← g.getType)).fvarSet
  let declarations := (← getLCtx).decls.toArray.filterMap id
  let dependencies ← declarations.mapM fun d => do
    return (d, collectFVars {} d.type, ← isProp d.type)
  for _ in [:declarations.size + 1] do
    let mut changed := false
    for (d, deps, proposition) in dependencies do
      if relevant.contains d.fvarId ||
          (proposition && (deps.fvarIds.isEmpty || deps.fvarIds.any relevant.contains)) then
        for v in deps.fvarIds.push d.fvarId do
          unless relevant.contains v do
            relevant := relevant.insert v
            changed := true
    unless changed do break
  let remove := declarations.filterMap fun d =>
    if relevant.contains d.fvarId then none else some d.fvarId
  let (g', cleared) ← g.tryClearMany' remove
  stats.modify fun s => { s with sliced := s.sliced + cleared.size }
  return g'

/-- Return a cached theorem only after exact structural key equality. The hash
selects a disk filename, while the full key is checked before accepting a file. -/
def cachedBitblaster (ctx : TacticContext) : UnsatProver Unit := fun goal reflected atoms => do
  let formula ← instantiateMVars reflected.expr
  if formula.hasFVar || formula.hasMVar then
    throwError "solver_bv: reflected cache key is not closed"
  let useCache := solver_bv.cache.get (← getOptions)
  if useCache then
    if let some name := (certificateCache.getState (← getEnv))[formula]? then
      stats.modify fun s => { s with theoremHits := s.theoremHits + 1 }
      return .ok ⟨mkConst name, ()⟩
  let directory := solver_bv.diskCache.get (← getOptions)
  let identity := "lean-4.34.1-lrat-v1\n" ++ reprStr formula
  let base := System.FilePath.mk directory / toString (hash identity)
  let keyPath := base.withExtension "key"
  let proofPath := base.withExtension "lrat"
  let mut proof : Expr := default
  if directory != "" && (← keyPath.pathExists) && (← proofPath.pathExists) then
    unless (← IO.FS.readFile keyPath) == identity do
      throwError "solver_bv: disk cache key mismatch (hash collision or stale data)"
    match ← lratChecker { ctx with lratPath := proofPath } goal reflected atoms with
    | .error error => return .error error
    | .ok answer => proof := answer.proof
    stats.modify fun s => { s with diskHits := s.diskHits + 1 }
  else
    stats.modify fun s => { s with externalCalls := s.externalCalls + 1 }
    match ← lratBitblaster ctx goal reflected atoms with
    | .error e => return .error e
    | .ok answer =>
      proof := answer.proof
      if directory != "" then
        IO.FS.createDirAll directory
        IO.FS.writeFile (proofPath.withExtension "lrat.tmp") answer.cert
        IO.FS.rename (proofPath.withExtension "lrat.tmp") proofPath
        IO.FS.writeFile (keyPath.withExtension "key.tmp") identity
        IO.FS.rename (keyPath.withExtension "key.tmp") keyPath
  stats.modify fun s => { s with checked := s.checked + 1 }
  if useCache then
    let thm ← mkAuxTheorem (← inferType proof) proof
    let .const name _ := thm | throwError "solver_bv: unexpected certificate theorem"
    modifyEnv fun env => certificateCache.addEntry env (formula, name)
    return .ok ⟨thm, ()⟩
  return .ok ⟨proof, ()⟩

/-- Standard BV normalization and reflection, with a cached UNSAT prover.
Preprocessing transformations and final reflection remain proof-producing. -/
def solve (g : MVarId) : TermElabM Unit := do
  let g ← sliceGoal g
  IO.FS.withTempFile fun _ path => do
    let ctx ← TacticContext.new path {}
    let params ← Grind.mkDefaultParams {}
    Grind.GrindM.run (params := params) do
      Normalize.PreProcessM.run' ctx.preProcessContext (.mvarIdTarget g) do
        unless ← Normalize.bvNormalize do
          let target ← Normalize.PreProcessM.getTargetMVarId
          let hypotheses ← Normalize.PreProcessM.getHyps
          let result ← M.run (hypotheses := hypotheses) do
            closeWithBVReflection target (cachedBitblaster ctx)
          match result with
          | .ok _ => pure ()
          | .error counterexample =>
            counterexample.goal.withContext do
              throwError (← explainCounterExampleQuality counterexample)

elab "solver_bv" : tactic => do
  let g ← getMainGoal
  solve g
  replaceMainGoal []

open Lean Elab Command in
elab "#solver_stats" : command => do
  let env ← getEnv
  let count ← IO.lazyPure fun _ => (certificateCache.getState env).size
  logInfo m!"solver_bv statistics ({count} cached formulas): {repr (← stats.get)}"

end Experiments.SolverSurvey
