import Experiments.WholeFunction.KernelSymbolic

/-! Proof-producing register prefixes for resource-aware clients. The client
supplies semantic cutpoints and a postcondition; actual rows determine every
ordinary instruction. No second register semantics is introduced. -/
namespace Xv6.WholeFunction.Symbolic
open MachCSL LeanRV64D

def Prefix (rows : List Binary.Row) (cut : BitVec 64 → Bool)
    (start : RegState) (post : RegState → Prop) : Prop :=
  ∃ result, Certificate rows cut start ⟨result, .cut⟩ ∧ post result

theorem Prefix.stop {rows : List Binary.Row} {cut : BitVec 64 → Bool}
    {s : RegState} {post : RegState → Prop}
    (hit : cut s.pc = true) (done : post s) : Prefix rows cut s post :=
  ⟨s, .stop s hit, done⟩

theorem Prefix.step {rows : List Binary.Row} {cut : BitVec 64 → Bool}
    {s : RegState} {post : RegState → Prop} (r : LocatedReg s.pc)
    (found : findReg s.pc rows = some r) (free : hartFree r.action = true)
    (tail : Prefix rows cut (r.action.run r.row.rvc canonical s) post) :
    Prefix rows cut s post := by
  obtain ⟨result, certificate, done⟩ := tail
  exact ⟨result, .step s r _ found free certificate, done⟩

end Xv6.WholeFunction.Symbolic

namespace Xv6.WholeFunction.Symbolic.Frontend
open Lean Meta Elab Tactic
open MachCSL (KCtx instrLen)

private def checkedEq (lhs rhs : Expr) : MetaM Expr := do
  unless ← withTransparency .all <| isDefEq lhs rhs do
    throwError "symbolic_prefix: computed metadata did not replay"
  let statement ← mkEq lhs rhs
  mkAuxTheorem statement (← mkEqRefl lhs)

/-- Normalize computational decoder fields, sealing validity proofs so later
symbolic steps do not repeatedly unfold the binary decoder's proof terms. -/
private def decodedAction (row : Expr) : MetaM Expr := do
  let code ← mkAppM ``Binary.Row.code #[row]
  let decoded ← withTransparency .all <| whnf (← mkAppM ``RegAction.decode #[code])
  unless decoded.isAppOfArity ``Option.some 2 do
    throwError "symbolic_prefix: unsupported register instruction {decoded}"
  let action ← withTransparency .all <| reduce (← mkAppM ``Subtype.val #[decoded.getAppArgs[1]!])
  let args ← action.getAppArgs.mapM fun arg => do
    if ← isProof arg then mkAuxTheorem (← inferType arg) arg
    else
      let ty ← inferType arg
      if ty.isAppOfArity ``BitVec 1 then
        let value ← withTransparency .all <| reduce (← mkAppM ``BitVec.toNat #[arg])
        let width ← withTransparency .all <| reduce ty.getAppArgs[0]!
        pure (mkApp2 (mkConst ``BitVec.ofNat) width value)
      else pure arg
  pure (mkAppN action.getAppFn args)

private partial def rowAt (rows pc : Expr) : MetaM Expr := do
  let xs ← whnf rows
  unless xs.isAppOfArity ``List.cons 3 do
    throwError "symbolic_prefix: no binary row at {pc}"
  let row := xs.getAppArgs[1]!
  let address ← mkAppM ``Binary.Row.pc #[row]
  if ← isDefEq pc address then return row
  rowAt xs.getAppArgs[2]! pc

register_option symbolicPrefix.cache : Bool := {
  defValue := true
  descr := "Reuse checked closed instruction lookup metadata across symbolic branches"
}
register_option symbolicPrefix.traceCache : Bool := {
  defValue := false
  descr := "Report closed instruction lookup cache hits and misses"
}

private structure ClosedLocation where
  rows : Expr
  pc : Expr
  row : Expr
  action : Expr
  located : Expr
  found : Expr
  free : Expr
  rvc : Expr

private initialize closedLocations :
    SimplePersistentEnvExtension ClosedLocation (Array ClosedLocation) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun imports => imports.foldl (· ++ ·) #[]
    asyncMode := .sync }

/-- Lookup evidence contains only closed binary rows and a closed PC. Local
machine expressions are intentionally absent, so another branch or theorem
can reuse the same checked declaration without re-decoding the instruction. -/
private def closedLocation (rows pc : Expr) : MetaM ClosedLocation := do
  -- Arithmetic paths may produce different Fin bound proofs for the same
  -- address. Key the lookup by a canonical numeric PC, never by those proofs.
  let addressValue ← withTransparency .all <| reduce (← mkAppM ``BitVec.toNat #[pc])
  let pc := mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 64) addressValue
  let closed := !rows.hasFVar && !rows.hasMVar && !pc.hasFVar && !pc.hasMVar
  let enabled := symbolicPrefix.cache.get (← getOptions) && closed
  if enabled then
    for cached in (closedLocations.getState (← getEnv)).reverse do
      if cached.rows == rows && cached.pc == pc then
        if symbolicPrefix.traceCache.get (← getOptions) then logInfo "prefix-cache: hit"
        return cached
  if symbolicPrefix.traceCache.get (← getOptions) then logInfo "prefix-cache: miss"
  let row ← rowAt rows pc
  let action ← decodedAction row
  let address ← checkedEq pc (← mkAppM ``Binary.Row.pc #[row])
  let decoded ← checkedEq (← mkAppM ``Binary.Row.code #[row]) (← mkAppM ``RegAction.code #[action])
  let located ← mkAppM ``LocatedReg.mk #[row, action, address, decoded]
  let found ← checkedEq (← mkAppM ``findReg #[pc, rows]) (← mkAppM ``Option.some #[located])
  let free ← checkedEq (← mkAppM ``hartFree #[action]) (mkConst ``Bool.true)
  let rvc ← withTransparency .all <| reduce (← mkAppM ``Binary.Row.rvc #[row])
  let value : ClosedLocation := ⟨rows, pc, row, action, located, found, free, rvc⟩
  if enabled then
    unless #[row, action, located, found, free, rvc].any (fun e => e.hasFVar || e.hasMVar) do
      modifyEnv fun env => closedLocations.addEntry env value
  return value

/-- A single generated step or semantic cut. Each decoder equality is checked
by the kernel and cached as a theorem; instruction ASTs are never client input. -/
elab "prefix_step" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let target := (← instantiateMVars (← g.getType)).consumeMData.headBeta
    unless target.isAppOfArity ``Prefix 4 do
      throwError "prefix_step: expected Symbolic.Prefix"
    let args := target.getAppArgs
    let rows := args[0]!; let cut := args[1]!; let s := args[2]!
    let pc ← reduce (← mkAppM ``RegState.pc #[s])
    if pc.hasFVar then throwError "prefix_step: branch condition needs splitting"
    let hit ← reduce (mkApp cut pc)
    if hit.isConstOf ``Bool.true then
      let proof ← checkedEq (mkApp cut (← mkAppM ``RegState.pc #[s])) (mkConst ``Bool.true)
      let step := mkAppN (mkConst ``Prefix.stop) #[rows, cut, s, args[3]!, proof]
      replaceMainGoal (← g.apply step)
    else
      let info ← closedLocation rows pc
      let step := mkAppN (mkConst ``Prefix.step)
        #[rows, cut, s, args[3]!, info.located, info.found, info.free]
      let goals ← g.apply step
      let run ← mkAppM ``RegAction.run #[info.action, info.rvc, mkConst ``canonical, s]
      let goal ← withTransparency .all <| goals[0]!.change (mkAppN (mkConst ``Prefix) #[rows, cut, run, args[3]!])
      replaceMainGoal [goal]
      evalTactic (← `(tactic| simp only [RegAction.run, KCtx.rget_eq, instrLen,
        BitVec.reduceEq,
        Bool.false_eq_true, ↓reduceIte]))

private partial def drive (fuel : Nat) (g : MVarId) : TacticM (List MVarId) :=
  g.withContext do
    let target := (← instantiateMVars (← g.getType)).consumeMData.headBeta
    if !target.isAppOfArity ``Prefix 4 then return [g]
    let args := target.getAppArgs
    -- Keep symbolic word arithmetic inside branch conditions opaque. Only
    -- expose enough of the PC to choose a closed row or split that branch.
    let pc ← whnf (← mkAppM ``RegState.pc #[args[2]!])
    setGoals [g]
    if pc.hasFVar then
      evalTactic (← `(tactic| split))
      let mut remaining := []
      for branch in ← getGoals do
        remaining := remaining ++ (← drive fuel branch)
      return remaining
    let hit ← withTransparency .all <| reduce (mkApp args[1]! pc)
    if !hit.isConstOf ``Bool.true && fuel == 0 then
      throwError "symbolic_prefix: fuel exhausted before a semantic cut"
    evalTactic (← `(tactic| prefix_step))
    let mut remaining := []
    for nextGoal in ← getGoals do
      remaining := remaining ++ (← drive (fuel - 1) nextGoal)
    return remaining

/-- Execute up to `fuel` real register instructions on every branch, leaving
only the client's semantic postcondition at checked cuts. Unsupported rows,
hart-dependent operands and exhausted paths fail rather than becoming cuts. -/
elab "symbolic_prefix " fuel:num : tactic => do
  let g ← getMainGoal
  g.withContext do
    let target := (← instantiateMVars (← g.getType)).consumeMData.headBeta
    unless target.isAppOfArity ``Prefix 4 do
      throwError "symbolic_prefix: expected Symbolic.Prefix"
  let rest := (← getGoals).tail
  let goals ← drive fuel.getNat g
  setGoals (goals ++ rest)

end Xv6.WholeFunction.Symbolic.Frontend
