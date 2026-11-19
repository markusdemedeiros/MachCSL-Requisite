import Lean

/-! Z3 selects arithmetic hypotheses; Lean's `omega` proves the result.

SMT output is a search hint, never a proof or axiom. Unsupported arithmetic is
abstracted, unsupported hypotheses are omitted, and a solver error, timeout,
unknown answer or failed replay rejects the tactic. The final proof does not
depend on Z3, its encoding, or the chosen core being correct.
-/
namespace Experiments.SmtSlice
open Lean Meta Elab Tactic

register_option smtSlice.solver : String := {
  defValue := ".lake/solver-python/bin/z3"
  descr := "Z3 executable used for untrusted arithmetic hypothesis selection"
}
register_option smtSlice.timeout : Nat := {
  defValue := 3000
  descr := "SMT search timeout in milliseconds"
}
register_option smtSlice.trace : Bool := {
  defValue := false
  descr := "Report the hypotheses selected for kernel-checked omega replay"
}

structure Encoding where
  atoms : Array (Expr × String) := #[]
  declarations : Array String := #[]
  bounds : Array String := #[]

abbrev EncodeM := StateT Encoding MetaM

def atom (e : Expr) (natural : Bool) : EncodeM String := do
  for (old, name) in (← get).atoms do
    if old == e then return name
  let name := s!"v{(← get).atoms.size}"
  modify fun st => { st with
    atoms := st.atoms.push (e, name)
    declarations := st.declarations.push s!"(declare-const {name} Int)"
    bounds := if natural then st.bounds.push s!"(assert (<= 0 {name}))" else st.bounds }
  return name

partial def number (e : Expr) : MetaM (Option Int) := do
  if let some n ← getNatValue? e then return some (Int.ofNat n)
  if let some n ← getIntValue? e then return some n
  if e.isAppOfArity ``HPow.hPow 6 then
    let some a ← number e.getAppArgs[4]! | return none
    let some b ← getNatValue? e.getAppArgs[5]! | return none
    if b ≤ 128 then return some (a ^ b)
  return none

def intLit (n : Int) : String :=
  if n < 0 then s!"(- {n.natAbs})" else toString n

partial def arithmetic (e : Expr) : EncodeM String := do
  let e := e.consumeMData
  if let some n ← number e then return intLit n
  let ty ← whnf (← inferType e)
  let natural := ty.isConstOf ``Nat
  unless natural || ty.isConstOf ``Int do throwError "smt_omega: not integer arithmetic"
  let args := e.getAppArgs
  let name := e.getAppFn.constName?.getD .anonymous
  if args.size ≥ 2 then
    let a := args[args.size - 2]!
    let b := args[args.size - 1]!
    if [``HAdd.hAdd, ``Nat.add, ``Int.add, ``HSub.hSub, ``Nat.sub, ``Int.sub,
        ``HMul.hMul, ``Nat.mul, ``Int.mul, ``HDiv.hDiv, ``Nat.div, ``Int.ediv,
        ``HMod.hMod, ``Nat.mod, ``Int.emod].contains name then
      -- Restrict products and divisors to linear integer arithmetic.
      let mul := [``HMul.hMul, ``Nat.mul, ``Int.mul].contains name
      let div := [``HDiv.hDiv, ``Nat.div, ``Int.ediv].contains name
      let mod := [``HMod.hMod, ``Nat.mod, ``Int.emod].contains name
      if mul && (← number a).isNone && (← number b).isNone then return ← atom e natural
      if div || mod then
        let some n ← number b | return ← atom e natural
        if n ≤ 0 then return ← atom e natural
      let x ← arithmetic a
      let y ← arithmetic b
      if [``HSub.hSub, ``Nat.sub, ``Int.sub].contains name then
        if natural then return s!"(ite (<= {y} {x}) (- {x} {y}) 0)"
        else return s!"(- {x} {y})"
      let op := if mul then "*" else if div then "div" else if mod then "mod" else "+"
      return s!"({op} {x} {y})"
  if name == ``Nat.succ then return s!"(+ {← arithmetic args.back!} 1)"
  if name == ``Neg.neg || name == ``Int.neg then return s!"(- {← arithmetic args.back!})"
  if name == ``Int.ofNat || name == ``Nat.cast then return ← arithmetic args.back!
  return ← atom e natural

partial def proposition (e : Expr) : EncodeM String := do
  let e := e.consumeMData
  if e.isConstOf ``True then return "true"
  if e.isConstOf ``False then return "false"
  if e.isAppOfArity ``Not 1 then return s!"(not {← proposition e.appArg!})"
  if e.isAppOfArity ``And 2 || e.isAppOfArity ``Or 2 || e.isAppOfArity ``Iff 2 then
    let op := if e.isAppOf ``And then "and" else if e.isAppOf ``Or then "or" else "="
    return s!"({op} {← proposition e.getAppArgs[0]!} {← proposition e.getAppArgs[1]!})"
  let args := e.getAppArgs
  let name := e.getAppFn.constName?.getD .anonymous
  if [``Eq, ``Ne, ``LT.lt, ``LE.le, ``Nat.le, ``Nat.lt, ``Int.le, ``Int.lt].contains name then
    let x ← arithmetic args[args.size - 2]!
    let y ← arithmetic args[args.size - 1]!
    let op := if name == ``Eq then "=" else if name == ``Ne then "distinct"
      else if [``LT.lt, ``Nat.lt, ``Int.lt].contains name then "<" else "<="
    return s!"({op} {x} {y})"
  throwError "smt_omega: unsupported proposition"

def selectCore : TacticM (Array FVarId) := withMainContext do
  let target ← instantiateMVars (← (← getMainGoal).getType)
  let (goal, enc) ← (proposition target).run {}
  let mut enc := enc
  let mut assertions : Array String := #[]
  let mut facts : Array FVarId := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    if !(← isProp decl.type) then continue
    try
      let (formula, next) ← (proposition (← instantiateMVars decl.type)).run enc
      enc := next
      assertions := assertions.push s!"(assert (! {formula} :named h{facts.size}))"
      facts := facts.push decl.fvarId
    catch _ => pure ()
  let query := String.intercalate "\n" <| [
    "(set-option :produce-unsat-cores true)",
    s!"(set-option :timeout {smtSlice.timeout.get (← getOptions)})",
    "(set-logic QF_LIA)"] ++ enc.declarations.toList ++ enc.bounds.toList ++
    assertions.toList ++ [s!"(assert (not {goal}))", "(check-sat)", "(get-unsat-core)"]
  let output ← IO.Process.output {
    cmd := smtSlice.solver.get (← getOptions), args := #["-in", "-smt2"] } query
  unless output.exitCode == 0 && output.stdout.startsWith "unsat\n" do
    throwError "smt_omega: no unsatisfiable core ({output.stdout.trimAscii}, {output.stderr.trimAscii})"
  let words := output.stdout.replace "(" " " |>.replace ")" " " |>.splitOn "\n"
  let tokens := words.flatMap (·.splitOn " ")
  let mut kept := #[]
  for token in tokens do
    if token.startsWith "h" then
      let some n := (token.drop 1).toString.toNat? | throwError "smt_omega: invalid core index"
      let some id := facts[n]? | throwError "smt_omega: core index out of range"
      kept := kept.push id
  if smtSlice.trace.get (← getOptions) then
    logInfo m!"smt_omega: selected {kept.size}/{facts.size} arithmetic hypotheses: {kept.map mkFVar}"
  return kept

elab "smt_omega" : tactic => do
  let kept ← selectCore
  let dropped ← withMainContext do
    let mut dropped := #[]
    for decl in ← getLCtx do
      if (← isProp decl.type) && !kept.contains decl.fvarId then
        dropped := dropped.push decl.fvarId
    return dropped
  let goal ← (← getMainGoal).tryClearMany dropped
  replaceMainGoal [goal]
  -- Untrusted selection is accepted only when the ordinary Lean proof closes.
  withoutRecover <| evalTactic (← `(tactic| omega))
  unless (← getGoals).isEmpty do throwError "smt_omega: replay left goals"

macro "bv_smt" : tactic =>
  `(tactic| ((try simp (config := { implicitDefEqProofs := false }) only [bitvec_to_nat] at *) <;> smt_omega))

end Experiments.SmtSlice
