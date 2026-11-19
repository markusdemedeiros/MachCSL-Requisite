import Experiments.ResourcePlanner.Rules
import Lean

/-! Bounded untrusted assignment of window requests to spatial resources.
The resulting Iris script consumes each chosen source and closing wand once.
Z3 never supplies proof terms, fraction changes, bounds, or ownership. -/
namespace Experiments.ResourcePlanner
open Lean Meta Elab Tactic Iris Iris.BI Iris.ProofMode

register_option resourcePlanner.solver : String := {
  defValue := ".lake/solver-python/bin/z3", descr := "Untrusted assignment solver" }
register_option resourcePlanner.timeout : Nat := {
  defValue := 1000, descr := "Assignment solver timeout in milliseconds" }
register_option resourcePlanner.trace : Bool := {
  defValue := false, descr := "Log candidate counts and selected linear routes" }

private def pair? (name : Name) (e : Expr) : Option (Expr × Expr) := do
  if !e.isAppOfArity name 4 then none
  else some (e.getArg! 2, e.getArg! 3)

private partial def flatten (e : Expr) : Array Expr :=
  match pair? ``BIBase.sep e.consumeMData with
  | some (a,b) => flatten a ++ flatten b
  | none => #[e]

private partial def introPattern (e : Expr) (stem : String) (start : Nat := 0) : String × Nat :=
  match pair? ``BIBase.sep e.consumeMData with
  | some (a,b) =>
    let (x,n) := introPattern a stem start
    let (y,m) := introPattern b stem n
    (s!"⟨{x}, {y}⟩",m)
  | none => ((if e.isAppOf ``BIBase.pure then "%" else "") ++ stem ++ toString start,start+1)

/-- Expose conjunction leaves of pure input facts to ordinary arithmetic
without consuming or changing the spatial source. -/
private partial def pureLeaves (proposition : Expr) (term : String) : List String :=
  if proposition.isAppOfArity ``And 2 then
    pureLeaves proposition.getAppArgs[0]! (term ++ ".1") ++
      pureLeaves proposition.getAppArgs[1]! (term ++ ".2")
  else [term]

private def buffer? (e : Expr) : Option (Expr × Expr × Expr) := do
  if !e.isAppOf ``MachCSL.byteBuf then none
  else
    let a := e.getAppArgs
    some (a[a.size-3]!,a[a.size-2]!,a[a.size-1]!)

private def window? (e : Expr) : Option (Expr × Expr × Expr) := do
  if !e.isAppOf ``List.take then none
  else
    let a := e.getAppArgs
    let n := a[a.size-2]!
    let tail := a.back!
    if !tail.isAppOf ``List.drop then none
    else
      let b := tail.getAppArgs
      some (b.back!,b[b.size-2]!,n)

private def same (a b : Expr) : MetaM Bool :=
  withoutModifyingState <| withTransparency .reducible <| isDefEq a b

/-- Standard augmenting-path matching: the deterministic baseline solves
exactly the same injective assignment constraints as Z3. -/
private partial def augment (choices : Array (Array Nat)) (request : Nat)
    (seen : Array Nat) (owners : Array (Option Nat)) : Option (Array (Option Nat)) × Array Nat := Id.run do
  let mut visited := seen
  for candidate in choices[request]! do
    if !visited.contains candidate then
      visited := visited.push candidate
      match owners[candidate]! with
      | none => return (some (owners.set! candidate (some request)),visited)
      | some previous =>
        let (updated,seen') := augment choices previous visited owners
        visited := seen'
        if let some updated := updated then
          return (some (updated.set! candidate (some request)),visited)
  return (none,visited)

def deterministic (choices : Array (Array Nat)) : Option (Array Nat) := do
  let capacity := choices.foldl (fun n cs => cs.foldl (fun m i => max m (i+1)) n) 0
  let mut owners : Array (Option Nat) := Array.replicate capacity none
  for request in [:choices.size] do
    owners ← (augment choices request #[] owners).1
  let mut plan := #[]
  for request in [:choices.size] do
    let some i := owners.toList.idxOf? (some request) | none
    plan := plan.push i
  return plan

private def smtAssignment (choices : Array (Array Nat)) : TacticM (Array Nat) := do
  let vars := (List.range choices.size).map fun i => s!"r{i}"
  let declarations := vars.map fun v => s!"(declare-const {v} Int)"
  let constraints := choices.toList.zipIdx.map fun (cs,i) =>
    "(assert (or " ++ String.intercalate " " (cs.toList.map fun c => s!"(= r{i} {c})") ++ "))"
  let distinct := if vars.length < 2 then [] else ["(assert (distinct " ++ String.intercalate " " vars ++ "))"]
  let query := String.intercalate "\n" <| [
    s!"(set-option :timeout {resourcePlanner.timeout.get (← getOptions)})", "(set-logic QF_LIA)"] ++
    declarations ++ constraints ++ distinct ++ ["(check-sat)", "(get-value (" ++ String.intercalate " " vars ++ "))"]
  let output ← IO.Process.output {
    cmd := resourcePlanner.solver.get (← getOptions), args := #["-in", "-smt2"] } query
  unless output.exitCode == 0 && output.stdout.startsWith "sat\n" do
    throwError "resource planner: no assignment ({output.stdout.trimAscii}, {output.stderr.trimAscii})"
  let tokens := (output.stdout.replace "(" " " |>.replace ")" " " |>.replace "\n" " ").splitOn " " |>.filter (· != "")
  let mut result := #[]
  for symbol in vars do
    let some i := tokens.idxOf? symbol | throwError "resource planner: missing assignment"
    let some value := tokens[i+1]? >>= String.toNat? | throwError "resource planner: malformed assignment"
    result := result.push value
  return result

structure Route where
  source : Nat
  a : Expr
  dq : Expr
  bytes : Expr
  off : Expr
  len : Expr
  identity : Bool := false
  deriving Inhabited

private def sourceRoutes (sources : Array Expr) (request : Expr) (write : Bool) : MetaM (Array Route) := do
  let mut out := #[]
  for i in [:sources.size] do
    if !write && (← same sources[i]! request) then
      out := out.push ⟨i,request,request,request,request,request,true⟩
    else if let some (address,dq,bytes) := buffer? request then
      if let some (whole,off,len) := window? bytes then
        if let some (base,owned,contents) := buffer? sources[i]! then
          if (← same owned dq) && (← same contents whole) then
            let offset ← mkAppM ``BitVec.ofNat #[mkNatLit 64,off]
            let expected ← mkAppM ``HAdd.hAdd #[base,offset]
            if ← same address expected then
              out := out.push ⟨i,base,dq,contents,off,len,false⟩
  return out

private def render (e : Expr) : MetaM String := do
  return "(" ++ (← PrettyPrinter.ppExpr e).pretty ++ ")"

private def runPlan (P A B : Expr) (new? : Option Expr) (useSolver : Bool) (purePrefix : Nat) : TacticM Unit := do
  let sources := flatten P
  let requests := flatten A
  let returns := flatten B
  unless 0 < requests.size && requests.size ≤ 8 && sources.size ≤ 32 do
    throwError "resource planner: supported bounds are 1–8 requests and at most 32 source atoms"
  unless returns.size == requests.size do throwError "resource planner: unmatched return resources"
  let mut modes : Array (Array (Nat × Bool)) := #[]
  for request in requests do
    let mut postOptions := #[]
    for k in [:returns.size] do
      if ← same request returns[k]! then postOptions := postOptions.push (k,false)
      else if let some new := new? then
        if let some (a,q,_) := buffer? request then
          if let some (b,r,bs) := buffer? returns[k]! then
            if (← same a b) && (← same q r) && (← same bs new) then
              postOptions := postOptions.push (k,true)
    modes := modes.push postOptions
  let some postPlan := deterministic (modes.map (·.map Prod.fst)) |
    throwError "resource planner: return contract is not supported or duplicates a resource"
  let writes := modes.zip postPlan |>.map fun (ms,k) => (ms.find? (fun p => p.1 == k)).get!.2
  let mut routes := #[]
  for j in [:requests.size] do routes := routes.push (← sourceRoutes sources requests[j]! writes[j]!)
  let choices := routes.map (·.map Route.source)
  let plan ← if useSolver then smtAssignment choices else
    match deterministic choices with
    | some plan => pure plan
    | none => throwError "resource planner: no injective assignment"
  unless plan.size == requests.size && plan.toList.eraseDups.length == plan.size do
    throwError "resource planner: solver duplicated a spatial resource"
  let mut selected := #[]
  for j in [:requests.size] do
    let some r := routes[j]!.find? (·.source == plan[j]!) |
      throwError "resource planner: solver chose a forbidden resource"
    selected := selected.push r
  let stem := "rp_" ++ (← mkFreshId).toString.replace "." "_" ++ "_"
  let src := stem ++ "src_"
  let req := stem ++ "req_"
  let ret := stem ++ "ret_"
  let close := stem ++ "close_"
  let rebuilt := stem ++ "rebuilt_"
  let fresh := stem ++ "new"
  let length := stem ++ "length"
  let mut script := s!"iintro {(introPattern P src).1}\n"
  for i in [:sources.size] do
    if sources[i]!.isAppOf ``BIBase.pure then
      for (term,j) in (pureLeaves sources[i]!.getAppArgs.back! (src ++ toString i)).zipIdx do
        script := script ++ s!"have {stem}fact_{i}_{j} := {term}\n"
  let mut preNames := #[]
  for j in [:selected.size] do
    let route := selected[j]!
    if route.identity then preNames := preNames.push (src ++ toString route.source)
    else
      let rule := if writes[j]! then "Experiments.ResourcePlanner.write_window" else "Experiments.ResourcePlanner.read_window"
      let args := if writes[j]! then #[route.a,route.bytes,route.off,route.len]
        else #[route.a,route.dq,route.bytes,route.off,route.len]
      let terms ← args.mapM fun e => do render e
      script := script ++ s!"icases {rule} {String.intercalate " " terms.toList} (by omega) $$ {src}{route.source} with ⟨{req}{j}, {close}{j}⟩\n"
      preNames := preNames.push (req ++ toString j)
  for _ in [:purePrefix] do
    script := script ++ "isplitl []\n· solve | iframe % | (ipureintro; first | assumption | omega)\n"
  script := script ++ "isplitl [" ++ String.intercalate " " preNames.toList ++ "]\n· iframe " ++
    String.intercalate " " preNames.toList ++ "\n· "
  if new?.isSome then script := script ++ s!"iintro %{fresh} %{length} {(introPattern B ret).1}\n"
  else script := script ++ s!"iintro {(introPattern B ret).1}\n"
  let mut finalNames := #[]
  for j in [:selected.size] do
    let route := selected[j]!
    let returned := ret ++ toString postPlan[j]!
    if route.identity then finalNames := finalNames.push returned
    else
      script := script ++ s!"  ihave {rebuilt}{j} := {close}{j} $$ " ++
        (if writes[j]! then s!"%{fresh} %{length} " else "") ++ returned ++ "\n"
      finalNames := finalNames.push (rebuilt ++ toString j)
  for i in [:sources.size] do
    if !plan.contains i && !sources[i]!.isAppOf ``BIBase.pure then finalNames := finalNames.push (src ++ toString i)
  script := script ++ "  iframe " ++ String.intercalate " " finalNames.toList ++ "\n  all_goals try (iframe %)\n  all_goals first | assumption | (ipureintro; first | assumption | omega)"
  if resourcePlanner.trace.get (← getOptions) then
    logInfo m!"resource planner: {if useSolver then "z3" else "deterministic"}; candidates={choices}; plan={plan}; returns={postPlan}"
  let parsed := Parser.runParserCategory (← getEnv) `tactic ("(\n" ++ script ++ "\n)")
  let .ok stx := parsed | throwError "resource planner: replay stx failure {parsed.toOption}\n{script}"
  withoutRecover <| evalTactic stx
  unless (← getGoals).isEmpty do throwError "resource planner: replay left obligations"

private def planGoal (write useSolver : Bool) : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← (← getMainGoal).getType)
  let some (_,_,P,result) := parseEntails? target | throwError "resource planner: expected an Iris entailment"
  let mut remaining := result
  let mut purePrefix := 0
  while purePrefix < 8 do
    let some (fact,rest) := pair? ``BIBase.sep remaining | break
    unless fact.isAppOf ``BIBase.pure do break
    purePrefix := purePrefix + 1
    remaining := rest
  let some (A,closing) := pair? ``BIBase.sep remaining | throwError "resource planner: expected a request and closing wand"
  if write then
    unless closing.isAppOf ``BIBase.forall do throwError "resource planner: expected arbitrary returned bytes"
    let .lam _ ty body _ := closing.getAppArgs.back! | throwError "resource planner: expected a return binder"
    withLocalDeclD `resource_return ty fun new => do
      let some (_,rest) := pair? ``BIBase.wand (body.instantiate1 new) |
        throwError "resource planner: expected a returned-length premise"
      let some (B,_) := pair? ``BIBase.wand rest | throwError "resource planner: expected returned ownership"
      runPlan P A B (some new) useSolver purePrefix
  else
    let some (B,_) := pair? ``BIBase.wand closing | throwError "resource planner: expected a closing wand"
    runPlan P A B none useSolver purePrefix

elab "resource_read" : tactic => planGoal false false
elab "resource_read_smt" : tactic => planGoal false true
elab "resource_write" : tactic => planGoal true false
elab "resource_write_smt" : tactic => planGoal true true

end Experiments.ResourcePlanner
