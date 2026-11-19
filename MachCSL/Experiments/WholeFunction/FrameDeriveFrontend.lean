import Experiments.WholeFunction.FrameDerive

/-! Proof-producing static-frame derivation. Only actual rows are input. The
frontend reifies the existing mixed decoder; all values and safety claims are
replayed with the existing evaluator and checked by Lean's kernel. -/
namespace Xv6.WholeFunction.FrameDerive.Frontend
open Lean Meta Elab Tactic MachCSL FrameCompiler
open LeanRV64D (instruction)

private def natValue (e : Lean.Expr) : MetaM Nat := do
  let e ← withTransparency .all <| reduce e
  let some n ← getNatValue? e | throwError "derive_frame: expected a closed natural"
  return n

private def bvValue (e : Lean.Expr) : MetaM Nat := do
  natValue (← mkAppM ``BitVec.toNat #[e])

private partial def compact (e : Lean.Expr) : MetaM Lean.Expr := do
  if ← isProof e then return ← mkAuxTheorem (← inferType e) e
  let type ← whnf (← inferType e)
  if type.isAppOfArity ``BitVec 1 then
    return mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit (← natValue type.getAppArgs[0]!)) (mkNatLit (← bvValue e))
  if type.isConstOf ``Nat then return mkNatLit (← natValue e)
  let e ← withTransparency .all <| whnf e
  if e.isApp then
    return mkAppN e.getAppFn (← e.getAppArgs.mapM compact)
  return e

private partial def rowsOf (rows : Lean.Expr) : MetaM (Array Lean.Expr) := do
  let rows ← withTransparency .all <| whnf rows
  if rows.isAppOfArity ``List.nil 1 then return #[]
  unless rows.isAppOfArity ``List.cons 3 do throwError "derive_frame: rows must be closed"
  return #[rows.getAppArgs[1]!] ++ (← rowsOf rows.getAppArgs[2]!)

private def decode (slots : Nat) (row : Lean.Expr) : MetaM Lean.Expr := do
  let code ← mkAppM ``Binary.Row.code #[row]
  let decoded ← withTransparency .all <| whnf (← mkAppM ``MixedAction.decode #[mkNatLit slots, code])
  unless decoded.isAppOfArity ``Option.some 2 do throwError "derive_frame: unsupported actual instruction"
  compact (← mkAppM ``Subtype.val #[decoded.getAppArgs[1]!])

private def stackAction (action : Lean.Expr) : MetaM Lean.Expr := do
  unless action.isAppOfArity ``MixedAction.stack 1 do throwError "derive_frame: expected a stack action"
  return action.getAppArgs[0]!

private def makePlan (rows actions : Array Lean.Expr) : MetaM Lean.Expr := do
  let entries ← rows.zip actions |>.mapM fun (row, action) => do
    let pc ← compact (← mkAppM ``Binary.Row.pc #[row])
    let rvc ← compact (← mkAppM ``Binary.Row.rvc #[row])
    mkAppM ``Prod.mk #[pc, ← mkAppM ``Prod.mk #[rvc, action]]
  let type ← mkAppM ``Prod #[mkApp (mkConst ``BitVec) (mkNatLit 64),
    ← mkAppM ``Prod #[mkConst ``Bool, mkConst ``MixedAction]]
  mkListLit type entries.toList

/-- Derive a sparse static frame, then replay universal safety/value goals.
This frontend requires a balanced single-ADDI push/pop pair: frame sizes are
8 through 2040 bytes. Although -2048 is a valid signed 12-bit push immediate,
+2048 cannot be represented by the required single pop instruction, so that
otherwise valid allocation is deliberately outside this static-frame fragment.
Branches, missing/duplicate restores, malformed offsets, and wrong frame setup
are rejected; an incomplete generated proof is never accepted as a certificate. -/
elab "derive_frame" : tactic => do
  let goal ← getMainGoal
  let pending := (← getGoals).tail
  goal.withContext do
    let target := (← instantiateMVars (← goal.getType)).consumeMData
    unless target.isAppOfArity ``Certificate 3 do throwError "derive_frame: expected FrameDerive.Certificate"
    let push := target.getAppArgs[0]!
    let saves := target.getAppArgs[1]!
    let returns := target.getAppArgs[2]!
    if push.hasFVar || saves.hasFVar || returns.hasFVar then
      throwError "derive_frame: actual row inputs must be closed"
    let pushCode ← withTransparency .all <| reduce (← mkAppM ``Binary.Row.code #[push])
    unless pushCode.isAppOfArity ``instruction.ITYPE 1 do throwError "derive_frame: expected an ADDI stack allocation"
    let tuple := pushCode.getAppArgs[0]!
    let imm ← compact (← mkAppM ``Prod.fst #[tuple])
    let immediate ← bvValue imm
    unless immediate > 2048 && (4096 - immediate) % 8 == 0 do
      throwError "derive_frame: balanced single-ADDI frames require an aligned size from 8 through 2040 bytes"
    let slots := (4096 - immediate) / 8
    let saveRows ← rowsOf saves
    let returnRows ← rowsOf returns
    unless !saveRows.isEmpty && returnRows.size ≥ 2 do throwError "derive_frame: missing save/setup or return rows"
    let saveActions ← saveRows.mapM fun row => do return ← decode slots row
    let returnActions ← returnRows.mapM fun row => do return ← decode slots row
    let mut saved : Array Lean.Expr := #[]
    let mut map : Array (Nat × Nat) := #[]
    for action in saveActions.extract 0 (saveActions.size - 1) do
      let a ← stackAction action
      unless a.isAppOfArity ``Stack.Action.save 3 do throwError "derive_frame: non-store in static save prefix"
      let reg := a.getAppArgs[1]!
      let slot := a.getAppArgs[2]!
      let pair := (← natValue slot, ← bvValue reg)
      if map.any (fun p => p.1 == pair.1 || p.2 == pair.2) then
        throwError "derive_frame: duplicate saved slot or register"
      map := map.push pair
      saved := saved.push (← mkAppM ``Prod.mk #[slot, reg])
    unless map.any (fun p => p.2 == 1) do throwError "derive_frame: original RA is not saved"
    let setup := saveActions.back!
    unless setup.isAppOfArity ``MixedAction.reg 1 &&
        setup.getAppArgs[0]!.isAppOfArity ``RegAction.addi 4 do
      throwError "derive_frame: expected final frame-pointer ADDI"
    let fp := setup.getAppArgs[0]!
    unless (← bvValue fp.getAppArgs[1]!) == 8 && (← bvValue fp.getAppArgs[2]!) == 2 do
      throwError "derive_frame: frame-pointer setup must target s0 from sp"
    let mut restored : Array Lean.Expr := #[]
    let mut seen : Array (Nat × Nat) := #[]
    for action in returnActions.extract 0 (returnActions.size - 2) do
      let a ← stackAction action
      unless a.isAppOfArity ``Stack.Action.load 4 do throwError "derive_frame: non-load in static restore prefix"
      let pair := (← natValue a.getAppArgs[2]!, ← bvValue a.getAppArgs[1]!)
      unless map.contains pair && !seen.contains pair do
        throwError "derive_frame: restore does not match a unique saved slot/register"
      seen := seen.push pair
      restored := restored.push (← mkAppOptM ``Subtype.mk #[some (mkApp (mkConst ``BitVec) (mkNatLit 5)),
        some (mkConst ``rdOk), some a.getAppArgs[1]!, some a.getAppArgs[3]!])
    unless seen.size == map.size do throwError "derive_frame: missing saved-register restore"
    let pop ← stackAction returnActions[returnActions.size - 2]!
    unless pop.isAppOfArity ``Stack.Action.pop 3 do throwError "derive_frame: expected balanced stack pop"
    let ret := returnActions.back!
    unless ret.isAppOfArity ``MixedAction.reg 1 && ret.getAppArgs[0]!.isAppOfArity ``RegAction.ret 1 &&
        (← bvValue ret.getAppArgs[0]!.getAppArgs[0]!) == 1 do
      throwError "derive_frame: expected return through restored RA"
    let savedType ← mkAppM ``Prod #[mkConst ``Nat, mkApp (mkConst ``BitVec) (mkNatLit 5)]
    let savedExpr ← mkListLit savedType saved.toList
    let registers ← mkListLit (mkConst ``SavedReg) restored.toList
    let popImm := pop.getAppArgs[0]!
    let popOffset := pop.getAppArgs[2]!
    let pushed ← decode slots push
    let pushed ← stackAction pushed
    unless pushed.isAppOfArity ``Stack.Action.push 3 do throwError "derive_frame: wrong allocation opcode"
    let layout ← mkAppM ``Layout.mk #[mkNatLit slots, registers, popImm, imm, popOffset, pushed.getAppArgs[2]!]
    let body ← compact (← mkAppM ``Binary.Row.next #[saveRows.back!])
    let returnPc ← compact (← mkAppM ``Binary.Row.pc #[returnRows[0]!])
    let savePlan ← makePlan saveRows saveActions
    let returnPlan ← makePlan returnRows returnActions
    let base := mkAppN (mkConst ``Certificate.mk) #[push, saves, returns,
      layout, savedExpr, body, returnPc, savePlan, returnPlan]
    let (obligations, _, _) ← forallMetaTelescopeReducing (← inferType base)
    goal.assign (mkAppN base obligations)
    setGoals (obligations.toList.map Lean.Expr.mvarId!)
    evalTactic (← `(tactic|
      all_goals first | binary_rfl | skip))
    let nextExpr ← mkAppM ``Binary.Row.next #[push]
    let nextValue ← compact nextExpr
    let nextEq ← mkEq nextExpr nextValue
    let nextProof ← mkAuxTheorem nextEq (← mkEqRefl nextExpr)
    let mut noted := []
    for g in ← getGoals do
      let (_, g) ← g.note `frame_next nextProof
      noted := noted ++ [g]
    setGoals noted
    evalTactic (← `(tactic|
      all_goals intros))
    evalTactic (← `(tactic|
      all_goals simp_all [FrameCompiler.planSafe, FrameCompiler.evalPlan,
        FrameCompiler.supported, FrameCompiler.saving, FrameCompiler.eval,
        StackValues.supported, StackValues.eval, StackReturn.supported, StackReturn.eval,
        MixedAction.Enabled, Stack.Action.Enabled, rawCells, savedState, returnedState,
        FrameEffects.initialContext, FrameEffects.restoredContext,
        savedCells, writeCell, Layout.restore, Layout.registers,
        Stack.addresses, List.range_succ, List.ofFn_succ, instrLen,
        RegAction.run, Stack.State.machine, KCtx.push_sp, KCtx.push_regs,
        KCtx.pop_regs, KCtx.setReg_regs, KCtx.setReg_sp, KCtx.rget_ne,
        KCtx.sp, RegMap.set_apply, BitVec.sub_add_cancel]))
    evalTactic (← `(tactic| all_goals bv_omega))
    unless (← getGoals).isEmpty do throwError "derive_frame: a safety or value obligation remains"
    setGoals pending

end Xv6.WholeFunction.FrameDerive.Frontend
