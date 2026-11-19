import Experiments.WholeFunction.KernelDispatch

/-! A callsite is checked binary metadata, not another instruction interpreter.
The JAL return address and the semantic callee continuation are deliberately
separate: a summary may consume a following load before it returns control. -/
namespace Xv6.WholeFunction
open MachCSL LeanRV64D

structure CallSite (rows : List Binary.Row) (pc target returnPC : BitVec 64) where
  located : LocatedCall pc
  found : findCall pc rows = some located
  linked : located.jump.link = 1#5
  target_eq : located.target = target
  return_eq : located.row.pc + instrLen located.row.rvc = returnPC
  ordinary_miss : ∀ slots, findMixed slots pc rows = none

namespace CallSite
variable {S : Type} {rows : List Binary.Row} {pc target returnPC : BitVec 64}

theorem unique_target {target' returnPC' : BitVec 64}
    (a : CallSite rows pc target returnPC) (b : CallSite rows pc target' returnPC') : target = target' := by
  have same := Option.some.inj (a.found.symm.trans b.found)
  exact a.target_eq.symm.trans ((congrArg LocatedCall.target same).trans b.target_eq)

theorem unique_return {target' returnPC' : BitVec 64}
    (a : CallSite rows pc target returnPC) (b : CallSite rows pc target' returnPC') : returnPC = returnPC' := by
  have same := Option.some.inj (a.found.symm.trans b.found)
  exact a.return_eq.symm.trans
    ((congrArg (fun r => r.row.pc + instrLen r.row.rvc) same).trans b.return_eq)

def entry (machine : S → Stack.State) (withMachine : S → Stack.State → S)
    (s : S) (target returnPC : BitVec 64) : S :=
  withMachine s ⟨(machine s).ctx.setReg 1#5 returnPC, target, (machine s).cells⟩

theorem entry_eq (D : Dispatcher S) (site : CallSite D.rows pc target returnPC)
    (s : S) (address : (D.machine s).pc = pc) (r : LocatedCall (D.machine s).pc)
    (found : findCall (D.machine s).pc D.rows = some r) :
    D.callEntry s r = entry D.machine D.withMachine s target returnPC := by
  subst pc
  rw [site.found] at found
  cases Option.some.inj found
  simp only [Dispatcher.callEntry, jalRun, entry, site.linked, site.return_eq]
  have target := site.target_eq
  unfold LocatedCall.target at target
  rw [target]

theorem entry_machine (D : Dispatcher S) (s : S) (target returnPC : BitVec 64) :
    D.machine (entry D.machine D.withMachine s target returnPC) =
      ⟨(D.machine s).ctx.setReg 1#5 returnPC,target,(D.machine s).cells⟩ := D.machine_with _ _

theorem entry_saved (D : Dispatcher S) (s : S) (target returnPC : BitVec 64) :
    calleeSaved (D.machine s).ctx.regs
      (D.machine (entry D.machine D.withMachine s target returnPC)).ctx.regs := by
  rw [entry_machine]
  simp [calleeSaved,KCtx.setReg_regs,RegMap.set_apply]

theorem entry_reg (D : Dispatcher S) (s : S) (target returnPC : BitVec 64)
    (r : BitVec 5) (other : r ≠ 1#5) :
    (D.machine (entry D.machine D.withMachine s target returnPC)).ctx.regs r =
      (D.machine s).ctx.regs r := by
  rw [entry_machine]
  simp [KCtx.setReg_regs,RegMap.set_apply,other]

theorem entry_link (D : Dispatcher S) (s : S) (target returnPC : BitVec 64) :
    (D.machine (entry D.machine D.withMachine s target returnPC)).ctx.regs 1#5 = returnPC := by
  rw [entry_machine]
  simp [KCtx.setReg_regs,RegMap.set_apply]

end CallSite
end Xv6.WholeFunction


/-! Derive callsite metadata from the actual decoder lookup. Clients state
only the intended PC, callee and return address; no instruction immediate or
register AST is handwritten. Every generated obligation is kernel checked. -/
namespace Xv6.WholeFunction
open MachCSL LeanRV64D

noncomputable def CallSite.of_computed (rows : List Binary.Row)
    (pc target returnPC : BitVec 64) (available : (findCall pc rows).isSome = true)
    (linked : ((findCall pc rows).get available).jump.link = 1#5)
    (target_eq : ((findCall pc rows).get available).target = target)
    (return_eq : ((findCall pc rows).get available).row.pc +
      instrLen ((findCall pc rows).get available).row.rvc = returnPC)
    (ordinary_miss : ∀ slots, findMixed slots pc rows = none) : CallSite rows pc target returnPC where
  located := (findCall pc rows).get available
  found := (Option.some_get available).symm
  linked := linked
  target_eq := target_eq
  return_eq := return_eq
  ordinary_miss := ordinary_miss

open Lean Meta Elab Tactic in
elab "callsite_rfl" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let type ← instantiateMVars (← goal.getType)
    let some (_, lhs, rhs) := type.eq? | throwError "expected a call metadata equality"
    unless ← withTransparency .all (isDefEq lhs rhs) do
      throwError "call metadata does not match the decoded instruction: {type}"
    let proof ← mkAuxTheorem type (← mkEqRefl lhs)
    goal.assign proof
    replaceMainGoal []

macro "checked_callsite" : tactic => `(tactic|
  exact CallSite.of_computed _ _ _ _ (by callsite_rfl) (by callsite_rfl)
    (by callsite_rfl) (by callsite_rfl) (by intro slots; callsite_rfl))

end Xv6.WholeFunction
