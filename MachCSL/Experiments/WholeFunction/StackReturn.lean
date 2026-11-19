import Experiments.WholeFunction.StackValueWp

/-! A value-sensitive return compiler. Its pure checker functionalizes the
existing stack-load/pop/return relation; `Linear.wp_rows` supplies every spatial
instruction proof and hart migration. The concrete plan is checked against
the complete actual copyin epilogue, with no import of ProofCopyin.
-/
namespace Xv6.WholeFunction.StackReturn
open Iris Iris.BI Iris.ProgramLogic MachCSL LeanRV64D
open StackValues (frameCells saveRegisters)
set_option linter.unusedSimpArgs false

def supported : MixedAction → Prop
  | .stack (.load ..) | .stack (.pop ..) => True
  | .reg (.ret rs) => rs ≠ 4#5
  | _ => False

def eval (a : MixedAction) (rvc : Bool) (s : Stack.State) : Stack.State :=
  match a with
  | .stack (.load _ rd i _) =>
    ⟨s.ctx.setReg rd (s.cells[i]?.getD (0#64, 0#64)).2, s.pc + instrLen rvc, s.cells⟩
  | .stack (.pop _ n _) => ⟨s.ctx.pop n, s.pc + instrLen rvc, []⟩
  | .reg a =>
    let r := a.run rvc ⟨0, by decide⟩ s.machine
    ⟨r.ctx, r.pc, s.cells⟩
  | _ => s

theorem next_eq_eval (a : MixedAction) (rvc : Bool) (cpu : CPU) (s t : Stack.State)
    (hs : supported a) (hn : a.Next rvc cpu s t) : t = eval a rvc s := by
  cases a with
  | reg a =>
    cases a <;> try exact False.elim hs
    rename_i rs
    cases hn
    simp only [eval, RegAction.run, Stack.State.machine]
    rw [StackValues.rget_hart_independent _ _ hs cpu ⟨0, by decide⟩]
  | stack a =>
    cases a <;> try exact False.elim hs
    · rename_i imm rd i valid
      obtain ⟨c, lookup, rfl⟩ := hn
      simp only [eval, lookup, Option.getD_some]
    · cases hn; rfl

abbrev Plan := List (BitVec 64 × Bool × MixedAction)

def planSafe : Plan → Stack.State → Prop
  | [], _ => True
  | (pc, rvc, a) :: rest, s => s.pc = pc ∧ supported a ∧ a.Enabled s ∧
      planSafe rest (eval a rvc s)

def evalPlan (p : Plan) (s : Stack.State) : Stack.State :=
  p.foldl (fun s a => eval a.2.2 a.2.1 s) s

def compileRows (slots : Nat) (rows : List Binary.Row) : List (Option (BitVec 64 × Bool × MixedAction)) :=
  rows.map fun row => (MixedAction.decode slots row.code).map fun a => (row.pc, row.rvc, a.val)

/-- A pure symbolic execution certificate implies the actual linear
backend's universal safety condition, including every possible hart.
-/
theorem plan_safe {slots : Nat} {rows : List Binary.Row} {p : Plan}
    (compiled : compileRows slots rows = p.map some) (s : Stack.State)
    (safe : planSafe p s) : Linear.Safe slots rows s := by
  induction rows generalizing p s with
  | nil => trivial
  | cons row rows ih =>
    cases p with
    | nil => simp [compileRows] at compiled
    | cons head p =>
      cases hd : MixedAction.decode slots row.code with
      | none => simp [compileRows, hd] at compiled
      | some a =>
        simp only [compileRows, List.map_cons, hd, Option.map_some,
          List.cons.injEq, Option.some.injEq] at compiled
        obtain ⟨rfl, hc⟩ := compiled
        obtain ⟨hp, hs, he, ht⟩ := safe
        refine ⟨a, hd, hp, he, ?_⟩
        intro cpu t hn
        rw [next_eq_eval a.val row.rvc cpu s t hs hn]
        exact ih hc _ ht

theorem plan_values {slots : Nat} {rows : List Binary.Row} {p : Plan}
    (compiled : compileRows slots rows = p.map some) {s t : Stack.State}
    (safe : planSafe p s) (run : Linear.RowRun slots rows s t) : t = evalPlan p s := by
  induction run generalizing p with
  | nil =>
    cases p with
    | nil => rfl
    | cons => simp [compileRows] at compiled
  | cons row a cpu hd hp hn tail ih =>
    cases p with
    | nil => simp [compileRows] at compiled
    | cons head p =>
      simp only [compileRows, List.map_cons, hd, Option.map_some,
        List.cons.injEq, Option.some.injEq] at compiled
      obtain ⟨rfl, hc⟩ := compiled
      obtain ⟨_, hs, _, ht⟩ := safe
      have he := next_eq_eval a.val row.rvc cpu _ _ hs hn
      subst he
      exact ih hc ht

noncomputable def rows : List Binary.Row := Binary.copyin.rows.drop 51 |>.take 14

/-- Expected decoder output, not executable compiler input. -/
def plan : Plan :=
  [(0x80001704#64, true, .stack (.load 88#12 1#5 0 (by decide))),
   (0x80001706#64, true, .stack (.load 80#12 8#5 1 (by decide))),
   (0x80001708#64, true, .stack (.load 72#12 9#5 2 (by decide))),
   (0x8000170a#64, true, .stack (.load 64#12 18#5 3 (by decide))),
   (0x8000170c#64, true, .stack (.load 56#12 19#5 4 (by decide))),
   (0x8000170e#64, true, .stack (.load 48#12 20#5 5 (by decide))),
   (0x80001710#64, true, .stack (.load 40#12 21#5 6 (by decide))),
   (0x80001712#64, true, .stack (.load 32#12 22#5 7 (by decide))),
   (0x80001714#64, true, .stack (.load 24#12 23#5 8 (by decide))),
   (0x80001716#64, true, .stack (.load 16#12 24#5 9 (by decide))),
   (0x80001718#64, true, .stack (.load 8#12 25#5 10 (by decide))),
   (0x8000171a#64, true, .stack (.load 0#12 26#5 11 (by decide))),
   (0x8000171c#64, true, .stack (.pop 96#12 12 (by decide))),
   (0x8000171e#64, true, .reg (.ret 1#5))]

set_option maxHeartbeats 0 in
theorem binary : compileRows 12 rows = plan.map some := by binary_rfl

def restore (entry current : KCtx) : KCtx :=
  saveRegisters.foldl (fun k r => k.setReg r (entry.regs r)) current

def result (entry current : KCtx) : Stack.State :=
  ⟨(restore entry current).pop 12, jumpPc (entry.regs 1#5), []⟩

set_option maxHeartbeats 0 in
theorem copyin_safe (entry current : KCtx) (sp : current.sp = entry.sp - 96#64) :
    planSafe plan ⟨current, 0x80001704#64, frameCells entry⟩ := by
  simp [planSafe, plan, supported, MixedAction.Enabled, Stack.Action.Enabled,
    eval, frameCells, Stack.addresses, saveRegisters, List.range_succ, instrLen,
    KCtx.setReg_sp, sp, RegAction.run, Stack.State.machine]
  all_goals bv_omega

set_option maxHeartbeats 0 in
theorem copyin_values (entry current : KCtx) :
    evalPlan plan ⟨current, 0x80001704#64, frameCells entry⟩ = result entry current := by
  simp [evalPlan, plan, eval, frameCells, Stack.addresses, saveRegisters, List.range_succ,
    instrLen, RegAction.run, Stack.State.machine, restore, result, KCtx.rget_ne,
    KCtx.pop_regs, KCtx.setReg_regs, RegMap.set_apply]

theorem result_calleeSaved (entry current : KCtx)
    (sp : current.sp = entry.sp - 96#64)
    (s11 : current.regs 27#5 = entry.regs 27#5) :
    calleeSaved entry.regs (result entry current).ctx.regs := by
  change current.regs 2#5 = entry.regs 2#5 - 96#64 at sp
  simp [calleeSaved, result, restore, saveRegisters, KCtx.pop_regs, KCtx.setReg_regs,
    RegMap.set_apply, KCtx.setReg_sp, sp, s11, KCtx.sp, BitVec.sub_add_cancel]

theorem result_a0 (entry current : KCtx) :
    (result entry current).ctx.regs 10#5 = current.regs 10#5 := by
  simp [result, restore, saveRegisters, KCtx.pop_regs, KCtx.setReg_regs, RegMap.set_apply]

theorem result_base (entry base : KCtx) (R : RegMap) (available : 12 ≤ base.avail) :
    (result entry ((base.pushed 12).withRegs R)).ctx =
      base.withRegs (result entry ((base.pushed 12).withRegs R)).ctx.regs := by
  apply KCtx.eq_withRegs
  all_goals simp [result, restore, saveRegisters, KCtx.pushed, KCtx.withRegs]
  omega

theorem result_indices (entry current : KCtx) :
    (result entry current).ctx.sie = current.sie ∧
    (result entry current).ctx.proc = current.proc := by
  simp [result, restore, saveRegisters]

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
variable [CurCtx] [KernelGeom] [KernelImage GF]

/-- All fourteen actual epilogue instructions, with exact restored register
values, released frame ownership, and the saved RA as the return target.
-/
theorem wp_copyin_return (entry current : KCtx) (cpu : CPU)
    (sp : current.sp = entry.sp - 96#64) :
    mixedOwn (GF := GF) cpu ⟨current, 0x80001704#64, frameCells entry⟩ ∗
      wpNext current.sie current.proc cpu (fun cpu' => iprop(
        mixedOwn cpu' (result entry current) -∗ wpLoop cpu')) ⊢ wpLoop cpu := by
  iintro ⟨Hstate, Hexit⟩
  iapply Linear.wp_rows 12 rows cpu _ (plan_safe binary _ (copyin_safe entry current sp))
    $$ [$Hstate Hexit]
  iapply wpNext_mono _ _ _ _ _ $$ Hexit
  iintro %cpu' Hexit %t %hr Hstate
  have he := plan_values binary (copyin_safe entry current sp) hr
  rw [copyin_values] at he
  rw [he]
  iapply Hexit $$ Hstate

end Xv6.WholeFunction.StackReturn

open Lean in
run_cmd do
  let baseline ← collectAxioms ``Xv6.WholeFunction.MixedAction.sound
  for decl in #[``Xv6.WholeFunction.StackReturn.binary,
      ``Xv6.WholeFunction.StackReturn.copyin_safe,
      ``Xv6.WholeFunction.StackReturn.copyin_values,
      ``Xv6.WholeFunction.StackReturn.wp_copyin_return] do
    let axioms ← collectAxioms decl
    let extra := axioms.filter fun a => !baseline.contains a
    unless extra.isEmpty do throwError "{decl}: new axioms {extra}"
    if axioms.contains ``sorryAx then throwError "{decl}: contains sorryAx"
  logInfo "Copyin epilogue adds no axioms beyond the checked mixed backend."
