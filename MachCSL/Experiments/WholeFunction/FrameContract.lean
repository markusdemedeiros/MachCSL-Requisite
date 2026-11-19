import Experiments.WholeFunction.FrameCompiler

/-! The common two-slot frame saving `ra` and `s0`, proved once for arbitrary
instruction addresses. Clients supply decoder certificates for their actual
rows; arbitrary initial stack contents and migration remain handled here. -/
namespace Xv6.WholeFunction.FrameContract
open Iris Iris.BI Iris.ProgramLogic MachCSL LeanRV64D FrameCompiler
set_option linter.unusedSimpArgs false

def layout : Layout := {
  slots := 2
  saved := [⟨1, by decide⟩, ⟨8, by decide⟩]
  popImm := 16#12
  pushImm := 4080#12
  popOffset := by decide
  pushOffset := by decide }

def frameCells (entry : KCtx) : List Stack.Cell := layout.frameCells entry []

def initialMachine (entry : KCtx) (pc : BitVec 64) : Stack.State :=
  ⟨(entry.push 2).setReg 8#5 entry.sp, pc, frameCells entry⟩

def returnResult (entry current : KCtx) : Stack.State :=
  ⟨(layout.restore entry current).pop 2, jumpPc (entry.regs 1#5), []⟩

def rawCells (entry : KCtx) (values : Fin 2 → BitVec 64) : List Stack.Cell :=
  (Stack.addresses entry.sp 2).zip (List.ofFn values)

set_option maxHeartbeats 0 in
theorem save_safe (entry : KCtx) (values : Fin 2 → BitVec 64) (pc : BitVec 64) :
    planSafe (layout.savePlan pc) ⟨entry.push 2, pc, rawCells entry values⟩ := by
  simp [planSafe, Layout.savePlan, layout, supported, saving,
    StackValues.supported, MixedAction.Enabled, Stack.Action.Enabled,
    eval, StackValues.eval, rawCells, Stack.addresses, List.range_succ, List.ofFn_succ,
    instrLen, KCtx.push_sp, KCtx.setReg_sp, RegAction.run, Stack.State.machine]
  all_goals bv_omega

set_option maxHeartbeats 0 in
theorem save_values (entry : KCtx) (values : Fin 2 → BitVec 64) (pc : BitVec 64) :
    evalPlan (layout.savePlan pc) ⟨entry.push 2, pc, rawCells entry values⟩ =
      initialMachine entry (pc + 6#64) := by
  simp [evalPlan, Layout.savePlan, layout, saving, eval, StackValues.eval,
    rawCells, Stack.addresses, List.range_succ, List.ofFn_succ, instrLen,
    RegAction.run, Stack.State.machine, initialMachine, frameCells, Layout.frameCells,
    Layout.registers, KCtx.push_sp, KCtx.push_regs, KCtx.setReg_regs, RegMap.set_apply,
    KCtx.rget_ne, KCtx.sp, BitVec.sub_add_cancel, BitVec.add_assoc]

set_option maxHeartbeats 0 in
theorem return_safe (entry current : KCtx) (pc : BitVec 64) (sp : current.sp = entry.sp - 16#64) :
    planSafe (layout.returnPlan pc) ⟨current, pc, frameCells entry⟩ := by
  simp [planSafe, Layout.returnPlan, layout, supported, saving, StackReturn.supported,
    MixedAction.Enabled, Stack.Action.Enabled, eval, StackReturn.eval, frameCells, Layout.frameCells,
    Layout.registers, Stack.addresses, List.range_succ, instrLen, KCtx.setReg_sp, sp,
    RegAction.run, Stack.State.machine]
  all_goals bv_omega

set_option maxHeartbeats 0 in
theorem return_values (entry current : KCtx) (pc : BitVec 64) :
    evalPlan (layout.returnPlan pc) ⟨current, pc, frameCells entry⟩ = returnResult entry current := by
  simp [evalPlan, Layout.returnPlan, layout, saving, eval, StackReturn.eval,
    frameCells, Layout.frameCells, Layout.registers, Stack.addresses, List.range_succ,
    instrLen, RegAction.run, Stack.State.machine, returnResult, Layout.restore,
    KCtx.rget_ne, KCtx.pop_regs, KCtx.setReg_regs, RegMap.set_apply]

theorem result_a0 (entry current : KCtx) :
    (returnResult entry current).ctx.regs 10#5 = current.regs 10#5 := by
  simp [returnResult, Layout.restore, Layout.registers, layout, KCtx.pop_regs, KCtx.setReg_regs, RegMap.set_apply]

theorem result_base (entry base : KCtx) (R : RegMap) (available : 2 ≤ base.avail) :
    (returnResult entry ((base.pushed 2).withRegs R)).ctx =
      base.withRegs (returnResult entry ((base.pushed 2).withRegs R)).ctx.regs := by
  apply KCtx.eq_withRegs
  all_goals simp [returnResult, Layout.restore, Layout.registers, layout, KCtx.pushed, KCtx.withRegs]
  omega

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
variable [CurCtx] [KernelGeom] [KernelImage GF]

/-- Actual decoder evidence is supplied independently for each binary. -/
theorem wp_prologue (push : Binary.Row) (rows : List Binary.Row)
    (pushCode : push.code = (.stack (.push layout.pushImm 2 layout.pushOffset) : MixedAction).code)
    (compiled : compileRows 2 rows = (layout.savePlan push.next).map some)
    (cpu : CPU) (entry : KCtx) (available : 2 ≤ entry.avail) :
    kernelText (GF := GF) ∗ kctx cpu entry ∗ pcIs cpu push.pc ∗
      wpNext entry.sie entry.proc cpu (fun cpu' => iprop(
        mixedOwn cpu' (initialMachine entry (push.next + 6#64)) -∗ wpLoop cpu'))
      ⊢ wpLoop cpu := by
  have safe (cells : List Stack.Cell) (shape : cells.map Prod.fst = Stack.addresses entry.sp 2) :
      planSafe (layout.savePlan push.next) ⟨entry.push 2, push.next, cells⟩ := by
    obtain ⟨values, rfl⟩ := cells_values entry.sp 2 cells shape
    exact save_safe entry values push.next
  have rule := wp_push_plan (GF := GF) layout push rows (layout.savePlan push.next)
    pushCode compiled cpu entry available safe
  simp only [show layout.slots = 2 from rfl] at rule
  iintro ⟨#HT, HK, HPC, Hexit⟩
  iapply rule $$ [$HT $HK $HPC Hexit]
  iapply wpNext_mono _ _ _ _ _ $$ Hexit
  iintro %cpu' Hexit %cells %shape Hstate
  obtain ⟨values, rfl⟩ := cells_values entry.sp 2 cells shape
  have eq := save_values entry values push.next
  change evalPlan (layout.savePlan push.next)
    ⟨entry.push 2, push.next, (Stack.addresses entry.sp 2).zip (List.ofFn values)⟩ = _ at eq
  rw [eq]
  iapply Hexit $$ Hstate

theorem wp_return (rows : List Binary.Row) (pc : BitVec 64)
    (compiled : compileRows 2 rows = (layout.returnPlan pc).map some)
    (entry current : KCtx) (cpu : CPU) (sp : current.sp = entry.sp - 16#64) :
    mixedOwn (GF := GF) cpu ⟨current, pc, frameCells entry⟩ ∗
      wpNext current.sie current.proc cpu (fun cpu' => iprop(
        mixedOwn cpu' (returnResult entry current) -∗ wpLoop cpu')) ⊢ wpLoop cpu := by
  have rule := wp_plan (GF := GF) compiled cpu _ (return_safe entry current pc sp)
  rw [return_values] at rule
  exact rule

end Xv6.WholeFunction.FrameContract

open Lean in
run_cmd do
  for decl in #[``Xv6.WholeFunction.FrameContract.save_safe,
      ``Xv6.WholeFunction.FrameContract.save_values,
      ``Xv6.WholeFunction.FrameContract.return_safe,
      ``Xv6.WholeFunction.FrameContract.return_values,
      ``Xv6.WholeFunction.FrameContract.result_a0,
      ``Xv6.WholeFunction.FrameContract.result_base] do
    let extra := (← collectAxioms decl).filter fun a =>
      !(#[``propext, ``Classical.choice, ``Quot.sound]).contains a
    unless extra.isEmpty do throwError "{decl}: unexpected axioms {extra}"
  let mut inherited : Array Name := #[]
  for rule in #[``Xv6.WholeFunction.FrameCompiler.wp_push_plan,
      ``Xv6.WholeFunction.FrameCompiler.wp_plan] do
    inherited := inherited ++ (← collectAxioms rule)
  for decl in #[``Xv6.WholeFunction.FrameContract.wp_prologue,
      ``Xv6.WholeFunction.FrameContract.wp_return] do
    let axioms ← collectAxioms decl
    let extra := axioms.filter fun a => !inherited.contains a
    unless extra.isEmpty do throwError "{decl}: new axioms {extra}"
    if axioms.contains ``sorryAx then throwError "{decl}: sorryAx"
  logInfo "Shared two-slot frame: pure laws use standard axioms; spatial importers add no axioms."
