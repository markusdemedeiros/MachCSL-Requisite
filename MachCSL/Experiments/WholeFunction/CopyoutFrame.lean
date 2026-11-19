import Experiments.WholeFunction.CopyoutFrameDefs

namespace Xv6.WholeFunction.CopyoutFrame
open Iris Iris.BI Iris.ProgramLogic MachCSL LeanRV64D FrameCompiler
set_option linter.unusedSimpArgs false

set_option maxHeartbeats 0 in
theorem save_binary : compileRows 14 saveRows = savePlan.map some := by binary_rfl
set_option maxHeartbeats 0 in
theorem return_binary : compileRows 14 returnRows = returnPlan.map some := by binary_rfl

def rawCells (entry : KCtx) (values : Fin 14 → BitVec 64) : List Stack.Cell :=
  (Stack.addresses entry.sp 14).zip (List.ofFn values)

set_option maxHeartbeats 0 in
theorem save_safe (entry : KCtx) (values : Fin 14 → BitVec 64) :
    planSafe savePlan ⟨entry.push 14, 0x800015c6#64, rawCells entry values⟩ := by
  simp [planSafe, savePlan, Layout.savePlan, layout, supported, saving,
    StackValues.supported, MixedAction.Enabled, Stack.Action.Enabled,
    eval, StackValues.eval, rawCells, Stack.addresses, List.range_succ, List.ofFn_succ,
    instrLen, KCtx.push_sp, KCtx.setReg_sp, RegAction.run, Stack.State.machine]
  all_goals bv_omega

set_option maxHeartbeats 0 in
theorem save_values (entry : KCtx) (values : Fin 14 → BitVec 64) :
    evalPlan savePlan ⟨entry.push 14, 0x800015c6#64, rawCells entry values⟩ =
      initialMachine entry (frameCells entry (values 13)) := by
  simp [evalPlan, savePlan, Layout.savePlan, layout, saving, eval, StackValues.eval,
    rawCells, Stack.addresses, List.range_succ, List.ofFn_succ, instrLen,
    RegAction.run, Stack.State.machine, initialMachine, frameCells, Layout.frameCells,
    Layout.registers, KCtx.push_sp, KCtx.push_regs, KCtx.setReg_regs, RegMap.set_apply,
    KCtx.rget_ne, KCtx.sp, BitVec.sub_add_cancel]

set_option maxHeartbeats 0 in
theorem return_safe (entry current : KCtx) (padding : BitVec 64)
    (sp : current.sp = entry.sp - 112#64) :
    planSafe returnPlan ⟨current, 0x80001662#64, frameCells entry padding⟩ := by
  simp [planSafe, returnPlan, Layout.returnPlan, layout, supported, saving, StackReturn.supported,
    MixedAction.Enabled, Stack.Action.Enabled, eval, StackReturn.eval, frameCells, Layout.frameCells,
    Layout.registers, Stack.addresses, List.range_succ, instrLen, KCtx.setReg_sp, sp,
    RegAction.run, Stack.State.machine]
  all_goals bv_omega

set_option maxHeartbeats 0 in
theorem return_values (entry current : KCtx) (padding : BitVec 64) :
    evalPlan returnPlan ⟨current, 0x80001662#64, frameCells entry padding⟩ = returnResult entry current := by
  simp [evalPlan, returnPlan, Layout.returnPlan, layout, saving, eval, StackReturn.eval,
    frameCells, Layout.frameCells, Layout.registers, Stack.addresses, List.range_succ,
    instrLen, RegAction.run, Stack.State.machine, returnResult, Layout.restore,
    KCtx.rget_ne, KCtx.pop_regs, KCtx.setReg_regs, RegMap.set_apply]

theorem result_calleeSaved (entry current : KCtx) (sp : current.sp = entry.sp - 112#64) :
    calleeSaved entry.regs (returnResult entry current).ctx.regs := by
  change current.regs 2#5 = entry.regs 2#5 - 112#64 at sp
  simp [calleeSaved, returnResult, Layout.restore, Layout.registers, layout,
    KCtx.pop_regs, KCtx.setReg_regs, RegMap.set_apply, KCtx.setReg_sp, sp, KCtx.sp,
    BitVec.sub_add_cancel]

theorem result_a0 (entry current : KCtx) :
    (returnResult entry current).ctx.regs 10#5 = current.regs 10#5 := by
  simp [returnResult, Layout.restore, Layout.registers, layout, KCtx.pop_regs, KCtx.setReg_regs, RegMap.set_apply]

theorem result_base (entry base : KCtx) (R : RegMap) (available : 14 ≤ base.avail) :
    (returnResult entry ((base.pushed 14).withRegs R)).ctx =
      base.withRegs (returnResult entry ((base.pushed 14).withRegs R)).ctx.regs := by
  apply KCtx.eq_withRegs
  all_goals simp [returnResult, Layout.restore, Layout.registers, layout, KCtx.pushed, KCtx.withRegs]
  omega

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
variable [CurCtx] [KernelGeom] [KernelImage GF]

theorem wp_prologue (cpu : CPU) (entry : KCtx) (available : 14 ≤ entry.avail) :
    kernelText (GF := GF) ∗ kctx cpu entry ∗ pcIs cpu 0x800015c4#64 ∗
      wpNext entry.sie entry.proc cpu (fun cpu' => iprop(
        ∀ cells, ⌜Frame entry cells⌝ -∗ mixedOwn cpu' (initialMachine entry cells) -∗ wpLoop cpu'))
      ⊢ wpLoop cpu := by
  have pc : Binary.copyout_002.pc = 0x800015c4#64 := by binary_rfl
  have hn : Binary.copyout_002.next = 0x800015c6#64 := by binary_rfl
  have safe (cells : List Stack.Cell) (shape : cells.map Prod.fst = Stack.addresses entry.sp 14) :
      planSafe savePlan ⟨entry.push 14, Binary.copyout_002.next, cells⟩ := by
    obtain ⟨values, rfl⟩ := cells_values entry.sp 14 cells shape
    rw [hn]
    exact save_safe entry values
  have rule := wp_push_plan (GF := GF) layout Binary.copyout_002 saveRows savePlan
    (by binary_rfl) save_binary cpu entry available safe
  simp only [layout] at rule
  rw [pc] at rule
  iintro ⟨#HT, HK, HPC, Hexit⟩
  iapply rule $$ [$HT $HK $HPC Hexit]
  iapply wpNext_mono _ _ _ _ _ $$ Hexit
  iintro %cpu' Hexit %cells %shape Hstate
  obtain ⟨values, rfl⟩ := cells_values entry.sp 14 cells shape
  have values_eq := save_values entry values
  rw [hn]
  change evalPlan savePlan ⟨entry.push 14, 0x800015c6#64,
    (Stack.addresses entry.sp 14).zip (List.ofFn values)⟩ = _ at values_eq
  rw [values_eq]
  iapply Hexit $$ %(frameCells entry (values 13)) %⟨values 13, rfl⟩ Hstate

theorem wp_return (entry current : KCtx) (cpu : CPU) (cells : List Stack.Cell)
    (frame : Frame entry cells) (sp : current.sp = entry.sp - 112#64) :
    mixedOwn (GF := GF) cpu ⟨current, 0x80001662#64, cells⟩ ∗
      wpNext current.sie current.proc cpu (fun cpu' => iprop(
        mixedOwn cpu' (returnResult entry current) -∗ wpLoop cpu')) ⊢ wpLoop cpu := by
  obtain ⟨padding, rfl⟩ := frame
  have rule := wp_plan (GF := GF) return_binary cpu _ (return_safe entry current padding sp)
  rw [return_values] at rule
  exact rule

end Xv6.WholeFunction.CopyoutFrame

open Lean in
run_cmd do
  let rules := #[``Xv6.WholeFunction.MixedAction.sound, ``MachCSL.wp_s_push]
  let mut baseline : Array Name := #[]
  for rule in rules do
    for ax in ← collectAxioms rule do
      if !baseline.contains ax then baseline := baseline.push ax
  let checks := #[``Xv6.WholeFunction.FrameCompiler.wp_plan,
    ``Xv6.WholeFunction.FrameCompiler.wp_push_plan,
    ``Xv6.WholeFunction.CopyoutFrame.wp_prologue,
    ``Xv6.WholeFunction.CopyoutFrame.wp_return]
  for decl in checks do
    let axioms ← collectAxioms decl
    let extra := axioms.filter fun a => !baseline.contains a
    unless extra.isEmpty do throwError "{decl}: new axioms {extra}"
    if axioms.contains ``sorryAx then throwError "{decl}: contains sorryAx"
  logInfo m!"Frame compiler and actual COPYOUT prologue/return add no axioms beyond {baseline.size} production-rule axioms."
