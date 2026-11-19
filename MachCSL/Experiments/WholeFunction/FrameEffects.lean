import Experiments.WholeFunction.FrameContract
import Experiments.WholeFunction.RegisterEffects

/-! Register restoration and ABI preservation, separate from algorithm-specific
loop invariants. These laws concern the existing frame evaluator. -/
namespace Xv6.WholeFunction.FrameEffects
open MachCSL LeanRV64D FrameCompiler

/-- The exact register set in the production calling convention. -/
def abiRegisters : List (BitVec 5) := [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

theorem calleeSaved_iff (before after : RegMap) :
    calleeSaved before after ↔ ∀ r ∈ abiRegisters, after r = before r := by
  simp [calleeSaved, abiRegisters]

private theorem restore_fold_regs (registers : List (BitVec 5)) (entry current : KCtx)
    (r : BitVec 5) :
    (registers.foldl (fun k rd => k.setReg rd (entry.regs rd)) current).regs r =
      if r ∈ registers then entry.regs r else current.regs r := by
  induction registers generalizing current with
  | nil => simp
  | cons rd registers ih =>
    simp only [List.foldl_cons, ih, List.mem_cons, KCtx.setReg_regs, RegMap.set_apply]
    by_cases hr : r = rd <;> by_cases hm : r ∈ registers <;> simp [hr, hm]

private theorem restore_fold_shape (registers : List (BitVec 5)) (entry current : KCtx) :
    registers.foldl (fun k rd => k.setReg rd (entry.regs rd)) current =
      current.withRegs (registers.foldl (fun k rd => k.setReg rd (entry.regs rd)) current).regs := by
  induction registers generalizing current with
  | nil => rfl
  | cons rd registers ih =>
    simp only [List.foldl_cons]
    rw [ih]
    rfl

theorem restore_regs (layout : Layout) (entry current : KCtx) (r : BitVec 5) :
    (layout.restore entry current).regs r =
      if r ∈ layout.registers then entry.regs r else current.regs r :=
  restore_fold_regs layout.registers entry current r

theorem restore_shape (layout : Layout) (entry current : KCtx) :
    layout.restore entry current = current.withRegs (layout.restore entry current).regs :=
  restore_fold_shape layout.registers entry current

/-- The save sequence changes the stack pointer and frame pointer; saved
register values reside in stack cells, not in another register semantics. -/
def initialContext (layout : Layout) (entry : KCtx) : KCtx :=
  (entry.push layout.slots).setReg 8#5 entry.sp

def restoredContext (layout : Layout) (entry current : KCtx) : KCtx :=
  (layout.restore entry current).pop layout.slots

/-- Every possibly changed ABI register must be restored. The stack pointer
has a separate balance law and cannot be an ordinary body destination. -/
def Accepts (layout : Layout) (writes : RegMask) : Prop :=
  ¬ writes.Contains 2#5 ∧
    ∀ r ∈ abiRegisters, r ≠ 2#5 → (r = 8#5 ∨ writes.Contains r) → r ∈ layout.registers

instance (layout : Layout) (writes : RegMask) : Decidable (Accepts layout writes) :=
  inferInstanceAs (Decidable (¬ writes.Contains 2#5 ∧
    ∀ r ∈ abiRegisters, r ≠ 2#5 → (r = 8#5 ∨ writes.Contains r) → r ∈ layout.registers))

theorem body_lookup {layout : Layout} {writes : RegMask} {entry current : KCtx}
    (frame : CtxFrame writes (initialContext layout entry) current)
    (r : BitVec 5) (outside : ¬ writes.Contains r) (sp : r ≠ 2#5) (fp : r ≠ 8#5) :
    current.regs r = entry.regs r := by
  simpa [initialContext, RegMap.set_apply, sp, fp] using frame.lookup r outside

theorem body_sp {layout : Layout} {writes : RegMask} {entry current : KCtx}
    (accepted : Accepts layout writes)
    (frame : CtxFrame writes (initialContext layout entry) current) :
    current.sp = entry.sp - 8#64 * BitVec.ofNat 64 layout.slots := by
  simpa [initialContext, KCtx.sp, RegMap.set_apply] using frame.lookup 2#5 accepted.1

theorem body_indices {layout : Layout} {writes : RegMask} {entry current : KCtx}
    (frame : CtxFrame writes (initialContext layout entry) current) :
    current.sie = entry.sie ∧ current.proc = entry.proc := by
  simpa [initialContext] using frame.indices

theorem restore_sp (layout : Layout) (entry current : KCtx) :
    (layout.restore entry current).sp = current.sp := by
  have outside : 2#5 ∉ layout.registers := by
    intro inside
    obtain ⟨rd, _, eq⟩ := List.mem_map.mp inside
    exact rd.property.2.1 eq
  change (layout.restore entry current).regs 2#5 = current.regs 2#5
  simp only [restore_regs, outside, ↓reduceIte]

theorem return_shape {layout : Layout} {writes : RegMask} {entry current : KCtx}
    (frame : CtxFrame writes (initialContext layout entry) current)
    (available : layout.slots ≤ entry.avail) :
    restoredContext layout entry current =
      entry.withRegs (restoredContext layout entry current).regs := by
  have shape : layout.restore entry current =
      (initialContext layout entry).withRegs (layout.restore entry current).regs := by
    calc layout.restore entry current = current.withRegs (layout.restore entry current).regs :=
          restore_shape layout entry current
         _ = _ := by rw [frame.shape]; rfl
  unfold restoredContext
  rw [shape]
  apply KCtx.eq_withRegs
  all_goals simp [initialContext]
  omega

theorem return_calleeSaved {layout : Layout} {writes : RegMask} {entry current : KCtx}
    (accepted : Accepts layout writes)
    (frame : CtxFrame writes (initialContext layout entry) current) :
    calleeSaved entry.regs (restoredContext layout entry current).regs := by
  rw [calleeSaved_iff]
  intro r abi
  by_cases sp : r = 2#5
  · subst r
    change (restoredContext layout entry current).sp = entry.sp
    simp [restoredContext, restore_sp, body_sp accepted frame, BitVec.sub_add_cancel]
  · by_cases saved : r ∈ layout.registers
    · simp [restoredContext, KCtx.pop_regs, RegMap.set_apply, sp, restore_regs, saved]
    · have fp : r ≠ 8#5 := fun eq => saved (accepted.2 r abi sp (Or.inl eq))
      have outside : ¬ writes.Contains r := fun inside => saved (accepted.2 r abi sp (Or.inr inside))
      simp [restoredContext, KCtx.pop_regs, RegMap.set_apply, sp, restore_regs, saved,
        body_lookup frame r outside sp fp]

open Iris Iris.BI Iris.ProgramLogic
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
variable [CurCtx] [KernelGeom] [KernelImage GF]

/-- Shared leaf-function return boundary. The ordinary body supplies a checked
register frame; restoration exports the ABI and result-register facts directly,
without exposing stack-machine record reconstruction to each client. -/
theorem wp_return_abi (rows : List Binary.Row) (pc : BitVec 64)
    (compiled : compileRows 2 rows = (FrameContract.layout.returnPlan pc).map some)
    (writes : RegMask) (accepted : Accepts FrameContract.layout writes)
    (entry current : KCtx) (cpu : CPU)
    (frame : CtxFrame writes (initialContext FrameContract.layout entry) current)
    (available : 2 ≤ entry.avail) :
    mixedOwn (GF := GF) cpu ⟨current, pc, FrameContract.frameCells entry⟩ ∗
      wpNext entry.sie entry.proc cpu (fun cpu' => iprop(
        ∀ (R : RegMap), ⌜calleeSaved entry.regs R ∧ R 10#5 = current.regs 10#5⌝ -∗
          kctx cpu' (entry.withRegs R) -∗ pcIs cpu' (jumpPc (entry.regs 1#5)) -∗ wpLoop cpu'))
      ⊢ wpLoop cpu := by
  iintro ⟨Hstate, Hexit⟩
  iapply FrameContract.wp_return rows pc compiled entry current cpu (body_sp accepted frame)
    $$ [$Hstate Hexit]
  have indices := body_indices frame
  rw [indices.1, indices.2]
  iapply wpNext_mono _ _ _ _ _ $$ Hexit
  iintro %cpu' Hexit Hstate
  dsimp only [mixedOwn, regOwn, Stack.State.machine]
  icases Hstate with ⟨⟨_, HK, HPC⟩, _⟩
  have shape := return_shape frame available
  change (FrameContract.returnResult entry current).ctx =
    entry.withRegs (FrameContract.returnResult entry current).ctx.regs at shape
  rw [(show (FrameContract.returnResult entry current).pc = jumpPc (entry.regs 1#5) from rfl)]
  iapply Hexit $$ %(FrameContract.returnResult entry current).ctx.regs
    %⟨return_calleeSaved accepted frame, FrameContract.result_a0 entry current⟩ [HK] HPC
  rw [← shape]
  iexact HK

end Xv6.WholeFunction.FrameEffects

open Lean in
run_cmd do
  for decl in #[``Xv6.WholeFunction.FrameEffects.restore_regs,
      ``Xv6.WholeFunction.FrameEffects.restore_shape,
      ``Xv6.WholeFunction.FrameEffects.return_shape,
      ``Xv6.WholeFunction.FrameEffects.return_calleeSaved] do
    let extra := (← collectAxioms decl).filter fun a =>
      !(#[``propext, ``Classical.choice, ``Quot.sound]).contains a
    unless extra.isEmpty do throwError "{decl}: unexpected axioms {extra}"
  let inherited ← collectAxioms ``Xv6.WholeFunction.FrameContract.wp_return
  let extra := (← collectAxioms ``Xv6.WholeFunction.FrameEffects.wp_return_abi).filter fun a =>
    !inherited.contains a
  unless extra.isEmpty do throwError "ABI return wrapper added axioms: {extra}"
  logInfo "Frame effects and ABI restoration checked; no additional axioms."
