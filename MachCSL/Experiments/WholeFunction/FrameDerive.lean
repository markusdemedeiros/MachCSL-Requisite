import Experiments.WholeFunction.FrameCompiler
import Experiments.WholeFunction.FrameEffects
import Experiments.WholeFunction.FrameDeriveLemmas

/-! Static frame certificates over the existing indexed stack evaluator.
The certificate is generated from actual decoder rows; arbitrary cell contents
and every possible hart remain quantified in the established execution rules. -/
namespace Xv6.WholeFunction.FrameDerive
open Iris Iris.BI Iris.ProgramLogic MachCSL LeanRV64D FrameCompiler

/-- The pre-allocation contents are arbitrary, including every scratch slot. -/
def rawCells (entry : KCtx) (n : Nat) (values : Fin n → BitVec 64) : List Stack.Cell :=
  (Stack.addresses entry.sp n).zip (List.ofFn values)

def savedState (layout : Layout) (saved : List (Nat × BitVec 5)) (body : BitVec 64)
    (entry : KCtx) (values : Fin layout.slots → BitVec 64) : Stack.State :=
  ⟨FrameEffects.initialContext layout entry, body,
    savedCells saved entry (rawCells entry layout.slots values)⟩

def returnedState (layout : Layout) (entry current : KCtx) : Stack.State :=
  ⟨FrameEffects.restoredContext layout entry current, jumpPc (entry.regs 1#5), []⟩

/-- Fields are executable metadata or checked consequences of the existing
`FrameCompiler.evalPlan`. There is no additional instruction interpreter.
In particular, the return certificate checks sparse loads against saved values,
restored RA, balanced SP, and complete release of the allocated cells. -/
structure Certificate (push : Binary.Row) (saveRows returnRows : List Binary.Row) where
  layout : Layout
  saved : List (Nat × BitVec 5)
  body : BitVec 64
  returnPc : BitVec 64
  savePlan : Plan
  returnPlan : Plan
  pushCode : push.code = (.stack (.push layout.pushImm layout.slots layout.pushOffset) : MixedAction).code
  saveCompiled : compileRows layout.slots saveRows = savePlan.map some
  returnCompiled : compileRows layout.slots returnRows = returnPlan.map some
  saveSafe : ∀ entry values,
    planSafe savePlan ⟨entry.push layout.slots, push.next, rawCells entry layout.slots values⟩
  saveValues : ∀ entry values,
    evalPlan savePlan ⟨entry.push layout.slots, push.next, rawCells entry layout.slots values⟩ =
      savedState layout saved body entry values
  returnSafe : ∀ entry current values,
    current.sp = entry.sp - 8#64 * BitVec.ofNat 64 layout.slots →
    planSafe returnPlan ⟨current, returnPc, (savedState layout saved body entry values).cells⟩
  returnValues : ∀ entry current values,
    evalPlan returnPlan ⟨current, returnPc, (savedState layout saved body entry values).cells⟩ =
      returnedState layout entry current

/-- Exact values for every actual linear execution, with arbitrary scratch. -/
theorem save_run {push : Binary.Row} {saveRows returnRows : List Binary.Row}
    (cert : Certificate push saveRows returnRows) (entry : KCtx)
    (values : Fin cert.layout.slots → BitVec 64) {t : Stack.State}
    (run : Linear.RowRun cert.layout.slots saveRows
      ⟨entry.push cert.layout.slots, push.next, rawCells entry cert.layout.slots values⟩ t) :
    t = savedState cert.layout cert.saved cert.body entry values := by
  rw [plan_values cert.saveCompiled (cert.saveSafe entry values) run, cert.saveValues]

theorem return_run {push : Binary.Row} {saveRows returnRows : List Binary.Row}
    (cert : Certificate push saveRows returnRows) (entry current : KCtx)
    (values : Fin cert.layout.slots → BitVec 64)
    (sp : current.sp = entry.sp - 8#64 * BitVec.ofNat 64 cert.layout.slots) {t : Stack.State}
    (run : Linear.RowRun cert.layout.slots returnRows
      ⟨current, cert.returnPc, (savedState cert.layout cert.saved cert.body entry values).cells⟩ t) :
    t = returnedState cert.layout entry current := by
  rw [plan_values cert.returnCompiled (cert.returnSafe entry current values sp) run, cert.returnValues]

/-- ABI coverage is checked separately against the actual body's write mask.
Scratch contents do not appear in this condition. -/
theorem return_abi {push : Binary.Row} {saveRows returnRows : List Binary.Row}
    (cert : Certificate push saveRows returnRows) {writes : RegMask} {entry current : KCtx}
    (accepted : FrameEffects.Accepts cert.layout writes)
    (frame : CtxFrame writes (FrameEffects.initialContext cert.layout entry) current)
    (available : cert.layout.slots ≤ entry.avail) :
    calleeSaved entry.regs (returnedState cert.layout entry current).ctx.regs ∧
      (returnedState cert.layout entry current).ctx =
        entry.withRegs (returnedState cert.layout entry current).ctx.regs :=
  ⟨FrameEffects.return_calleeSaved accepted frame, FrameEffects.return_shape frame available⟩

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
variable [CurCtx] [KernelGeom] [KernelImage GF]

/-- Generic push/save importer, including arbitrary allocated cells and migration. -/
theorem wp_save {push : Binary.Row} {saveRows returnRows : List Binary.Row}
    (cert : Certificate push saveRows returnRows) (cpu : CPU) (entry : KCtx)
    (available : cert.layout.slots ≤ entry.avail) :
    kernelText (GF := GF) ∗ kctx cpu entry ∗ pcIs cpu push.pc ∗
      wpNext entry.sie entry.proc cpu (fun cpu' => iprop(
        ∀ values : Fin cert.layout.slots → BitVec 64,
          mixedOwn cpu' (savedState cert.layout cert.saved cert.body entry values) -∗ wpLoop cpu'))
      ⊢ wpLoop cpu := by
  have safe cells (shape : cells.map Prod.fst = Stack.addresses entry.sp cert.layout.slots) :
      planSafe cert.savePlan ⟨entry.push cert.layout.slots, push.next, cells⟩ := by
    obtain ⟨values, rfl⟩ := cells_values entry.sp cert.layout.slots cells shape
    exact cert.saveSafe entry values
  iintro ⟨#HT, HK, HPC, Hexit⟩
  iapply wp_push_plan cert.layout push saveRows cert.savePlan cert.pushCode cert.saveCompiled
    cpu entry available safe $$ [$HT $HK $HPC Hexit]
  iapply wpNext_mono _ _ _ _ _ $$ Hexit
  iintro %cpu' Hexit %cells %shape Hstate
  obtain ⟨values, rfl⟩ := cells_values entry.sp cert.layout.slots cells shape
  have result := cert.saveValues entry values
  change evalPlan cert.savePlan ⟨entry.push cert.layout.slots, push.next,
    (Stack.addresses entry.sp cert.layout.slots).zip (List.ofFn values)⟩ = _ at result
  rw [result]
  iapply Hexit $$ %values Hstate

/-- Generic restore/pop/return importer. All saved values and RA are checked. -/
theorem wp_return {push : Binary.Row} {saveRows returnRows : List Binary.Row}
    (cert : Certificate push saveRows returnRows) (cpu : CPU) (entry current : KCtx)
    (values : Fin cert.layout.slots → BitVec 64)
    (sp : current.sp = entry.sp - 8#64 * BitVec.ofNat 64 cert.layout.slots) :
    mixedOwn (GF := GF) cpu
        ⟨current, cert.returnPc, (savedState cert.layout cert.saved cert.body entry values).cells⟩ ∗
      wpNext current.sie current.proc cpu (fun cpu' => iprop(
        mixedOwn cpu' (returnedState cert.layout entry current) -∗ wpLoop cpu')) ⊢ wpLoop cpu := by
  have rule := wp_plan (GF := GF) cert.returnCompiled cpu _ (cert.returnSafe entry current values sp)
  rw [cert.returnValues] at rule
  exact rule

end Xv6.WholeFunction.FrameDerive
