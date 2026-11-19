import Experiments.WholeFunction.CopyoutFrame
import Experiments.WholeFunction.CopyinEntry

/-! Actual copyout entry paths compiled by the finite-row backend. In
particular the zero-length return imposes no condition on the return PC:
the continuation is handed back immediately after the return instruction.
-/
namespace Xv6.WholeFunction.CopyoutEntry
open Iris Iris.BI Iris.ProgramLogic MachCSL LeanRV64D
set_option linter.unusedSimpArgs false

def initial (k : KCtx) : Stack.State := ⟨k, 0x800015c2#64, []⟩
def branched (k : KCtx) : Stack.State :=
  ⟨k, if k.regs 14#5 = 0#64 then 0x8000165c#64 else 0x800015c4#64, []⟩
def zeroMiddle (k : KCtx) : Stack.State := ⟨k.setReg 10#5 0#64, 0x8000165e#64, []⟩
def zeroResult (k : KCtx) : Stack.State :=
  ⟨k.setReg 10#5 0#64, jumpPc (k.regs 1#5), []⟩

noncomputable def branchAction : {a : MixedAction // Binary.copyout_000.code = a.code} :=
  ⟨.reg (.branch 154#13 14#5 0#5 (by decide) .BEQ), by binary_rfl⟩
noncomputable def zeroAction : {a : MixedAction // Binary.copyout_09a.code = a.code} :=
  ⟨.reg (.addi 0#12 10#5 0#5 (by decide)), by binary_rfl⟩
noncomputable def retAction : {a : MixedAction // Binary.copyout_09c.code = a.code} :=
  ⟨.reg (.ret 1#5), by binary_rfl⟩

theorem decode_branch : MixedAction.decode 14 Binary.copyout_000.code = some branchAction := by binary_rfl
theorem decode_zero : MixedAction.decode 14 Binary.copyout_09a.code = some zeroAction := by binary_rfl
theorem decode_ret : MixedAction.decode 14 Binary.copyout_09c.code = some retAction := by binary_rfl

theorem branch_next (k : KCtx) (cpu : CPU) (t : Stack.State)
    (hn : branchAction.val.Next Binary.copyout_000.rvc cpu (initial k) t) : t = branched k := by
  cases hn
  simp [branchAction, RegAction.run, initial, branched, Stack.State.machine,
    KCtx.rget_eq, bcond, show Binary.copyout_000.rvc = true from by binary_rfl, instrLen]

theorem zero_next (k : KCtx) (cpu : CPU) (t : Stack.State)
    (hn : zeroAction.val.Next Binary.copyout_09a.rvc cpu ⟨k, 0x8000165c#64, []⟩ t) :
    t = zeroMiddle k := by
  cases hn
  simp [zeroAction, RegAction.run, zeroMiddle, Stack.State.machine,
    KCtx.rget_eq, show Binary.copyout_09a.rvc = true from by binary_rfl, instrLen]

theorem ret_next (k : KCtx) (cpu : CPU) (t : Stack.State)
    (hn : retAction.val.Next Binary.copyout_09c.rvc cpu (zeroMiddle k) t) : t = zeroResult k := by
  cases hn
  simp [retAction, RegAction.run, zeroMiddle, zeroResult, Stack.State.machine,
    KCtx.rget_eq, KCtx.setReg, RegMap.set]

open CopyinEntry (run_tail wp_path)

theorem branch_safe (k : KCtx) : Linear.Safe 14 [Binary.copyout_000] (initial k) :=
  ⟨branchAction, decode_branch, rfl, trivial, fun _ _ _ => trivial⟩

theorem branch_values (k : KCtx) (t : Stack.State)
    (hr : Linear.RowRun 14 [Binary.copyout_000] (initial k) t) : t = branched k := by
  have tail := run_tail decode_branch (branch_next k) hr
  cases tail
  rfl

noncomputable def zeroRows : List Binary.Row := [Binary.copyout_000, Binary.copyout_09a, Binary.copyout_09c]

theorem zero_safe (k : KCtx) (hz : k.regs 14#5 = 0#64) : Linear.Safe 14 zeroRows (initial k) := by
  refine ⟨branchAction, decode_branch, rfl, trivial, ?_⟩
  intro cpu t hn
  rw [branch_next k cpu t hn]
  simp only [branched, hz, ↓reduceIte]
  refine ⟨zeroAction, decode_zero, rfl, trivial, ?_⟩
  intro cpu t hn
  rw [zero_next k cpu t hn]
  exact ⟨retAction, decode_ret, rfl, trivial, fun _ _ _ => trivial⟩

theorem zero_values (k : KCtx) (hz : k.regs 14#5 = 0#64) (t : Stack.State)
    (hr : Linear.RowRun 14 zeroRows (initial k) t) : t = zeroResult k := by
  have h1 := run_tail decode_branch (branch_next k) hr
  simp only [branched, hz, ↓reduceIte] at h1
  have h2 := run_tail decode_zero (zero_next k) h1
  have h3 := run_tail decode_ret (ret_next k) h2
  cases h3
  rfl

theorem zero_calleeSaved (k : KCtx) : calleeSaved k.regs (zeroResult k).ctx.regs := by
  simp [zeroResult, calleeSaved, KCtx.setReg_regs, RegMap.set_apply]

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
variable [CurCtx] [KernelGeom] [KernelImage GF]

/-- Complete zero-length machine path, preserving arbitrary linear payload.
No outside-function assumption is placed on the saved return address.
-/
theorem wp_copyout_zero (cpu : CPU) (k : KCtx) (hz : k.regs 14#5 = 0#64) (P : IProp GF) :
    regOwn cpu ⟨k, 0x800015c2#64⟩ ∗ P ∗ wpNext k.sie k.proc cpu (fun cpu' => iprop(
      regOwn cpu' ⟨k.setReg 10#5 0#64, jumpPc (k.regs 1#5)⟩ ∗ P -∗ wpLoop cpu'))
      ⊢ wpLoop cpu := by
  iintro ⟨Hstate, HP, Hexit⟩
  iapply wp_path 14 zeroRows cpu (initial k) (zeroResult k) (zero_safe k hz)
    (zero_values k hz) P $$ [Hstate HP Hexit]
  isplitl [Hstate]
  · unfold mixedOwn initial Stack.State.machine
    iframe Hstate
    unfold Stack.owns
    iapply BigSepL.bigSepL_nil.mpr
    itrivial
  · iframe HP
    iapply wpNext_intro_pin
    iintro %cpu' %hpin ⟨Hstate, HP⟩
    unfold mixedOwn zeroResult Stack.State.machine
    icases Hstate with ⟨Hstate, _⟩
    ihave Hexit := wpNext_at k.sie k.proc cpu cpu' _ hpin $$ Hexit
    iapply Hexit $$ [$Hstate $HP]

/-- Nonempty entry branch followed by the complete value-sensitive prologue.
The caller's payload is carried linearly through both compiled blocks.
-/
theorem wp_copyout_enter (cpu : CPU) (k : KCtx) (hn : k.regs 14#5 ≠ 0#64)
    (available : 14 ≤ k.avail) (P : IProp GF) :
    regOwn cpu ⟨k, 0x800015c2#64⟩ ∗ P ∗ wpNext k.sie k.proc cpu (fun cpu' => iprop(
      ∀ cells, ⌜CopyoutFrame.Frame k cells⌝ -∗
        mixedOwn cpu' (CopyoutFrame.initialMachine k cells) ∗ P -∗ wpLoop cpu')) ⊢ wpLoop cpu := by
  iintro ⟨Hstate, HP, Hexit⟩
  iapply wp_path 14 [Binary.copyout_000] cpu (initial k) (branched k)
    (branch_safe k) (branch_values k) P $$ [Hstate HP Hexit]
  isplitl [Hstate]
  · unfold mixedOwn initial Stack.State.machine
    iframe Hstate
    unfold Stack.owns
    iapply BigSepL.bigSepL_nil.mpr
    itrivial
  · iframe HP
    iapply wpNext_intro_pin
    iintro %cpu' %hpin ⟨Hstate, HP⟩
    unfold mixedOwn regOwn branched Stack.State.machine
    simp only [ite_eq_right hn]
    icases Hstate with ⟨⟨#HT, HK, HPC⟩, _⟩
    iapply CopyoutFrame.wp_prologue cpu' k available $$ [$HT $HK $HPC HP Hexit]
    iapply wpNext_intro_pin
    iintro %cpu'' %hpin' %cells %frame Hstate
    ihave Hexit := wpNext_at k.sie k.proc cpu cpu'' _ (fun h => (hpin' h).trans (hpin h)) $$ Hexit
    unfold mixedOwn regOwn Stack.State.machine
    iapply Hexit $$ %cells %frame [$Hstate $HP]

end Xv6.WholeFunction.CopyoutEntry

open Lean in
run_cmd do
  let baseline ← collectAxioms ``Xv6.WholeFunction.MixedAction.sound
  for decl in #[``Xv6.WholeFunction.CopyoutEntry.wp_copyout_zero,
      ``Xv6.WholeFunction.CopyoutEntry.wp_copyout_enter] do
    let axioms ← collectAxioms decl
    let extra := axioms.filter fun a => !baseline.contains a
    unless extra.isEmpty do throwError "{decl}: new axioms {extra}"
    if axioms.contains ``sorryAx then throwError "{decl}: contains sorryAx"
  logInfo "Copyout entry paths add no axioms beyond the checked mixed backend."
