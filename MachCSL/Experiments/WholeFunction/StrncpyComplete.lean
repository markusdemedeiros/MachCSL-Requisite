import Experiments.WholeFunction.StrncpyCompile

/-! The unchanged STRNCPY contract from checked binary plans, the shared byte
memory compiler, and the shared stack-frame compiler. -/
namespace Xv6.WholeFunction.Strncpy
open Iris Iris.BI Iris.ProgramLogic MachCSL LeanRV64D Memory
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
variable [CurCtx] [KernelGeom] [KernelImage GF]

theorem wp_body (cpu : CPU) (i : Inputs) (valid : Valid i) :
    mixedOwn (GF := GF) cpu (StrncpyFrame.initialMachine i.entry) ∗
    byteBuf i.dst (DFrac.own 1) i.old ∗ byteBuf i.src i.fraction i.source ∗
    wpNext i.entry.sie i.entry.proc cpu (fun cpu' => iprop(
      ∀ (current : KCtx) (dst : List (BitVec 8)), ⌜CtxFrame writes (StrncpyFrame.initialMachine i.entry).ctx current ∧ post i dst⌝ -∗
      mixedOwn cpu' ⟨current, 0x80000e64#64, StrncpyFrame.frameCells i.entry⟩ -∗
      byteBuf i.dst (DFrac.own 1) dst -∗ byteBuf i.src i.fraction i.source -∗ wpLoop cpu'))
    ⊢ wpLoop cpu := by
  iintro ⟨Hstate, Hdst, Hsrc, Hexit⟩
  iapply wp_framed bodyRows writes writes_checked (StrncpyFrame.initialMachine i.entry)
    (Good i) Exit (compile i valid) cpu (initial i)
    ⟨initial_good i valid, BodyFrame.refl writes (initial i)⟩ $$ [Hstate Hdst Hsrc Hexit]
  isplitl [Hstate Hdst Hsrc]
  · unfold fullOwn payload owns initial Inputs.buffers Buffer.owns Inputs.dstBuffer Inputs.srcBuffer
    iframe Hstate Hdst Hsrc
    iapply BigSepL.bigSepL_nil.mpr
    itrivial
  · rw [(show (StrncpyFrame.initialMachine i.entry).ctx.sie = i.entry.sie from rfl),
      (show (StrncpyFrame.initialMachine i.entry).ctx.proc = i.entry.proc from rfl)]
    iapply wpNext_mono _ _ _ _ _ $$ Hexit
    iintro %cpu' Hexit %t %good %exit Hfull
    obtain ⟨semantic, frame⟩ := good
    obtain ⟨dst, good, result⟩ := good_done semantic exit
    unfold fullOwn
    icases Hfull with ⟨Hstate, Hbuffers⟩
    unfold payload owns
    rw [good.buffers]
    unfold Inputs.buffers
    icases Hbuffers with ⟨Hdst, Hsrc, _⟩
    unfold Buffer.owns Inputs.dstBuffer Inputs.srcBuffer
    iapply Hexit $$ %t.machine.ctx %dst %⟨frame.context, result⟩ [Hstate] Hdst Hsrc
    have machine : t.machine = ⟨t.machine.ctx, 0x80000e64#64, StrncpyFrame.frameCells i.entry⟩ := by
      cases ht : t.machine with
      | mk ctx pc cells =>
        have hp := exit
        have hc := frame.cells
        simp only [Exit, ht] at hp hc
        change cells = StrncpyFrame.frameCells i.entry at hc
        simp [hp, hc]
    rw [← machine]
    iexact Hstate

end

/-- Original STRNCPY specification, including unchanged fractional source,
zero padding, callee-saved registers, stack release, and interrupt migration. -/
theorem compiled_strncpy : STRNCPY := ⟨fun {hlc GF} _ _ cpu k old source n dq available arg bound dstLength srcLength => by
  unfold wp_strncpy_body
  iintro ⟨HK, HPC, Hdst, Hsrc, Hexit⟩
  icases kctx_kernelText _ _ $$ HK with ⟨#HT, HK⟩
  let i : Inputs := ⟨k, old, source, n, dq⟩
  have valid : Valid i := ⟨arg, bound, dstLength, srcLength⟩
  rw [(show strncpyAddr = 0x80000e26#64 from rfl)]
  iapply StrncpyFrame.wp_prologue cpu k available $$ [$HT $HK $HPC Hdst Hsrc Hexit]
  iapply wpNext_intro_pin
  iintro %cpu' %pin Hstate
  ihave Hexit := wpNext_shift _ _ _ _ _ pin $$ Hexit
  have body := wp_body (GF := GF) cpu' i valid
  dsimp only [i, Inputs.dst, Inputs.src] at body
  iapply body $$ [$Hstate $Hdst $Hsrc Hexit]
  iapply wpNext_intro_pin
  iintro %cpu'' %pin' %current %dst %⟨frame, result⟩ Hstate Hdst Hsrc
  ihave Hexit := wpNext_shift _ _ _ _ _ pin' $$ Hexit
  have returning := FrameEffects.wp_return_abi (GF := GF) StrncpyFrame.returnRows 0x80000e64#64
    StrncpyFrame.return_binary writes frame_accepted k current cpu'' frame available
  change mixedOwn cpu'' ⟨current, 0x80000e64#64, StrncpyFrame.frameCells k⟩ ∗ _ ⊢ _ at returning
  iapply returning $$ [$Hstate Hdst Hsrc Hexit]
  iapply wpNext_intro_pin
  iintro %cpu''' %pin'' %R %⟨saved, returned⟩ HK HPC
  ihave Hexit := wpNext_at _ _ _ cpu''' _ pin'' $$ Hexit
  have arg : current.regs 10#5 = k.regs 10#5 :=
    FrameEffects.body_lookup (layout := StrncpyFrame.layout) (writes := writes) frame 10#5 (by decide) (by decide) (by decide)
  iapply Hexit $$ %R %dst HK HPC Hdst Hsrc %⟨saved, returned.trans arg, result⟩⟩

end Xv6.WholeFunction.Strncpy
