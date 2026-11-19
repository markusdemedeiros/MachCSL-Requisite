import Experiments.WholeFunction.StrlenCompile
import Xv6.SpecStrlen

/-! Complete unchanged STRLEN from checked rows, the generic guarded byte
backend, and the shared frame compiler. No ProofStrlen import, iteration
adapter, abstract-body assumption, or whole-machine termination claim. -/
namespace Xv6.WholeFunction.Strlen
open Iris Iris.BI Iris.ProgramLogic MachCSL LeanRV64D Memory
set_option linter.unusedSimpArgs false

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
variable [CurCtx] [KernelGeom] [KernelImage GF]

theorem wp_body (cpu : CPU) (i : Inputs) (valid : Valid i) :
    mixedOwn (GF := GF) cpu (StrlenFrame.initialMachine i.entry) ∗
    byteBuf i.base i.fraction i.bytes ∗
    wpNext i.entry.sie i.entry.proc cpu (fun cpu' => iprop(
      ∀ current : KCtx, ⌜CtxFrame writes (FrameEffects.initialContext FrameContract.layout i.entry) current ∧
        current.regs 10#5 = BitVec.ofNat 64 i.length⌝ -∗
      mixedOwn cpu' ⟨current, 0x80000ec2#64, StrlenFrame.frameCells i.entry⟩ -∗
      byteBuf i.base i.fraction i.bytes -∗ wpLoop cpu')) ⊢ wpLoop cpu := by
  iintro ⟨Hstate, Hbuffer, Hexit⟩
  have rule := wp_framed (GF := GF) bodyRows writes writes_checked (StrlenFrame.initialMachine i.entry)
    (Good i) Exit (compile i valid) cpu (initial i) ⟨initial_good i, BodyFrame.refl writes (initial i)⟩
  simp only [StrlenFrame.initialMachine, KCtx.setReg_sie, KCtx.push_sie,
    KCtx.setReg_proc, KCtx.push_proc] at rule
  iapply rule $$ [Hstate Hbuffer Hexit]
  isplitl [Hstate Hbuffer]
  · unfold fullOwn payload owns initial
    iframe Hstate
    iapply BigSepL.bigSepL_singleton.mpr
    unfold Buffer.owns Inputs.buffer
    iexact Hbuffer
  · iapply wpNext_mono _ _ _ _ _ $$ Hexit
    iintro %cpu' Hexit %t %good %exit Hfull
    have done := good_done good.1 exit
    unfold fullOwn
    icases Hfull with ⟨Hstate, Hbuffer⟩
    iapply Hexit $$ %t.machine.ctx %⟨good.2.context, done.result⟩ [Hstate] [Hbuffer]
    · have machine : t.machine = ⟨t.machine.ctx, 0x80000ec2#64, StrlenFrame.frameCells i.entry⟩ := by
        cases ht : t.machine with
        | mk ctx pc cells =>
          have hp := exit
          have hc := good.2.cells
          simp only [Exit, ht, StrlenFrame.initialMachine] at hp hc
          simp [hp, hc]
      rw [← machine]
      iexact Hstate
    · unfold payload owns
      rw [done.buffers]
      ihave Hbuffer := BigSepL.bigSepL_singleton.mp $$ Hbuffer
      unfold Buffer.owns Inputs.buffer
      iexact Hbuffer

end

/-- The original public STRLEN contract, for every admitted fractional C
string, arbitrary length below 2^31, and either interrupt mode. -/
theorem compiled_strlen : STRLEN := ⟨fun {hlc GF} _ _ cpu k bytes dq available bound => by
  unfold wp_strlen_body
  iintro ⟨HK, HPC, Hstring, Hexit⟩
  icases cstr_elim _ _ _ $$ Hstring with ⟨%nonzero, Hbuffer⟩
  icases kctx_kernelText _ _ $$ HK with ⟨#HT, HK⟩
  let i : Inputs := ⟨k, bytes ++ [0#8], dq, bytes.length⟩
  have valid : Valid i := ⟨cstrAt_of_nonul bytes nonzero, bound⟩
  rw [(show strlenAddr = 0x80000ea2#64 from rfl)]
  iapply StrlenFrame.wp_prologue cpu k available $$ [$HT $HK $HPC Hbuffer Hexit]
  iapply wpNext_intro_pin
  iintro %cpu' %pin Hstate
  ihave Hexit := wpNext_shift _ _ _ _ _ pin $$ Hexit
  have body := wp_body (GF := GF) cpu' i valid
  dsimp only [i, Inputs.base] at body
  iapply body $$ [$Hstate $Hbuffer Hexit]
  iapply wpNext_intro_pin
  iintro %cpu'' %pin' %current %⟨frame, result⟩ Hstate Hbuffer
  ihave Hexit := wpNext_shift _ _ _ _ _ pin' $$ Hexit
  have ret := FrameEffects.wp_return_abi (GF := GF) StrlenFrame.returnRows 0x80000ec2#64
    StrlenFrame.return_binary writes writes_accepted k current cpu'' frame available
  rw [(show FrameContract.frameCells k = StrlenFrame.frameCells k from rfl)] at ret
  iapply ret $$ [$Hstate Hbuffer Hexit]
  iapply wpNext_intro_pin
  iintro %cpu''' %pin'' %R %⟨abi, resultReg⟩ HK HPC
  ihave Hexit := wpNext_at _ _ _ cpu''' _ pin'' $$ Hexit
  iapply Hexit $$ %R HK HPC [Hbuffer] %⟨abi, resultReg.trans result⟩
  iapply cstr_intro _ _ _ nonzero $$ Hbuffer⟩

end Xv6.WholeFunction.Strlen
