import Experiments.WholeFunction.CopyinExit
import Experiments.WholeFunction.CopyinEntry

namespace Xv6.WholeFunction.Copyin
open Iris Iris.BI Iris.ProgramLogic MachCSL
open Experiments.WholeFunction

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
variable [Xv6G GF] [WchG GF] [CurCtx]

theorem publicReturn_shift (i : Inputs) (cpu cpu' : CPU)
    (pin : i.entry.sie = false ∨ i.entry.proc = 0#64 → cpu' = cpu) :
    publicReturn (GF := GF) i cpu ⊢ publicReturn i cpu' :=
  wpNext_shift i.entry.sie i.entry.proc cpu cpu' _ pin

/-- Complete function boundary from the body certificate. The empty case is
compiled separately, so no restriction is imposed on the caller's return PC.
The final theorem will instantiate the body with the generated CFG proof. -/
theorem wp_of_body (i : Inputs) (γl : GName) (γk : KmemNames) (valid : Valid i)
    (body : 0 < i.old.length → BodyCertificate (GF := GF) i γl γk)
    (cpu : CPU) :
    kctx cpu i.entry ∗ pcIs cpu copyinAddr ∗ payload i γl γk (initialBody i) ∗
      publicReturn i cpu ⊢@{IProp GF} wpLoop cpu := by
  rw [show copyinAddr = 0x80001688#64 from rfl]
  iintro ⟨HK, HPC, HP, Hreturn⟩
  icases kctx_kernelText cpu i.entry $$ HK with ⟨#HT, HK⟩
  by_cases empty : i.old.length = 0
  · have hz : i.entry.regs 14#5 = 0#64 := by rw [valid.length, empty]
    have old : i.old = [] := List.length_eq_zero_iff.mp empty
    iapply CopyinEntry.wp_copyin_zero cpu i.entry hz (payload i γl γk (initialBody i))
      $$ [HT HK HPC HP Hreturn]
    isplitl [HK HPC]
    · unfold regOwn
      iframe HT HK HPC
    · iframe HP
      iapply wpNext_intro_pin
      iintro %cpu' %pin ⟨Hstate, HP⟩
      unfold regOwn
      icases Hstate with ⟨_, HK, HPC⟩
      irevert HP
      unfold payload initialBody Copy.initial Copy.buffer
      simp only [List.length_nil, List.drop_zero, List.nil_append]
      iintro ⟨_, _, HP, Hdst, Hlend⟩
      irevert Hreturn
      unfold publicReturn
      iintro Hreturn
      ihave Hreturn := wpNext_at i.entry.sie i.entry.proc cpu cpu' _ pin $$ Hreturn
      iapply Hreturn $$ %i.entry.spie %i.entry.spp %(i.entry.setReg 10#5 0#64).regs
        %(fun _ => ⟨rfl, rfl⟩) [HK] [HPC] [Hlend] [HP Hdst]
        %(CopyinEntry.zero_calleeSaved i.entry)
      · rw [show (i.entry.withSpie i.entry.spie i.entry.spp).withRegs
            (i.entry.setReg 10#5 0#64).regs = i.entry.setReg 10#5 0#64 from rfl]
        iexact HK
      · iexact HPC
      · iexists i.lend
        iframe Hlend
        ipureintro; exact Nat.le_refl _
      · iexists i.table, i.old
        isplitr [HP Hdst]
        · ipureintro
          refine ⟨UMemL.extSz_refl _ _, Or.inl ⟨?_, ?_, ?_, ?_⟩⟩
          · simp [KCtx.setReg_regs]
          · simp [old, UMemL.umemRead_zero]
          · rw [empty]; exact UMemL.umMapped_zero _ _
          · intro j hj; omega
        · rw [UMemL.viewFaulted_self]
          iframe HP Hdst
  · have hn : i.entry.regs 14#5 ≠ 0#64 := by
      rw [valid.length]
      intro hz
      have h := congrArg BitVec.toNat hz
      simp only [BitVec.toNat_ofNat] at h
      have := valid.bound
      omega
    iapply CopyinEntry.wp_copyin_enter cpu i.entry hn (by have := valid.stack; omega)
      (payload i γl γk (initialBody i)) $$ [HT HK HPC HP Hreturn]
    isplitl [HK HPC]
    · unfold regOwn
      iframe HT HK HPC
    · iframe HP
      iapply wpNext_intro_pin
      iintro %cpu' %pin ⟨Hstate, HP⟩
      ihave Hreturn := publicReturn_shift i cpu cpu' pin $$ Hreturn
      iapply body (by omega) cpu' $$ [Hstate HP Hreturn]
      isplitl [Hstate HP]
      · unfold fullOwn initialBody
        iframe Hstate HP
      · iapply wpNext_intro_pin
        iintro %cpu'' %pin' %s %done Hstate
        ihave Hreturn := publicReturn_shift i cpu' cpu'' pin' $$ Hreturn
        iapply wp_exit i γl γk cpu'' s done (by have := valid.stack; omega)
          $$ [$Hstate $Hreturn]

end

/-- The body is the only remaining certificate required to export the
unchanged public interface. Its implementation is the generated CFG proof. -/
structure BodyProvider : Prop where
  body : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
    [Xv6G GF] [WchG GF] [CurCtx] (i : Inputs) (γl : GName) (γk : KmemNames),
    Valid i → 0 < i.old.length → BodyCertificate (GF := GF) i γl γk

theorem copyin_of_body (provider : BodyProvider) : COPYIN :=
  ⟨fun {hlc GF} _ _ _ _ cpu k γl γk P M old ke hnoff hK hlk hroot hsz hlen hbound => by
    let i : Inputs := ⟨k, P, M, old, ke⟩
    have valid : Valid i := ⟨hnoff, hK, hlk, hroot, hsz, hlen, hbound⟩
    have h := wp_of_body (GF := GF) i γl γk valid
      (fun positive => provider.body i γl γk valid positive) cpu
    unfold wp_copyin_body
    iintro ⟨HK, HPC, HL, HA, HP, HB, HE, HR⟩
    iapply h $$ [HK HPC HL HA HP HB HE HR]
    unfold payload initialBody Effect.buffer Copy.initial publicReturn
    simp only [List.length_nil, List.drop_zero, List.nil_append]
    dsimp only [i, Inputs.dst, Inputs.src, Inputs.size]
    iframe HK HPC HL HA HP HE HR
    iexact HB⟩

end Xv6.WholeFunction.Copyin
