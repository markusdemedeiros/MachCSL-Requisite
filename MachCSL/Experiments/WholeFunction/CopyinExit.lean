import Experiments.WholeFunction.CopyinModel
import Experiments.WholeFunction.KernelCalls
import Experiments.WholeFunction.StackReturn

namespace Xv6.WholeFunction.Copyin
open Iris Iris.BI Iris.ProgramLogic MachCSL
open Experiments.WholeFunction

/-- The semantic body boundary before the binary epilogue. Its facts are
derived from the operational invariant; none is a spatial WP assumption. -/
structure BodyResult (i : Inputs) (s : State) : Prop where
  pc : s.machine.pc = 0x80001704#64
  cells : s.machine.cells = StackValues.frameCells i.entry
  context : s.machine.ctx =
    ((i.entry.withSpie s.machine.ctx.spie s.machine.ctx.spp).pushed 12).withRegs s.machine.ctx.regs
  sp : s.machine.ctx.sp = i.entry.sp - 96#64
  s11 : s.machine.ctx.regs 27#5 = i.entry.regs 27#5
  flags : i.entry.sie = false →
    s.machine.ctx.spie = i.entry.spie ∧ s.machine.ctx.spp = i.entry.spp
  post : Copy.CopyinPost i.size i.src (s.machine.ctx.regs 10#5)
    i.table i.image i.old s.memory
  image : s.memory.image = viewFaulted i.table s.memory.table i.image
  lend : i.lend ≤ s.memory.lend

def initialBody (i : Inputs) : State :=
  ⟨StackValues.prologueResult i.entry, Copy.initial i.table i.image i.lend⟩

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
variable [Xv6G GF] [WchG GF] [CurCtx]

def BodyCertificate (i : Inputs) (γl : GName) (γk : KmemNames) : Prop :=
  ∀ cpu, fullOwn State.machine (payload (GF := GF) i γl γk) cpu (initialBody i) ∗
    wpNext i.entry.sie i.entry.proc cpu (fun cpu' => iprop(
      ∀ s, ⌜BodyResult i s⌝ -∗ fullOwn State.machine (payload i γl γk) cpu' s -∗ wpLoop cpu'))
    ⊢ wpLoop cpu

/-- Exactly the continuation of the unchanged public COPYIN contract. -/
def publicReturn (i : Inputs) (cpu : CPU) : IProp GF :=
  wpNext i.entry.sie i.entry.proc cpu (fun cpu' => iprop(
    ∀ spie : Bool, ∀ spp : Bool, ∀ R' : RegMap,
    ⌜i.entry.sie = false → spie = i.entry.spie ∧ spp = i.entry.spp⌝ -∗
    kctx cpu' ((i.entry.withSpie spie spp).withRegs R') -∗
    pcIs cpu' (jumpPc (i.entry.regs 1#5)) -∗
    (∃ k' : Nat, ⌜i.lend ≤ k'⌝ ∗ actLend i.entry.proc k') -∗
    (∃ (P' : UPtd) (bs' : List (BitVec 8)),
      ⌜i.table.extSz i.size P' ∧
        ((R' 10#5 = 0#64 ∧ bs' = umemRead (viewFaulted i.table P' i.image) i.src.toNat i.old.length ∧
          umMapped P' i.src.toNat i.old.length ∧ uvaRprefix P' i.src i.old.length) ∨
         (R' 10#5 = -1#64 ∧ (∃ d, d ≤ i.old.length ∧
           bs' = umemRead (viewFaulted i.table P' i.image) i.src.toNat d ++ i.old.drop d) ∧
           ∃ e, e < i.old.length ∧ ¬ uvaRmapped i.table (i.src + BitVec.ofNat 64 e).toNat))⌝ ∗
      procPtAt P' (viewFaulted i.table P' i.image) ∗ byteBuf i.dst (DFrac.own 1) bs') -∗
    ⌜calleeSaved i.entry.regs R'⌝ -∗ wpLoop cpu'))

theorem wp_exit (i : Inputs) (γl : GName) (γk : KmemNames) (cpu : CPU)
    (s : State) (done : BodyResult i s) (available : 12 ≤ i.entry.avail) :
    fullOwn State.machine (payload i γl γk) cpu s ∗ publicReturn i cpu ⊢@{IProp GF} wpLoop cpu := by
  have indices : s.machine.ctx.sie = i.entry.sie ∧ s.machine.ctx.proc = i.entry.proc := by
    exact ⟨by simpa using congrArg KCtx.sie done.context,
      by simpa using congrArg KCtx.proc done.context⟩
  have context := StackReturn.result_base i.entry
    (i.entry.withSpie s.machine.ctx.spie s.machine.ctx.spp) s.machine.ctx.regs available
  rw [← done.context] at context
  have saved := StackReturn.result_calleeSaved i.entry s.machine.ctx done.sp done.s11
  have a0 := StackReturn.result_a0 i.entry s.machine.ctx
  unfold fullOwn mixedOwn regOwn Stack.State.machine payload
  iintro ⟨⟨⟨⟨#HT, HK, HPC⟩, Hcells⟩, ⟨#Hlock, #Halloc, HP, Hdst, Hlend⟩⟩, Hreturn⟩
  iapply StackReturn.wp_copyin_return i.entry s.machine.ctx cpu done.sp
    $$ [HT HK HPC Hcells HP Hdst Hlend Hreturn]
  isplitl [HK HPC Hcells]
  · unfold mixedOwn regOwn Stack.State.machine
    rw [← done.pc, ← done.cells]
    iframe HT HK HPC Hcells
  · iapply wpNext_intro_pin
    iintro %cpu' %pin Hstate
    unfold mixedOwn regOwn Stack.State.machine
    icases Hstate with ⟨⟨_, HK, HPC⟩, _⟩
    irevert Hreturn
    unfold publicReturn
    iintro Hreturn
    ihave Hreturn := wpNext_at i.entry.sie i.entry.proc cpu cpu' _
      (by simpa only [indices.1, indices.2] using pin) $$ Hreturn
    iapply Hreturn $$ %s.machine.ctx.spie %s.machine.ctx.spp
      %(StackReturn.result i.entry s.machine.ctx).ctx.regs %done.flags [HK] [HPC] [Hlend] [HP Hdst] %saved
    · rw [← context]
      iexact HK
    · irevert HPC
      simp only [StackReturn.result, Stack.State.machine]
      iintro HPC
      iexact HPC
    · iexists s.memory.lend
      iframe Hlend
      ipureintro; exact done.lend
    · iexists s.memory.table, (Copy.buffer s.memory i.old)
      isplitr [HP Hdst]
      · ipureintro
        rw [a0]
        exact done.post
      · rw [← done.image]
        iframe HP Hdst

end Xv6.WholeFunction.Copyin
