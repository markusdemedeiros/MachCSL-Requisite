import Experiments.WholeFunction.CopyoutModel
import Experiments.WholeFunction.KernelCalls
import Experiments.WholeFunction.CopyoutFrame
import Xv6.SpecCopyout

namespace Xv6.WholeFunction.Copyout
open Iris Iris.BI Iris.ProgramLogic MachCSL
open Experiments.WholeFunction

/-- The semantic body boundary before the binary epilogue. Its facts are
derived from the operational invariant; none is a spatial WP assumption. -/
structure BodyResult (i : Inputs) (s : State) : Prop where
  pc : s.machine.pc = 0x80001662#64
  cells : CopyoutFrame.Frame i.entry s.machine.cells
  context : s.machine.ctx =
    ((i.entry.withSpie s.machine.ctx.spie s.machine.ctx.spp).pushed 14).withRegs s.machine.ctx.regs
  sp : s.machine.ctx.sp = i.entry.sp - 112#64
  flags : i.entry.sie = false →
    s.machine.ctx.spie = i.entry.spie ∧ s.machine.ctx.spp = i.entry.spp
  post : Post i (s.machine.ctx.regs 10#5) s.memory
  lend : i.lend ≤ s.memory.lend

def initialBody (i : Inputs) (cells : List Stack.Cell) : State :=
  ⟨CopyoutFrame.initialMachine i.entry cells, Copy.initial i.table i.image i.lend⟩

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
variable [Xv6G GF] [WchG GF] [CurCtx]

def BodyCertificate (i : Inputs) (γl : GName) (γk : KmemNames) : Prop :=
  ∀ cells, CopyoutFrame.Frame i.entry cells → ∀ cpu, fullOwn State.machine (payload (GF := GF) i γl γk) cpu (initialBody i cells) ∗
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
    byteBuf i.src i.fraction i.bytes -∗
    (∃ (P' : UPtd) (M' : Effect.Image),
      ⌜i.table.extSz i.size P' ∧
        ((R' 10#5 = 0#64 ∧ M' = umemWrite (viewFaulted i.table P' i.image) i.dst.toNat i.bytes ∧
          umMapped P' i.dst.toNat i.bytes.length ∧ uvaWprefix P' i.dst i.bytes.length) ∨
         (R' 10#5 = -1#64 ∧ ∃ d, d < i.bytes.length ∧
           M' = umemWrite (viewFaulted i.table P' i.image) i.dst.toNat (i.bytes.take d) ∧
           umMapped P' i.dst.toNat d ∧ uvaWprefix P' i.dst d ∧
           ¬ uvaWmapped i.table (i.dst + BitVec.ofNat 64 d).toNat))⌝ ∗
      procPtAt P' M') -∗
    ⌜calleeSaved i.entry.regs R'⌝ -∗ wpLoop cpu'))

theorem wp_exit (i : Inputs) (γl : GName) (γk : KmemNames) (cpu : CPU)
    (s : State) (done : BodyResult i s) (available : 14 ≤ i.entry.avail) :
    fullOwn State.machine (payload i γl γk) cpu s ∗ publicReturn i cpu ⊢@{IProp GF} wpLoop cpu := by
  have indices : s.machine.ctx.sie = i.entry.sie ∧ s.machine.ctx.proc = i.entry.proc := by
    exact ⟨by simpa using congrArg KCtx.sie done.context,
      by simpa using congrArg KCtx.proc done.context⟩
  have context := CopyoutFrame.result_base i.entry
    (i.entry.withSpie s.machine.ctx.spie s.machine.ctx.spp) s.machine.ctx.regs available
  rw [← done.context] at context
  have saved := CopyoutFrame.result_calleeSaved i.entry s.machine.ctx done.sp
  have a0 := CopyoutFrame.result_a0 i.entry s.machine.ctx
  unfold fullOwn mixedOwn regOwn Stack.State.machine payload
  iintro ⟨⟨⟨⟨#HT, HK, HPC⟩, Hcells⟩, ⟨#Hlock, #Halloc, HP, Hdst, Hlend⟩⟩, Hreturn⟩
  iapply CopyoutFrame.wp_return i.entry s.machine.ctx cpu s.machine.cells done.cells done.sp
    $$ [HT HK HPC Hcells HP Hdst Hlend Hreturn]
  isplitl [HK HPC Hcells]
  · unfold mixedOwn regOwn Stack.State.machine
    rw [← done.pc]
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
      %(CopyoutFrame.returnResult i.entry s.machine.ctx).ctx.regs %done.flags [HK] [HPC] [Hlend] [Hdst] [HP] %saved
    · rw [← context]
      iexact HK
    · irevert HPC
      simp only [CopyoutFrame.returnResult, Stack.State.machine]
      iintro HPC
      iexact HPC
    · iexists s.memory.lend
      iframe Hlend
      ipureintro; exact done.lend
    · iexact Hdst
    · iexists s.memory.table, s.memory.image
      isplitr [HP]
      · ipureintro
        rw [a0]
        exact done.post
      · iexact HP

end Xv6.WholeFunction.Copyout
