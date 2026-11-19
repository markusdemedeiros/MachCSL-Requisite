import Experiments.WholeFunction.StackCells
import Experiments.WholeFunction.ControlFlow
import Experiments.WholeFunction.KernelReg

/-! Uniform transfer rules for stack frames. A frame is introduced by `push`,
updated by arbitrary indexed saves/loads, and checked by address shape before
`pop`. Register values and slot contents remain symbolic. Each push here starts
an empty frame; outer caller frames can be kept in the surrounding BI frame.
-/
namespace Xv6.WholeFunction.Stack
open Iris Iris.BI Iris.ProgramLogic MachCSL LeanRV64D

structure State where
  ctx : KCtx
  pc : BitVec 64
  cells : List Cell

inductive Action where
  | push (imm : BitVec 12) (n : Nat)
      (offset : imm.signExtend 64 = -(8#64 * BitVec.ofNat 64 n))
  | save (imm : BitVec 12) (rs : BitVec 5) (index : Nat)
  | load (imm : BitVec 12) (rd : BitVec 5) (index : Nat) (valid : rdOk rd)
  | pop (imm : BitVec 12) (n : Nat)
      (offset : imm.signExtend 64 = 8#64 * BitVec.ofNat 64 n)

def Action.code : Action → instruction
  | .push imm _ _ | .pop imm _ _ => .ITYPE (imm, .Regidx 2#5, .Regidx 2#5, .ADDI)
  | .save imm rs _ => .STORE (imm, .Regidx rs, .Regidx 2#5, 8)
  | .load imm rd _ _ => .LOAD (imm, .Regidx 2#5, .Regidx rd, false, 8)

def Action.Enabled (a : Action) (s : State) : Prop :=
  match a with
  | .push _ n _ => n ≤ s.ctx.avail ∧ s.cells = []
  | .save imm _ i | .load imm _ i _ =>
      ∃ c, s.cells[i]? = some c ∧ c.1 = s.ctx.sp + imm.signExtend 64
  | .pop _ n _ => s.cells.map Prod.fst = addresses (s.ctx.sp + 8#64 * BitVec.ofNat 64 n) n

def Action.Next (a : Action) (rvc : Bool) (cpu : CPU) (s t : State) : Prop :=
  match a with
  | .push _ n _ => ∃ cells, cells.map Prod.fst = addresses s.ctx.sp n ∧
      t = ⟨s.ctx.push n, s.pc + instrLen rvc, cells⟩
  | .save _ rs i => ∃ c, s.cells[i]? = some c ∧
      t = ⟨s.ctx, s.pc + instrLen rvc, s.cells.set i (c.1, s.ctx.rget cpu rs)⟩
  | .load _ rd i _ => ∃ c, s.cells[i]? = some c ∧
      t = ⟨s.ctx.setReg rd c.2, s.pc + instrLen rvc, s.cells⟩
  | .pop _ n _ => t = ⟨s.ctx.pop n, s.pc + instrLen rvc, []⟩

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
variable [CurCtx] [KernelGeom] [KernelImage GF]

theorem stack_rget (cpu : CPU) (k : KCtx) : k.rget cpu 2#5 = k.sp :=
  KCtx.rget_ne cpu k 2#5 (by decide) (by decide)

theorem Action.sound (a : Action) (rvc : Bool) (cpu : CPU) (s : State)
    (enabled : a.Enabled s) :
    instr (GF := GF) s.pc rvc a.code ∗ kctx cpu s.ctx ∗ pcIs cpu s.pc ∗ owns s.cells ∗
    ▷ wpNext s.ctx.sie s.ctx.proc cpu (fun cpu' => iprop(
      ∀ t, ⌜a.Next rvc cpu' s t⌝ -∗
        kctx cpu' t.ctx -∗ pcIs cpu' t.pc -∗ owns t.cells -∗ wpLoop cpu'))
    ⊢ wpLoop cpu := by
  cases a with
  | push imm n offset =>
    simp only [Action.code]
    obtain ⟨bound, empty⟩ := enabled
    iintro ⟨HI, HK, HPC, _, Hnext⟩
    iapply wp_s_push cpu s.ctx s.pc rvc imm n bound offset $$ [$HI $HK $HPC Hnext]
    inext
    iapply wpNext_intro_pin
    iintro %cpu' %hpin HK HPC Hframe
    icases stack_values s.ctx.sp n $$ Hframe with ⟨%cells, %shape, Hcells⟩
    ihave Hnext := wpNext_at _ _ _ cpu' _ hpin $$ Hnext
    iapply Hnext $$ %(⟨s.ctx.push n, s.pc + instrLen rvc, cells⟩ : State)
      %(show Action.Next (.push imm n offset) rvc cpu' s _ from ⟨cells, shape, rfl⟩)
      HK HPC Hcells
  | save imm rs i =>
    simp only [Action.code]
    obtain ⟨c, lookup, addr⟩ := enabled
    iintro ⟨HI, HK, HPC, Hcells, Hnext⟩
    icases cell_acc s.cells i c lookup $$ Hcells with ⟨Hc, Hclose⟩
    have rule := wp_s_sd (GF := GF) (lent := false) cpu s.ctx s.pc rvc imm 2#5 rs (by decide) c.2
    rw [stack_rget, ← addr] at rule
    iapply rule $$ [$HI $HK $HPC $Hc Hnext Hclose]
    inext
    iapply wpNext_intro_pin
    iintro %cpu' %hpin HK HPC Hc
    ihave Hcells := Hclose $$ %(s.ctx.rget cpu' rs) Hc
    ihave Hnext := wpNext_at _ _ _ cpu' _ hpin $$ Hnext
    iapply Hnext $$ %(⟨s.ctx, s.pc + instrLen rvc,
      s.cells.set i (c.1, s.ctx.rget cpu' rs)⟩ : State)
      %(show Action.Next (.save imm rs i) rvc cpu' s _ from ⟨c, lookup, rfl⟩)
      HK HPC Hcells
  | load imm rd i valid =>
    simp only [Action.code]
    obtain ⟨c, lookup, addr⟩ := enabled
    iintro ⟨HI, HK, HPC, Hcells, Hnext⟩
    icases cell_acc s.cells i c lookup $$ Hcells with ⟨Hc, Hclose⟩
    have rule := wp_s_ld (GF := GF) (lent := false) cpu s.ctx s.pc rvc imm rd 2#5 (by decide) valid (DFrac.own 1) c.2
    rw [stack_rget, ← addr] at rule
    iapply rule $$ [$HI $HK $HPC $Hc Hnext Hclose]
    inext
    iapply wpNext_intro_pin
    iintro %cpu' %hpin HK HPC Hc
    ihave Hcells := Hclose $$ %c.2 Hc
    have same : s.cells.set i (c.1, c.2) = s.cells := by
      exact (List.getElem?_eq_some_iff.mp lookup).2 ▸
        List.set_getElem_self (List.getElem?_eq_some_iff.mp lookup).1
    rw [same]
    ihave Hnext := wpNext_at _ _ _ cpu' _ hpin $$ Hnext
    iapply Hnext $$ %(⟨s.ctx.setReg rd c.2, s.pc + instrLen rvc, s.cells⟩ : State)
      %(show Action.Next (.load imm rd i valid) rvc cpu' s _ from ⟨c, lookup, rfl⟩)
      HK HPC Hcells
  | pop imm n offset =>
    simp only [Action.code]
    iintro ⟨HI, HK, HPC, Hcells, Hnext⟩
    ihave Hframe := values_stack (s.ctx.sp + 8#64 * BitVec.ofNat 64 n) n s.cells enabled $$ Hcells
    iapply wp_s_pop cpu s.ctx s.pc rvc imm n offset $$ [$HI $HK $HPC $Hframe Hnext]
    inext
    iapply wpNext_intro_pin
    iintro %cpu' %hpin HK HPC
    ihave Hnext := wpNext_at _ _ _ cpu' _ hpin $$ Hnext
    iapply Hnext $$ %(⟨s.ctx.pop n, s.pc + instrLen rvc, []⟩ : State) %rfl HK HPC []
    unfold owns
    iapply BigSepL.bigSepL_nil.mpr
    itrivial

def State.machine (s : State) : RegState := ⟨s.ctx, s.pc⟩

/-- Abstract-state lifting used by the shared control-flow compiler. The
target may depend on the whole nondeterministic successor (including freshly
exposed stack values); client resources change only through `hframe`.
-/
theorem Action.transfer_frame {S : Type} (machine : S → State)
    (payload : S → IProp GF) (a : Action) (row : Binary.Row) (s : S)
    (target : CPU → State → S)
    (hpc : (machine s).pc = row.pc) (hcode : row.code = a.code)
    (enabled : a.Enabled (machine s))
    (hrun : ∀ cpu t, a.Next row.rvc cpu (machine s) t → machine (target cpu t) = t)
    (hframe : ∀ cpu t, a.Next row.rvc cpu (machine s) t → payload s ⊢ payload (target cpu t))
    (sie : Bool) (proc : BitVec 64)
    (hsie : (machine s).ctx.sie = sie) (hproc : (machine s).ctx.proc = proc)
    (edge : S → S → Prop)
    (hedge : ∀ cpu t, a.Next row.rvc cpu (machine s) t → edge s (target cpu t)) :
    Transfer (fun cpu s => iprop(regOwn cpu (machine s).machine ∗
      owns (machine s).cells ∗ payload s)) sie proc edge s := by
  intro cpu
  unfold regOwn State.machine
  iintro ⟨⟨⟨#HT, HK, HPC⟩, Hcells, HF⟩, Hnext⟩
  ihave #HI := row.instr (GF := GF) $$ HT
  rw [← hpc, hcode]
  iapply a.sound row.rvc cpu (machine s) enabled $$ [$HI $HK $HPC $Hcells Hnext HF]
  inext
  rw [hsie, hproc]
  iapply wpNext_intro_pin
  iintro %cpu' %hpin %t %hstep HK HPC Hcells
  ihave Hnext := wpNext_at _ _ _ cpu' _ hpin $$ Hnext
  iapply Hnext $$ %(target cpu' t) %(hedge cpu' t hstep) [HT HK HPC Hcells HF]
  dsimp only
  rw [hrun cpu' t hstep]
  iframe HT HK HPC Hcells
  iapply hframe cpu' t hstep $$ HF

end Xv6.WholeFunction.Stack
