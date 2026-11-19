import Experiments.WholeFunction.KernelGraph
import Experiments.WholeFunction.StackDecode

/-! A single generated CFG backend combining register/control instructions
and owned stack frames. The program supplies a frame size and a pure invariant;
lookup, decoding, spatial instruction rules and guarded cyclic composition are
shared. Callee contracts and other memory instructions remain explicit cuts. -/
namespace Xv6.WholeFunction
open Iris Iris.BI Iris.ProgramLogic MachCSL LeanRV64D

inductive MixedAction where
  | reg (action : RegAction)
  | stack (action : Stack.Action)

def MixedAction.code : MixedAction → instruction
  | .reg a => a.code
  | .stack a => a.code

def MixedAction.decode (slots : Nat) (i : instruction) : Option {a : MixedAction // i = a.code} :=
  match RegAction.decode i with
  | some a => some ⟨.reg a.val, a.property⟩
  | none => (Stack.Action.decode slots i).map fun a => ⟨.stack a.val, a.property⟩

def MixedAction.Enabled (a : MixedAction) (s : Stack.State) : Prop :=
  match a with
  | .reg _ => True
  | .stack a => a.Enabled s

def MixedAction.Next (a : MixedAction) (rvc : Bool) (cpu : CPU) (s t : Stack.State) : Prop :=
  match a with
  | .reg a => let r := a.run rvc cpu s.machine; t = ⟨r.ctx, r.pc, s.cells⟩
  | .stack a => a.Next rvc cpu s t

structure LocatedMixed (pc : BitVec 64) where
  row : Binary.Row
  action : MixedAction
  address : pc = row.pc
  decoded : row.code = action.code

def findMixed (slots : Nat) (pc : BitVec 64) : List Binary.Row → Option (LocatedMixed pc)
  | [] => none
  | row :: rest =>
    if hp : pc = row.pc then
      (MixedAction.decode slots row.code).map (fun a => ⟨row, a.val, hp, a.property⟩)
    else findMixed slots pc rest

/-- Lookup cannot introduce an instruction or symbolic action absent from the
checked program table. Useful for uniform frame-shape/instruction-class checks. -/
theorem findMixed_sound (slots : Nat) (pc : BitVec 64) (rows : List Binary.Row)
    (r : LocatedMixed pc) (found : findMixed slots pc rows = some r) :
    r.row ∈ rows ∧ MixedAction.decode slots r.row.code = some ⟨r.action, r.decoded⟩ := by
  induction rows with
  | nil => simp [findMixed] at found
  | cons row rest ih =>
    simp only [findMixed] at found
    split at found
    · rename_i hp
      cases hd : MixedAction.decode slots row.code with
      | none => simp [hd] at found
      | some a =>
        simp only [hd, Option.map_some, Option.some.injEq] at found
        cases found
        exact ⟨List.mem_cons_self, hd⟩
    · obtain ⟨mem, hd⟩ := ih found
      exact ⟨List.mem_cons_of_mem row mem, hd⟩

def MixedEdge (slots : Nat) (rows : List Binary.Row) (s t : Stack.State) : Prop :=
  ∃ r, findMixed slots s.pc rows = some r ∧ ∃ cpu, r.action.Next r.row.rvc cpu s t

def MixedCut (slots : Nat) (rows : List Binary.Row) (s : Stack.State) : Prop :=
  findMixed slots s.pc rows = none

def MixedReady (slots : Nat) (rows : List Binary.Row) (s : Stack.State) : Prop :=
  ∀ r, findMixed slots s.pc rows = some r → r.action.Enabled s

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
variable [CurCtx] [KernelGeom] [KernelImage GF]

def mixedOwn (cpu : CPU) (s : Stack.State) : IProp GF :=
  iprop(regOwn cpu s.machine ∗ Stack.owns s.cells)

theorem MixedAction.sound (a : MixedAction) (rvc : Bool) (cpu : CPU) (s : Stack.State)
    (enabled : a.Enabled s) :
    instr (GF := GF) s.pc rvc a.code ∗ kctx cpu s.ctx ∗ pcIs cpu s.pc ∗ Stack.owns s.cells ∗
    ▷ wpNext s.ctx.sie s.ctx.proc cpu (fun cpu' => iprop(
      ∀ t, ⌜a.Next rvc cpu' s t⌝ -∗
        kctx cpu' t.ctx -∗ pcIs cpu' t.pc -∗ Stack.owns t.cells -∗ wpLoop cpu'))
      ⊢ wpLoop cpu := by
  cases a with
  | stack a => exact a.sound rvc cpu s enabled
  | reg a =>
    simp only [MixedAction.code]
    iintro ⟨HI, HK, HPC, HF, Hnext⟩
    have rule := a.sound (GF := GF) rvc cpu s.machine
    dsimp only [Stack.State.machine] at rule
    iapply rule $$ [$HI $HK $HPC HF Hnext]
    inext
    iapply wpNext_intro_pin
    iintro %cpu' %hpin HK HPC
    ihave Hnext := wpNext_at _ _ _ cpu' _ hpin $$ Hnext
    ihave Hstep := Hnext $$ %(⟨(a.run rvc cpu' s.machine).ctx,
      (a.run rvc cpu' s.machine).pc, s.cells⟩ : Stack.State) %rfl
    dsimp only [Stack.State.machine]
    iapply Hstep $$ HK HPC HF

theorem MixedAction.indices (a : MixedAction) (rvc : Bool) (cpu : CPU) (s t : Stack.State)
    (hn : a.Next rvc cpu s t) : t.ctx.sie = s.ctx.sie ∧ t.ctx.proc = s.ctx.proc := by
  cases a with
  | reg a =>
    cases hn
    exact ⟨a.run_sie .., a.run_proc ..⟩
  | stack a => exact a.next_indices rvc cpu s t hn

/-- Uniform actual-binary transfer, with stack validity separated into the
pure invariant. Both fresh stack contents and hart migrations are universal. -/
theorem mixed_graph_transfer (slots : Nat) (rows : List Binary.Row) (s : Stack.State)
    (sie : Bool) (proc : BitVec 64) (hsie : s.ctx.sie = sie) (hproc : s.ctx.proc = proc)
    (ready : MixedReady slots rows s) (hcut : ¬ MixedCut slots rows s) :
    Transfer (mixedOwn (GF := GF)) sie proc (MixedEdge slots rows) s := by
  unfold MixedCut at hcut
  cases hfind : findMixed slots s.pc rows with
  | none => exact False.elim (hcut hfind)
  | some r =>
    intro cpu
    unfold mixedOwn regOwn Stack.State.machine
    iintro ⟨⟨⟨#HT, HK, HPC⟩, HF⟩, Hnext⟩
    ihave #HI := r.row.instr (GF := GF) $$ HT
    rw [← r.address, r.decoded]
    iapply r.action.sound r.row.rvc cpu s (ready r hfind) $$ [$HI $HK $HPC $HF Hnext]
    inext
    rw [hsie, hproc]
    iapply wpNext_intro_pin
    iintro %cpu' %hp %t %hn HK HPC HF
    ihave Hnext := wpNext_at _ _ _ cpu' _ hp $$ Hnext
    iapply Hnext $$ %t %(show MixedEdge slots rows s t from ⟨r, hfind, cpu', hn⟩) [HT HK HPC HF]
    dsimp only
    iframe HT HK HPC HF

/-- A whole register/stack region is compiled from the binary table with only
pure readiness and preservation obligations, including loops and branches. -/
theorem wp_mixed_graph (slots : Nat) (rows : List Binary.Row) (inv : Stack.State → Prop)
    (ready : ∀ s, inv s → MixedReady slots rows s)
    (preserved : ∀ s t, inv s → MixedEdge slots rows s t → inv t)
    (cpu : CPU) (s : Stack.State) (entry : inv s) :
    mixedOwn (GF := GF) cpu s ∗ wpNext s.ctx.sie s.ctx.proc cpu (fun cpu' => iprop(
      ∀ t, ⌜inv t⌝ -∗ ⌜MixedCut slots rows t⌝ -∗ mixedOwn cpu' t -∗ wpLoop cpu'))
      ⊢ wpLoop cpu := by
  let good (t : Stack.State) := t.ctx.sie = s.ctx.sie ∧ t.ctx.proc = s.ctx.proc ∧ inv t
  have closed : Closed good (MixedCut slots rows) (MixedEdge slots rows) := by
    constructor
    intro a b ha _ he
    obtain ⟨r, hr, c, hn⟩ := he
    have hx := r.action.indices r.row.rvc c a b hn
    exact ⟨hx.1.trans ha.1, hx.2.trans ha.2.1,
      preserved a b ha.2.2 ⟨r, hr, c, hn⟩⟩
  iintro ⟨Hstate, Hexit⟩
  iapply wp_control_flow (mixedOwn (GF := GF)) s.ctx.sie s.ctx.proc closed
    (fun a ha hc => mixed_graph_transfer slots rows a _ _ ha.1 ha.2.1 (ready a ha.2.2) hc)
    cpu s (show good s from ⟨rfl, rfl, entry⟩) $$ [$Hstate Hexit]
  iapply wpNext_intro_pin
  iintro %cpu' %hp %t %hg %hc Hstate
  ihave Hexit := wpNext_at _ _ _ cpu' _ hp $$ Hexit
  iapply Hexit $$ %t %hg.2.2 %hc Hstate

end Xv6.WholeFunction
