import MachCSL.Wp
import MachCSL.RequisiteAdequacy
import Iris.ProgramLogic.ThreadPool

/-!
Regression for the coherence repair to MachCSL's state interpretation.
Run from the checkout root with:

  lake env lean Requisiteness/Coherence.lean

The byte at `addr` has an old value 0 and a newer value 1 written by another
hart. Two well-formed states differ only in their per-byte coherence floors
(1 versus 0). The program reads this byte, then either waits forever on a
reserved write (value 1) or fails (value 0). `high_adequate` and
`low_not_adequate` establish the operational safety difference.

Before the repair these states had identical interpretations; commit 81a062d67
contains the original checked impossibility proof. The repaired interpretation
provides a persistent coherence receipt for the high state, and the low state's
interpretation is incompatible with that receipt. This removes that particular
obstruction. `high_initializable` additionally applies the full requisiteness
theorem to initialize this program with the new physical interpretation.
-/
namespace MachCSL.Requisiteness
noncomputable section
open Classical
open Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.Language
open Iris.ProgramLogic.Language.Notation
open Sail Sail.ConcurrencyInterfaceV1 Sail.ArchSem LeanRV64D

set_option autoImplicit false
set_option maxRecDepth 2048

def reader : CPU := ⟨0, by decide⟩
def writer : CPU := ⟨1, by decide⟩
def addr : PAddr := 0x80000000#64
def history : Hist := [⟨1, 1, 1#8⟩, ⟨0, 0, 0#8⟩]

def machine (base : MState) (floor : Nat) : MState :=
  { base with
    mem := (∅ : FlatMem).insert addr history
    log := [1]
    tv := fun _ => 0
    itv := fun _ => 0
    hr := fun _ => ⟨1, fun _ => floor, false⟩
    resv := fun c => if c = writer then some ((∅ : Resv).insert addr 1#8) else none
    devrt := fun _ => DevRt.init }

def state (base : MState) (floor : Nat) : GState :=
  ⟨machine base floor, 0, true⟩

def readReq : Mem_read_request 1 64 Arch.pa Arch.translation Arch.arch_ak :=
  { access_kind := .AK_explicit ⟨.AV_plain, .AS_normal⟩
    va := none, pa := addr, translation := (), size := 1, tag := false }

def writeReq : Mem_write_request 1 64 Arch.pa Arch.translation Arch.arch_ak :=
  { access_kind := .AK_explicit ⟨.AV_plain, .AS_normal⟩
    va := none, pa := addr, translation := (), size := 1,
    value := some 1#8, tag := none }

def fail : SailM Unit := .impure (.error (.Assertion "coherence violation")) (fun v => nomatch v)
def wait : SailM Unit := .impure (.ok (.memWrite 1 64 writeReq)) (fun _ => fail)
def program : SailM Unit := .impure (.ok (.memRead 1 64 readReq))
  (fun r => if r = .Ok (1#8, none) then wait else fail)
def expr : Expr := .hart 0 reader program

theorem reserved (base : MState) (floor : Nat) :
    othersReserve (machine base floor).resv reader addr 1 := by
  refine ⟨writer, by decide, (∅ : Resv).insert addr 1#8, ?_, 0, by decide, ?_⟩
  · simp [machine]
  · simp

theorem ram : ramBytes addr 1 := by
  intro j hj
  have : j = 0 := by omega
  subst j
  decide

theorem read_byte (base : MState) (floor tv : Nat) :
    (machine base floor).mem.read (hartAgent reader) tv addr =
      some (if tv = 0 then 0#8 else 1#8) := by
  by_cases h : tv = 0
  · subst tv; simp [machine, FlatMem.read, history, Hist.read, HEnt.visible, hartAgent, reader]
  · have : 1 ≤ tv := by omega
    simp [machine, FlatMem.read, history, Hist.read, HEnt.visible, hartAgent, reader, h, this]

theorem machine_ok (base : MState) (floor : Nat) (hf : floor ≤ 1) :
    mmOk (machine base floor) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a H h
    by_cases ha : a = addr
    · subst a
      have : H = history := by simpa [machine] using h.symm
      subst H
      change histOk [1] history
      simp [histOk, history]
    · simp [machine, Ne.symm ha] at h
  · intro c
    simp [machine, MState.top, HRead.bound, hf]
  · intro c r hr a v hv
    by_cases hc : c = writer
    · have : r = (∅ : Resv).insert addr 1#8 := by simpa [machine, hc] using hr.symm
      subst r
      by_cases ha : a = addr
      · subst a
        have : v = 1#8 := by simpa using hv.symm
        subst v
        simp [machine, history, Hist.top]
      · simp [Ne.symm ha] at hv
    · simp [machine, hc] at hr
  · intro a H h
    by_cases ha : a = addr
    · subst a; decide
    · simp [machine, Ne.symm ha] at h
  · intro d; exact Nat.zero_lt_succ 0

theorem wait_step (base : MState) (floor : Nat) (m' : SailM Unit) (σ' : MState) :
    hartStep reader wait (machine base floor) m' σ' ↔
      m' = wait ∧ σ' = machine base floor := by
  have hn := not_devBytes_of_ramBytes ram (by decide)
  simp only [hartStep, wait, evStep, blockedStep, writeReq]
  simp only [hn, false_and, reserved, not_true_eq_false, and_false, exists_false,
    false_or, true_and]
  exact and_comm

theorem load_high (base : MState) (v : (Outcome.memRead 1 64 readReq).ret) (σ' : MState)
    (h : evStep reader (.memRead 1 64 readReq) (machine base 1) v σ') :
    v = .Ok (1#8, none) ∧ σ' = machine base 1 := by
  have hn := not_devBytes_of_ramBytes ram (by decide)
  simp only [evStep, readReq, akIfetch, akPlain, akExcl, Bool.not_false,
    Bool.true_and, Bool.false_eq_true, hn, false_and, and_false, false_or, or_false,
    true_and] at h
  obtain ⟨_, tv, w, _, htop, hcoh, hread, rfl, rfl⟩ := h
  have hlow : 1 ≤ tv := by simpa [HRead.cohOk, machine] using hcoh 0 (by decide)
  have htv : tv = 1 := by change tv ≤ 1 at htop; omega
  subst tv
  have hw := hread 0 (by decide)
  change (machine base 1).mem.read (hartAgent reader) 1 addr = some (nthByte w 0) at hw
  rw [read_byte] at hw
  have hw' : w = 1#8 := by simpa [nthByte, BitVec.extractLsb'] using hw.symm
  subst w
  refine ⟨rfl, ?_⟩
  unfold MState.afterLoad
  congr 1
  funext c
  simp only [updCpu, machine]
  split
  · simp [HRead.afterLoad]
  · rfl

theorem program_high_step (base : MState) (m' : SailM Unit) (σ' : MState) :
    hartStep reader program (machine base 1) m' σ' →
      m' = wait ∧ σ' = machine base 1 := by
  intro h
  rcases h with ⟨v, hm, hv⟩ | ⟨hb, _⟩
  · obtain ⟨rfl, rfl⟩ := load_high base v σ' hv
    simpa [program] using hm
  · simp [blockedStep, readReq, akExcl] at hb

theorem load_at (base : MState) (floor tv : Nat) (hf : floor ≤ tv) (htv : tv ≤ 1) :
    evStep reader (.memRead 1 64 readReq) (machine base floor)
      (.Ok ((if tv = 0 then 0#8 else 1#8), none))
      ((machine base floor).afterLoad reader addr 1 tv) := by
  refine Or.inr (Or.inr (Or.inl ⟨ram, rfl, tv, _, Nat.zero_le _, htv, ?_, ?_, rfl, rfl⟩))
  · intro j hj; exact hf
  · intro j hj
    have : j = 0 := by omega
    subst j
    change (machine base floor).mem.read (hartAgent reader) tv addr = _
    rw [read_byte]
    simp [nthByte, BitVec.extractLsb']

theorem fail_stuck (σ : MState) : ¬ PrimStep.Reducible (Expr.hart 0 reader fail,
    (⟨σ, 0, true⟩ : GState)) := by
  rintro ⟨κ, e', g', efs, h⟩
  rcases h.2 with ⟨_, _, m', σ', _, hs, _⟩ | ⟨hn, _⟩
  · exact hs
  · exact hn ⟨rfl, rfl⟩

def waiting : Expr := .hart 0 reader wait

theorem high_step (base : MState) (e : Expr) (he : e = expr ∨ e = waiting)
    (κ : List Obs) (e' : Expr) (g' : GState) (efs : List Expr)
    (hs : PrimStep.primStep (e, state base 1) κ (e', g', efs)) :
    e' = waiting ∧ g' = state base 1 ∧ efs = [] := by
  rcases he with rfl | rfl
  · obtain ⟨rfl, h⟩ := primStep_hart_inv hs
    rcases h with ⟨_, _, m', σ', rfl, hs', rfl⟩ | ⟨hn, _⟩
    · obtain ⟨rfl, rfl⟩ := program_high_step base m' σ' hs'
      exact ⟨rfl, rfl, rfl⟩
    · exact False.elim (hn ⟨rfl, rfl⟩)
  ·
    obtain ⟨rfl, h⟩ := primStep_hart_inv hs
    rcases h with ⟨_, _, m', σ', rfl, hs', rfl⟩ | ⟨hn, _⟩
    · obtain ⟨rfl, rfl⟩ := (wait_step base 1 m' σ').mp hs'
      exact ⟨rfl, rfl, rfl⟩
    · exact False.elim (hn ⟨rfl, rfl⟩)

theorem high_reducible (base : MState) (e : Expr) (he : e = expr ∨ e = waiting) :
    PrimStep.Reducible (e, state base 1) := by
  have hh : hartStep reader program (machine base 1) wait (machine base 1) := by
    have hl := load_at base 1 1 (by decide) (by decide)
    have hs := (load_high base _ _ hl).2
    rw [hs] at hl
    exact Or.inl ⟨.Ok (1#8, none), by simp, hl⟩
  rcases he with rfl | rfl
  · exact ⟨[], waiting, state base 1, [], rfl,
      Or.inl ⟨⟨rfl, rfl⟩, rfl, wait, machine base 1, rfl, hh, rfl⟩⟩
  · exact ⟨[], waiting, state base 1, [], rfl,
      Or.inl ⟨⟨rfl, rfl⟩, rfl, wait, machine base 1, rfl,
        (wait_step base 1 wait (machine base 1)).mpr ⟨rfl, rfl⟩, rfl⟩⟩

theorem singleton_step_inv (e : Expr) (g : GState) (κ : List Obs)
    (C : List Expr × GState) (hs : Step ([e], g) κ C) :
    ∃ e' g' efs, C = (e' :: efs, g') ∧
      PrimStep.primStep (e, g) κ (e', g', efs) := by
  generalize hstart : ([e], g) = start at hs
  cases hs with
  | @atomic e0 g0 κ e' g' efs hs t1 t2 =>
    have hl := congrArg (fun C : List Expr × GState => C.1.length) hstart
    simp only [List.length_singleton, List.length_append, List.length_cons] at hl
    have ht1 : t1 = [] := by cases t1 <;> simp_all
    have ht2 : t2 = [] := by cases t2 <;> simp_all
    subst t1 t2
    simp only [List.nil_append, Prod.mk.injEq, List.cons.injEq, _root_.and_true] at hstart
    obtain ⟨rfl, rfl⟩ := hstart
    exact ⟨e', g', efs, rfl, hs⟩

theorem high_safe (base : MState) : cfgSafe ([expr], state base 1) := by
  intro C hr
  have hi : ∃ e, C = ([e], state base 1) ∧ (e = expr ∨ e = waiting) := by
    induction hr with
    | refl => exact ⟨expr, rfl, Or.inl rfl⟩
    | @tail C₁ C₂ hr hs ih =>
      obtain ⟨e, rfl, he⟩ := ih
      obtain ⟨κ, hs⟩ := hs
      obtain ⟨e', g', efs, rfl, hp⟩ := singleton_step_inv e (state base 1) κ C₂ hs
      obtain ⟨rfl, rfl, rfl⟩ := high_step base e he κ e' g' efs hp
      exact ⟨waiting, rfl, Or.inr rfl⟩
  obtain ⟨e, rfl, he⟩ := hi
  intro e' hm
  have : e' = e := by simpa using hm
  subst e'
  exact Or.inr (high_reducible base e he)

theorem high_adequate (base : MState) :
    adequate .NotStuck expr (state base 1) (fun _ _ => True) := by
  constructor
  · intro _ _ v; exact nomatch v
  · intro tp g e _ hr hm
    exact high_safe base hr hm

theorem low_step_fail (base : MState) :
    PrimStep.primStep (expr, state base 0) []
      (.hart 0 reader fail, ⟨(machine base 0).afterLoad reader addr 1 0, 0, true⟩, []) := by
  refine ⟨rfl, Or.inl ⟨⟨rfl, rfl⟩, rfl, fail, _, rfl, ?_, rfl⟩⟩
  have hne : (Result.Ok (0#8, (none : Option Bool)) : Result _ Arch.abort) ≠ .Ok (1#8, none) := by
    intro h
    injection h with h
    exact (by decide : (0#8) ≠ 1#8) (congrArg Prod.fst h)
  exact Or.inl ⟨.Ok (0#8, none), by simp [hne],
    load_at base 0 0 (by decide) (by decide)⟩

theorem low_not_adequate (base : MState) :
    ¬ adequate .NotStuck expr (state base 0) (fun _ _ => True) := by
  intro h
  have hs : ([expr], state base 0) -·->ₜₚ*
      ([Expr.hart 0 reader fail], ⟨(machine base 0).afterLoad reader addr 1 0, 0, true⟩) :=
    .single ⟨[], Step.of_primStep (t₁ := []) (t₂ := []) (low_step_fail base)⟩
  have hn := h.adequate_not_stuck _ _ (.hart 0 reader fail) rfl hs (by simp)
  rcases hn with hv | hr
  · simp [ToVal.toVal] at hv
  · exact fail_stuck _ hr

/-- The high state supplies a persistent receipt without consuming its model. -/
theorem high_receipt {hlc : HasLC} {GF : BundledGFunctors} [MachFixedGS hlc GF]
    (E : EraGS) (base : MState) :
    memModelAt (GF := GF) E (machine base 1) ⊢
      memModelAt E (machine base 1) ∗ cohLbAt E reader (fun _ => 1) :=
  memModel_cohLb_get E (machine base 1) reader

/-- Retaining the high state's receipt rules out the unsafe low state in that era. -/
theorem low_rejects_high_receipt {hlc : HasLC} {GF : BundledGFunctors}
    [MachFixedGS hlc GF] (E : EraGS) (base : MState) :
    memModelAt (GF := GF) E (machine base 0) ∗ cohLbAt E reader (fun _ => 1) ⊢ False := by
  iintro H
  ihave %h := memModel_cohLb E (machine base 0) reader (fun _ => 1) $$ H
  ipureintro
  have hx := h addr
  exact Nat.not_succ_le_zero 0 hx

/-- The originally obstructed safe program now has a jointly initialized WP. -/
theorem high_initializable {hlc : HasLC} {GF : BundledGFunctors}
    [F : MachFixedGS hlc GF] [GhostMapG GF Nat Expr RegMapF]
    (base : MState) (κs : List Obs) :
    ⊢@{IProp GF} |={⊤}=> ∃ N : PhysicalNames,
      letI := F.withPhysicalNames N κs
      iprop(stateInterp (state base 1) 0 κs 0 ∗
        WP expr @ Stuckness.NotStuck; ⊤ {{ _v, ⌜True⌝ }}) :=
  Requisite.wp_alloc_requisiteness expr (state base 1) (fun _ => True) (high_adequate base) κs

/-- The unsafe low state cannot acquire a WP under the same ownership rule. -/
theorem low_not_provable {hlc : HasLC} {GF : BundledGFunctors}
    [MachGpreS hlc GF] (base : MState) :
    ¬ (∀ [MachFixedGS hlc GF],
      Requisite.ownState (state base 0) ⊢@{IProp GF}
        WP expr @ Stuckness.NotStuck; ⊤ {{ _v, ⌜True⌝ }}) := by
  intro hwp
  exact low_not_adequate base (Requisite.wp_adequacy expr (state base 0) (fun _ => True) hwp)

/-- info: 'MachCSL.Requisiteness.high_receipt' depends on axioms: [propext, choice, Quot.sound] -/
#guard_msgs in
#print axioms high_receipt

/-- info: 'MachCSL.Requisiteness.low_rejects_high_receipt' depends on axioms: [propext, choice, Quot.sound] -/
#guard_msgs in
#print axioms low_rejects_high_receipt

/-- info: 'MachCSL.Requisiteness.high_adequate' depends on axioms: [propext, choice, Quot.sound] -/
#guard_msgs in
#print axioms high_adequate

/-- info: 'MachCSL.Requisiteness.high_initializable' depends on axioms: [propext, choice, Quot.sound] -/
#guard_msgs in
#print axioms high_initializable

/-- info: 'MachCSL.Requisiteness.low_not_provable' depends on axioms: [propext, choice, Quot.sound] -/
#guard_msgs in
#print axioms low_not_provable

end
end MachCSL.Requisiteness
