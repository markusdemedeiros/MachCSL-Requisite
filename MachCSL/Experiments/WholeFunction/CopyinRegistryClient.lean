import Experiments.WholeFunction.KernelCallRegistry
import Experiments.WholeFunction.CopyinCallClosure
import Experiments.WholeFunction.CopyinStart
import Experiments.WholeFunction.CopyinBoundary

/-! COPYIN's finite witnessed registry. The semantic loop invariant and callee
join proofs are reused, while readiness, call lookup and return dispatch use the
shared registry directly. No old target-ladder spatial specification is used. -/
namespace Xv6.WholeFunction.Copyin.RegistryClient
open Iris Iris.BI Iris.ProgramLogic MachCSL LeanRV64D

private theorem three_cases (j : Fin 3) : j = 0 ∨ j = 1 ∨ j = 2 := by omega

noncomputable def walkFamily (i : Inputs) : CalleeFamily State.machine := {
  target := KA.«walkaddr», Witness := Unit
  Enabled := fun _ => WalkEnabled i, Next := fun _ => WalkNext i
  cells := fun _ _ _ h => WalkNext.cells h
  indices := fun _ _ _ h => WalkNext.indices h
  saved := fun _ _ _ h => by obtain ⟨R, rfl, saved, _⟩ := h; exact saved }

noncomputable def faultFamily (i : Inputs) : CalleeFamily State.machine := {
  target := KA.«vmfault», Witness := Unit
  Enabled := fun _ => FaultEnabled i, Next := fun _ => FaultNext i
  cells := fun _ _ _ h => FaultNext.cells h
  indices := fun _ _ _ h => FaultNext.indices h
  saved := fun _ _ _ h => by obtain ⟨_, _, R, _, rfl, _, saved, _⟩ := h; exact saved }

/-- Both the actual length and the leaf witness survive in registry returns. -/
noncomputable def readFamily (i : Inputs) : CalleeFamily State.machine := {
  target := KA.«memmove», Witness := Nat × BitVec 64
  Enabled := fun w s => ReadEnabled i s w.1 w.2
  Next := fun w s => ReadNext i s w.1
  cells := fun _ _ _ h => ReadNext.cells h
  indices := fun _ _ _ h => ReadNext.indices h
  saved := fun _ _ _ h => by obtain ⟨R, rfl, saved, _⟩ := h; exact saved }

noncomputable def family (i : Inputs) : Fin 3 → CalleeFamily State.machine :=
  Fin.cases (walkFamily i) (Fin.cases (faultFamily i) (fun _ => readFamily i))

private def target : Fin 3 → BitVec 64 :=
  Fin.cases KA.«walkaddr» (Fin.cases KA.«vmfault» (fun _ => KA.«memmove»))

private theorem family_target (i : Inputs) (j : Fin 3) : (family i j).target = target j := by
  rcases three_cases j with rfl | rfl | rfl <;> rfl

noncomputable def registry (i : Inputs) : CalleeRegistry State.machine 3 := {
  family := family i
  distinct := by
    have unique : Function.Injective target := by unfold Function.Injective target; decide
    intro a b same
    apply unique
    rw [← family_target i a, ← family_target i b]
    exact same }

noncomputable def calls (i : Inputs) : RegisteredCalls State 3 := {
  slots := 12, rows := Binary.copyin.rows
  machine := State.machine, withMachine := State.withMachine
  machine_with := fun _ _ => rfl
  callees := registry i }

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
variable [Xv6G GF] [WchG GF] [CurCtx]

theorem sound (WA : WALKADDR) (VF : VMFAULT) (MM : MEMMOVE)
    (i : Inputs) (γl : GName) (γk : KmemNames) :
    (registry i).Sound (payload (GF := GF) i γl γk) := by
  intro j w s enabled
  rcases three_cases j with rfl | rfl | rfl
  · exact walk_spec WA i γl γk s enabled
  · exact fault_spec VF i γl γk s enabled
  · exact read_spec MM i γl γk s w.1 w.2 enabled

set_option maxHeartbeats 0 in
noncomputable def walkSite : CallSite Binary.copyin.rows
    0x800016ea#64 KA.«walkaddr» 0x800016ee#64 := by checked_callsite

set_option maxHeartbeats 0 in
noncomputable def faultSite : CallSite Binary.copyin.rows
    0x800016f8#64 KA.«vmfault» 0x800016fc#64 := by checked_callsite

set_option maxHeartbeats 0 in
noncomputable def moveSite : CallSite Binary.copyin.rows
    0x800016d0#64 KA.«memmove» 0x800016d4#64 := by checked_callsite

noncomputable def walkAnnotation {i : Inputs} (valid : Valid i) :
    AnnotatedSite (calls i) (Good i) := {
  callee := 0, pc := 0x800016ea#64, returnPC := 0x800016ee#64, binary := walkSite
  Precondition := WalkCall i
  enabled := fun s _ h => ⟨(), walk_ready valid h⟩
  closes := fun _ _ h _ _ _ step => walk_call_good valid h step }

noncomputable def faultAnnotation {i : Inputs} (valid : Valid i) :
    AnnotatedSite (calls i) (Good i) := {
  callee := 1, pc := 0x800016f8#64, returnPC := 0x800016fc#64, binary := faultSite
  Precondition := FaultCall i
  enabled := fun s _ h => ⟨(), fault_ready valid h⟩
  closes := fun _ _ h _ _ _ step => fault_call_good valid h step }

noncomputable def moveAnnotation {i : Inputs} (valid : Valid i) :
    AnnotatedSite (calls i) (Good i) := {
  callee := 2, pc := 0x800016d0#64, returnPC := 0x800016d4#64, binary := moveSite
  Precondition := fun s => ∃ w, MoveCall i s w
  enabled := by
    intro s _ ⟨w, h⟩
    obtain ⟨leaf, enabled⟩ := move_ready valid h
    exact ⟨(readLength (enter s KA.«memmove» 0x800016d4#64), leaf), enabled⟩
  closes := by
    intro s _ ⟨w, h⟩ ⟨n, leaf⟩ t enabled step
    change ReadEnabled i (enter s KA.«memmove» 0x800016d4#64) n leaf at enabled
    change ReadNext i (enter s KA.«memmove» 0x800016d4#64) n t at step
    have len := move_length h
    have fit := enabled.fit
    unfold readLength at len
    rw [enabled.lenArg, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at len
    exact move_call_good valid h (by simpa only [len] using step) }

noncomputable def sites {i : Inputs} (valid : Valid i) : Fin 3 → AnnotatedSite (calls i) (Good i) :=
  Fin.cases (walkAnnotation valid) (Fin.cases (faultAnnotation valid) (fun _ => moveAnnotation valid))

/-- Exactly the active semantic endpoint envelope; no arbitrary state is
admitted by merely being at one of the call PCs. -/
theorem atSite_iff {i : Inputs} (valid : Valid i) (s : State) :
    (calls i).AtSite (sites valid) s ↔ Endpoint i s ∧ ¬ BodyExit s := by
  constructor
  · rintro ⟨j, matchSite⟩
    rcases three_cases j with rfl | rfl | rfl
    · change s.machine.pc = 0x800016ea#64 ∧ WalkCall i s at matchSite
      exact ⟨.walk matchSite.2, by intro done; have := matchSite.1.symm.trans done; contradiction⟩
    · change s.machine.pc = 0x800016f8#64 ∧ FaultCall i s at matchSite
      exact ⟨.fault matchSite.2, by intro done; have := matchSite.1.symm.trans done; contradiction⟩
    · change s.machine.pc = 0x800016d0#64 ∧ ∃ w, MoveCall i s w at matchSite
      obtain ⟨pc, w, h⟩ := matchSite
      exact ⟨.move w h, by intro done; have := pc.symm.trans done; contradiction⟩
  · rintro ⟨endpoint, active⟩
    cases endpoint with
    | walk h => exact ⟨0, h.pc, h⟩
    | fault h => exact ⟨1, h.pc, h⟩
    | move w h => exact ⟨2, h.pc, w, h⟩
    | done h => exact False.elim (active h.pc)

theorem good_ready {i : Inputs} (valid : Valid i) (s : State)
    (h : Good i s) (active : ¬ BodyExit s) : (calls i).dispatcher.Ready s := by
  obtain ⟨goal, cut, hm, hc, cert, endpoint⟩ := h
  rcases cert.cut_cases rfl with he | ⟨r, found, _, _⟩
  · have hs := state_eq_of_parts s goal hm hc he
    subst goal
    exact (calls i).atSite_ready (sites valid) ((atSite_iff valid s).2 ⟨endpoint, active⟩)
  · have hm := Symbolic.findMixed_of_findReg 12 s.machine.pc Binary.copyin.rows r found
    simp only [RegisteredCalls.dispatcher, Dispatcher.Ready, calls, hm,
      Symbolic.mixed, MixedAction.Enabled]

theorem good_closed {i : Inputs} (valid : Valid i) (s t : State)
    (h : Good i s) (active : ¬ BodyExit s) (edge : (calls i).dispatcher.Edge s t) : Good i t := by
  cases edge with
  | ordinary r found cpu t step => exact good_ordinary h active r found cpu t step
  | call r hm found ready t step =>
    exact (calls i).atSite_closed (sites valid)
      ((atSite_iff valid s).2 ⟨good_call_endpoint h hm, active⟩) r found step

/-- Unknown callee addresses are rejected before a semantic summary is used. -/
theorem unknown_target_not_ready (i : Inputs) (s : State)
    (walk : s.machine.pc ≠ KA.«walkaddr») (fault : s.machine.pc ≠ KA.«vmfault»)
    (move : s.machine.pc ≠ KA.«memmove») : ¬ (registry i).Ready s := by
  rintro ⟨j, w, pc, enabled⟩
  rcases three_cases j with rfl | rfl | rfl
  · exact walk pc
  · exact fault pc
  · exact move pc

/-- An actual descriptor cannot relabel the memmove JAL as a walkaddr call. -/
theorem reject_wrong_target :
    ¬ Nonempty (CallSite Binary.copyin.rows 0x800016d0#64 KA.«walkaddr» 0x800016d4#64) := by
  rintro ⟨bad⟩
  have same := Option.some.inj (bad.found.symm.trans moveSite.found)
  have target := bad.target_eq
  rw [same, moveSite.target_eq] at target
  contradiction

theorem reject_wrong_return :
    ¬ Nonempty (CallSite Binary.copyin.rows 0x800016d0#64 KA.«memmove» 0#64) := by
  rintro ⟨bad⟩
  have same := Option.some.inj (bad.found.symm.trans moveSite.found)
  have result := bad.return_eq
  rw [same, moveSite.return_eq] at result
  contradiction

theorem reject_wrong_pc {i : Inputs} (valid : Valid i) (s : State)
    (pc : s.machine.pc = 0#64) : ¬ (calls i).AtSite (sites valid) s := by
  rintro ⟨j, matched⟩
  rcases three_cases j with rfl | rfl | rfl
  · exact (by decide : 0#64 ≠ 0x800016ea#64) (pc.symm.trans matched.1)
  · exact (by decide : 0#64 ≠ 0x800016f8#64) (pc.symm.trans matched.1)
  · exact (by decide : 0#64 ≠ 0x800016d0#64) (pc.symm.trans matched.1)

theorem reject_zero_read (i : Inputs) (s : State) (leaf : BitVec 64) :
    ¬ (readFamily i).Enabled (0, leaf) s := fun h => Nat.lt_irrefl 0 h.positive

/-- A memmove return exposes one shared witness for enabling and effect. -/
theorem read_return_witness {i : Inputs} {s t : State}
    (pc : s.machine.pc = KA.«memmove») (step : (registry i).Next s t) :
    ∃ n leaf, ReadEnabled i s n leaf ∧ ReadNext i s n t := by
  obtain ⟨⟨n, leaf⟩, enabled, result⟩ := (registry i).next_at 2 pc step
  exact ⟨n, leaf, enabled, result⟩

theorem wp_body (WA : WALKADDR) (VF : VMFAULT) (MM : MEMMOVE)
    (i : Inputs) (γl : GName) (γk : KmemNames) (valid : Valid i)
    (cpu : CPU) (s : State) (entry : Good i s) :
    fullOwn State.machine (payload (GF := GF) i γl γk) cpu s ∗
    wpNext i.entry.sie i.entry.proc cpu (fun cpu' => iprop(
      ∀ t, ⌜Good i t⌝ -∗ ⌜BodyExit t⌝ -∗
        fullOwn State.machine (payload i γl γk) cpu' t -∗ wpLoop cpu')) ⊢ wpLoop cpu :=
  (calls i).dispatcher.wp_body (payload i γl γk)
    (fun _ _ => by dsimp only [RegisteredCalls.dispatcher, calls, payload, State.withMachine]; iintro H; iexact H)
    ((registry i).spec _ (sound WA VF MM i γl γk)) i.entry.sie i.entry.proc (Good i) BodyExit
    (good_closed valid) (good_ready valid) (fun _ h => good_indices h) cpu s entry

theorem body_certificate (WA : WALKADDR) (VF : VMFAULT) (MM : MEMMOVE)
    (i : Inputs) (γl : GName) (γk : KmemNames) (valid : Valid i)
    (positive : 0 < i.old.length) : BodyCertificate (GF := GF) i γl γk := by
  intro cpu
  iintro ⟨Hstate, Hnext⟩
  iapply wp_body WA VF MM i γl γk valid cpu (initialBody i)
    (initial_good i valid positive) $$ [$Hstate Hnext]
  iapply wpNext_intro_pin
  iintro %cpu' %pin %t %good %done Hstate
  ihave Hnext := wpNext_at i.entry.sie i.entry.proc cpu cpu' _ pin $$ Hnext
  iapply Hnext $$ %t %(good_exit_result good done) Hstate

end Xv6.WholeFunction.Copyin.RegistryClient

namespace Xv6.WholeFunction.Copyin.RegistryClient
/-- The unchanged public contract, now through finite registry dispatch. -/
theorem compiled_copyin (WA : WALKADDR) (VF : VMFAULT) (MM : MEMMOVE) : COPYIN :=
  copyin_of_body ⟨fun i γl γk valid positive => body_certificate WA VF MM i γl γk valid positive⟩
end Xv6.WholeFunction.Copyin.RegistryClient

open Lean in
run_cmd do
  let baseline ← collectAxioms ``Xv6.WholeFunction.Copyin.wp_of_body
  let generic ← collectAxioms ``Xv6.WholeFunction.Dispatcher.wp_body
  let allowed := baseline ++ generic
  for name in #[``Xv6.WholeFunction.Copyin.RegistryClient.sound,
      ``Xv6.WholeFunction.Copyin.RegistryClient.good_closed,
      ``Xv6.WholeFunction.Copyin.RegistryClient.compiled_copyin] do
    let axioms ← collectAxioms name
    let extra := axioms.filter fun a => !allowed.contains a
    unless extra.isEmpty do throwError "{name}: unexpected axioms {extra}"
    if axioms.contains ``sorryAx then throwError "{name}: sorryAx"
  logInfo "Finite COPYIN registry: full contract checked without new axioms."


open Lean in
run_cmd do
  let forbidden : Array Name := #[
    `Xv6.WholeFunction.Copyin.registered_spec,
    `Xv6.WholeFunction.Copyin.compile,
    `Xv6.WholeFunction.Copyin.wp_body_from_invariant,
    `Xv6.WholeFunction.Copyin.endpoint_call_good,
    `Xv6.WholeFunction.Copyin.walk_entry,
    `Xv6.WholeFunction.Copyin.fault_entry,
    `Xv6.WholeFunction.Copyin.move_entry,
    `Xv6.WholeFunction.Copyin.compiled_copyin]
  let env ← getEnv
  let mut seen : Std.HashSet Name := {}
  let mut todo := #[``Xv6.WholeFunction.Copyin.RegistryClient.compiled_copyin]
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    unless seen.contains name do
      seen := seen.insert name
      if forbidden.contains name then throwError "Old dispatch dependency: {name}"
      if let some info := env.find? name then
        todo := todo ++ info.type.getUsedConstants
        if let some value := info.value? then todo := todo ++ value.getUsedConstants
  logInfo "Finite COPYIN registry: no dependency on old dispatch/entry/closure adapters."
