import Experiments.WholeFunction.KernelCallRegistry
import Experiments.WholeFunction.CopyoutCallClosure
import Experiments.WholeFunction.CopyoutClosure
import Experiments.WholeFunction.CopyoutStart
import Experiments.WholeFunction.CopyoutBoundary

namespace Xv6.WholeFunction.Copyout.Registered
open Iris Iris.BI Iris.ProgramLogic MachCSL

def walkFamily (i : Inputs) : CalleeFamily State.machine where
  target := KA.«walkaddr»
  Witness := Unit
  Enabled := fun _ => WalkEnabled i
  Next := fun _ => WalkNext i
  cells := fun _ _ _ h => h.cells
  indices := fun _ _ _ h => h.indices
  saved := by intro _ s t h; obtain ⟨R,rfl,saved,_⟩ := h; exact saved

def faultFamily (i : Inputs) : CalleeFamily State.machine where
  target := KA.«vmfault»
  Witness := Unit
  Enabled := fun _ => FaultEnabled i
  Next := fun _ => FaultNext i
  cells := fun _ _ _ h => h.cells
  indices := fun _ _ _ h => h.indices
  saved := by intro _ s t h; obtain ⟨spie,spp,R,mem,rfl,_,saved,_⟩ := h; exact saved

def probeFamily (i : Inputs) : CalleeFamily State.machine where
  target := KA.«walk»
  Witness := BitVec 64
  Enabled := fun w s => ProbeEnabled i s w
  Next := fun w s t => ProbeNext i s w t
  cells := fun _ _ _ h => h.cells
  indices := fun _ _ _ h => h.indices
  saved := by intro _ s t h; obtain ⟨R,rfl,saved,_⟩ := h; exact saved

def writeFamily (i : Inputs) : CalleeFamily State.machine where
  target := KA.«memmove»
  Witness := Nat × BitVec 64
  Enabled := fun w s => WriteEnabled i s w.1 w.2
  Next := fun w s t => WriteNext i s w.1 t
  cells := fun _ _ _ h => h.cells
  indices := fun _ _ _ h => h.indices
  saved := by intro _ s t h; obtain ⟨R,rfl,saved,_⟩ := h; exact saved

def families (i : Inputs) : Fin 4 → CalleeFamily State.machine :=
  Fin.cases (walkFamily i) (Fin.cases (faultFamily i) (Fin.cases (probeFamily i) (fun _ => writeFamily i)))

def registry (i : Inputs) : CalleeRegistry State.machine 4 where
  family := families i
  distinct := by
    let target : Fin 4 → BitVec 64 :=
      Fin.cases KA.«walkaddr» (Fin.cases KA.«vmfault» (Fin.cases KA.«walk» (fun _ => KA.«memmove»)))
    have targets (j : Fin 4) : (families i j).target = target j := by
      refine Fin.cases rfl (fun j => Fin.cases rfl (fun j => Fin.cases rfl (fun _ => rfl) j) j) j
    have unique : Function.Injective target := by unfold Function.Injective target; decide
    intro a b same
    apply unique
    rw [← targets a,← targets b]
    exact same

noncomputable def calls (i : Inputs) : RegisteredCalls State 4 where
  slots := 14
  rows := Binary.copyout.rows
  machine := State.machine
  withMachine := State.withMachine
  machine_with := fun _ _ => rfl
  callees := registry i

noncomputable def walkSite : CallSite Binary.copyout.rows 0x80001622#64 KA.«walkaddr» 0x80001626#64 := by checked_callsite

noncomputable def faultSite : CallSite Binary.copyout.rows 0x80001632#64 KA.«vmfault» 0x80001636#64 := by checked_callsite

noncomputable def probeSite : CallSite Binary.copyout.rows 0x80001640#64 KA.«walk» 0x80001644#64 := by checked_callsite

noncomputable def writeSite : CallSite Binary.copyout.rows 0x80001604#64 KA.«memmove» 0x80001608#64 := by checked_callsite

noncomputable def walkAnnotation (i : Inputs) (valid : Valid i) : AnnotatedSite (calls i) (Good i) where
  callee := 0
  pc := 0x80001622#64
  returnPC := 0x80001626#64
  binary := walkSite
  Precondition := WalkCall i
  enabled := fun s _ h => ⟨(), walk_ready valid h⟩
  closes := fun _ _ h _ _ _ result => walk_call_good valid h result

noncomputable def faultAnnotation (i : Inputs) (valid : Valid i) : AnnotatedSite (calls i) (Good i) where
  callee := 1
  pc := 0x80001632#64
  returnPC := 0x80001636#64
  binary := faultSite
  Precondition := FaultCall i
  enabled := fun s _ h => ⟨(), fault_ready valid h⟩
  closes := fun _ _ h _ _ _ result => fault_call_good valid h result

noncomputable def probeAnnotation (i : Inputs) (valid : Valid i) : AnnotatedSite (calls i) (Good i) where
  callee := 2
  pc := 0x80001640#64
  returnPC := 0x80001644#64
  binary := probeSite
  Precondition := fun s => ∃ w, ProbeCall i s w
  enabled := by
    intro s _ h
    obtain ⟨w,h⟩ := h
    exact probe_ready valid h
  closes := by
    intro s _ h w t enabled result
    obtain ⟨v,h⟩ := h
    have same := probe_same_leaf h enabled
    subst w
    exact probe_call_good valid h result

noncomputable def writeAnnotation (i : Inputs) (valid : Valid i) : AnnotatedSite (calls i) (Good i) where
  callee := 3
  pc := 0x80001604#64
  returnPC := 0x80001608#64
  binary := writeSite
  Precondition := fun s => ∃ w, MoveCall i s w
  enabled := by
    intro s _ h
    obtain ⟨w,h⟩ := h
    have ready := move_ready valid h
    change ∃ w', WriteEnabled i (enter s KA.«memmove» 0x80001608#64)
      (writeLength (enter s KA.«memmove» 0x80001608#64)) w' at ready
    obtain ⟨w',enabled⟩ := ready
    exact ⟨⟨_,w'⟩,enabled⟩
  closes := by
    intro s _ h witness t enabled result
    obtain ⟨w,h⟩ := h
    change WriteEnabled i (enter s KA.«memmove» 0x80001608#64) witness.1 witness.2 at enabled
    have nb : witness.1 < 2^64 := by have := enabled.bound; have := valid.bound; omega
    have count := congrArg BitVec.toNat enabled.lenArg
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt nb] at count
    have same : witness.1 = chunk i s := count.symm.trans (move_length h)
    change WriteNext i (enter s KA.«memmove» 0x80001608#64) witness.1 t at result
    rw [same] at result
    exact move_call_good valid h result

noncomputable def annotations (i : Inputs) (valid : Valid i) : Fin 4 → AnnotatedSite (calls i) (Good i) :=
  Fin.cases (walkAnnotation i valid) (Fin.cases (faultAnnotation i valid)
    (Fin.cases (probeAnnotation i valid) (fun _ => writeAnnotation i valid)))

theorem endpoint_covered {i : Inputs} (valid : Valid i) {s : State}
    (h : Endpoint i s) (active : ¬ BodyExit s) :
    (calls i).AtSite (annotations i valid) s := by
  cases h with
  | walk h => exact ⟨0,h.pc,h⟩
  | fault h => exact ⟨1,h.pc,h⟩
  | probe w h => exact ⟨2,h.pc,w,h⟩
  | move w h => exact ⟨3,h.pc,w,h⟩
  | done h => exact (active h.pc).elim

theorem ready {i : Inputs} (valid : Valid i) (s : State) (h : Good i s) (active : ¬ BodyExit s) :
    (calls i).dispatcher.Ready s := by
  rcases Residual.decode_or_endpoint h with he | ⟨r,found⟩
  · exact (calls i).atSite_ready (annotations i valid) (endpoint_covered valid he active)
  · have mixed := Symbolic.findMixed_of_findReg 14 s.machine.pc Binary.copyout.rows r found
    simp only [Dispatcher.Ready, RegisteredCalls.dispatcher, calls,mixed,
      Symbolic.mixed,MixedAction.Enabled]

theorem closed {i : Inputs} (valid : Valid i) (s t : State) (h : Good i s) (active : ¬ BodyExit s)
    (edge : (calls i).dispatcher.Edge s t) : Good i t := by
  cases edge with
  | ordinary r found cpu t step => exact good_ordinary h active r found cpu t step
  | call r hm hf enabled t step =>
    exact (calls i).atSite_closed (annotations i valid)
      (endpoint_covered valid (good_call_endpoint h hm) active) r hf step

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [WchG GF] [CurCtx]

theorem sound (WA : WALKADDR) (VF : VMFAULT) (W : WALK_NOALLOC) (MM : MEMMOVE)
    (i : Inputs) (γl : GName) (γk : KmemNames) : (registry i).Sound (payload (GF := GF) i γl γk) := by
  intro j
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ ?_ j) j) j
  · intro _ s enabled; exact walk_spec WA i γl γk s enabled
  · intro _ s enabled; exact fault_spec VF i γl γk s enabled
  · intro w s enabled; exact probe_spec W i γl γk s w enabled
  · intro _ witness s enabled; exact write_spec MM i γl γk s witness.1 witness.2 enabled

private theorem owned_wf (i : Inputs) (γl : GName) (γk : KmemNames) (cpu : CPU) (s : State) :
    fullOwn State.machine (payload (GF := GF) i γl γk) cpu s ⊢
      fullOwn State.machine (payload i γl γk) cpu s ∗ ⌜uptWf s.memory.table⌝ := by
  unfold fullOwn payload
  iintro ⟨Hmachine,Hlock,Halloc,Htable,Hsource,Hlend⟩
  icases UMemL.procPtAt_wf _ _ $$ Htable with ⟨Htable,%wf⟩
  isplitl [Hmachine Hlock Halloc Htable Hsource Hlend]
  · iframe
  · ipureintro; exact wf

theorem body_certificate (WA : WALKADDR) (VF : VMFAULT) (W : WALK_NOALLOC) (MM : MEMMOVE)
    (i : Inputs) (γl : GName) (γk : KmemNames) (valid : Valid i)
    (positive : 0 < i.bytes.length) : BodyCertificate (GF := GF) i γl γk := by
  intro cells frame cpu
  iintro ⟨Hstate,Hnext⟩
  icases owned_wf i γl γk cpu (initialBody i cells) $$ Hstate with ⟨Hstate,%wf⟩
  have body := (calls i).dispatcher.wp_body (GF := GF) (payload i γl γk)
    (fun _ _ => by dsimp only [RegisteredCalls.dispatcher,calls,payload,State.withMachine]; iintro H; iexact H)
    ((registry i).spec _ (sound WA VF W MM i γl γk))
    i.entry.sie i.entry.proc (Good i) BodyExit (closed valid) (ready valid)
    (fun _ h => good_indices h) cpu (initialBody i cells)
    (initial_good i valid positive cells frame wf)
  dsimp only [RegisteredCalls.dispatcher,calls] at body
  iapply body $$ [$Hstate Hnext]
  iapply wpNext_intro_pin
  iintro %cpu' %pin %t %good %done Hstate
  ihave Hnext := wpNext_at i.entry.sie i.entry.proc cpu cpu' _ pin $$ Hnext
  iapply Hnext $$ %t %(good_exit_result good done) Hstate

end

theorem compiled_copyout (WA : WALKADDR) (VF : VMFAULT) (W : WALK_NOALLOC) (MM : MEMMOVE) : COPYOUT :=
  copyout_of_body ⟨fun i γl γk valid positive => body_certificate WA VF W MM i γl γk valid positive⟩

end Xv6.WholeFunction.Copyout.Registered

open Lean in
run_cmd do
  let baseline ← collectAxioms ``Xv6.WholeFunction.Copyout.wp_of_body
  let generic ← collectAxioms ``Xv6.WholeFunction.Dispatcher.wp_body
  let allowed := baseline ++ generic
  for name in #[``Xv6.WholeFunction.Copyout.Registered.sound,
      ``Xv6.WholeFunction.Copyout.Registered.closed,
      ``Xv6.WholeFunction.Copyout.Registered.compiled_copyout] do
    let axs ← collectAxioms name
    let extra := axs.filter fun a => !allowed.contains a
    unless extra.isEmpty do throwError "{name}: unexpected axioms {extra}"
    if axs.contains ``sorryAx then throwError "{name}: sorryAx"
  let forbidden : Array Name := #[
    `Xv6.WholeFunction.Copyout.registered_spec,
    `Xv6.WholeFunction.Copyout.wp_body_from_invariant,
    `Xv6.WholeFunction.Copyout.endpoint_call_good,
    `Xv6.WholeFunction.Copyout.walk_entry,
    `Xv6.WholeFunction.Copyout.fault_entry,
    `Xv6.WholeFunction.Copyout.probe_entry,
    `Xv6.WholeFunction.Copyout.move_entry,
    `Xv6.WholeFunction.Copyout.compiled_copyout]
  let env ← getEnv
  let mut seen : Std.HashSet Name := {}
  let mut todo := #[``Xv6.WholeFunction.Copyout.Registered.compiled_copyout]
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    unless seen.contains name do
      seen := seen.insert name
      if forbidden.contains name then throwError "Old dispatch dependency: {name}"
      if let some info := env.find? name then
        todo := todo ++ info.type.getUsedConstants
        if let some value := info.value? then todo := todo ++ value.getUsedConstants
  let axioms ← collectAxioms ``Xv6.WholeFunction.Copyout.Registered.compiled_copyout
  logInfo m!"Finite COPYOUT registry: full contract, {axioms.size} inherited axioms, no old target/entry dispatch dependencies."
