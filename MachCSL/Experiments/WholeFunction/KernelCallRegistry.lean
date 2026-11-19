import Experiments.WholeFunction.KernelCallSites

/-! A finite, witnessed registry for semantic callee contracts. Enabled
witnesses are retained in the return relation: a page-table leaf or copy chunk
cannot be silently replaced after executing the callee. -/
namespace Xv6.WholeFunction
open Iris Iris.BI Iris.ProgramLogic MachCSL

structure CalleeFamily {S : Type} (machine : S → Stack.State) where
  target : BitVec 64
  Witness : Type
  Enabled : Witness → S → Prop
  Next : Witness → S → S → Prop
  cells : ∀ w s t, Next w s t → (machine t).cells = (machine s).cells
  indices : ∀ w s t, Next w s t →
    (machine t).ctx.sie = (machine s).ctx.sie ∧ (machine t).ctx.proc = (machine s).ctx.proc
  saved : ∀ w s t, Next w s t → calleeSaved (machine s).ctx.regs (machine t).ctx.regs

structure CalleeRegistry {S : Type} (machine : S → Stack.State) (n : Nat) where
  family : Fin n → CalleeFamily machine
  distinct : Function.Injective (fun j => (family j).target)

namespace CalleeRegistry
variable {S : Type} {machine : S → Stack.State} {n : Nat} (R : CalleeRegistry machine n)

def Ready (s : S) : Prop :=
  ∃ j w, (machine s).pc = (R.family j).target ∧ (R.family j).Enabled w s

def Next (s t : S) : Prop :=
  ∃ j w, (machine s).pc = (R.family j).target ∧
    (R.family j).Enabled w s ∧ (R.family j).Next w s t

theorem next_cells {s t : S} (h : R.Next s t) : (machine t).cells = (machine s).cells := by
  obtain ⟨j,w,_,_,h⟩ := h
  exact (R.family j).cells w s t h

theorem next_indices {s t : S} (h : R.Next s t) :
    (machine t).ctx.sie = (machine s).ctx.sie ∧ (machine t).ctx.proc = (machine s).ctx.proc := by
  obtain ⟨j,w,_,_,h⟩ := h
  exact (R.family j).indices w s t h

theorem next_saved {s t : S} (h : R.Next s t) :
    calleeSaved (machine s).ctx.regs (machine t).ctx.regs := by
  obtain ⟨j,w,_,_,h⟩ := h
  exact (R.family j).saved w s t h

/-- Recover both the enabled witness and its exact semantic result. The
registry's checked target uniqueness removes any target-dispatch case split. -/
theorem next_at {s t : S} (j : Fin n) (pc : (machine s).pc = (R.family j).target)
    (h : R.Next s t) : ∃ w, (R.family j).Enabled w s ∧ (R.family j).Next w s t := by
  obtain ⟨j',w,address,enabled,result⟩ := h
  have same : j' = j := R.distinct (address.symm.trans pc)
  subst j'
  exact ⟨w,enabled,result⟩

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
variable [CurCtx] [KernelGeom] [KernelImage GF]

def Sound (payload : S → IProp GF) : Prop :=
  ∀ j w s, (R.family j).Enabled w s →
    CalleeSpec machine payload ((R.family j).Next w s) s

theorem spec (payload : S → IProp GF) (sound : R.Sound payload)
    (s : S) (ready : R.Ready s) : CalleeSpec machine payload (R.Next s) s := by
  obtain ⟨j,w,pc,enabled⟩ := ready
  intro cpu
  iintro ⟨Hstate,Hnext⟩
  iapply sound j w s enabled cpu $$ [$Hstate Hnext]
  iapply wpNext_intro_pin
  iintro %cpu' %pin %t %result Hstate
  ihave Hnext := wpNext_at _ _ _ cpu' _ pin $$ Hnext
  iapply Hnext $$ %t %(show R.Next s t from ⟨j,w,pc,enabled,result⟩) Hstate

end CalleeRegistry

/-- The existing dispatcher plus a finite registry. No instruction execution
or call execution is redefined here. -/
structure RegisteredCalls (S : Type) (n : Nat) where
  slots : Nat
  rows : List Binary.Row
  machine : S → Stack.State
  withMachine : S → Stack.State → S
  machine_with : ∀ s m, machine (withMachine s m) = m
  callees : CalleeRegistry machine n

namespace RegisteredCalls
variable {S : Type} {n : Nat} (C : RegisteredCalls S n)

def dispatcher : Dispatcher S := {
  slots := C.slots, rows := C.rows, machine := C.machine, withMachine := C.withMachine
  machine_with := C.machine_with
  callReady := C.callees.Ready, callNext := C.callees.Next
  call_cells := fun _ _ h => C.callees.next_cells h
  call_indices := fun _ _ h => C.callees.next_indices h }

def entry (s : S) (j : Fin n) (returnPC : BitVec 64) : S :=
  CallSite.entry C.machine C.withMachine s (C.callees.family j).target returnPC

theorem entry_pc (s : S) (j : Fin n) (returnPC : BitVec 64) :
    (C.machine (C.entry s j returnPC)).pc = (C.callees.family j).target := by
  change (C.machine (C.withMachine s _)).pc = _
  rw [C.machine_with]

end RegisteredCalls

/-- A semantic cutpoint annotation. Its binary descriptor fixes the actual
JAL, while the registered summary determines its continuation (which may be
beyond the JAL return address). Only algorithm-specific enabling and joining
obligations remain; endpoint dispatch and ABI transport are shared. -/
structure AnnotatedSite {S : Type} {n : Nat} (C : RegisteredCalls S n) (Post : S → Prop) where
  callee : Fin n
  pc : BitVec 64
  returnPC : BitVec 64
  binary : CallSite C.rows pc (C.callees.family callee).target returnPC
  Precondition : S → Prop
  enabled : ∀ s, (C.machine s).pc = pc → Precondition s →
    ∃ w, (C.callees.family callee).Enabled w (C.entry s callee returnPC)
  closes : ∀ s, (C.machine s).pc = pc → Precondition s →
    ∀ w t, (C.callees.family callee).Enabled w (C.entry s callee returnPC) →
      (C.callees.family callee).Next w (C.entry s callee returnPC) t → Post t

namespace AnnotatedSite
variable {S : Type} {n : Nat} {C : RegisteredCalls S n} {Post : S → Prop}
variable (A : AnnotatedSite C Post)

def Matches (s : S) : Prop := (C.machine s).pc = A.pc ∧ A.Precondition s

theorem ready {s : S} (h : A.Matches s) : C.dispatcher.Ready s := by
  have miss : findMixed C.slots (C.machine s).pc C.rows = none := by
    rw [h.1]; exact A.binary.ordinary_miss C.slots
  simp only [Dispatcher.Ready, RegisteredCalls.dispatcher, miss]
  cases found : findCall (C.machine s).pc C.rows with
  | none => rw [h.1,A.binary.found] at found; cases found
  | some r =>
    change C.callees.Ready (C.dispatcher.callEntry s r)
    rw [A.binary.entry_eq C.dispatcher s h.1 r found]
    obtain ⟨w,enabled⟩ := A.enabled s h.1 h.2
    exact ⟨A.callee,w,C.entry_pc s A.callee A.returnPC,enabled⟩

theorem closed {s t : S} (h : A.Matches s) (r : LocatedCall (C.machine s).pc)
    (found : findCall (C.machine s).pc C.rows = some r)
    (step : C.callees.Next (C.dispatcher.callEntry s r) t) : Post t := by
  rw [A.binary.entry_eq C.dispatcher s h.1 r found] at step
  obtain ⟨w,enabled,result⟩ := C.callees.next_at A.callee
    (C.entry_pc s A.callee A.returnPC) step
  exact A.closes s h.1 h.2 w t enabled result

end AnnotatedSite

namespace RegisteredCalls
variable {S : Type} {n m : Nat} (C : RegisteredCalls S n) {Post : S → Prop}

def AtSite (sites : Fin m → AnnotatedSite C Post) (s : S) : Prop :=
  ∃ j, (sites j).Matches s

theorem atSite_ready (sites : Fin m → AnnotatedSite C Post) {s : S}
    (h : C.AtSite sites s) : C.dispatcher.Ready s := by
  obtain ⟨j,h⟩ := h
  exact (sites j).ready h

theorem atSite_closed (sites : Fin m → AnnotatedSite C Post) {s t : S}
    (h : C.AtSite sites s) (r : LocatedCall (C.machine s).pc)
    (found : findCall (C.machine s).pc C.rows = some r)
    (step : C.callees.Next (C.dispatcher.callEntry s r) t) : Post t := by
  obtain ⟨j,h⟩ := h
  exact (sites j).closed h r found step

end RegisteredCalls
end Xv6.WholeFunction
