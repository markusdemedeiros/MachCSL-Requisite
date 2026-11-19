import Experiments.WholeFunction.KernelFull

/-! Uniform dispatch of decoded instructions and registered semantic calls.
Function clients supply a machine lens and callee contracts. All instruction
framing, JAL execution, migration and control-flow composition is shared.
-/
namespace Xv6.WholeFunction
open Iris Iris.BI Iris.ProgramLogic MachCSL

structure Dispatcher (S : Type) where
  slots : Nat
  rows : List Binary.Row
  machine : S → Stack.State
  withMachine : S → Stack.State → S
  machine_with : ∀ s m, machine (withMachine s m) = m
  callReady : S → Prop
  callNext : S → S → Prop
  call_cells : ∀ s t, callNext s t → (machine t).cells = (machine s).cells
  call_indices : ∀ s t, callNext s t →
    (machine t).ctx.sie = (machine s).ctx.sie ∧
    (machine t).ctx.proc = (machine s).ctx.proc

namespace Dispatcher
variable {S : Type} (D : Dispatcher S)

def callEntry (s : S) (r : LocatedCall (D.machine s).pc) : S :=
  D.withMachine s (jalRun r.row r.jump.imm r.jump.link (D.machine s))

def Ready (s : S) : Prop :=
  match findMixed D.slots (D.machine s).pc D.rows with
  | some r => r.action.Enabled (D.machine s)
  | none => match findCall (D.machine s).pc D.rows with
    | some r => D.callReady (D.callEntry s r)
    | none => False

inductive Edge : S → S → Prop
  | ordinary (s : S) (r : LocatedMixed (D.machine s).pc)
      (found : findMixed D.slots (D.machine s).pc D.rows = some r)
      (cpu : CPU) (t : Stack.State) (step : r.action.Next r.row.rvc cpu (D.machine s) t) :
      Edge s (D.withMachine s t)
  | call (s : S) (r : LocatedCall (D.machine s).pc)
      (notMixed : findMixed D.slots (D.machine s).pc D.rows = none)
      (found : findCall (D.machine s).pc D.rows = some r)
      (ready : D.callReady (D.callEntry s r)) (t : S)
      (step : D.callNext (D.callEntry s r) t) : Edge s t

theorem Edge.indices {s t : S} (step : D.Edge s t) :
    (D.machine t).ctx.sie = (D.machine s).ctx.sie ∧
    (D.machine t).ctx.proc = (D.machine s).ctx.proc := by
  cases step with
  | ordinary r found cpu t step =>
    rw [D.machine_with]
    cases ha : r.action with
    | reg a =>
      rw [ha] at step
      cases step
      exact ⟨a.run_sie .., a.run_proc ..⟩
    | stack a =>
      rw [ha] at step
      exact a.next_indices r.row.rvc cpu (D.machine s) t step
  | call r _ _ _ t step =>
    have h := D.call_indices _ _ step
    simpa only [callEntry, D.machine_with, jalRun, KCtx.setReg_sie, KCtx.setReg_proc] using h

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
variable [CurCtx] [KernelGeom] [KernelImage GF]

private theorem summary_mono (payload : S → IProp GF)
    (P Q : S → Prop) (s : S) (summary : CallSummary D.machine payload P s)
    (weaken : ∀ t, P t → Q t) : CallSummary D.machine payload Q s := by
  intro cpu
  iintro ⟨Hstate, Hnext⟩
  iapply summary cpu $$ [$Hstate Hnext]
  iapply wpNext_intro_pin
  iintro %cpu' %pin %t %ht Hstate
  ihave Hnext := wpNext_at _ _ _ cpu' _ pin $$ Hnext
  iapply Hnext $$ %t %(weaken t ht) Hstate

/-- A successful decoder lookup determines every instruction action. Calls
are fused with their actual JAL and a proved semantic summary. -/
noncomputable def compile (payload : S → IProp GF)
    (frame : ∀ s m, payload s ⊢ payload (D.withMachine s m))
    (callee : ∀ s, D.callReady s → CalleeSpec D.machine payload (D.callNext s) s)
    (s : S) (ready : D.Ready s) : FullPlan D.machine payload (D.Edge) s := by
  cases hm : findMixed D.slots (D.machine s).pc D.rows with
  | some r =>
    have enabled : r.action.Enabled (D.machine s) := by simpa only [Ready, hm] using ready
    exact .instruction ⟨r.row, r.action, (fun _ t => D.withMachine s t), r.address,
      r.decoded, enabled, (fun _ t _ => D.machine_with s t),
      (fun _ t _ => frame s t), (fun cpu t hn => Edge.ordinary s r hm cpu t hn)⟩
  | none =>
    cases hc : findCall (D.machine s).pc D.rows with
    | none => exact False.elim (by simpa only [Ready, hm, hc] using ready)
    | some r =>
      have enabled : D.callReady (D.callEntry s r) := by
        simpa only [Ready, hm, hc] using ready
      have summary := summary_from_spec D.machine payload
        (D.callNext (D.callEntry s r)) (D.callEntry s r) (callee _ enabled)
        (fun t hn => D.call_cells _ t hn)
      have lifted := summary_mono D payload (D.callNext (D.callEntry s r))
        (D.Edge s) (D.callEntry s r) summary (fun t hn => Edge.call s r hm hc enabled t hn)
      exact .call (CallPlan.from_lookup D.machine payload (D.Edge) s (D.callEntry s r) r
        (D.machine_with s _) (frame s _) lifted)

theorem wp_body (payload : S → IProp GF)
    (frame : ∀ s m, payload s ⊢ payload (D.withMachine s m))
    (callee : ∀ s, D.callReady s → CalleeSpec D.machine payload (D.callNext s) s)
    (sie : Bool) (proc : BitVec 64) (good exit : S → Prop)
    (closed : ∀ s t, good s → ¬ exit s → D.Edge s t → good t)
    (ready : ∀ s, good s → ¬ exit s → D.Ready s)
    (indices : ∀ s, good s → (D.machine s).ctx.sie = sie ∧ (D.machine s).ctx.proc = proc)
    (cpu : CPU) (s : S) (entry : good s) :
    fullOwn D.machine payload cpu s ∗
    wpNext sie proc cpu (fun cpu' => iprop(
      ∀ t, ⌜good t⌝ -∗ ⌜exit t⌝ -∗ fullOwn D.machine payload cpu' t -∗ wpLoop cpu'))
      ⊢ wpLoop cpu :=
  wp_full D.machine payload sie proc good exit (D.Edge) ⟨closed⟩ indices
    (fun t hg hc => D.compile payload frame callee t (ready t hg hc)) cpu s entry

end Dispatcher
end Xv6.WholeFunction
