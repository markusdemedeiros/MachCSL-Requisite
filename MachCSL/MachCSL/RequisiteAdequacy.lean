import MachCSL.RequisiteAllocation
import MachCSL.Adequacy

namespace MachCSL.Requisite
open Iris Iris.BI Iris.ProgramLogic

variable {hlc : HasLC} {GF : BundledGFunctors}

/-- An inert resource-model record. The physical interpretation only uses its
camera capacities and the names replaced by `state_alloc`. No resource-model
invariant or client specification is assumed. -/
@[reducible] def initialFixedGS [MachGpreS hlc GF] (Hinv : InvGS_gen hlc GF) :
    MachFixedGS hlc GF :=
  bootFixedGS Hinv 0 0 0 0 0 0 iprop(True)
    (fun _ => iprop(True)) (fun _ P => P) 0 [] iprop(True) 0
    rxTagTriv (fun _ => inferInstance) (fun _ => inferInstance)
    killCredTriv inferInstance inferInstance consResTriv (fun _ _ _ => inferInstance)
    wildNone (fun _ => inferInstance) (fun _ => inferInstance)
    wildNone (fun _ => inferInstance) (fun _ => inferInstance)
    (fun _ _ => True) (fun _ => iprop(True)) (fun _ _ => iprop(True)) iprop(True)
    (fun _ _ => iprop(True)) (fun _ _ => inferInstance) (fun _ => iprop(True))
    (fun _ _ => iprop(True)) (fun _ _ => inferInstance)

/-- Adequacy with precisely the ownership predicate used for requisiteness. -/
theorem wp_adequacy [MachGpreS hlc GF]
    (e : Expr) (g : GState) (φ : Val → Prop)
    (Hwp : ∀ [MachFixedGS hlc GF],
      ownState g ⊢@{IProp GF} WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }}) :
    adequate .NotStuck e g (fun v _ => φ v) := by
  apply wp_adequacy_gen (hlc := hlc) (GF := GF) .NotStuck e g φ
  intro Hinv κs
  let F := initialFixedGS (GF := GF) Hinv
  letI : MachFixedGS hlc GF := F
  imod state_alloc g 0 κs 0 with ⟨%N, Hstate, Hown⟩
  letI := F.withPhysicalNames N κs
  ihave Hwp := Hwp $$ Hown
  imodintro
  iexists (fun g κs => physicalInterp (GF := GF) g κs), (fun _ : Val => iprop(True))
  iframe Hstate Hwp

/-- Safety and the semantic MachCSL WP coincide, using a jointly allocatable
state ownership predicate. Both directions use the same state interpretation. -/
theorem adequate_iff_wp [MachGpreS hlc GF] [GhostMapG GF Nat Expr RegMapF]
    (e : Expr) (g : GState) (φ : Val → Prop) :
    adequate .NotStuck e g (fun v _ => φ v) ↔
      ∀ [MachFixedGS hlc GF],
        ownState g ⊢@{IProp GF} WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }} := by
  constructor
  · intro hs F
    exact wp_requisiteness e g φ hs
  · exact wp_adequacy e g φ

end MachCSL.Requisite
