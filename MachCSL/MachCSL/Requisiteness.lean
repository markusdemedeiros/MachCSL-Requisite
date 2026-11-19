import MachCSL.Resources
import MachCSL.RequisiteFramework

/-! Semantic requisiteness for MachCSL's exact physical state interpretation.
The local state includes the entire machine and an existential past history;
the shared thread-pool invariant handles arbitrary forks and schedules. -/
namespace MachCSL
open Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.Language Iris.Std
open Iris.ProgramLogic.Language.Notation

namespace Requisite
variable {hlc : HasLC} {GF : BundledGFunctors} [MachFixedGS hlc GF]

/-- Full ownership of a physical snapshot and the client's history half. -/
def ownState (g : GState) : IProp GF := iprop%
  ∃ h : List Obs,
    ExactState.frag (MachFixedGS.exactNames (hlc := hlc) (GF := GF)).machine (g, h) ∗
    obsFrag h

instance (g : GState) : Timeless (ownState (hlc := hlc) (GF := GF) g) := by
  unfold ownState; infer_instance

/-- Exact snapshots match every primitive step, including observations and forks. -/
instance stateSimulation : RequisiteFramework.StateSimulation (Expr := Expr)
    (ownState (hlc := hlc) (GF := GF)) where
  timeless _ := inferInstance
  fork_post v := nomatch v
  update e g gl ns κ κs nt hred := by
    simp only [stateInterp_eq]
    unfold physicalInterp ownState
    iintro ⟨⟨%h, %ht, Ha, Hpool, Hobs⟩, ⟨%hl, Hf, Hobsf⟩⟩
    ihave %heq := ExactState.agree $$ [$Ha $Hf]
    have hg : g = gl := congrArg Prod.fst heq
    have hh : h = hl := congrArg Prod.snd heq
    subst gl; subst hl
    imodintro
    isplit
    · ipureintro; exact hred
    iintro %e' %g' %efs %hstep
    imod ExactState.update _ (g, h) (g', h ++ κ) $$ [$Ha $Hf] with ⟨Ha, Hf⟩
    imod obsUpdate h (h ++ κ) (by exact ⟨κ, rfl⟩) $$ [$Hobs $Hobsf] with ⟨Hobs, Hobsf⟩
    imodintro
    iexists g'
    isplit
    · ipureintro; exact hstep
    isplitl [Ha Hpool Hobs]
    · iexists (h ++ κ)
      iframe Ha Hpool Hobs
      ipureintro
      simpa only [List.append_assoc] using ht
    · iexists (h ++ κ)
      iframe Hf Hobsf

/-- Operational adequacy implies the actual MachCSL weakest precondition.
No boot, memory well-formedness, no-fork, or device-runtime assumption is used. -/
theorem wp_requisiteness [GhostMapG GF Nat Expr RegMapF]
    (e : Expr) (g : GState) (φ : Val → Prop)
    (hsafe : adequate .NotStuck e g (fun v _ => φ v)) :
    ownState g ⊢@{IProp GF} WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }} := by
  iintro Hstate
  iapply fupd_wp
  imod (ghost_map_alloc_empty (GF := GF) (K := Nat) (V := Expr) (H := RegMapF))
    with ⟨%γ, Htp⟩
  letI : TpinvGS GF Expr RegMapF := ⟨γ⟩
  imodintro
  iapply RequisiteFramework.wp_requisiteness
    (ownState := ownState (hlc := hlc) (GF := GF)) e g φ hsafe $$ [Htp] Hstate
  unfold tpInvIni
  iexact Htp

end Requisite
end MachCSL
