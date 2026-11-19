import MachCSL.Requisiteness

namespace MachCSL
open Iris Iris.BI Iris.ProgramLogic

/-- Names used by the physical interpretation; the other resource-model names
are irrelevant to allocation of an arbitrary operational state. -/
structure PhysicalNames where
  exact : ExactStateNames
  obs : GName
  hist : GName

@[reducible] def MachFixedGS.withPhysicalNames {hlc : HasLC} {GF : BundledGFunctors}
    (F : MachFixedGS hlc GF) (N : PhysicalNames) (T : List Obs) : MachFixedGS hlc GF :=
  { F with exactNames := N.exact, obsName := N.obs, obsHist := N.hist, obsTotal := T }

namespace Requisite
variable {hlc : HasLC} {GF : BundledGFunctors} [F : MachFixedGS hlc GF]

/-- Joint allocation rules out a vacuous ownership precondition. Every machine
state is supported, including states not reachable from the fixed boot image. -/
theorem state_alloc (g : GState) (ns : Nat) (κs : List Obs) (nt : Nat) :
    ⊢@{IProp GF} |==> ∃ N : PhysicalNames,
      letI := F.withPhysicalNames N κs
      iprop(stateInterp g ns κs nt ∗ ownState g) := by
  imod ExactState.alloc (g, ([] : List Obs)) with ⟨%γmachine, Hmachine, Hlocal⟩
  imod NonAtomicInvariant.alloc (GF := GF) with ⟨%γpool, Hpool⟩
  imod ghost_var_alloc (GF := GF) ([] : List Obs) with ⟨%γobs, Hobs⟩
  have hsplit := (ghost_var_fractional (GF := GF) γobs ([] : List Obs)).fractional
    (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at hsplit
  icases hsplit.1 $$ Hobs with ⟨HobsA, HobsF⟩
  imod MonoList.own_alloc (GF := GF) ([] : List Obs) with ⟨%γhist, Hhist, _⟩
  imodintro
  iexists (⟨⟨γmachine, γpool⟩, γobs, γhist⟩ : PhysicalNames)
  simp only [stateInterp_eq]
  unfold physicalInterp ownState obsAuth obsHalf obsFrag obsHistAuth
  isplitl [Hmachine Hpool HobsA Hhist]
  · iexists ([] : List Obs)
    iframe Hmachine Hpool HobsA Hhist
    ipureintro; rfl
  · iexists ([] : List Obs)
    iframe Hlocal HobsF

/-- The complete initialization converse: operational safety yields a jointly
allocated physical interpretation and the actual MachCSL WP. -/
theorem wp_alloc_requisiteness [GhostMapG GF Nat Expr RegMapF]
    (e : Expr) (g : GState) (φ : Val → Prop)
    (hsafe : adequate .NotStuck e g (fun v _ => φ v)) (κs : List Obs) :
    ⊢@{IProp GF} |={⊤}=> ∃ N : PhysicalNames,
      letI := F.withPhysicalNames N κs
      iprop(stateInterp g 0 κs 0 ∗ WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }}) := by
  imod state_alloc g 0 κs 0 with ⟨%N, Hstate, Hown⟩
  letI := F.withPhysicalNames N κs
  imodintro
  iexists N
  iframe Hstate
  iapply wp_requisiteness e g φ hsafe $$ Hown

end Requisite
end MachCSL
