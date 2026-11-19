import MachCSL.Requisiteness

/-!
Continuation requisiteness for an operational region. Unlike ordinary
adequacy, the certificate stops at a function's return PC and hands its
spatial state to a continuation. It does not pretend MachCSL has values.

This is an exact-state boundary, not an importer for xv6's resource model:
that model stores the exclusive exact-state fragment inside `resourceInv`.
To instantiate the generic theorem with footprint ownership one must prove
a corresponding `StateSimulation`, including every interfering transition.
-/
namespace MachCSL.WholeFunction
open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProgramLogic.Language
open Iris.ProgramLogic.Language.Notation

section Generic
variable {E S O V : Type} [Language E S O V]

/-- A region need not terminate, but every execution that has not reached its
cutpoint must remain safe and inside the region. All nondeterministic steps
are quantified. Forks require a separate thread-pool contract and are excluded
here, rather than silently discarded. -/
structure Region (good cut : E → S → Prop) : Prop where
  nonvalue : ∀ e s, good e s → ¬ cut e s → ToVal.toVal e = none
  safe : ∀ e s, good e s → ¬ cut e s → PrimStep.Reducible (e, s)
  closed : ∀ e s κ e' s' forks, good e s → ¬ cut e s →
    (e, s) -<κ>-> (e', s', forks) → forks = [] ∧ good e' s'

variable {GF : BundledGFunctors} {hlc : HasLC} [IrisGS_gen hlc E GF]
variable {own : S → IProp GF} [SS : RequisiteFramework.StateSimulation (Expr := E) own]

/-- Requisiteness with a spatial continuation at an arbitrary operational
cutpoint. The frame survives unchanged; the returned state owner may differ
from the entry owner. The cutpoint is not a language value or a fake return.
No induction over instruction syntax or loop bodies is required here. -/
theorem wp_region {good cut : E → S → Prop} (region : Region good cut)
    (frame : IProp GF) (post : V → IProp GF)
    (resume : ∀ e s, good e s → cut e s →
      own s ∗ frame ⊢ WP e @ Stuckness.NotStuck; ⊤ {{ post }})
    (e : E) (s : S) (entry : good e s) :
    own s ∗ frame ⊢ WP e @ Stuckness.NotStuck; ⊤ {{ post }} := by
  classical
  iloeb as IH generalizing %e %s %entry
  iintro ⟨Hlocal, Hframe⟩
  by_cases hcut : cut e s
  · iapply resume e s entry hcut $$ [$Hlocal $Hframe]
  · iapply wp_lift_step_fupd (region.nonvalue e s entry hcut)
    iintro %sp %ns %κ %κs %nt Hphys
    imod fupd_mask_subseteq (E2 := ∅) Std.LawfulSet.empty_subset with Hmask
    imod SS.update e sp s ns κ κs nt (region.safe e s entry hcut)
      $$ [$Hphys $Hlocal] with ⟨%Hred, Hstep⟩
    imodintro
    isplitr
    · ipureintro; exact Hred
    iintro %e' %sp' %forks %Hprim _ !> !>
    imod Hstep $$ %e' %sp' %forks %Hprim with ⟨%s', %HlocalStep, Hphys, Hlocal⟩
    obtain ⟨rfl, hgood⟩ := region.closed e s κ e' s' forks entry hcut HlocalStep
    imod Hmask with -
    imodintro
    iframe Hphys
    isplitl [Hlocal Hframe]
    · iapply IH $$ %e' %s' %hgood [$Hlocal $Hframe]
    · iapply BigSepL.bigSepL_nil.mpr
      itrivial

/-- The continuation is linear: it may own a caller's resources and is only
consumed at a cutpoint. It need not be persistent or provable from nothing. -/
theorem wp_region_cps {good cut : E → S → Prop} (region : Region good cut)
    (frame : IProp GF) (post : V → IProp GF)
    (e : E) (s : S) (entry : good e s) :
    (∀ e' s', ⌜good e' s'⌝ -∗ ⌜cut e' s'⌝ -∗
      own s' ∗ frame -∗ WP e' @ Stuckness.NotStuck; ⊤ {{ post }}) -∗
    own s ∗ frame -∗ WP e @ Stuckness.NotStuck; ⊤ {{ post }} := by
  let K : IProp GF := iprop(∀ e' s', ⌜good e' s'⌝ -∗ ⌜cut e' s'⌝ -∗
      own s' ∗ frame -∗ WP e' @ Stuckness.NotStuck; ⊤ {{ post }})
  have hresume (e' : E) (s' : S) (hg : good e' s') (hc : cut e' s') :
      own s' ∗ (frame ∗ K) ⊢ WP e' @ Stuckness.NotStuck; ⊤ {{ post }} := by
    iintro ⟨Hown, Hframe, HK⟩
    iapply HK $$ %e' %s' %hg %hc [$Hown $Hframe]
  iintro HK ⟨Hown, Hframe⟩
  iapply wp_region region (iprop(frame ∗ K)) post hresume e s entry
    $$ [$Hown $Hframe $HK]

end Generic

section Machine
variable {hlc : HasLC} {GF : BundledGFunctors} [MachFixedGS hlc GF]

/-- Actual MachCSL WP obtained from an operational certificate and an exact
state continuation. `True` is the only relevant value postcondition because
MachCSL's `Val` is empty; return information resides in `cut` and `resume`. -/
theorem wp_exact_region {good cut : Expr → GState → Prop}
    (region : Region good cut) (frame : IProp GF)
    (resume : ∀ e g, good e g → cut e g →
      Requisite.ownState g ∗ frame ⊢@{IProp GF}
        WP e @ Stuckness.NotStuck; ⊤ {{ _v, True }})
    (e : Expr) (g : GState) (entry : good e g) :
    Requisite.ownState g ∗ frame ⊢@{IProp GF}
      WP e @ Stuckness.NotStuck; ⊤ {{ _v, True }} :=
  wp_region region frame (fun _ => iprop(True)) resume e g entry

end Machine
end MachCSL.WholeFunction

open Classical
/-- info: 'MachCSL.WholeFunction.wp_region_cps' depends on axioms: [propext, choice, Quot.sound] -/
#guard_msgs in
#print axioms MachCSL.WholeFunction.wp_region_cps

/-- info: 'MachCSL.WholeFunction.wp_exact_region' depends on axioms: [propext, choice, Quot.sound] -/
#guard_msgs in
#print axioms MachCSL.WholeFunction.wp_exact_region
