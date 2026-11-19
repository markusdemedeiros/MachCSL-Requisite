import MachCSL.ResourceLifting

/-! Spatial continuation requisiteness over an abstract footprint.

The exact-state requisite instance cannot coexist with the production resource
invariant. This theorem uses the same guarded simulation argument with a local
abstract state instead. It leaves the state interpretation unchanged and borrows
the resource model through `wp_lift_resource`.

There are two separate obligations: a pure operational region certificate, and
a resource simulation proved once for the chosen abstract machine. The latter
must realize every actual primitive transition from every compatible physical
state, updating ghost protocols as well as bytes. It has no WP in its type.
Neither condition is supplied merely by a final-state relation or a binary hash.
-/
namespace MachCSL.WholeFunction
open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProgramLogic.Language
open Iris.ProgramLogic.Language.Notation

variable {A : Type}

/-- The VCG's pure obligation, separated from all Iris resource obligations. -/
structure FootprintRegion (enabled : Expr → A → Prop)
    (step : Expr → A → Expr → A → Prop) (good cut : Expr → A → Prop) : Prop where
  safe : ∀ e a, good e a → ¬ cut e a → enabled e a
  closed : ∀ e a e' a', good e a → ¬ cut e a → step e a e' a' → good e' a'

variable {hlc : HasLC} {GF : BundledGFunctors} [MachFixedGS hlc GF]

/-- Once-for-model resource refinement of the abstract transition relation.
The current physical state is arbitrary: all facts about it must be obtained
from `resourceInterp` and the owned footprint. Universal primitive successors
account for machine nondeterminism. Other threads' framed resources cannot be
changed illegally because these are Iris frame-preserving updates.

This interface excludes forks. A backend with spawning must instead provide
child-thread contracts. Calls and interrupt/migration paths must be refined by
this relation or discharged through separate sound composition theorems; an
abstract summary alone does not establish this obligation. -/
structure FootprintSimulation (own : A → IProp GF) (enabled : Expr → A → Prop)
    (step : Expr → A → Expr → A → Prop) where
  update (e : Expr) (a : A) (ready : enabled e a)
      (g : GState) (ns : Nat) (κ κs : List Obs) (nt : Nat) :
    resourceInterp g ns (κ ++ κs) nt ∗ own a ⊢ |={⊤,∅}=>
      ⌜PrimStep.Reducible (e, g)⌝ ∗
      ▷ ∀ e' g' forks, ⌜(e, g) -<κ>-> (e', g', forks)⌝ -∗ £ 1 ={∅,⊤}=∗
        ∃ a', ⌜forks = [] ∧ step e a e' a'⌝ ∗
          resourceInterp g' (ns + 1) κs (nt + forks.length) ∗ own a'

/-- A verified abstract region and its once-for-model spatial simulation imply
the actual MachCSL WP. The exit continuation receives the evolved footprint
and unchanged frame. No exact-state fragment is required. -/
theorem wp_footprint_region {own : A → IProp GF} {enabled : Expr → A → Prop}
    {step : Expr → A → Expr → A → Prop} {good cut : Expr → A → Prop}
    (simulation : FootprintSimulation own enabled step)
    (region : FootprintRegion enabled step good cut) (frame : IProp GF)
    (resume : ∀ e a, good e a → cut e a →
      own a ∗ frame ⊢ WP e @ Stuckness.NotStuck; ⊤ {{ _v, True }})
    (e : Expr) (a : A) (entry : good e a) :
    resourceInv -∗ own a ∗ frame -∗
      WP e @ Stuckness.NotStuck; ⊤ {{ _v, True }} := by
  classical
  iintro #Hworld
  iloeb as IH generalizing %e %a %entry
  iintro ⟨Hown, Hframe⟩
  by_cases hcut : cut e a
  · iapply resume e a entry hcut $$ [$Hown $Hframe]
  · iapply wp_lift_resource e $$ Hworld
    iintro %g %ns %κ %κs %nt Hres
    imod simulation.update e a (region.safe e a entry hcut) g ns κ κs nt
      $$ [$Hres $Hown] with ⟨%Hred, Hstep⟩
    imodintro
    isplit
    · ipureintro; exact Hred
    inext
    iintro %e' %g' %forks %Hprim Hcredit
    imod Hstep $$ %e' %g' %forks %Hprim Hcredit with ⟨%a', %Habstract, Hres, Hown⟩
    obtain ⟨rfl, hstep⟩ := Habstract
    imodintro
    iframe Hres
    isplitl [Hown Hframe]
    · iapply IH $$ %e' %a' %(region.closed e a e' a' entry hcut hstep)
        [$Hown $Hframe]
    · exact BigSepL.bigSepL_nil_intro

/-- Linear continuation form: caller resources in the continuation need not
be persistent. It is consumed only when an operational cutpoint is reached. -/
theorem wp_footprint_region_cps {own : A → IProp GF} {enabled : Expr → A → Prop}
    {step : Expr → A → Expr → A → Prop} {good cut : Expr → A → Prop}
    (simulation : FootprintSimulation own enabled step)
    (region : FootprintRegion enabled step good cut) (frame : IProp GF)
    (e : Expr) (a : A) (entry : good e a) :
    resourceInv -∗
    (∀ e' a', ⌜good e' a'⌝ -∗ ⌜cut e' a'⌝ -∗ own a' ∗ frame -∗
      WP e' @ Stuckness.NotStuck; ⊤ {{ _v, True }}) -∗
    own a ∗ frame -∗ WP e @ Stuckness.NotStuck; ⊤ {{ _v, True }} := by
  let K : IProp GF := iprop(∀ e' a', ⌜good e' a'⌝ -∗ ⌜cut e' a'⌝ -∗
      own a' ∗ frame -∗ WP e' @ Stuckness.NotStuck; ⊤ {{ _v, True }})
  have hresume (e' : Expr) (a' : A) (hg : good e' a') (hc : cut e' a') :
      own a' ∗ (frame ∗ K) ⊢ WP e' @ Stuckness.NotStuck; ⊤ {{ _v, True }} := by
    iintro ⟨Hown, Hframe, HK⟩
    iapply HK $$ %e' %a' %hg %hc [$Hown $Hframe]
  iintro #Hworld HK ⟨Hown, Hframe⟩
  iapply wp_footprint_region simulation region (iprop(frame ∗ K)) hresume e a entry
    $$ Hworld [$Hown $Hframe $HK]

end MachCSL.WholeFunction

open Classical
/-- info: 'MachCSL.WholeFunction.wp_footprint_region_cps' depends on axioms: [propext, choice, Quot.sound] -/
#guard_msgs in
#print axioms MachCSL.WholeFunction.wp_footprint_region_cps
