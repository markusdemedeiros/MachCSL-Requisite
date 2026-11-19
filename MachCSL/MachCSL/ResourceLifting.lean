import MachCSL.Resources
import Iris.ProgramLogic.Lifting

/-! Borrowing the rich resource model during a physical step. The non-atomic
invariant is protected by a token in the physical interpretation; borrowing it
does not reserve a mask from callbacks, so existing client invariants remain
available to the instruction rules. -/
namespace MachCSL
open Iris Iris.BI Iris.ProgramLogic Iris.Std
open Iris.ProgramLogic.Language Iris.ProgramLogic.Language.Notation

variable {hlc : HasLC} {GF : BundledGFunctors} [MachFixedGS hlc GF]

instance (E : EraGS) (σ : MState) : Timeless (eraInterp (hlc := hlc) (GF := GF) E σ) := by
  unfold eraInterp regInterpAt genHeapInterp memModelAt hartViewsAt devInterpAt
  infer_instance

instance (R : RegMapF EraGS) (g : GState) : Timeless (eraCur (hlc := hlc) (GF := GF) R g) := by
  cases hp : g.pow <;> simp only [eraCur, hp] <;> infer_instance

instance (g : GState) : Timeless (powerInterp (hlc := hlc) (GF := GF) g) := by
  unfold powerInterp genAuth startAuth diskFixedInterp
  infer_instance

instance : Timeless (resourceInvBody (hlc := hlc) (GF := GF)) := by
  unfold resourceInvBody
  infer_instance

/-- Borrow the resource model at the physical state and return it at any new
state. The interpretation's pool token enforces exclusive access. -/
theorem resourceInterp_acc (g : GState) (ns : Nat) (κs : List Obs) (nt : Nat) :
    resourceInv ∗ stateInterp g ns κs nt ⊢@{IProp GF} |={⊤}=>
      resourceInterp g ns κs nt ∗
      (∀ (g' : GState) (ns' : Nat) (κs' : List Obs) (nt' : Nat),
        resourceInterp g' ns' κs' nt' ={⊤}=∗ stateInterp g' ns' κs' nt') := by
  simp only [stateInterp_eq]
  unfold resourceInv physicalInterp
  iintro ⟨#Hinv, ⟨%h, %ht, Ha, Hpool, Hobs⟩⟩
  imod NonAtomicInvariant.inv_acc CoPset.subseteq_top CoPset.subseteq_top
    $$ Hinv Hpool with ⟨>Hbody, Hpool, Hclose⟩
  unfold resourceInvBody
  icases Hbody with ⟨%gl, %hl, Hf, Hpower, %hwf⟩
  ihave %heq := ExactState.agree $$ [$Ha $Hf]
  have hg : g = gl := congrArg Prod.fst heq
  have hh : h = hl := congrArg Prod.snd heq
  subst gl; subst hl
  imodintro
  isplitl [Hpower Hobs]
  · unfold resourceInterp obsInterp
    iframe Hpower
    iexists h
    iframe Hobs
    ipureintro; exact ⟨ht, hwf⟩
  · iintro %g' %ns' %κs' %nt' Hres
    unfold resourceInterp obsInterp
    icases Hres with ⟨Hpower, ⟨%h', %ht', %hwf', Hobs⟩⟩
    imod ExactState.update _ (g, h) (g', h') $$ [$Ha $Hf] with ⟨Ha, Hf⟩
    imod Hclose $$ [Hf Hpower Hpool] with Hpool
    · iframe Hpool
      inext
      iexists g', h'
      iframe Hf Hpower
      ipureintro; exact hwf'
    imodintro
    iexists h'
    iframe Ha Hpool Hobs
    ipureintro; exact ht'

/-- The existing instruction-rule callback, over the protected resource model,
proves a WP for the new exact physical interpretation. -/
theorem wp_lift_resource (e : Expr) :
    ⊢@{IProp GF} resourceInv -∗
    (∀ (g : GState) (ns : Nat) (κ κs : List Obs) (nt : Nat),
      resourceInterp g ns (κ ++ κs) nt ={⊤,∅}=∗
      ⌜PrimStep.Reducible (e, g)⌝ ∗
      ▷ ∀ e' g' efs, ⌜(e, g) -<κ>-> (e', g', efs)⌝ -∗ £ 1 ={∅,⊤}=∗
        resourceInterp g' (ns + 1) κs (nt + efs.length) ∗
        WP e' @ Stuckness.NotStuck; ⊤ {{ _v, True }} ∗
        [∗list] ef ∈ efs, WP ef @ Stuckness.NotStuck; ⊤ {{ _v, True }}) -∗
      WP e @ Stuckness.NotStuck; ⊤ {{ _v, True }} := by
  iintro #Hinv H
  iapply wp_lift_step rfl
  iintro %g %ns %κ %κs %nt Hphys
  imod resourceInterp_acc g ns (κ ++ κs) nt $$ [$Hinv $Hphys] with ⟨Hres, Hclose⟩
  imod H $$ %g %ns %κ %κs %nt Hres with ⟨%Hred, Hstep⟩
  imodintro
  isplit
  · ipureintro; exact Hred
  inext
  iintro %e' %g' %efs %Hstep Hcred
  imod Hstep $$ %e' %g' %efs %Hstep Hcred with ⟨Hres, Hwp, Hfork⟩
  imod Hclose $$ %g' %(ns + 1) %κs %(nt + efs.length) Hres with Hphys
  imodintro
  iframe Hphys Hwp Hfork

end MachCSL
