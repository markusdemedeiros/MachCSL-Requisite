import MachCSL.Requisiteness
import MachCSL.ResourceLifting

/-! A checked obstruction to treating exact-state requisiteness as an importer
for existing spatial xv6 proofs. The resource invariant and exact-state owner
both require the SAME exclusive fragment. They cannot be active together.
This concerns this particular representation, not spatial requisiteness in
general: a different local simulation may own just a separated footprint. -/
namespace MachCSL.WholeFunction
open Iris Iris.BI Iris.Std Iris.ProgramLogic

variable {hlc : HasLC} {GF : BundledGFunctors} [MachFixedGS hlc GF]

theorem exact_owner_resource_body_false (g : GState) :
    Requisite.ownState g ∗ resourceInvBody ⊢@{IProp GF} False := by
  unfold Requisite.ownState resourceInvBody ExactState.frag
  iintro ⟨⟨%h, Hf, _⟩, ⟨%g', %h', Hf', _, _⟩⟩
  icombine Hf Hf' gives %hv
  ipureintro
  exact ExclAuth.frag_op_valid.mp hv

/-- At a physical proof step, the production resource invariant cannot be
combined with the exact owner used by the requisite theorem. Opening the
invariant exhibits two exclusive fragments; this is a resource conflict, not
a missing automation lemma. -/
theorem exact_owner_resource_world_false (g s : GState) (ns : Nat)
    (κs : List Obs) (nt : Nat) :
    Requisite.ownState g ∗ resourceInv ∗ stateInterp s ns κs nt
      ⊢@{IProp GF} |={⊤}=> False := by
  simp only [stateInterp_eq]
  unfold resourceInv physicalInterp
  iintro ⟨Hown, #Hinv, ⟨%h, %ht, Ha, Hpool, Hobs⟩⟩
  imod NonAtomicInvariant.inv_acc CoPset.subseteq_top CoPset.subseteq_top
    $$ Hinv Hpool with ⟨>Hbody, Hpool, Hclose⟩
  ihave Hfalse := exact_owner_resource_body_false g $$ [$Hown $Hbody]
  iexact Hfalse

end MachCSL.WholeFunction

open Classical
/-- info: 'MachCSL.WholeFunction.exact_owner_resource_world_false' depends on axioms: [propext, choice, Quot.sound] -/
#guard_msgs in
#print axioms MachCSL.WholeFunction.exact_owner_resource_world_false
