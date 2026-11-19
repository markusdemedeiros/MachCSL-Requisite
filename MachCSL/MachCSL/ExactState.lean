import MachCSL.Lang
import Iris.Algebra.Lib.ExclAuth
import Iris.Instances.Lib.NaInvariants
import Iris.ProgramLogic.WeakestPre

/-! Exact ownership of the physical machine and its observed history. The
resource model used by instruction proofs is a separate protected invariant;
this camera records every physical field, including device task bookkeeping. -/
namespace MachCSL
open Iris Iris.BI Iris.CMRA Iris.ProgramLogic Iris.ProgramLogic.Language ExclAuth

abbrev MachineSnapshot := GState × List Obs
abbrev ExactStateRF : COFE.OFunctorPre :=
  constOF (ExclAuthR (A := stateO MachineSnapshot))

class ExactStateG (GF : BundledGFunctors) where
  elem : ElemG GF ExactStateRF
attribute [reducible, instance] ExactStateG.elem

structure ExactStateNames where
  machine : GName
  pool : NaInvPoolName

namespace ExactState
variable {GF : BundledGFunctors} [ExactStateG GF]
open ExclAuth

def auth (γ : GName) (s : MachineSnapshot) : IProp GF :=
  iOwn (E := ExactStateG.elem) γ (●E (⟨s⟩ : stateO MachineSnapshot))
def frag (γ : GName) (s : MachineSnapshot) : IProp GF :=
  iOwn (E := ExactStateG.elem) γ (◯E (⟨s⟩ : stateO MachineSnapshot))

instance (γ : GName) (s : MachineSnapshot) : Timeless (auth (GF := GF) γ s) := by
  unfold auth; infer_instance
instance (γ : GName) (s : MachineSnapshot) : Timeless (frag (GF := GF) γ s) := by
  unfold frag; infer_instance

theorem agree (γ : GName) (s t : MachineSnapshot) :
    auth (GF := GF) γ s ∗ frag γ t ⊢ ⌜s = t⌝ := by
  unfold auth frag
  iintro ⟨Ha, Hf⟩
  icombine Ha Hf gives %hv
  ipureintro
  exact DiscreteO.eqv_inj (ExclAuth.agree hv)

theorem update (γ : GName) (s t : MachineSnapshot) :
    auth (GF := GF) γ s ∗ frag γ s ⊢ |==> (auth γ t ∗ frag γ t) := by
  unfold auth frag
  apply (iOwn_update_op (E := ExactStateG.elem) (γ := γ)
    (ExclAuth.update (a := (⟨s⟩ : stateO MachineSnapshot))
      (b := (⟨s⟩ : stateO MachineSnapshot)) (a' := (⟨t⟩ : stateO MachineSnapshot)))).trans
  apply bupd_mono
  exact iOwn_op.mp

theorem alloc (s : MachineSnapshot) :
    ⊢@{IProp GF} |==> ∃ γ, auth γ s ∗ frag γ s := by
  unfold auth frag
  imod iOwn_alloc (F := ExactStateRF)
    ((●E (⟨s⟩ : stateO MachineSnapshot)) • ◯E (⟨s⟩ : stateO MachineSnapshot))
    ExclAuth.valid with ⟨%γ, Ha, Hf⟩
  imodintro
  iexists γ
  iframe Ha Hf

end ExactState
end MachCSL
