import MachCSL.TsoMem
import Iris.Algebra.Functions
import Iris.BI.Lib.MonoNat

/-! Symbolic monotone coherence maps. One ghost name represents all addresses;
no address enumeration is needed. The authority follows the physical map and
persistent lower bounds remember what a hart has already read. -/
namespace MachCSL
open Iris Iris.BI Iris.CMRA

abbrev CoherenceRF : COFE.OFunctorPre := constOF (PAddr → MonoNat)

class CoherenceG (GF : BundledGFunctors) where
  elem : ElemG GF CoherenceRF

attribute [reducible, instance] CoherenceG.elem

/-- A permitted plain read never lowers a coherence floor. -/
theorem HRead.afterLoad_coh_mono (hr : HRead) (pa : PAddr) (n tvn : Nat)
    (h : hr.cohOk pa n tvn) (a : PAddr) : hr.coh a ≤ (hr.afterLoad pa n tvn).coh a := by
  simp only [HRead.afterLoad]
  split
  · rename_i ha
    obtain ⟨j, hj, rfl⟩ := ha
    exact h j hj
  · exact Nat.le_refl _

namespace Coherence
variable {GF : BundledGFunctors} [CoherenceG GF]

def auth (γ : GName) (f : PAddr → Nat) : IProp GF :=
  iOwn (E := CoherenceG.elem) γ (fun a => MonoNat.auth (.own 1) (.ofNat (f a)))

def lb (γ : GName) (f : PAddr → Nat) : IProp GF :=
  iOwn (E := CoherenceG.elem) γ (fun a => MonoNat.lb (.ofNat (f a)))

instance (γ : GName) (f : PAddr → Nat) : Timeless (auth (GF := GF) γ f) := by
  unfold auth; infer_instance

instance (γ : GName) (f : PAddr → Nat) : Timeless (lb (GF := GF) γ f) := by
  unfold lb; infer_instance

instance (γ : GName) (f : PAddr → Nat) : Persistent (lb (GF := GF) γ f) := by
  letI : CMRA.CoreId (fun a => MonoNat.lb (.ofNat (f a))) :=
    CMRA.coreId_iff_core_eqv_self.mpr (funext fun a => by
      change CMRA.core (MonoNat.lb (.ofNat (f a))) = _
      exact CMRA.core_eqv_self _)
  unfold lb; infer_instance

theorem valid (γ : GName) (f g : PAddr → Nat) :
    auth (GF := GF) γ f ∗ lb γ g ⊢ ⌜∀ a, g a ≤ f a⌝ := by
  unfold auth lb
  iintro ⟨Ha, Hl⟩
  ihave %hv := iOwn_cmraValid_op $$ [$Ha $Hl]
  ipureintro
  intro a
  exact (MonoNat.both_valid (.ofNat (f a)) (.ofNat (g a))).mp (hv a)

theorem get_lb (γ : GName) (f : PAddr → Nat) :
    auth (GF := GF) γ f ⊢ lb γ f := by
  unfold auth lb
  iintro H
  iapply iOwn_mono $$ H
  exact DiscreteFun.inc_iff.mpr (fun a => MonoNat.included (.own 1) (.ofNat (f a)))

theorem weaken (γ : GName) (f g : PAddr → Nat) (h : ∀ a, g a ≤ f a) :
    lb (GF := GF) γ f ⊢ lb γ g := by
  unfold lb
  iintro H
  iapply iOwn_mono $$ H
  exact DiscreteFun.inc_iff.mpr (fun a => MonoNat.lb_mono _ _ (h a))

theorem alloc (f : PAddr → Nat) :
    ⊢@{IProp GF} |==> ∃ γ, auth γ f ∗ lb γ f := by
  imod iOwn_alloc (F := CoherenceRF) (fun a => MonoNat.auth (.own 1) (.ofNat (f a)))
    (fun a => MonoNat.auth_valid (.ofNat (f a))) with ⟨%γ, H⟩
  imodintro
  iexists γ
  ihave #Hl : lb γ f $$ [H]
  · iapply get_lb
    unfold auth
    iexact H
  unfold auth
  iframe H Hl

theorem update (γ : GName) (f g : PAddr → Nat) (h : ∀ a, f a ≤ g a) :
    auth (GF := GF) γ f ⊢ |==> auth γ g := by
  unfold auth
  iintro H
  iapply iOwn_update $$ H
  exact discreteFun_update (fun a => MonoNat.update (.ofNat (g a)) (h a))

end Coherence
end MachCSL
