/-
SPDX-License-Identifier: BSD-3-Clause
Copyright (C) 2026, Johannes Hostert, Zichen Zhang, Puming Liu,
Simon Gregersen, Ralf Jung, and Joseph Tassarotti.

Adapted from the Rocq development accompanying
"Completeness of Iris-Based Program Logics" (2026).
https://gitlab.mpi-sws.org/johannes/iris-completeness
Source revision: 0a0dd8ae249069eb2b4b78774649d0cd0b5c7b0c.
See LICENSE.iris-completeness for the license and disclaimer.
-/
import Req.Requisiteness
import Iris.HeapLang.PrimitiveLaws
import Iris.BI.BigOp.BigSepSet

/-! HeapLang's semantic state simulation. Ownership includes tombstones and
existentially hidden prophecy predictions; no primitive WP rules are assumed. -/
namespace Req.HeapLang
open Iris Iris.BI Iris.Std Iris.HeapLang Iris.ProgramLogic
open Iris.ProgramLogic.Language Iris.ProgramLogic.Language.Notation

variable {GF : BundledGFunctors} {hlc : HasLC} [HeapLangGS hlc GF]

abbrev ownHeap (h : HeapF (Option Val)) : IProp GF :=
  bigSepM (fun l ov => pointsTo l (.own 1) ov) h

abbrev ownProphs (ps : Std.ExtTreeSet ProphId) : IProp GF :=
  iprop([∗set] p ∈ ps, ∃ vs, proph p vs)

/-- Full internal ownership of a local state, including deallocated cells. -/
abbrev ownState (σ : State) : IProp GF := iprop(ownHeap σ.heap ∗ ownProphs σ.usedProphId)

instance (σ : State) : Timeless (ownState (GF := GF) σ) := by infer_instance

/-- Inclusion preserves both live values and tombstones. -/
def HeapSub (small large : HeapF (Option Val)) : Prop :=
  ∀ l ov, get? small l = some ov → get? large l = some ov

theorem heap_agree (h hl : HeapF (Option Val)) :
    genHeapInterp (GF := GF) h ∗ ownHeap hl ⊢ ⌜HeapSub hl h⌝ := by
  iintro ⟨Hauth, Hlocal⟩
  unfold HeapSub
  iapply pure_forall.mpr
  iintro %l
  iapply pure_forall.mpr
  iintro %ov
  iapply pure_imp.mpr
  iintro %Hlookup
  ihave Hpt := BigSepM.bigSepM_lookup Hlookup $$ Hlocal
  icases genHeap_valid $$ [$Hauth $Hpt] with >%Hvalid
  ipureintro; exact Hvalid

theorem prophs_agree (κ : List Observation) (ps psl : Std.ExtTreeSet ProphId) :
    prophMapInterp (GF := GF) κ ps ∗ ownProphs psl ⊢ ⌜psl ⊆ ps⌝ := by
  iintro ⟨Hauth, Hlocal⟩
  iapply pure_forall.mpr
  iintro %p
  iapply pure_imp.mpr
  iintro %Hmem
  icases BigSepS.bigSepS_elem_of Hmem $$ Hlocal with ⟨%vs, Hp⟩
  ihave ⟨%Hp, _⟩ := ProphMap.agree κ ps p vs $$ [$Hauth $Hp]
  ipureintro; exact Hp

theorem state_agree (σ σl : State) (ns : Nat) (κ : List Observation) (nt : Nat) :
    stateInterp σ ns κ nt ∗ ownState (GF := GF) σl ⊢
      ⌜HeapSub σl.heap σ.heap ∧ σl.usedProphId ⊆ σ.usedProphId⌝ := by
  simp only [stateInterp]
  iintro ⟨⟨Hheap, Hproph⟩, Hheapl, Hprophl⟩
  ihave %Hh := heap_agree $$ [$Hheap $Hheapl]
  ihave %Hp := prophs_agree $$ [$Hproph $Hprophl]
  ipureintro; exact ⟨Hh, Hp⟩

/-- Base reducibility is preserved when the physical state extends the local state. -/
theorem base_reducible_mono {e : Exp} {σl σ : State}
    (hh : HeapSub σl.heap σ.heap) (hp : σl.usedProphId ⊆ σ.usedProphId)
    (hr : BaseStep.Reducible (e, σl)) : BaseStep.Reducible (e, σ) := by
  obtain ⟨κ, e', σl', efs, hs⟩ := hr
  induction hs generalizing σ with
  | allocNS n v σl l hn hf => exact ⟨_, _, _, _, alloc_fresh v n σ hn⟩
  | newProphS σl p hf =>
    obtain ⟨p', hs⟩ := new_proph_id_fresh σ
    exact ⟨_, _, _, _, hs⟩
  | freeS l v σl hl => exact ⟨_, _, _, _, .freeS l v σ (hh _ _ hl)⟩
  | loadS l v σl hl => exact ⟨_, _, _, _, .loadS l v σ (hh _ _ hl)⟩
  | storeS l v w σl hl => exact ⟨_, _, _, _, .storeS l v w σ (hh _ _ hl)⟩
  | xchgS l v w σl hl => exact ⟨_, _, _, _, .xchgS l v w σ (hh _ _ hl)⟩
  | cmpXchgS l v1 v2 vl σl b hl hc hb =>
    exact ⟨_, _, _, _, .cmpXchgS l v1 v2 vl σ b (hh _ _ hl) hc hb⟩
  | faaS l i1 i2 σl hl => exact ⟨_, _, _, _, .faaS l i1 i2 σ (hh _ _ hl)⟩
  | resolveS p v e σl w σl' κ ts hs hmem ih =>
    obtain ⟨κ', e', σ', efs, hs'⟩ := ih hh hp
    have hv : ∃ v', e' = .val v' := by
      have ha := base_step_to_val_always_to_val hs hs'
      exact Option.isSome_iff_exists.mp ha |>.imp fun v hv => (coe_of_toVal_eq_some hv).symm
    obtain ⟨v', rfl⟩ := hv
    exact ⟨_, _, _, _, .resolveS p v' e σ w σ' κ' efs hs'
      (Std.ExtTreeSet.mem_iff_contains.mp (hp p (Std.ExtTreeSet.mem_iff_contains.mpr hmem)))⟩
  | _ => exact ⟨_, _, _, _, by constructor <;> assumption⟩

/-- Update the authoritative heap and the owned cell together. -/
theorem heap_update (σ σl : State) (l : Loc) (old new : Option Val)
    (hl : get? (M := HeapF) σl.heap l = some old) :
    genHeapInterp (GF := GF) σ.heap ∗ ownHeap σl.heap ==∗
      genHeapInterp (σ.initHeap l 1 new).heap ∗ ownHeap (σl.initHeap l 1 new).heap := by
  simp
  iintro ⟨Hauth, Hlocal⟩
  icases BigSepM.bigSepM_insert_acc hl $$ Hlocal with ⟨Hl, Hclose⟩
  imod genHeap_update (v₂ := new) $$ [$Hauth $Hl] with ⟨Hauth, Hl⟩
  imodintro
  iframe Hauth
  iapply Hclose $$ Hl

theorem fresh_mono {h hl : HeapF (Option Val)} (hh : HeapSub hl h)
    {l : Loc} {n : Int} (hf : ∀ i : Int, 0 ≤ i → i < n → get? h (l + i) = none) :
    ∀ i : Int, 0 ≤ i → i < n → get? hl (l + i) = none := by
  intro i hi hn
  cases he : get? hl (l + i) with
  | none => rfl
  | some ov => have := hh _ _ he; rw [hf i hi hn] at this; contradiction

theorem heap_alloc (σ σl : State) (l : Loc) (n : Int) (v : Val)
    (hf : ∀ i : Int, 0 ≤ i → i < n → get? (M := HeapF) σ.heap (l + i) = none)
    (hfl : ∀ i : Int, 0 ≤ i → i < n → get? (M := HeapF) σl.heap (l + i) = none) :
    genHeapInterp (GF := GF) σ.heap ∗ ownHeap σl.heap ==∗
      genHeapInterp (σ.initHeap l n v).heap ∗ ownHeap (σl.initHeap l n v).heap := by
  iintro ⟨Hauth, Hlocal⟩
  imod genHeap_alloc_big (allocCells l n.toNat v) σ.heap (allocCells_disjoint hf)
    $$ Hauth with ⟨Hauth, Hnew, _⟩
  imodintro
  isplitl [Hauth]
  · iapply genHeapInterp_eqv (Std.PartialMap.equiv.symm _ _ initHeap_heap_eq) $$ Hauth
  · iapply (BigSepM.bigSepM_eqv_of_perm initHeap_heap_eq).2
    iapply (BigSepM.bigSepM_union (allocCells_disjoint hfl)).2
    iframe

theorem proph_alloc (κ : List Observation) (ps psl : Std.ExtTreeSet ProphId) (p : ProphId)
    (hf : p ∉ ps) (hfl : p ∉ psl) :
    prophMapInterp (GF := GF) κ ps ∗ ownProphs psl ==∗
      prophMapInterp κ (ps.insert p) ∗ ownProphs (psl.insert p) := by
  iintro ⟨Hauth, Hlocal⟩
  imod ProphMap.new_proph p ps κ hf $$ Hauth with ⟨Hauth, Hp⟩
  imodintro
  rw [← insert_eq_singleton_union_extTreeSet]
  iframe Hauth
  unfold ownProphs
  rw [insert_eq_singleton_union_extTreeSet (ps := psl) (p := p)]
  iapply (BigSepS.bigSepS_union (show ({p} : Std.ExtTreeSet ProphId compare) ## psl from by
    intro x ⟨hx, hm⟩
    rw [Std.LawfulSet.mem_singleton] at hx
    exact hfl (hx ▸ hm))).2
  iframe Hlocal
  iapply BigSepS.bigSepS_singleton.mpr
  iexists (prophListResolves κ p)
  iexact Hp

theorem proph_resolve (κ : List Observation) (ps psl : Std.ExtTreeSet ProphId)
    (p : ProphId) (v : Val × Val) (hm : p ∈ psl) :
    prophMapInterp (GF := GF) ((p, v) :: κ) ps ∗ ownProphs psl ==∗
      prophMapInterp κ ps ∗ ownProphs psl := by
  iintro ⟨Hauth, Hlocal⟩
  icases BigSepS.bigSepS_elem_of_acc hm $$ Hlocal with ⟨⟨%vs, Hp⟩, Hclose⟩
  imod ProphMap.resolve_proph p v κ ps vs $$ [$Hauth $Hp] with ⟨%vs', _, Hauth, Hp⟩
  imodintro
  iframe Hauth
  iapply Hclose
  iexists vs'
  iexact Hp

/-- Every physical base step has a matching local step and resource update. -/
theorem base_update {e : Exp} {σ : State} {κ : List Observation} {e' : Exp}
    {σ' : State} {efs : List Exp} (hs : BaseStep e σ κ e' σ' efs)
    (σl : State) (κs : List Observation) (hr : BaseStep.Reducible (e, σl)) :
    genHeapInterp (GF := GF) σ.heap ∗ prophMapInterp (κ ++ κs) σ.usedProphId ∗ ownState σl
      ⊢ |={∅}=> ∃ σl', ⌜BaseStep e σl κ e' σl' efs⌝ ∗
        genHeapInterp σ'.heap ∗ prophMapInterp κs σ'.usedProphId ∗ ownState σl' := by
  induction hs generalizing σl κs with
  | freeS l v σ hl =>
    obtain ⟨_, _, _, _, hls⟩ := hr
    cases hls with
    | freeS _ vl _ hll =>
      simp only [List.nil_append]
      iintro ⟨Hh, Hp, Hhl, Hpl⟩
      imod heap_update σ σl l (some vl) none hll $$ [$Hh $Hhl] with ⟨Hh, Hhl⟩
      imodintro
      iexists (σl.initHeap l 1 none)
      simp only [ownState]
      iframe
      ipureintro; exact .freeS l vl σl hll
  | loadS l v σ hl =>
    obtain ⟨_, _, _, _, hls⟩ := hr
    cases hls with
    | loadS _ vl _ hll =>
      simp only [List.nil_append]
      iintro ⟨Hh, Hp, Hhl, Hpl⟩
      ihave %hh := heap_agree σ.heap σl.heap $$ [$Hh $Hhl]
      have heq := hh l (some vl) hll
      change σ.get? l = _ at heq
      rw [hl] at heq
      cases Option.some.inj (Option.some.inj heq)
      imodintro
      iexists σl
      simp only [ownState]
      iframe
      ipureintro; exact .loadS l v σl hll
  | storeS l v w σ hl =>
    obtain ⟨_, _, _, _, hls⟩ := hr
    cases hls with
    | storeS _ vl _ _ hll =>
      simp only [List.nil_append]
      iintro ⟨Hh, Hp, Hhl, Hpl⟩
      imod heap_update σ σl l (some vl) (some w) hll $$ [$Hh $Hhl] with ⟨Hh, Hhl⟩
      imodintro
      iexists (σl.initHeap l 1 (some w))
      simp only [ownState]
      iframe
      ipureintro; exact .storeS l vl w σl hll
  | xchgS l v w σ hl =>
    obtain ⟨_, _, _, _, hls⟩ := hr
    cases hls with
    | xchgS _ vl _ _ hll =>
      simp only [List.nil_append]
      iintro ⟨Hh, Hp, Hhl, Hpl⟩
      ihave %hh := heap_agree σ.heap σl.heap $$ [$Hh $Hhl]
      have heq := hh l (some vl) hll
      change σ.get? l = _ at heq
      rw [hl] at heq
      cases Option.some.inj (Option.some.inj heq)
      imod heap_update σ σl l (some v) (some w) hll $$ [$Hh $Hhl] with ⟨Hh, Hhl⟩
      imodintro
      iexists (σl.initHeap l 1 (some w))
      simp only [ownState]
      iframe
      ipureintro; exact .xchgS l v w σl hll
  | faaS l i1 i2 σ hl =>
    obtain ⟨_, _, _, _, hls⟩ := hr
    cases hls with
    | faaS _ j1 _ _ hll =>
      simp only [List.nil_append]
      iintro ⟨Hh, Hp, Hhl, Hpl⟩
      ihave %hh := heap_agree σ.heap σl.heap $$ [$Hh $Hhl]
      have heq := hh l (some (.lit (.int j1))) hll
      change σ.get? l = _ at heq
      rw [hl] at heq
      have : i1 = j1 := by simpa using heq
      subst j1
      imod heap_update σ σl l (some (.lit (.int i1))) (some (.lit (.int (i1+i2)))) hll
        $$ [$Hh $Hhl] with ⟨Hh, Hhl⟩
      imodintro
      iexists (σl.initHeap l 1 (some (.lit (.int (i1+i2)))))
      simp only [ownState]
      iframe
      ipureintro; exact .faaS l i1 i2 σl hll
  | cmpXchgS l v1 v2 vl σ b hl hc hb =>
    obtain ⟨_, _, _, _, hls⟩ := hr
    cases hls with
    | cmpXchgS _ _ _ vl' _ b' hll hc' hb' =>
      simp only [List.nil_append]
      iintro ⟨Hh, Hp, Hhl, Hpl⟩
      ihave %hh := heap_agree σ.heap σl.heap $$ [$Hh $Hhl]
      have heq := hh l (some vl') hll
      change σ.get? l = _ at heq
      rw [hl] at heq
      cases Option.some.inj (Option.some.inj heq)
      cases b with
      | false =>
        imodintro
        iexists σl
        simp only [ownState, Bool.false_eq_true, ↓reduceIte]
        iframe
        ipureintro; exact .cmpXchgS l v1 v2 vl σl false hll hc hb
      | true =>
        imod heap_update σ σl l (some vl) (some v2) hll $$ [$Hh $Hhl] with ⟨Hh, Hhl⟩
        imodintro
        iexists (σl.initHeap l 1 (some v2))
        simp only [ownState, ↓reduceIte]
        iframe
        ipureintro; exact .cmpXchgS l v1 v2 vl σl true hll hc hb
  | allocNS n v σ l hn hf =>
    simp only [List.nil_append]
    iintro ⟨Hh, Hp, Hhl, Hpl⟩
    ihave %hh := heap_agree σ.heap σl.heap $$ [$Hh $Hhl]
    have hfl := fresh_mono hh hf
    imod heap_alloc σ σl l n v hf hfl $$ [$Hh $Hhl] with ⟨Hh, Hhl⟩
    imodintro
    iexists (σl.initHeap l n v)
    simp only [ownState]
    iframe
    ipureintro; exact .allocNS n v σl l hn hfl
  | newProphS σ p hf =>
    simp only [List.nil_append]
    iintro ⟨Hh, Hp, Hhl, Hpl⟩
    ihave %hp := prophs_agree κs σ.usedProphId σl.usedProphId $$ [$Hp $Hpl]
    have hfp : p ∉ σ.usedProphId := fun hm => hf (Std.ExtTreeSet.mem_iff_contains.mp hm)
    have hfpl : p ∉ σl.usedProphId := fun hm => hfp (hp p hm)
    imod proph_alloc κs σ.usedProphId σl.usedProphId p hfp hfpl $$ [$Hp $Hpl] with ⟨Hp, Hpl⟩
    imodintro
    iexists { σl with usedProphId := σl.usedProphId.insert p }
    simp only [ownState]
    iframe
    ipureintro; exact .newProphS σl p (fun hc => hfpl (Std.ExtTreeSet.mem_iff_contains.mpr hc))
  | resolveS p v e σ w σ' κ ts hs hm ih =>
    obtain ⟨_, _, _, _, hls⟩ := hr
    cases hls with
    | resolveS _ vl _ _ _ σl' κl tsl hinner hml =>
      iintro ⟨Hh, Hp, Hlocal⟩
      rw [List.append_assoc]
      simp only [List.singleton_append]
      imod ih σl ((p, (v, w)) :: κs) ⟨_, _, _, _, hinner⟩ $$ [$Hh $Hp $Hlocal]
        with ⟨%σl2, %hmatch, Hh, Hp, Hhl, Hpl⟩
      have hml2 : p ∈ σl2.usedProphId :=
        base_step_more_proph_ids hmatch p (Std.ExtTreeSet.mem_iff_contains.mpr hml)
      imod proph_resolve κs σ'.usedProphId σl2.usedProphId p (v,w) hml2 $$ [$Hp $Hpl]
        with ⟨Hp, Hpl⟩
      imodintro
      iexists σl2
      simp only [ownState]
      iframe
      ipureintro; exact .resolveS p v e σl w σl2 κ ts hmatch hml
  | _ =>
    simp only [List.nil_append]
    iintro ⟨Hh, Hp, Hhl, Hpl⟩
    imodintro
    iexists σl
    simp only [ownState]
    iframe
    ipureintro
    constructor <;> assumption

/-- HeapLang satisfies the semantic step simulation, for all its operations. -/
instance heapLangStateSimulation : StateSimulation (Expr := Exp) (ownState (GF := GF)) where
  timeless _ := inferInstance
  fork_post _ := by change ⊢ (iprop(True) : IProp GF); ipureintro; trivial
  update e σ σl ns κ κs nt hr := by
    obtain ⟨κl, el', σl', efsl, hctx⟩ := hr
    cases hctx with
    | @intro e0 e0' K hb =>
      iintro ⟨Hphys, Hlocal⟩
      ihave %Hsub := state_agree σ σl ns (κ ++ κs) nt $$ [$Hphys $Hlocal]
      have hrl : BaseStep.Reducible (e0, σl) := ⟨_, _, _, _, hb⟩
      have hrp := base_reducible_mono Hsub.1 Hsub.2 hrl
      imodintro
      isplitr
      · ipureintro
        exact EctxLanguage.primStep_reducible_fill_of_baseStep_reducible hrp
      iintro %e' %σ' %efs %hs
      obtain ⟨e0new, rfl, hb'⟩ :=
        EctxLanguage.exists_baseStep_of_primStep_fill_of_redex_baseStep_reducible hrp hs
      icases (stateInterp_split σ ns (κ ++ κs) nt).mp $$ Hphys with ⟨Hh, Hp⟩
      imod base_update hb' σl κs hrl $$ [$Hh $Hp $Hlocal]
        with ⟨%σlnew, %hbl, Hh, Hp, Hlocal⟩
      imodintro
      iexists σlnew
      simp only [stateInterp]
      iframe Hh Hp Hlocal
      ipureintro
      exact .intro hbl

/-- HeapLang requisiteness, obtained directly from its state simulation. -/
theorem wp_requisiteness {H : Type → Type} [LawfulFiniteMap H Nat]
    [GhostMapG GF Nat Exp H] (e : Exp) (σ : State) (φ : Val → Prop)
    (h : adequate .NotStuck e σ (fun v _ => φ v)) :
    ownState (GF := GF) σ ⊢ WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }} := by
  iintro Hlocal
  iapply fupd_wp
  imod tpInv_alloc (GF := GF) (Expr := Exp) (H := H) with ⟨%γ, Hini⟩
  letI TI : TpinvGS GF Exp H := { toGhostMapG := inferInstance, tp_name := γ }
  imodintro
  iapply Req.wp_requisiteness e σ φ h $$ Hini Hlocal

/-- The empty state requires no resources. -/
theorem ownState_empty : ⊢ ownState (GF := GF) (default : State) := by
  change ⊢ iprop(bigSepM (fun l ov => pointsTo (GF := GF) l (.own 1) ov)
    (∅ : HeapF (Option Val)) ∗ ownProphs (∅ : Std.ExtTreeSet ProphId compare))
  isplit
  · iapply BigSepM.bigSepM_empty.mpr; itrivial
  · iapply BigSepS.bigSepS_empty.mpr; itrivial

/-- In particular, a program adequate in every state has a WP with no precondition. -/
theorem wp_requisiteness_nopre {H : Type → Type} [LawfulFiniteMap H Nat]
    [GhostMapG GF Nat Exp H] (e : Exp) (φ : Val → Prop)
    (h : ∀ σ, adequate .NotStuck e σ (fun v _ => φ v)) :
    ⊢@{IProp GF} WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }} := by
  iapply wp_requisiteness (H := H) e default φ (h default)
  iapply ownState_empty

/-- Sequential requisiteness retains the final local state and a stateful postcondition. -/
theorem wp_requisiteness_nofork (e : Exp) (σ : State) (φ : Val → State → Prop)
    (h : AdequateNoFork .NotStuck e σ φ) :
    ownState (GF := GF) σ ⊢
      WP e @ Stuckness.NotStuck; ⊤ {{ v, ∃ σ', ownState σ' ∗ ⌜φ v σ'⌝ }} :=
  Req.wp_requisiteness_nofork e σ φ h

end Req.HeapLang
