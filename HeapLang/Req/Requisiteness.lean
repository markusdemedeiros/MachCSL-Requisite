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
import Iris.ProgramLogic.Lifting
import Iris.ProgramLogic.ThreadPool
import Iris.Instances.Lib.Invariants

/-! Semantic requisiteness from a local state simulation. The proof uses WP
lifting directly, independently of the abstract completeness framework. -/
namespace Req
open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProgramLogic.Language
open Iris.ProgramLogic.Language.Notation

variable {Expr State Obs Val : Type} [Language Expr State Obs Val]
variable {GF : BundledGFunctors} {hlc : HasLC} [ι : IrisGS_gen hlc Expr GF]

/-- A local state can match every physical step, including its observations and forks. -/
class StateSimulation (ownState : State → IProp GF) where
  timeless σ : Timeless (ownState σ)
  fork_post v : ⊢ ι.forkPost v
  update (e : Expr) (σ σl : State) (ns : Nat) (κ κs : List Obs) (nt : Nat) :
    PrimStep.Reducible (e, σl) →
    stateInterp σ ns (κ ++ κs) nt ∗ ownState σl ⊢ |={∅}=>
      ⌜PrimStep.Reducible (e, σ)⌝ ∗
      (∀ e' σ' efs, ⌜(e, σ) -<κ>-> (e', σ', efs)⌝ ={∅}=∗
        ∃ σl', ⌜(e, σl) -<κ>-> (e', σl', efs)⌝ ∗
          stateInterp σ' (ns + 1) κs (nt + efs.length) ∗ ownState σl')

attribute [instance] StateSimulation.timeless

variable {ownState : State → IProp GF} [SS : StateSimulation (Expr := Expr) ownState]
variable {H : Type → Type} [LawfulFiniteMap H Nat] [TI : TpinvGS GF Expr H]

def requisiteN : Namespace := nroot .@ (2 : Pos)

/-- The local configuration stays safe and reachable from the initial configuration. -/
abbrev requisiteInv (initial : List Expr × State) : IProp GF := iprop%
  ∃ tp σ, ownState σ ∗ tpInv tp ∗ ⌜cfgSafe (tp, σ)⌝ ∗ ⌜initial -·->ₜₚ* (tp, σ)⌝

instance (initial : List Expr × State) : Timeless (requisiteInv (ownState := ownState) initial) := by
  unfold requisiteInv
  infer_instance

/-- Each thread tracks its expression in the shared local configuration. -/
theorem wp_requisite_thread (initial : List Expr × State) (n : Nat) (e : Expr) :
    inv requisiteN (requisiteInv (ownState := ownState) initial) -∗
    (n ↪thread e) -∗ WP e @ Stuckness.NotStuck; ⊤ {{ v, n ↪thread (ToVal.ofVal v : Expr) }} := by
  iintro #Hinv
  iloeb as IH generalizing %n %e
  iintro He
  cases hv : ToVal.toVal e with
  | some v =>
    obtain rfl := (coe_of_toVal_eq_some hv).symm
    iapply wp_value'
    iexact He
  | none =>
    iapply wp_lift_step_fupd hv
    iintro %σ %ns %κ %κs %nt Hphys
    imod inv_acc_timeless (show (requisiteN : CoPset) ⊆ ⊤ from fun _ _ => CoPset.mem_full)
      $$ Hinv with ⟨⟨%tp, %σl, Hlocal, Htp, %Hsafe, %Hreach⟩, Hclose⟩
    ihave %Hlu := tpInv_lookup $$ Htp He
    have Hred : PrimStep.Reducible (e, σl) := by
      rcases Hsafe .refl (List.mem_of_getElem? Hlu) with hval | hred
      · simp [hv] at hval
      · exact hred
    imod fupd_mask_subseteq (E2 := ∅) Std.LawfulSet.empty_subset with Hmask
    imod SS.update e σ σl ns κ κs nt Hred $$ [$Hphys $Hlocal] with ⟨%HredPhys, Hstep⟩
    imodintro
    isplitr
    · ipureintro; exact HredPhys
    iintro %e' %σ' %efs %Hprim _ !> !>
    imod Hstep $$ %e' %σ' %efs %Hprim with ⟨%σl', %HlocalStep, Hphys', Hlocal'⟩
    imod Hmask with -
    imod tpInv_update $$ Htp He with ⟨Htp, He⟩
    imod tpInv_new_threads efs $$ Htp with ⟨Htp, Hchildren⟩
    have Hcfg : (tp, σl) -·->ₜₚ (tp.set n e' ++ efs, σl') := ⟨κ, cfg_step Hlu HlocalStep⟩
    imod Hclose $$ [Hlocal' Htp] with -
    · unfold requisiteInv
      iexists (tp.set n e' ++ efs), σl'
      iframe
      isplit
      · ipureintro; exact fun h => Hsafe (.head Hcfg h)
      · ipureintro; exact Hreach.trans (.single Hcfg)
    imodintro
    iframe Hphys'
    isplitl [He]
    · iapply IH $$ He
    · iapply (BigSepL.bigSepL_impl) $$ Hchildren
      iintro !> %k %ef %_ Hchild
      ihave Hw := IH $$ Hchild
      iapply wp_wand $$ Hw
      iintro %v _
      iapply SS.fork_post

/-- Operational adequacy implies the semantic weakest precondition. -/
theorem wp_requisiteness (e : Expr) (σ : State) (φ : Val → Prop)
    (h : adequate .NotStuck e σ (fun v _ => φ v)) :
    tpInvIni (TI := TI) -∗ ownState σ -∗ WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }} := by
  iintro Hini Hlocal
  iapply fupd_wp
  imod tpInv_set [e] $$ Hini with ⟨Htp, Hthreads⟩
  imod inv_alloc requisiteN ⊤ (requisiteInv (ownState := ownState) ([e], σ))
    $$ [Htp Hlocal] with #Hinv
  · inext
    unfold requisiteInv
    iexists [e], σ
    iframe
    isplit
    · ipureintro; exact fun {_} hreach {_} hmem => h.adequate_not_stuck _ _ _ rfl hreach hmem
    · ipureintro; exact .refl
  ihave He := BigSepL.bigSepL_singleton $$ Hthreads
  imodintro
  iapply wp_fupd
  ihave Hw := wp_requisite_thread ([e], σ) 0 e $$ Hinv He
  iapply wp_wand $$ Hw
  iintro %v Hv
  imod inv_acc_timeless (show (requisiteN : CoPset) ⊆ ⊤ from fun _ _ => CoPset.mem_full)
    $$ Hinv with ⟨⟨%tp, %σ', Hlocal, Htp, %Hsafe, %Hreach⟩, Hclose⟩
  ihave %Hlu := tpInv_lookup $$ Htp Hv
  imod Hclose $$ [Hlocal Htp] with -
  · unfold requisiteInv
    iexists tp, σ'
    iframe ∗ %
  imodintro
  ipureintro
  cases tp with
  | nil => simp at Hlu
  | cons hd rest =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at Hlu
    subst hd
    exact h.adequate_result rest σ' v Hreach

/-- For sequential executions, return ownership of the final local state. -/
theorem wp_requisiteness_nofork (e : Expr) (σ : State) (φ : Val → State → Prop)
    (h : AdequateNoFork .NotStuck e σ φ) :
    ownState σ ⊢ WP e @ Stuckness.NotStuck; ⊤ {{ v, ∃ σ', ownState σ' ∗ ⌜φ v σ'⌝ }} := by
  iloeb as IH generalizing %e %σ %h
  iintro Hlocal
  cases hv : ToVal.toVal e with
  | some v =>
    obtain rfl := (coe_of_toVal_eq_some hv).symm
    iapply wp_value'
    iexists σ
    iframe Hlocal
    ipureintro
    exact h.result (t₂ := []) .refl
  | none =>
    have hred : PrimStep.Reducible (e, σ) := by
      rcases h.not_stuck (e₂ := e) rfl (t₂ := [e]) .refl (by simp) with hval | hred
      · simp [hv] at hval
      · exact hred
    iapply wp_lift_step_fupd hv
    iintro %σp %ns %κ %κs %nt Hphys
    imod fupd_mask_subseteq (E2 := ∅) Std.LawfulSet.empty_subset with Hmask
    imod SS.update e σp σ ns κ κs nt hred $$ [$Hphys $Hlocal] with ⟨%HredPhys, Hstep⟩
    imodintro
    isplitr
    · ipureintro; exact HredPhys
    iintro %e' %σp' %efs %Hprim _ !> !>
    imod Hstep $$ %e' %σp' %efs %Hprim with ⟨%σ', %HlocalStep, Hphys, Hlocal⟩
    have hefs : efs = [] := adequateNoFork_efs_nil h .refl (by simp) HlocalStep
    subst efs
    imod Hmask with -
    imodintro
    iframe Hphys
    isplitl [Hlocal]
    · iapply IH $$ %e' %σ' %(adequateNoFork_primStep HlocalStep h) Hlocal
    · iapply BigSepL.bigSepL_nil.mpr
      itrivial

end Req
