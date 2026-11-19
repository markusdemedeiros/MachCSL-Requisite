import Experiments.WholeFunction.RequisiteFootprint
import MachCSL.Wp

/-! Lift a silent per-hart resource simulation through MachCSL's actual era,
power, observation, and protected-resource bookkeeping. Dead generations
stutter while retaining the footprint. No WP occurs in the simulation input.
-/
namespace MachCSL.WholeFunction
open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProgramLogic.Language
open Iris.ProgramLogic.Language.Notation
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D

variable {A : Type} {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]

structure HartFootprintSimulation (cpu : CPU) (own : A → IProp GF)
    (code : A → SailM Unit) (enabled : A → Prop) (edge : A → A → Prop) where
  update (a : A) (ready : enabled a) (σ : MState) :
    machInterp σ ∗ own a ⊢ |={⊤,∅}=>
      ⌜hartObsM cpu (code a) σ = [] ∧ ∃ m' σ', hartStep cpu (code a) σ m' σ'⌝ ∗
      ▷ ∀ m' σ', ⌜hartStep cpu (code a) σ m' σ'⌝ -∗ £ 1 ={∅,⊤}=∗
        ∃ a', ⌜m' = code a' ∧ edge a a'⌝ ∗ machInterp σ' ∗ own a'

def hartOwn (own : A → IProp GF) (a : A) : IProp GF := iprop(genCert ∗ own a)

def hartEnabled (cpu : CPU) (code : A → SailM Unit) (enabled : A → Prop)
    (e : Expr) (a : A) : Prop :=
  e = Expr.hart (genId (hlc := hlc) (GF := GF)) cpu (code a) ∧ enabled a

def hartEdge (cpu : CPU) (code : A → SailM Unit) (edge : A → A → Prop)
    (_e : Expr) (a : A) (e' : Expr) (a' : A) : Prop :=
  e' = Expr.hart (genId (hlc := hlc) (GF := GF)) cpu (code a') ∧ (a' = a ∨ edge a a')

/-- This adapter proves the full physical resource simulation from a local
hart-event simulation. Its stuttering alternative is necessary for power loss.
It neither assumes that the current era is live nor changes the machine SI. -/
theorem HartFootprintSimulation.toFootprint {cpu : CPU} {own : A → IProp GF}
    {code : A → SailM Unit} {enabled : A → Prop} {edge : A → A → Prop}
    (sim : HartFootprintSimulation cpu own code enabled edge) :
    FootprintSimulation (hartOwn own) (hartEnabled (GF := GF) cpu code enabled)
      (hartEdge (GF := GF) cpu code edge) where
  update e a ready g ns obs obs' nt := by
    obtain ⟨rfl, ready⟩ := ready
    unfold hartOwn
    iintro ⟨Hres, ⟨#Hcert, Hown⟩⟩
    ihave #Hparts := genCert_parts $$ Hcert
    icases Hparts with ⟨Hborn, Hstarted, Hregistered⟩
    rw [resourceInterp_eq]
    icases Hres with ⟨Hpower, Hobs⟩
    unfold powerInterp
    icases Hpower with ⟨Hgen, Hstart, ⟨%R, HR, %Hok, Hcur⟩, Hdisk⟩
    ihave %Hb' := genAuth_born _ _ $$ Hgen Hborn
    ihave %Hs' := startAuth_started _ _ $$ Hstart Hstarted
    by_cases hge : g.gen = genId (hlc := hlc) (GF := GF)
    · have hpow : g.pow = true := by
        cases h : g.pow
        · simp [startCount, h] at Hs'; omega
        · rfl
      have hl : threadLive g (genId (hlc := hlc) (GF := GF)) := ⟨hpow, hge⟩
      rw [eraCur_true hpow]
      icases Hcur with ⟨%E, %HE, Hera⟩
      ihave %HRg := eraRegistered_lookup _ _ _ $$ HR Hregistered
      have HRg' : get? R g.gen = some (MachGS.era (hlc := hlc) (GF := GF)) := by
        rw [hge]; exact HRg
      have hEq : E = MachGS.era (hlc := hlc) (GF := GF) := by
        rw [HE] at HRg'; exact Option.some.inj HRg'
      subst hEq
      rw [eraInterp_ambient]
      imod sim.update a ready g.m $$ [$Hera $Hown] with ⟨%⟨hsil, Hred⟩, Hstep⟩
      imodintro
      isplit
      · ipureintro
        obtain ⟨m', σ', hs⟩ := Hred
        exact ⟨_, .hart _ cpu m', { g with m := σ' }, [], primStep_hart_live hl hs⟩
      inext
      iintro %e₂ %g₂ %forks %Hprim Hcred
      obtain ⟨rfl, h⟩ := primStep_hart_inv Hprim
      rcases h with ⟨_, hobs, m', σ', rfl, hs, rfl⟩ | ⟨hnl, _, _⟩
      · imod Hstep $$ %m' %σ' %hs Hcred with ⟨%a', %Habstract, Hσ', Hown⟩
        obtain ⟨rfl, hedge⟩ := Habstract
        imodintro
        iexists a'
        isplit
        · ipureintro; exact ⟨rfl, rfl, Or.inr hedge⟩
        have hnil : obs = [] := hobs.trans hsil
        subst obs
        simp only [hsil] at Hprim
        simp only [hsil]
        ihave Hobs := obsInterp_silent_nil _ _ _ _ _ obs' Hprim $$ Hobs
        isplitl [Hgen Hstart HR Hσ' Hdisk Hobs]
        · rw [resourceInterp_eq]
          unfold powerInterp
          iframe Hobs
          rw [show startCount { g with m := σ' } = startCount g from rfl]
          iframe Hgen Hstart
          have hdk : diskFixedInterp (hlc := hlc) (GF := GF) { g with m := σ' } = diskFixedInterp g := by
            unfold diskFixedInterp
            rw [show diskOf σ'.devs = diskOf g.m.devs from hartStep_diskOf hs]
          rw [hdk]
          iframe Hdisk
          iexists R
          iframe HR
          isplit
          · ipureintro; exact Hok
          rw [eraCur_true (g := { g with m := σ' }) hpow]
          iexists (MachGS.era (hlc := hlc) (GF := GF))
          isplit
          · ipureintro; exact HRg'
          rw [eraInterp_ambient]
          iexact Hσ'
        · iframe Hcert Hown
      · exact absurd hl hnl
    · have hnl : ¬ threadLive g (genId (hlc := hlc) (GF := GF)) := fun h => hge h.2
      iapply fupd_mask_intro LawfulSet.empty_subset
      iintro Hclose
      isplit
      · ipureintro
        exact ⟨[], .hart _ cpu (code a), g, [], primStep_hart_dead hnl⟩
      inext
      iintro %e₂ %g₂ %forks %Hprim _
      obtain ⟨rfl, h⟩ := primStep_hart_inv Hprim
      rcases h with ⟨hl, _⟩ | ⟨_, rfl, rfl, rfl⟩
      · exact absurd hl hnl
      imod Hclose
      imodintro
      iexists a
      isplit
      · ipureintro; exact ⟨rfl, rfl, Or.inl rfl⟩
      ihave Hobs := obsInterp_silent_nil _ _ _ _ _ obs' Hprim $$ Hobs
      isplitl [Hgen Hstart HR Hcur Hdisk Hobs]
      · rw [resourceInterp_eq]
        unfold powerInterp
        iframe Hobs Hgen Hstart Hdisk
        iexists R
        iframe HR Hcur
        ipureintro; exact Hok
      · iframe Hcert Hown

end MachCSL.WholeFunction
