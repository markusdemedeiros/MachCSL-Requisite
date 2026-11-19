import MachCSL.WpSmodeFrame

/-! Guarded whole-control-flow composition at the production kernel boundary.
The transfer backend must prove actual instruction/call WPs. This module
discharges their cyclic composition and hart transport once, leaving pure
abstract invariants separate from spatial ownership. It does not claim that
an arbitrary abstract relation describes a binary.
-/
namespace Xv6.WholeFunction
open Iris Iris.BI Iris.ProgramLogic MachCSL

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
variable {S : Type}

/-- One progressing transfer, possibly a whole basic block or certified call.
The later is essential: an arbitrary zero-step self-edge is not a certificate.
All possible returned abstract states must be handled by the continuation.
The production backend, rather than this definition, certifies their coverage.
-/
def Transfer (own : CPU → S → IProp GF) (sie : Bool) (proc : BitVec 64)
    (edge : S → S → Prop) (s : S) : Prop :=
  ∀ cpu, own cpu s ∗ ▷ wpNext sie proc cpu (fun cpu' => iprop(
    ∀ s', ⌜edge s s'⌝ -∗ own cpu' s' -∗ wpLoop cpu')) ⊢ wpLoop cpu

/-- A pure invariant over a control-flow graph and its exit cutpoints. -/
structure Closed (good cut : S → Prop) (edge : S → S → Prop) : Prop where
  step : ∀ s s', good s → ¬ cut s → edge s s' → good s'

/-- Close all cycles at once. The linear caller continuation survives arbitrary
numbers of steps and migrations; it is consumed only at an exit. Neither
termination nor fixed-hart execution is assumed. -/
theorem wp_control_flow (own : CPU → S → IProp GF) (sie : Bool) (proc : BitVec 64)
    {good cut : S → Prop} {edge : S → S → Prop}
    (closed : Closed good cut edge)
    (backend : ∀ s, good s → ¬ cut s → Transfer own sie proc edge s)
    (cpu : CPU) (s : S) (entry : good s) :
    own cpu s ∗ wpNext sie proc cpu (fun cpu' => iprop(
      ∀ s', ⌜good s'⌝ -∗ ⌜cut s'⌝ -∗ own cpu' s' -∗ wpLoop cpu'))
      ⊢ wpLoop cpu := by
  classical
  iloeb as IH generalizing %cpu %s %entry
  iintro ⟨Hown, Hexit⟩
  by_cases hc : cut s
  · ihave Hexit := wpNext_self sie proc cpu _ $$ Hexit
    iapply Hexit $$ %s %entry %hc Hown
  · iapply backend s entry hc cpu $$ [$Hown Hexit]
    inext
    iapply wpNext_intro_pin
    iintro %cpu' %hpin %s' %hedge Hown
    have hgood := closed.step s s' entry hc hedge
    ihave Hexit := wpNext_shift sie proc cpu cpu' _ hpin $$ Hexit
    iapply IH $$ %cpu' %s' %hgood [$Hown $Hexit]

end Xv6.WholeFunction

/-- info: 'Xv6.WholeFunction.wp_control_flow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Xv6.WholeFunction.wp_control_flow
