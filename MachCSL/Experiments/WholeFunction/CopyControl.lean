import Experiments.WholeFunction.ControlFlow
import Experiments.WholeFunction.CopyContracts

/-! Composition of the actual guarded MachCSL control-flow rule with the
copy-family effect certificates. The caller supplies a certified transfer
backend and local edge summaries. The trace invariant and whole-loop pure
postcondition are derived here. This is not an instance of the actual
copyin binary backend, nor an ownership conversion from ownState.
-/
namespace Experiments.WholeFunction.Copy

open Xv6 Iris Iris.BI Iris.ProgramLogic MachCSL

/-- Literally the pure result appearing in SpecCopyin; the buffer accessor
expands to the copied prefix followed by the untouched destination suffix. -/
def CopyinPost (sz a r : BitVec 64) (P : UPtd) (M : Image)
    (old : List (BitVec 8)) (s : State) : Prop :=
  P.extSz sz s.table ∧
    ((r = 0#64 ∧ buffer s old = umemRead (viewFaulted P s.table M) a.toNat old.length ∧
        umMapped s.table a.toNat old.length ∧ uvaRprefix s.table a old.length) ∨
     (r = -1#64 ∧ (∃ d, d ≤ old.length ∧
        buffer s old = umemRead (viewFaulted P s.table M) a.toNat d ++ old.drop d) ∧
      ∃ e, e < old.length ∧ ¬ uvaRmapped P (a + BitVec.ofNat 64 e).toNat))

/-- Control bookkeeping may stutter at the memory-summary level. Every
actual backend transfer must nevertheless progress under the guarded
`Xv6.WholeFunction.Transfer` contract; this relation does not waive that. -/
def Effect (dir : Direction) (sz a : BitVec 64) (s t : State) : Prop :=
  s = t ∨ Step dir sz a s t

theorem trace_effect {dir : Direction} {sz a : BitVec 64} {s t u : State}
    (h : Trace dir sz a s t) (he : Effect dir sz a t u) : Trace dir sz a s u := by
  rcases he with rfl | he
  · exact h
  · exact .snoc h he

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]

/-- Whole-control-flow copyin rule. Only primitive effects, a real spatial
transfer backend, and return tests are supplied. In particular there is no
per-loop induction, cumulative image equation, or final prefix proof among
the premises. The backend and `own` must still instantiate the real binary,
register/stack ABI, page ownership, and callee/interruption contracts.
-/
theorem wp_copyin_control_flow {S : Type}
    (own : CPU → S → IProp GF) (view : S → State) (ret : S → BitVec 64)
    (sie : Bool) (proc : BitVec 64) (sz a : BitVec 64)
    (P : UPtd) (M : Image) (old : List (BitVec 8)) (ke : Nat)
    (cut : S → Prop) (edge : S → S → Prop)
    (effects : ∀ s t, edge s t → Effect .read sz a (view s) (view t))
    (exit : ∀ s, cut s → (view s).copied.length ≤ old.length ∧
      ((ret s = 0#64 ∧ (view s).copied.length = old.length) ∨
       (ret s = -1#64 ∧ ∃ e, e < old.length ∧
         ¬ uvaRmapped (view s).table (a + BitVec.ofNat 64 e).toNat)))
    (backend : ∀ s, Trace .read sz a (initial P M ke) (view s) → ¬ cut s →
      Xv6.WholeFunction.Transfer own sie proc edge s)
    (cpu : CPU) (s : S) (entry : view s = initial P M ke) :
    own cpu s ∗ wpNext sie proc cpu (fun cpu' => iprop(
      ∀ s', ⌜CopyinPost sz a (ret s') P M old (view s')⌝ -∗
        ⌜(view s').image = viewFaulted P (view s').table M⌝ -∗
        ⌜ke ≤ (view s').lend⌝ -∗ own cpu' s' -∗ wpLoop cpu')) ⊢ wpLoop cpu := by
  have closed : Xv6.WholeFunction.Closed
      (fun s => Trace .read sz a (initial P M ke) (view s)) cut edge :=
    ⟨fun s t ht _ he => trace_effect ht (effects s t he)⟩
  have hentry : Trace .read sz a (initial P M ke) (view s) := entry ▸ Trace.refl _
  iintro ⟨Hown, Hexit⟩
  iapply Xv6.WholeFunction.wp_control_flow own sie proc closed backend cpu s hentry $$ [Hown Hexit]
  iframe Hown
  iapply wpNext_mono _ _ _ _ _ $$ Hexit
  iintro %cpu' Hexit %s' %htrace %hcut Hown
  have hi := trace_certificate htrace
  obtain ⟨hbound, hret⟩ := exit s' hcut
  have hp : CopyinPost sz a (ret s') P M old (view s') := copyin_contract old htrace hbound hret
  have hm := (trace_read htrace).1
  iapply Hexit $$ %s' %hp %hm %hi.lend Hown

#print axioms wp_copyin_control_flow

end Experiments.WholeFunction.Copy
