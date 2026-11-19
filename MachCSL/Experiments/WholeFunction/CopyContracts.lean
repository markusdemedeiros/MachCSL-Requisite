import Experiments.WholeFunction.CopyEffects
import Xv6.SpecCopyin
import Xv6.SpecCopyout
import Xv6.SpecCopyinstr

/-! Exact pure components of the production contracts, obtained from the
shared memory-effect trace. These theorems do not discharge the resource,
ABI, interruption, instruction-execution, or callee obligations of COPYIN,
COPYOUT, COPYINSTR. Those obligations belong to the VCG/spatial bridge.
-/
namespace Experiments.WholeFunction.Copy

open Xv6

def buffer (s : State) (old : List (BitVec 8)) : List (BitVec 8) :=
  s.copied ++ old.drop s.copied.length

/-- The read certificate exposes exactly the image named by SpecCopyin. -/
theorem trace_read {sz a : BitVec 64} {P : UPtd} {M : Image} {ke : Nat} {s : State}
    (h : Trace .read sz a (initial P M ke) s) :
    s.image = viewFaulted P s.table M ∧
    s.copied = umemRead (viewFaulted P s.table M) a.toNat s.copied.length := by
  have hi := trace_certificate h
  have hm : s.image = viewFaulted P s.table M := hi.memory
  exact ⟨hm, hm ▸ hi.read rfl⟩

/-- COPYIN's failure witness is deliberately existential over the requested
run, unlike COPYOUT's failure at the first unwritten byte. -/
theorem copyin_contract {sz a r : BitVec 64} {P : UPtd} {M : Image} {ke : Nat}
    {s : State} (old : List (BitVec 8))
    (h : Trace .read sz a (initial P M ke) s)
    (bound : s.copied.length ≤ old.length)
    (exit : (r = 0#64 ∧ s.copied.length = old.length) ∨
      (r = -1#64 ∧ ∃ e, e < old.length ∧
        ¬ uvaRmapped s.table (a + BitVec.ofNat 64 e).toNat)) :
    P.extSz sz s.table ∧
      ((r = 0#64 ∧ buffer s old = umemRead (viewFaulted P s.table M) a.toNat old.length ∧
          umMapped s.table a.toNat old.length ∧ uvaRprefix s.table a old.length) ∨
       (r = -1#64 ∧ (∃ d, d ≤ old.length ∧
          buffer s old = umemRead (viewFaulted P s.table M) a.toNat d ++ old.drop d) ∧
        ∃ e, e < old.length ∧ ¬ uvaRmapped P (a + BitVec.ofNat 64 e).toNat)) := by
  have hi := trace_certificate h
  have hr := (trace_read h).2
  refine ⟨hi.extension, ?_⟩
  rcases exit with ⟨hz, hn⟩ | ⟨hf, he⟩
  · left
    refine ⟨hz, ?_, hn ▸ hi.mapped, hn ▸ hi.access⟩
    dsimp [buffer]
    rw [hn, List.drop_length, List.append_nil]
    simpa only [hn] using hr
  · obtain ⟨e, he, hbad⟩ := he
    exact Or.inr ⟨hf, ⟨s.copied.length, bound, congrArg (· ++ old.drop s.copied.length) hr⟩,
      e, he, fun hp => hbad (UMemL.uvaRmapped_mono hi.extension.1 hp)⟩

/-- COPYOUT retains the strict failure prefix, returned-table writability,
and entry-table failure reason. Source-buffer ownership is separate. -/
theorem copyout_contract {sz a r : BitVec 64} {P : UPtd} {M : Image} {ke : Nat}
    {s : State} (src : List (BitVec 8))
    (h : Trace .write sz a (initial P M ke) s)
    (exit : (r = 0#64 ∧ s.copied = src) ∨
      (r = -1#64 ∧ s.copied.length < src.length ∧ s.copied = src.take s.copied.length ∧
        ¬ uvaWmapped s.table (a + BitVec.ofNat 64 s.copied.length).toNat)) :
    P.extSz sz s.table ∧
      ((r = 0#64 ∧ s.image = umemWrite (viewFaulted P s.table M) a.toNat src ∧
          umMapped s.table a.toNat src.length ∧ uvaWprefix s.table a src.length) ∨
       (r = -1#64 ∧ ∃ d, d < src.length ∧
          s.image = umemWrite (viewFaulted P s.table M) a.toNat (src.take d) ∧
          umMapped s.table a.toNat d ∧ uvaWprefix s.table a d ∧
          ¬ uvaWmapped P (a + BitVec.ofNat 64 d).toNat)) := by
  have hi := trace_certificate h
  refine ⟨hi.extension, ?_⟩
  rcases exit with ⟨hz, hb⟩ | ⟨hf, hn, hb, he⟩
  · left
    refine ⟨hz, ?_, ?_, ?_⟩
    · simpa only [imageAfter, hb] using hi.memory
    · simpa only [hb] using hi.mapped
    · simpa only [hb, permission, uvaWprefix] using hi.access
  · right
    refine ⟨hf, s.copied.length, hn, ?_, hi.mapped, hi.access,
      fun hp => he (UMemL.uvaWmapped_mono hi.extension.1 hp)⟩
    calc s.image = umemWrite (viewFaulted P s.table M) a.toNat s.copied := hi.memory
         _ = _ := congrArg (umemWrite (viewFaulted P s.table M) a.toNat) hb

/-- First-NUL evidence is local to the bytes read, not a pre-assumed
umemStr postcondition. Fault/exhaustion only yield the existing weak failure
arm: the production contract does not promise failure means no NUL. -/
theorem copyinstr_contract {sz a r : BitVec 64} {P : UPtd} {M : Image} {ke : Nat}
    {s : State} (old : List (BitVec 8))
    (h : Trace .read sz a (initial P M ke) s)
    (bound : s.copied.length ≤ old.length)
    (exit : (r = 0#64 ∧ ∃ d, s.copied.length = d + 1 ∧
        (∀ j, j < d → umemByte s.image (a.toNat + j) ≠ 0#8) ∧
        umemByte s.image (a.toNat + d) = 0#8) ∨ r = -1#64) :
    P.extSz sz s.table ∧
      ((r = 0#64 ∧ ∃ str, umemStr (viewFaulted P s.table M) a.toNat old.length = some str ∧
          buffer s old = str ++ old.drop str.length ∧ umMapped s.table a.toNat str.length) ∨
       (r = -1#64 ∧ ∃ d, d ≤ old.length ∧
          buffer s old = umemRead (viewFaulted P s.table M) a.toNat d ++ old.drop d)) := by
  have hi := trace_certificate h
  obtain ⟨hm, hr⟩ := trace_read h
  refine ⟨hi.extension, ?_⟩
  rcases exit with ⟨hz, d, hd, hn, hzero⟩ | hf
  · left
    refine ⟨hz, s.copied, ?_, rfl, hi.mapped⟩
    have hs := UMemL.umemStr_of_nul s.image a.toNat old.length d (by omega) hn hzero
    rw [hm] at hs
    rw [hr, hd]
    exact hs
  · exact Or.inr ⟨hf, s.copied.length, bound, congrArg (· ++ old.drop s.copied.length) hr⟩

end Experiments.WholeFunction.Copy
