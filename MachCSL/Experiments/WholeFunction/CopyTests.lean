import Experiments.WholeFunction.CopyRuns

/-! Regression and rejection checks for the copy-effect compiler boundary.
The conclusions below are pure contract components; none asserts COPYIN,
COPYOUT or COPYINSTR without the missing machine/resource refinement.
-/
namespace Experiments.WholeFunction.Copy.Tests

open Xv6

/-- Zero-length copyin succeeds with the unmodified table and image. -/
example (sz a : BitVec 64) (P : UPtd) (M : Image) (ke : Nat) :
    P.extSz sz P ∧
      ((0#64 = 0#64 ∧ buffer (initial P M ke) [] = umemRead (viewFaulted P P M) a.toNat 0 ∧
          umMapped P a.toNat 0 ∧ uvaRprefix P a 0) ∨
       (0#64 = -1#64 ∧ (∃ d, d ≤ 0 ∧
          buffer (initial P M ke) [] = umemRead (viewFaulted P P M) a.toNat d ++ [].drop d) ∧
        ∃ e, e < 0 ∧ ¬ uvaRmapped P (a + BitVec.ofNat 64 e).toNat)) :=
  copyin_contract [] (.refl _) (Nat.zero_le _) (Or.inl ⟨rfl, rfl⟩)

/-- Zero-length copyout has exactly SpecCopyout's success arm; in
particular the source may be empty without any page or permission premise. -/
example (sz a : BitVec 64) (P : UPtd) (M : Image) (ke : Nat) :
    P.extSz sz P ∧
      ((0#64 = 0#64 ∧ M = umemWrite (viewFaulted P P M) a.toNat [] ∧
          umMapped P a.toNat 0 ∧ uvaWprefix P a 0) ∨
       (0#64 = -1#64 ∧ ∃ d, d < 0 ∧
          M = umemWrite (viewFaulted P P M) a.toNat ([].take d) ∧
          umMapped P a.toNat d ∧ uvaWprefix P a d ∧
          ¬ uvaWmapped P (a + BitVec.ofNat 64 d).toNat)) :=
  write_run_contract (src := []) (ke := ke) .start (Or.inl ⟨rfl, rfl⟩)

/-- Empty capacity for a string is a failure, not an empty successful
NUL-terminated string. The failure contract does not assert no-NUL. -/
example (sz a : BitVec 64) (P : UPtd) (M : Image) (ke : Nat) :
    P.extSz sz P ∧
      ((-1#64 = 0#64 ∧ ∃ str, umemStr (viewFaulted P P M) a.toNat 0 = some str ∧
          buffer (initial P M ke) [] = str ++ [].drop str.length ∧ umMapped P a.toNat str.length) ∨
       (-1#64 = -1#64 ∧ ∃ d, d ≤ 0 ∧
          buffer (initial P M ke) [] = umemRead (viewFaulted P P M) a.toNat d ++ [].drop d)) :=
  copyinstr_contract [] (.refl _) (Nat.zero_le _) (Or.inr rfl)

/-- Two writes separated by a fault retain the first write. This checks
the critical commutation through viewFaulted used by chunked xv6 callers. -/
theorem two_chunks_with_fault (sz a : BitVec 64) (P Q : UPtd) (M : Image)
    (ke ke' : Nat) (first second : List (BitVec 8))
    (hfirst : Step .write sz a (initial P M ke)
      (transfer .write a (initial P M ke) first))
    (he : P.extSz sz Q) (hk : ke ≤ ke')
    (hsecond : Step .write sz a
      (extend (transfer .write a (initial P M ke) first) Q ke')
      (transfer .write a (extend (transfer .write a (initial P M ke) first) Q ke') second)) :
    umemWrite (viewFaulted P Q (umemWrite M a.toNat first)) (a.toNat + first.length) second =
      umemWrite (viewFaulted P Q M) a.toNat (first ++ second) := by
  have ht := Trace.snoc (Trace.snoc (Trace.snoc (.refl _) hfirst)
    (.fault _ Q ke' he hk)) hsecond
  have hi := trace_certificate ht
  simpa only [transfer, extend, initial, imageAfter, List.nil_append,
    List.length_nil, Nat.add_zero] using hi.memory

/-- A newly allocated page really is zeroed, regardless of the old image
outside the mapped domain. This is stronger than merely extending a map. -/
example (P Q : UPtd) (M : Image) (page : Nat) (w : BitVec 64)
    (absent : Iris.Std.PartialMap.get? P.um page = none)
    (present : Iris.Std.PartialMap.get? Q.um page = some w) :
    viewFaulted P Q M page = List.replicate 4096 0#8 := by
  simp [viewFaulted, absent, present]

/-- Read access is insufficient for a write; the write trace requires the
actual uvaWmapped predicate. Both permission variants grow monotonically. -/
example (P Q : UPtd) (h : P.ext Q) (va : Nat)
    (bad : ¬ uvaWmapped Q va) : ¬ uvaWmapped P va := by
  intro hp
  exact bad (permission_mono .write h hp)

/-- A trace cannot substitute different source bytes after copying, even
if its length and page-map facts happen to match. -/
theorem reject_wrong_source {sz a : BitVec 64} {P : UPtd} {M : Image} {ke : Nat}
    {src : List (BitVec 8)} {s : State}
    (wrong : s.copied ≠ src.take s.copied.length) :
    ¬ WriteRun sz a src P M ke s := by
  intro h
  exact wrong (write_run_certificate h).2.2

/-- Full source consumption cannot exceed the caller's buffer. -/
theorem reject_write_overrun {sz a : BitVec 64} {P : UPtd} {M : Image} {ke : Nat}
    {src : List (BitVec 8)} {s : State} (over : src.length < s.copied.length) :
    ¬ WriteRun sz a src P M ke s := by
  intro h
  have hb := (write_run_certificate h).2.1
  omega

/-- A scanner cannot consume a NUL and then continue scanning. -/
theorem reject_scan_after_nul {sz a : BitVec 64} {P : UPtd} {M : Image} {ke max : Nat}
    {s : State} (zero : 0#8 ∈ s.copied) : ¬ ScanRun sz a max P M ke s := by
  intro h
  exact (scan_run_certificate h).2.2 _ zero rfl

theorem reject_scan_overrun {sz a : BitVec 64} {P : UPtd} {M : Image} {ke max : Nat}
    {s : State} (over : max < s.copied.length) : ¬ ScanRun sz a max P M ke s := by
  intro h
  have hb := (scan_run_certificate h).2.1
  omega

/-- Terminating at the first NUL preserves the first-NUL/mapped-prefix
conjuncts of SpecCopyinstr, including the terminator in the copied length. -/
example {sz a : BitVec 64} {P : UPtd} {M : Image} {ke : Nat} {s : State}
    (old : List (BitVec 8)) (h : ScanRun sz a old.length P M ke s)
    (room : s.copied.length < old.length)
    (nul : Step .read sz a s (transfer .read a s [0#8])) :
    P.extSz sz s.table ∧ ∃ str,
      umemStr (viewFaulted P s.table M) a.toNat old.length = some str ∧
      buffer (transfer .read a s [0#8]) old = str ++ old.drop str.length ∧
      umMapped s.table a.toNat str.length := scan_nul_contract old h room nul

#print axioms trace_certificate
#print axioms copyin_contract
#print axioms copyout_contract
#print axioms copyinstr_contract
#print axioms write_run_contract
#print axioms scan_nul_contract

end Experiments.WholeFunction.Copy.Tests
