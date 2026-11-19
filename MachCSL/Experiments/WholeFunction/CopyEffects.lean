import Xv6.UMemLemmas

/-!
Memory-effect certificates for the actual xv6 copy family. These are summaries
for a whole-function VCG, not a replacement instruction semantics or a claim
that an arbitrary binary implements the summaries. A caller must certify the
control-flow and the callee/ownership boundaries separately.

Unlike a list-copy model, the effects include growing UPtd maps, lazy-page
zeroing, read/write permissions at wrapped machine addresses, page boundaries,
and the monotonically increasing allocation lend counter. The same trace
algebra serves copyin, copyout and the byte/chunk loops of copyinstr.
-/
namespace Experiments.WholeFunction.Copy

open Xv6

abbrev Image := Nat → List (BitVec 8)

inductive Direction where
  | read | write
  deriving DecidableEq

def permission : Direction → UPtd → Nat → Prop
  | .read => uvaRmapped
  | .write => uvaWmapped

theorem permission_mono (dir : Direction) {P Q : UPtd} (h : P.ext Q)
    {va : Nat} : permission dir P va → permission dir Q va := by
  cases dir with
  | read => exact UMemL.uvaRmapped_mono h
  | write => exact UMemL.uvaWmapped_mono h

def imageAfter : Direction → Image → Nat → List (BitVec 8) → Image
  | .read, M, _, _ => M
  | .write, M, a, bs => umemWrite M a bs

structure State where
  table : UPtd
  image : Image
  copied : List (BitVec 8)
  lend : Nat

def initial (P : UPtd) (M : Image) (ke : Nat) : State := ⟨P, M, [], ke⟩

def extend (s : State) (Q : UPtd) (ke : Nat) : State :=
  ⟨Q, viewFaulted s.table Q s.image, s.copied, ke⟩

def transfer (dir : Direction) (a : BitVec 64) (s : State)
    (chunk : List (BitVec 8)) : State :=
  ⟨s.table, imageAfter dir s.image (a.toNat + s.copied.length) chunk,
    s.copied ++ chunk, s.lend⟩

/-- One operation boundary. Extension abstracts a successful fault, not an
arbitrary memory mutation. Transfer requires only the local page evidence;
the cumulative image equation is proved below, never assumed by a step. -/
inductive Step (dir : Direction) (sz a : BitVec 64) : State → State → Prop
  | fault (s : State) (Q : UPtd) (ke : Nat)
      (extension : s.table.extSz sz Q) (lend : s.lend ≤ ke) :
      Step dir sz a s (extend s Q ke)
  | chunk (s : State) (bs : List (BitVec 8))
      (positive : 0 < bs.length)
      (page : (a.toNat + s.copied.length) % 4096 + bs.length ≤ 4096)
      (mapped : umMapped s.table (a.toNat + s.copied.length) bs.length)
      (access : ∀ j, j < bs.length →
        permission dir s.table (a + BitVec.ofNat 64 (s.copied.length + j)).toNat)
      (read : dir = .read → bs = umemRead s.image (a.toNat + s.copied.length) bs.length) :
      Step dir sz a s (transfer dir a s bs)

inductive Trace (dir : Direction) (sz a : BitVec 64) : State → State → Prop
  | refl (s : State) : Trace dir sz a s s
  | snoc {s t u : State} : Trace dir sz a s t → Step dir sz a t u → Trace dir sz a s u

/-- New lazy pages cannot change a previously read, mapped prefix. -/
theorem read_viewFaulted (P Q : UPtd) (M : Image) (a n : Nat)
    (hm : umMapped P a n) :
    umemRead (viewFaulted P Q M) a n = umemRead M a n := by
  apply List.ext_getElem?
  intro i
  rw [UMemL.umemRead_getElem?, UMemL.umemRead_getElem?]
  split
  next hi =>
    have h := hm i hi
    have hn : ¬ (Iris.Std.PartialMap.get? P.um ((a + i) / 4096)).isNone := by
      cases he : Iris.Std.PartialMap.get? P.um ((a + i) / 4096) <;> simp_all
    simp only [umemByte, viewFaulted, show ¬ ((Iris.Std.PartialMap.get? P.um
      ((a + i) / 4096)).isNone ∧ _) from fun hc => hn hc.1, ↓reduceIte]
  next => rfl

structure Invariant (dir : Direction) (sz a : BitVec 64)
    (P : UPtd) (M : Image) (ke : Nat) (s : State) : Prop where
  extension : P.extSz sz s.table
  mapped : umMapped s.table a.toNat s.copied.length
  access : ∀ j, j < s.copied.length →
    permission dir s.table (a + BitVec.ofNat 64 j).toNat
  lend : ke ≤ s.lend
  memory : s.image = imageAfter dir (viewFaulted P s.table M) a.toNat s.copied
  read : dir = .read → s.copied = umemRead s.image a.toNat s.copied.length

theorem invariant_initial (dir : Direction) (sz a : BitVec 64)
    (P : UPtd) (M : Image) (ke : Nat) :
    Invariant dir sz a P M ke (initial P M ke) := by
  refine ⟨UMemL.extSz_refl _ _, UMemL.umMapped_zero _ _, ?_, Nat.le_refl _, ?_, ?_⟩
  · intro j hj; simp [initial] at hj
  · cases dir <;> simp [initial, imageAfter, UMemL.viewFaulted_self, UMemL.umemWrite_nil]
  · intro _; rfl

theorem invariant_step {dir : Direction} {sz a : BitVec 64}
    {P : UPtd} {M : Image} {ke : Nat} {s t : State}
    (hi : Invariant dir sz a P M ke s) (hs : Step dir sz a s t) :
    Invariant dir sz a P M ke t := by
  cases hs with
  | fault Q ke' he hk =>
    refine ⟨UMemL.extSz_trans hi.extension he,
      UMemL.umMapped_ext he.1 hi.mapped,
      fun j hj => permission_mono dir he.1 (hi.access j hj),
      Nat.le_trans hi.lend hk, ?_, ?_⟩
    · change viewFaulted s.table Q s.image = _
      rw [hi.memory]
      cases dir with
      | read => exact UMemL.viewFaulted_trans M hi.extension.1 he.1
      | write =>
        dsimp [imageAfter]
        rw [UMemL.viewFaulted_umemWrite _ _ _ hi.mapped,
          UMemL.viewFaulted_trans M hi.extension.1 he.1]
        rfl
    · intro hr
      subst dir
      change s.copied = umemRead (viewFaulted s.table Q s.image) a.toNat s.copied.length
      rw [read_viewFaulted _ _ _ _ _ hi.mapped]
      exact hi.read rfl
  | chunk bs hp hpage hm ha hr =>
    refine ⟨hi.extension, ?_, ?_, hi.lend, ?_, ?_⟩
    · simpa [transfer] using UMemL.umMapped_append hi.mapped hm
    · intro j hj
      change j < (s.copied ++ bs).length at hj
      rw [List.length_append] at hj
      by_cases hj0 : j < s.copied.length
      · exact hi.access j hj0
      · have h := ha (j - s.copied.length) (by omega)
        simpa only [transfer, Nat.add_sub_cancel' (by omega : s.copied.length ≤ j)] using h
    · change imageAfter dir s.image (a.toNat + s.copied.length) bs = _
      rw [hi.memory]
      cases dir with
      | read => rfl
      | write => exact (UMemL.umemWrite_append _ _ _ _).symm
    · intro hdir
      subst dir
      change s.copied ++ bs = umemRead s.image a.toNat (s.copied ++ bs).length
      rw [List.length_append, UMemL.umemRead_append]
      rw [← hi.read rfl, ← hr rfl]

/-- Whole-loop certificate, independent of the number of pages, allocation
faults, and transfers (including one-byte string-loop transfers). -/
theorem trace_certificate {dir : Direction} {sz a : BitVec 64}
    {P : UPtd} {M : Image} {ke : Nat} {s : State}
    (h : Trace dir sz a (initial P M ke) s) : Invariant dir sz a P M ke s := by
  induction h with
  | refl => exact invariant_initial _ _ _ _ _ _
  | snoc _ hs ih => exact invariant_step ih hs

end Experiments.WholeFunction.Copy
