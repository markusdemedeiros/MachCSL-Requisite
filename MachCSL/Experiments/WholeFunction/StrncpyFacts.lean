import Xv6.SpecStrncpy
import Xv6.FsWords
import Xv6.StepLemmas
import MachCSL.BvLemmas

/-! Pure prefix/padding and machine-arithmetic certificates for STRNCPY.
There is no import of the original function proof or any iteration adapter.
-/
namespace Xv6.WholeFunction.StrncpyFacts
open MachCSL LeanRV64D
set_option linter.unusedSimpArgs false

abbrev Bytes := List (BitVec 8)

def copied (src old : Bytes) (i : Nat) : Bytes := src.take i ++ old.drop i

def padded (src old : Bytes) (k j : Nat) : Bytes :=
  src.take k ++ List.replicate (j - k) 0#8 ++ old.drop j

theorem copied_zero (src old : Bytes) : copied src old 0 = old := by simp [copied]

theorem copied_length (src old : Bytes) (i : Nat) (ho : i ≤ old.length) (hs : i ≤ src.length) :
    (copied src old i).length = old.length := by simp [copied, Nat.min_eq_left hs]; omega

theorem copied_lookup (src old : Bytes) (i j : Nat) (hs : i ≤ src.length) :
    (copied src old i)[j]? = if j < i then src[j]? else old[j]? := by
  simp only [copied, List.getElem?_append, List.length_take, Nat.min_eq_left hs,
    List.getElem?_take, List.getElem?_drop]
  by_cases hj : j < i
  · simp [hj]
  · simp [hj, show i + (j - i) = j by omega]

theorem copied_get (src old : Bytes) (i j : Nat) (hj : j < i) (hs : i ≤ src.length) :
    (copied src old i)[j]? = src[j]? := by rw [copied_lookup _ _ _ _ hs, ite_eq_left hj]

theorem copied_set (src old : Bytes) (i : Nat) (b : BitVec 8)
    (hi : i < old.length) (hb : src[i]? = some b) :
    (copied src old i).set i b = copied src old (i + 1) := by
  have hs : i < src.length := (List.getElem?_eq_some_iff.mp hb).1
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_set, copied_lookup _ _ _ _ (by omega),
    copied_lookup _ _ _ _ (by omega), copied_length _ _ _ (by omega) (by omega)]
  by_cases he : i = j
  · subst j; simp [hi, hb]
  · by_cases hj : j < i <;> simp [he, hj, show (j < i + 1) ↔ (j < i) by omega]

theorem padded_length (src old : Bytes) (k j : Nat)
    (hkj : k ≤ j) (hjo : j ≤ old.length) (hks : k ≤ src.length) :
    (padded src old k j).length = old.length := by
  simp only [padded, List.length_append, List.length_take, Nat.min_eq_left hks,
    List.length_replicate, List.length_drop]
  omega

theorem padded_lookup (src old : Bytes) (k j x : Nat) (hkj : k ≤ j) (hks : k ≤ src.length) :
    (padded src old k j)[x]? =
      if x < k then src[x]? else if x < j then some 0#8 else old[x]? := by
  simp only [padded, List.getElem?_append, List.length_append, List.length_take,
    Nat.min_eq_left hks, List.length_replicate, List.getElem?_take,
    List.getElem?_replicate, List.getElem?_drop]
  by_cases hk : x < k
  · simp [hk, show x < k + (j - k) by omega]
  · by_cases hj : x < j
    · simp [hk, hj, show x < k + (j - k) by omega, show x - k < j - k by omega]
    · simp [hk, hj, show ¬ x < k + (j - k) by omega, show j + (x - (k + (j - k))) = x by omega]

theorem padded_get_before (src old : Bytes) (k j x : Nat)
    (hkj : k ≤ j) (hks : k ≤ src.length) (hx : x < k) :
    (padded src old k j)[x]? = src[x]? := by rw [padded_lookup _ _ _ _ _ hkj hks, ite_eq_left hx]

theorem padded_get_zero (src old : Bytes) (k j x : Nat)
    (hkj : k ≤ j) (hks : k ≤ src.length) (hxk : k ≤ x) (hxj : x < j) :
    (padded src old k j)[x]? = some 0#8 := by
  rw [padded_lookup _ _ _ _ _ hkj hks, ite_eq_right (by omega), ite_eq_left hxj]

theorem padded_set (src old : Bytes) (k j : Nat)
    (hkj : k ≤ j) (hjo : j < old.length) (hks : k ≤ src.length) :
    (padded src old k j).set j 0#8 = padded src old k (j + 1) := by
  apply List.ext_getElem?
  intro x
  rw [List.getElem?_set, padded_length _ _ _ _ hkj (by omega) hks,
    padded_lookup _ _ _ _ _ hkj hks, padded_lookup _ _ _ _ _ (by omega) hks]
  by_cases he : j = x
  · subst x; simp [hjo, show ¬ j < k by omega]
  · by_cases hk : x < k
    · simp [he, hk]
    · by_cases hx : x < j <;> simp [he, hk, hx, show (x < j + 1) ↔ (x < j) by omega]

theorem copied_nul (src old : Bytes) (k : Nat) (nul : src[k]? = some 0#8) :
    copied src old (k + 1) = padded src old k (k + 1) := by
  have hs : k < src.length := (List.getElem?_eq_some_iff.mp nul).1
  apply List.ext_getElem?
  intro x
  rw [copied_lookup _ _ _ _ (by omega), padded_lookup _ _ _ _ _ (by omega) (by omega)]
  by_cases hk : x < k
  · simp [hk, show x < k + 1 by omega]
  · by_cases he : x = k
    · subst x; simp [nul]
    · simp [hk, show ¬ x < k + 1 by omega]

theorem copied_post (src old : Bytes) (n : Nat) (hs : n ≤ src.length)
    (nonzero : ∀ j, j < n → src[j]? ≠ some 0#8) : sncPost src (copied src old n) n :=
  Or.inl ⟨nonzero, fun j hj => copied_get _ _ _ _ hj hs⟩

theorem padded_post (src old : Bytes) (k n : Nat) (hk : k < n)
    (nonzero : ∀ j, j < k → src[j]? ≠ some 0#8) (nul : src[k]? = some 0#8) :
    sncPost src (padded src old k n) n := by
  have hs : k < src.length := (List.getElem?_eq_some_iff.mp nul).1
  exact Or.inr ⟨k, hk, nonzero, nul,
    fun j hj => padded_get_before _ _ _ _ _ (by omega) (by omega) hj,
    fun j hjk hjn => padded_get_zero _ _ _ _ _ (by omega) (by omega) hjk hjn⟩

theorem E_add (x y : BitVec 64) :
    (x + y).extractLsb' 0 32 = x.extractLsb' 0 32 + y.extractLsb' 0 32 :=
  BitVec.extractLsb'_add (by decide)

theorem sext32 (m : Nat) (hm : m < 2 ^ 31) :
    ((BitVec.ofNat 64 m).extractLsb' 0 32).signExtend 64 = BitVec.ofNat 64 m := by
  rw [Xv6.extractLsb'_ofNat64 m (by omega), MachCSL.signExtend_ofNat32 m hm]

theorem addiw_dec (m : Nat) (h0 : 0 < m) (hm : m < 2 ^ 31) :
    ((BitVec.ofNat 64 m + (-1#64)).extractLsb' 0 32).signExtend 64 = BitVec.ofNat 64 (m - 1) := by
  have h : BitVec.ofNat 64 m + (-1#64) = BitVec.ofNat 64 (m - 1) := by bv_omega
  rw [h, sext32 (m - 1) (by omega)]

theorem slt_zero (m : Nat) (hm : m < 2 ^ 63) :
    BitVec.slt 0#64 (BitVec.ofNat 64 m) = decide (0 < m) := by
  have h0 : (0#64 : BitVec 64).toInt = 0 := by decide
  simp only [BitVec.slt, MachCSL.toInt_ofNat m hm, h0, decide_eq_decide]
  omega

theorem ite_blez {α : Type} (m : Nat) (hm : m < 2 ^ 63) (x y : α) :
    (if bcond .BGE 0#64 (BitVec.ofNat 64 m) then x else y) = if m = 0 then x else y := by
  simp only [bcond, slt_zero m hm]
  by_cases h : m = 0
  · subst m; simp
  · have hp : 0 < m := by omega
    simp [h, hp]

theorem ite_bgtz {α : Type} (m : Nat) (hm : m < 2 ^ 63) (x y : α) :
    (if bcond .BLT 0#64 (BitVec.ofNat 64 m) then x else y) = if m = 0 then y else x := by
  simp only [bcond, slt_zero m hm]
  by_cases h : m = 0
  · subst m; simp
  · have hp : 0 < m := by omega
    simp [h, hp]

theorem byte_zero (b : BitVec 8) : b.setWidth 64 = 0#64 ↔ b = 0#8 := by
  constructor
  · intro h; have := congrArg (BitVec.setWidth 8) h; simpa using this
  · intro h; subst b; rfl

theorem byte_extract (b : BitVec 8) : (b.setWidth 64).extractLsb' 0 8 = b := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, Nat.mod_eq_of_lt b.isLt]

theorem pad_w (dst : BitVec 64) (n i : Nat) (hi : i < n) (hn : n < 2 ^ 31) :
    BitVec.extractLsb' 0 32 (BitVec.signExtend 64 (BitVec.extractLsb' 0 32
      (BitVec.signExtend 64
        ((dst + BitVec.ofNat 64 (i + 1)).extractLsb' 0 32 +
          (BitVec.ofNat 64 (n - i)).extractLsb' 0 32) + (-1#64)))) =
      (dst + BitVec.ofNat 64 n).extractLsb' 0 32 := by
  rw [Xv6.fw_ext32, E_add, Xv6.fw_ext32, E_add, E_add,
    Xv6.extractLsb'_ofNat64 (i + 1) (by omega), Xv6.extractLsb'_ofNat64 (n - i) (by omega),
    Xv6.extractLsb'_ofNat64 n (by omega)]
  have negone : (-1#64).extractLsb' 0 32 = -1#32 := by decide
  rw [negone]
  generalize dst.extractLsb' 0 32 = D
  bv_omega

theorem subw_pad (w dst : BitVec 64) (n j : Nat) (hj : j ≤ n) (hn : n < 2 ^ 31)
    (hw : w.extractLsb' 0 32 = (dst + BitVec.ofNat 64 n).extractLsb' 0 32) :
    (w.extractLsb' 0 32 - (dst + BitVec.ofNat 64 j).extractLsb' 0 32).signExtend 64 =
      BitVec.ofNat 64 (n - j) := by
  rw [hw, E_add, E_add, Xv6.extractLsb'_ofNat64 n (by omega), Xv6.extractLsb'_ofNat64 j (by omega)]
  have h : dst.extractLsb' 0 32 + BitVec.ofNat 32 n -
      (dst.extractLsb' 0 32 + BitVec.ofNat 32 j) = BitVec.ofNat 32 (n - j) := by bv_omega
  rw [h, MachCSL.signExtend_ofNat32 (n - j) (by omega)]

end Xv6.WholeFunction.StrncpyFacts

open Lean in
run_cmd do
  let mut baseline : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for lemma in #[``Xv6.fw_ext32, ``Xv6.extractLsb'_ofNat64,
      ``MachCSL.signExtend_ofNat32, ``MachCSL.toInt_ofNat] do
    for ax in ← collectAxioms lemma do
      if !baseline.contains ax then baseline := baseline.push ax
  for lemma in #[``Xv6.WholeFunction.StrncpyFacts.copied_set,
      ``Xv6.WholeFunction.StrncpyFacts.padded_set,
      ``Xv6.WholeFunction.StrncpyFacts.copied_nul,
      ``Xv6.WholeFunction.StrncpyFacts.copied_post,
      ``Xv6.WholeFunction.StrncpyFacts.padded_post,
      ``Xv6.WholeFunction.StrncpyFacts.pad_w,
      ``Xv6.WholeFunction.StrncpyFacts.subw_pad] do
    let axioms ← collectAxioms lemma
    let extra := axioms.filter fun ax => !baseline.contains ax
    unless extra.isEmpty do throwError "{lemma}: new axioms {extra}"
    if axioms.contains ``sorryAx then throwError "{lemma}: contains sorryAx"
  logInfo "STRNCPY facts add no axioms beyond existing arithmetic lemmas."
