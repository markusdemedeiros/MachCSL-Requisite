import Xv6.FsBytesInv
import Lean.Util.CollectAxioms

/-! Finite-map reconstruction for the byte/cache invariant. Lookup observations
are the sole interface: no map representation, list elements, or ownership
fractions are unfolded. Existing block splice and byte-range definitions remain
authoritative. -/
namespace Experiments.MapOverlay
open Xv6 Iris Iris.Std Iris.Std.PartialMap MachCSL

/-- A fitting list splice is precisely a left-biased byte-map overlay. This
one observation certificate handles the prefix, written range, and suffix. -/
theorem splice_overlay (base off : Nat) (xs ys : List (BitVec 8))
    (fit : off + ys.length ≤ xs.length) :
    isOverlay (mapSeq base (blkSplice off ys xs)) (mapSeq (base + off) ys) (mapSeq base xs) := by
  intro a
  cases hp : get? (mapSeq (base + off) ys) a <;>
    grind (ext := false) (splits := 24) only [mapSeq_get?, blkSplice_getElem?_lt,
    blkSplice_getElem?_mid, blkSplice_getElem?_ge, List.getElem?_eq_none_iff,
    List.getElem?_eq_some_iff, Option.orElse_some, Option.orElse_none]

/-- Transport a submap through the same overlay, without redoing range or
payload cases in each invariant field. -/
theorem overlay_transport (small large patch small' large' : RegMapF (BitVec 8))
    (hs : isOverlay small' patch small) (hl : isOverlay large' patch large)
    (sub : small ⊆ large) : small' ⊆ large' := by
  intro a v hv
  rw [hs a] at hv
  rw [hl a]
  cases hp : get? patch a with
  | none => simpa only [hp, Option.orElse_none] using sub a v (by simpa [hp] using hv)
  | some w => simpa only [hp, Option.orElse_some] using hv

/-- Exact replacement for the invariant's splice-submap obligation. -/
theorem splice_sub (L' L : RegMapF (BitVec 8)) (b off : Nat)
    (subNew bsOld : List (BitVec 8))
    (hov : isOverlay L' (mapSeq (b * BSZ + off) subNew) L)
    (hlbo : bsOld.length = BSIZE) (hoff : off + subNew.length ≤ BSIZE)
    (hbs : mapSeq (b * BSZ) bsOld ⊆ L) :
    mapSeq (b * BSZ) (blkSplice off subNew bsOld) ⊆ L' :=
  overlay_transport _ _ _ _ _ (splice_overlay _ _ _ _ (by omega)) hov hbs

/-- The patch has no key in another whole block. Arithmetic proves the
range separation; the source byte remains opaque. -/
theorem other_block_absent (b b' off : Nat) (subNew bs' : List (BitVec 8))
    (hlen : bs'.length = BSIZE) (fit : off + subNew.length ≤ BSIZE) (hne : b' ≠ b)
    (a : Nat) (v : BitVec 8) (present : get? (mapSeq (b' * BSZ) bs') a = some v) :
    get? (mapSeq (b * BSZ + off) subNew) a = none := by
  obtain ⟨hbase, hvalue⟩ := (mapSeq_get?_some _ _ _ _).1 present
  have hindex := (List.getElem?_eq_some_iff.1 hvalue).1
  rw [mapSeq_get?]
  split
  · apply List.getElem?_eq_none
    simp only [BSZ, BSIZE] at *
    omega
  · rfl

/-- Exact replacement for the invariant's untouched-block obligation. -/
theorem other_sub (L' L : RegMapF (BitVec 8)) (b b' off : Nat)
    (subNew bs' : List (BitVec 8))
    (hov : isOverlay L' (mapSeq (b * BSZ + off) subNew) L)
    (hlen' : bs'.length = BSIZE) (hoff : off + subNew.length ≤ BSIZE) (hne : b' ≠ b)
    (h : mapSeq (b' * BSZ) bs' ⊆ L) : mapSeq (b' * BSZ) bs' ⊆ L' := by
  intro a v hv
  rw [hov a, other_block_absent b b' off subNew bs' hlen' hoff hne a v hv]
  exact h a v hv

/-- Replacing existing keys changes values, not the authority's domain. -/
theorem overlay_domain (L' patch L : RegMapF (BitVec 8))
    (hov : isOverlay L' patch L)
    (covered : ∀ a v, get? patch a = some v → ∃ old, get? L a = some old) (a : Nat) :
    (∃ v, get? L' a = some v) ↔ ∃ v, get? L a = some v := by
  simp only [hov a]
  cases hp : get? patch a with
  | none => simp only [Option.orElse_none]
  | some v =>
    constructor
    · intro _; exact covered a v hp
    · intro _; exact ⟨v, rfl⟩

/-- Complete pure reconstruction at the real log-write boundary: update one
cache block and the corresponding byte-authority interval together. The
unchanged caller still supplies its ownership and invariant-opening proof. -/
theorem cache_splice (L' L : RegMapF (BitVec 8)) (C : BlockMap)
    (homeL : List Nat) (Xv : Nat → List (BitVec 8)) (b off : Nat)
    (subNew bsOld : List (BitVec 8))
    (hok : FsBytesOk L C [] homeL Xv) (entry : get? C b = some bsOld)
    (fit : off + subNew.length ≤ BSIZE)
    (hov : isOverlay L' (mapSeq (b * BSZ + off) subNew) L) :
    FsBytesOk L' (insert C b (blkSplice off subNew bsOld)) [] homeL Xv := by
  have hlen := hok.lens b bsOld entry
  have hwhole : mapSeq (b * BSZ) bsOld ⊆ L := hok.tie b bsOld entry (by simp)
  refine {
    dom := dom_insert_home C homeL b _ hok.dom ((hok.dom b).1 ⟨bsOld, entry⟩)
    lens := lens_insert C b _ hok.lens (by rw [blkSplice_length _ _ _ (by omega)]; exact hlen)
    tie := ?_
    bdom := ?_
    xsub := hok.xsub
    xval := by intro b' hb'; simp at hb' }
  · intro b' bs' hget _
    by_cases hb : b = b'
    · subst b'
      rw [LawfulPartialMap.get?_insert_eq rfl] at hget
      cases hget
      exact splice_sub L' L b off subNew bsOld hov hlen fit hwhole
    · rw [LawfulPartialMap.get?_insert_ne hb] at hget
      exact other_sub L' L b b' off subNew bs' hov (hok.lens b' bs' hget)
        fit (Ne.symm hb) (hok.tie b' bs' hget (by simp))
  · intro a
    apply Iff.trans (overlay_domain L' _ L hov ?_ a) (hok.bdom a)
    intro address value hv
    obtain ⟨hstart, hend⟩ := (mapSeq_isSome _ _ _).1 ⟨value, hv⟩
    obtain ⟨old, hold⟩ := (mapSeq_isSome (b * BSZ) bsOld address).2 ⟨by omega, by omega⟩
    exact ⟨old, hwhole address old hold⟩

end Experiments.MapOverlay
