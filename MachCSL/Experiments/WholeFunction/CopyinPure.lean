import Experiments.WholeFunction.CopyContracts
import Xv6.CopyLemmas

/-! Pure arithmetic and memory-effect obligations for the generated full
copyin control flow. No production ProofCopyin declarations are imported.
The chunk selector is the actual page-remainder/minimum branch computation.
-/
namespace Xv6.WholeFunction.Copyin
open MachCSL LeanRV64D
open Experiments.WholeFunction.Copy

def chunkSize (a d len : Nat) : Nat := min (4096 - (a + d) % 4096) (len - d)

theorem chunk_facts (a d len : Nat) (hd : d < len) :
    0 < chunkSize a d len ∧ d + chunkSize a d len ≤ len ∧
      (a + d) % 4096 + chunkSize a d len ≤ 4096 ∧
      chunkSize a d len < 2 ^ 31 ∧
      (d + chunkSize a d len = len ∨
        (a + d) % 4096 + chunkSize a d len = 4096) := by
  have hm := Nat.mod_lt (a + d) (by decide : 0 < 4096)
  unfold chunkSize
  by_cases h : 4096 - (a + d) % 4096 ≤ len - d
  · rw [Nat.min_eq_left h]
    omega
  · rw [Nat.min_eq_right (by omega)]
    omega

/-- A non-final transfer consumes the remainder of a page, so the next
iteration has an aligned cursor. No global no-wrap hypothesis is needed:
the valid page address itself bounds the entire transferred chunk. -/
theorem next_cursor (a d len : Nat) (hd : d < len)
    (pageBound : (a + d) / 4096 * 4096 < 2 ^ 38)
    (more : d + chunkSize a d len < len) :
    d < d + chunkSize a d len ∧
      a + (d + chunkSize a d len) ≤ 2 ^ 38 ∧
      (a + (d + chunkSize a d len)) % 4096 = 0 := by
  obtain ⟨hp, _, _, _, hh⟩ := chunk_facts a d len hd
  have hfit : (a + d) % 4096 + chunkSize a d len = 4096 := by omega
  have he : a + (d + chunkSize a d len) = ((a + d) / 4096 + 1) * 4096 := by omega
  refine ⟨by omega, ?_, ?_⟩
  · omega
  · rw [he, Nat.mul_mod]
    simp

theorem wrapped_toNat (a : BitVec 64) (d : Nat) (h : a.toNat + d < 2 ^ 64) :
    (a + BitVec.ofNat 64 d).toNat = a.toNat + d := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  have hd : d < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt h]

theorem rounded_source (a d : Nat) (nowrap : a + d < 2 ^ 64) :
    BitVec.ofNat 64 (a + d) &&& 0xFFFFFFFFFFFFF000#64 =
      BitVec.ofNat 64 ((a + d) / 4096 * 4096) := by
  have mask (x : BitVec 64) : x &&& 0xFFFFFFFFFFFFF000#64 = (x >>> 12) <<< 12 := by
    change x &&& (BitVec.allOnes 64 <<< 12) = (x >>> 12) <<< 12
    apply BitVec.eq_of_getLsbD_eq
    intro j
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_allOnes,
      BitVec.getLsbD_ushiftRight]
    by_cases hj : j < 12
    · simp [hj]
    · have he : 12 + (j - 12) = j := by omega
      by_cases hb : j < 64
      · simp [hj, hb, he, show j - 12 < 64 by omega]
      · simp [hj, hb, he, BitVec.getLsbD_of_ge x j (by omega : 64 ≤ j)]
  rw [mask]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.reducePow, Nat.mod_eq_of_lt nowrap]

theorem page_readable_chunk (P : UPtd) (a : BitVec 64) (d n : Nat) (w : BitVec 64)
    (leaf : Iris.Std.PartialMap.get? P.um ((a.toNat + d) / 4096) = some w)
    (readable : pteVU w) (fit : (a.toNat + d) % 4096 + n ≤ 4096)
    (pageBound : (a.toNat + d) / 4096 * 4096 < 2 ^ 38) :
    ∀ j, j < n → uvaRmapped P (a + BitVec.ofNat 64 (d + j)).toNat := by
  intro j hj
  rw [wrapped_toNat a (d + j) (by omega)]
  exact ⟨(a.toNat + d) / 4096, w, (a.toNat + d) % 4096 + j,
    leaf, readable, by omega, by omega⟩

def readChunk (a : BitVec 64) (s : State) (n : Nat) : List (BitVec 8) :=
  umemRead s.image (a.toNat + s.copied.length) n

/-- The whole transfer effect is obtained from one mapped readable page;
the compiler does not supply a global prefix/image equation. -/
theorem readChunk_step (sz a : BitVec 64) (s : State) (n : Nat) (w : BitVec 64)
    (positive : 0 < n)
    (leaf : Iris.Std.PartialMap.get? s.table.um ((a.toNat + s.copied.length) / 4096) = some w)
    (readable : pteVU w) (fit : (a.toNat + s.copied.length) % 4096 + n ≤ 4096)
    (pageBound : (a.toNat + s.copied.length) / 4096 * 4096 < 2 ^ 38) :
    Step .read sz a s (transfer .read a s (readChunk a s n)) := by
  have hlen : (readChunk a s n).length = n := UMemL.umemRead_length ..
  apply Step.chunk
  · rwa [hlen]
  · rwa [hlen]
  · rw [hlen]
    exact UMemL.umMapped_page fit (by rw [leaf]; rfl)
  · rw [hlen]
    exact page_readable_chunk s.table a s.copied.length n w leaf readable fit pageBound
  · intro _
    rw [hlen]
    rfl

theorem readChunk_trace {sz a : BitVec 64} {P : UPtd} {M : Image} {ke : Nat}
    {s : State} (trace : Trace .read sz a (initial P M ke) s)
    (n : Nat) (w : BitVec 64) (positive : 0 < n)
    (leaf : Iris.Std.PartialMap.get? s.table.um ((a.toNat + s.copied.length) / 4096) = some w)
    (readable : pteVU w) (fit : (a.toNat + s.copied.length) % 4096 + n ≤ 4096)
    (pageBound : (a.toNat + s.copied.length) / 4096 * 4096 < 2 ^ 38) :
    Trace .read sz a (initial P M ke) (transfer .read a s (readChunk a s n)) :=
  .snoc trace (readChunk_step sz a s n w positive leaf readable fit pageBound)

/-- Registers updated after memmove use machine addition/subtraction;
the cursor/remaining-length annotations are canonical natural counts. -/
theorem chunk_register_updates (a dst : BitVec 64) (d n len : Nat)
    (bound : d + n ≤ len) (len64 : len < 2 ^ 64) :
    (a + BitVec.ofNat 64 d) + BitVec.ofNat 64 n = a + BitVec.ofNat 64 (d + n) ∧
    (dst + BitVec.ofNat 64 d) + BitVec.ofNat 64 n = dst + BitVec.ofNat 64 (d + n) ∧
    BitVec.ofNat 64 (len - d) - BitVec.ofNat 64 n = BitVec.ofNat 64 (len - (d + n)) := by
  refine ⟨by rw [BitVec.add_assoc, ← BitVec.ofNat_add],
    by rw [BitVec.add_assoc, ← BitVec.ofNat_add], ?_⟩
  rw [co_ofNat_sub (len - d) n (by omega) (by omega)]
  congr 1
  omega

end Xv6.WholeFunction.Copyin
