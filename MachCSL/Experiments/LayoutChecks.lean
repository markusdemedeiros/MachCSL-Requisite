import Xv6.DinodeSlot
import Xv6.ElfFile
import Lean.Util.CollectAxioms

namespace MachCSL.Layout
open Iris Iris.BI Xv6

/-- Relocation preserves both successful and out-of-bounds ELF reads. -/
theorem elfRead_relocate (pre payload : ElfBytes) (n : Nat) :
    elfRead (pre ++ payload) pre.length n = elfRead payload 0 n := by
  have hv : leAt (pre ++ payload) pre.length n = leAt payload 0 n := by
    unfold leAt leBytes
    congr 1
    apply List.map_congr_left
    intro j _
    simp only [Nat.zero_add, List.getElem!_eq_getElem?_getD]
    have h : (pre ++ payload)[pre.length + j]? = payload[j]? := by layout_lookup []
    rw [h]
  simp only [elfRead, List.length_append, Nat.zero_add, hv, Nat.add_le_add_iff_left]

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [CurCtx]

/-- A variable-sized prefix, a word and a tail, at any ownership fraction. -/
theorem word_field (a : BitVec 64) (dq : DFrac) (pre tail : List (BitVec 8)) (w : BitVec 32)
    (ha : (a + BitVec.ofNat 64 pre.length).toNat % 4 = 0) :
    byteBuf (GF := GF) a dq ((pre ++ wordToBytes4 w) ++ tail) ⊣⊢
      byteBuf a dq pre ∗ wordPointsTo (a + BitVec.ofNat 64 pre.length) 4 dq w ∗
        byteBuf (a + BitVec.ofNat 64 (pre.length + 4)) dq tail := by
  layout_resources [(fun a dq w h => BiEntails.to_eq (byteBuf_word4 (GF := GF) a dq w h))]

example (a : BitVec 64) (w : BitVec 32) : True := by
  fail_if_success
    have missing_alignment : byteBuf (GF := GF) a (DFrac.own 1) (wordToBytes4 w) ⊣⊢
        wordPointsTo a 4 (DFrac.own 1) w := by
      layout_resources [(fun a dq w h => BiEntails.to_eq (byteBuf_word4 (GF := GF) a dq w h))]
  fail_if_success
    have wrong_offset (pre tail : List Nat) (j : Nat) :
        (pre ++ tail)[pre.length + j + 1]? = tail[j]? := by layout_lookup []
  fail_if_success
    have changed_fraction (ha : a.toNat % 4 = 0) :
        byteBuf (GF := GF) a DFrac.discard (wordToBytes4 w) ⊣⊢ wordPointsTo a 4 (DFrac.own 1) w := by
      layout_resources [(fun a dq w h => BiEntails.to_eq (byteBuf_word4 (GF := GF) a dq w h))]
  trivial

open Lean Elab Command in
run_cmd do
  let mut allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for ax in (← liftCoreM <| collectAxioms ``elfRead_relocate) do
    unless allowed.contains ax do throwError "unexpected pure assumption: {ax}"
  allowed := allowed ++ (← liftCoreM <| collectAxioms ``byteBuf_word4)
  for decl in #[``word_field] do
    for ax in (← liftCoreM <| collectAxioms decl) do
      unless allowed.contains ax do throwError "unexpected assumption: {decl}: {ax}"

end MachCSL.Layout
