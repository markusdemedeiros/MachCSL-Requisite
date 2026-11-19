import Xv6.UMemLemmas

/-! Replay rules for inferred window borrowing. Prefixes and suffixes are
hidden in the linear closing wand, not exposed as client predicates. -/
namespace Experiments.ResourcePlanner
open Iris Iris.BI MachCSL
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [CurCtx]

theorem read_window (a : BitVec 64) (dq : DFrac) (bs : List (BitVec 8)) (off n : Nat)
    (bound : off + n ≤ bs.length) :
    byteBuf (GF := GF) a dq bs ⊢
      byteBuf (a + BitVec.ofNat 64 off) dq ((bs.drop off).take n) ∗
      (byteBuf (a + BitVec.ofNat 64 off) dq ((bs.drop off).take n) -∗ byteBuf a dq bs) := by
  iintro H
  icases Xv6.UMemL.byteBuf_split_td a dq bs off n bound $$ H with ⟨Hpre, Hwin, Hpost⟩
  isplitl [Hwin]
  · iexact Hwin
  · iintro Hwin
    have len : ((bs.drop off).take n).length = n := by
      simp only [List.length_take, List.length_drop]; omega
    ihave H := Xv6.UMemL.byteBuf_join_td a dq bs ((bs.drop off).take n) off n bound len
      $$ [$Hpre $Hwin $Hpost]
    rw [← List.drop_drop, List.take_append_drop, List.take_append_drop]
    iexact H

theorem write_window (a : BitVec 64) (bs : List (BitVec 8)) (off n : Nat)
    (bound : off + n ≤ bs.length) :
    byteBuf (GF := GF) a (DFrac.own 1) bs ⊢
      byteBuf (a + BitVec.ofNat 64 off) (DFrac.own 1) ((bs.drop off).take n) ∗
      (∀ new : List (BitVec 8), ⌜new.length = n⌝ -∗
        byteBuf (a + BitVec.ofNat 64 off) (DFrac.own 1) new -∗
        byteBuf a (DFrac.own 1) (bs.take off ++ (new ++ bs.drop (off + n)))) := by
  iintro H
  icases Xv6.UMemL.byteBuf_split_td a (DFrac.own 1) bs off n bound $$ H
    with ⟨Hpre, Hwin, Hpost⟩
  isplitl [Hwin]
  · iexact Hwin
  · iintro %new %len Hwin
    iapply Xv6.UMemL.byteBuf_join_td a (DFrac.own 1) bs new off n bound len
      $$ [$Hpre $Hwin $Hpost]

end Experiments.ResourcePlanner
