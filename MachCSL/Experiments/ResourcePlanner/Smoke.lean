import Experiments.ResourcePlanner.Planner
namespace Experiments.ResourcePlanner
open Iris Iris.BI MachCSL
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [CurCtx]
set_option resourcePlanner.trace true
example (a : BitVec 64) (q : DFrac) (bs : List (BitVec 8)) (i n : Nat)
    (bound : i+n ≤ bs.length) (F : IProp GF) :
    F ∗ byteBuf a q bs ⊢
      byteBuf (a + BitVec.ofNat 64 i) q ((bs.drop i).take n) ∗
      (byteBuf (a + BitVec.ofNat 64 i) q ((bs.drop i).take n) -∗ F ∗ byteBuf a q bs) := by
  resource_read
example (a : BitVec 64) (bs : List (BitVec 8)) (i n : Nat)
    (bound : i+n ≤ bs.length) (F : IProp GF) :
    F ∗ byteBuf a (DFrac.own 1) bs ⊢
      byteBuf (a + BitVec.ofNat 64 i) (DFrac.own 1) ((bs.drop i).take n) ∗
      (∀ new : List (BitVec 8), ⌜new.length = n⌝ -∗
        byteBuf (a + BitVec.ofNat 64 i) (DFrac.own 1) new -∗
        F ∗ byteBuf a (DFrac.own 1) (bs.take i ++ (new ++ bs.drop (i+n)))) := by
  resource_write_smt
end Experiments.ResourcePlanner
