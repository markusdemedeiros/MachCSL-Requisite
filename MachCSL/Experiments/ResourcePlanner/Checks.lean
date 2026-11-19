import Experiments.ResourcePlanner.Planner
import Lean.Util.CollectAxioms
namespace Experiments.ResourcePlanner.Checks
open Iris Iris.BI MachCSL
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [CurCtx]
set_option resourcePlanner.trace true

/-- Genuine competing assignments: two fractional owners, two requested windows.
Neither source may be reused, even though their types are identical. -/
theorem competing (a : BitVec 64) (bs : List (BitVec 8)) (i j n : Nat)
    (firstBound : i+n ≤ bs.length) (secondBound : j+n ≤ bs.length) (F : IProp GF) :
    byteBuf a (DFrac.own (1 : Qp).half) bs ∗
      (F ∗ byteBuf a (DFrac.own (1 : Qp).half) bs) ⊢
      (byteBuf (a+BitVec.ofNat 64 j) (DFrac.own (1 : Qp).half) ((bs.drop j).take n) ∗
        byteBuf (a+BitVec.ofNat 64 i) (DFrac.own (1 : Qp).half) ((bs.drop i).take n)) ∗
      ((byteBuf (a+BitVec.ofNat 64 i) (DFrac.own (1 : Qp).half) ((bs.drop i).take n) ∗
        byteBuf (a+BitVec.ofNat 64 j) (DFrac.own (1 : Qp).half) ((bs.drop j).take n)) -∗
        (byteBuf a (DFrac.own (1 : Qp).half) bs ∗ byteBuf a (DFrac.own (1 : Qp).half) bs) ∗ F) := by
  resource_read_smt

/-- A real assignment bottleneck: request 0 can use either the whole
buffer or the existing window; request 1 can use only the whole buffer.
A greedy first-match choice fails; both planners must reserve that owner. -/
theorem competing_bottleneck (a : BitVec 64) (bs : List (BitVec 8)) (i j n : Nat)
    (firstBound : i+n ≤ bs.length) (secondBound : j+n ≤ bs.length) :
    byteBuf (GF := GF) a (DFrac.own (1 : Qp).half) bs ∗
      byteBuf (a+BitVec.ofNat 64 i) (DFrac.own (1 : Qp).half) ((bs.drop i).take n) ⊢
      (byteBuf (a+BitVec.ofNat 64 i) (DFrac.own (1 : Qp).half) ((bs.drop i).take n) ∗
        byteBuf (a+BitVec.ofNat 64 j) (DFrac.own (1 : Qp).half) ((bs.drop j).take n)) ∗
      ((byteBuf (a+BitVec.ofNat 64 j) (DFrac.own (1 : Qp).half) ((bs.drop j).take n) ∗
        byteBuf (a+BitVec.ofNat 64 i) (DFrac.own (1 : Qp).half) ((bs.drop i).take n)) -∗
        byteBuf a (DFrac.own (1 : Qp).half) bs ∗
          byteBuf (a+BitVec.ofNat 64 i) (DFrac.own (1 : Qp).half) ((bs.drop i).take n)) := by
  resource_read_smt

private def Loan (a : BitVec 64) (q : DFrac) (bs : List (BitVec 8)) (i n : Nat) : Prop :=
  byteBuf (GF := GF) a q bs ⊢
    byteBuf (a+BitVec.ofNat 64 i) q ((bs.drop i).take n) ∗
    (byteBuf (a+BitVec.ofNat 64 i) q ((bs.drop i).take n) -∗ byteBuf a q bs)

/-- The fallback assumption only closes the test declaration after both tactics
have been required to fail; it is not an axiom or an input rule for planning. -/
example (a : BitVec 64) (q : DFrac) (bs : List (BitVec 8)) (i n : Nat)
    (tooFar : bs.length < i+n) (fallback : Loan (GF := GF) a q bs i n) : Loan (GF := GF) a q bs i n := by
  unfold Loan
  fail_if_success resource_read
  fail_if_success resource_read_smt
  exact fallback

example (a : BitVec 64) (bs : List (BitVec 8)) (i n : Nat) (bound : i+n ≤ bs.length)
    (fallback : byteBuf (GF := GF) a (DFrac.own (1 : Qp).half) bs ⊢
      byteBuf (a+BitVec.ofNat 64 i) (DFrac.own 1) ((bs.drop i).take n) ∗
      (byteBuf (a+BitVec.ofNat 64 i) (DFrac.own 1) ((bs.drop i).take n) -∗
        byteBuf a (DFrac.own (1 : Qp).half) bs)) :
    byteBuf (GF := GF) a (DFrac.own (1 : Qp).half) bs ⊢
      byteBuf (a+BitVec.ofNat 64 i) (DFrac.own 1) ((bs.drop i).take n) ∗
      (byteBuf (a+BitVec.ofNat 64 i) (DFrac.own 1) ((bs.drop i).take n) -∗
        byteBuf a (DFrac.own (1 : Qp).half) bs) := by
  fail_if_success resource_read
  fail_if_success resource_read_smt
  exact fallback

example (a : BitVec 64) (bs : List (BitVec 8)) (i n m : Nat)
    (bound : i+n ≤ bs.length) (different : n < m)
    (fallback : byteBuf (GF := GF) a (DFrac.own 1) bs ⊢
      byteBuf (a+BitVec.ofNat 64 i) (DFrac.own 1) ((bs.drop i).take n) ∗
      (∀ new : List (BitVec 8), ⌜new.length = m⌝ -∗
        byteBuf (a+BitVec.ofNat 64 i) (DFrac.own 1) new -∗
        byteBuf a (DFrac.own 1) (bs.take i ++ (new ++ bs.drop (i+n))))) :
    byteBuf (GF := GF) a (DFrac.own 1) bs ⊢
      byteBuf (a+BitVec.ofNat 64 i) (DFrac.own 1) ((bs.drop i).take n) ∗
      (∀ new : List (BitVec 8), ⌜new.length = m⌝ -∗
        byteBuf (a+BitVec.ofNat 64 i) (DFrac.own 1) new -∗
        byteBuf a (DFrac.own 1) (bs.take i ++ (new ++ bs.drop (i+n)))) := by
  fail_if_success resource_write
  fail_if_success resource_write_smt
  exact fallback

example (a : BitVec 64) (bs : List (BitVec 8)) (i n : Nat) (bound : i+n ≤ bs.length)
    (fallback : byteBuf (GF := GF) a (DFrac.own 1) bs ⊢
      (byteBuf (a+BitVec.ofNat 64 i) (DFrac.own 1) ((bs.drop i).take n) ∗
        byteBuf (a+BitVec.ofNat 64 i) (DFrac.own 1) ((bs.drop i).take n)) ∗
      ((byteBuf (a+BitVec.ofNat 64 i) (DFrac.own 1) ((bs.drop i).take n) ∗
        byteBuf (a+BitVec.ofNat 64 i) (DFrac.own 1) ((bs.drop i).take n)) -∗ byteBuf a (DFrac.own 1) bs)) :
    byteBuf (GF := GF) a (DFrac.own 1) bs ⊢
      (byteBuf (a+BitVec.ofNat 64 i) (DFrac.own 1) ((bs.drop i).take n) ∗
        byteBuf (a+BitVec.ofNat 64 i) (DFrac.own 1) ((bs.drop i).take n)) ∗
      ((byteBuf (a+BitVec.ofNat 64 i) (DFrac.own 1) ((bs.drop i).take n) ∗
        byteBuf (a+BitVec.ofNat 64 i) (DFrac.own 1) ((bs.drop i).take n)) -∗ byteBuf a (DFrac.own 1) bs) := by
  fail_if_success resource_read
  fail_if_success resource_read_smt
  exact fallback

/-- A matching fractional destination still cannot be updated arbitrarily:
write replay requires full ownership, not merely an address/type match. -/
example (a : BitVec 64) (bs : List (BitVec 8)) (i n : Nat) (bound : i+n ≤ bs.length)
    (fallback : byteBuf (GF := GF) a (DFrac.own (1 : Qp).half) bs ⊢
      byteBuf (a+BitVec.ofNat 64 i) (DFrac.own (1 : Qp).half) ((bs.drop i).take n) ∗
      (∀ new : List (BitVec 8), ⌜new.length = n⌝ -∗
        byteBuf (a+BitVec.ofNat 64 i) (DFrac.own (1 : Qp).half) new -∗
        byteBuf a (DFrac.own (1 : Qp).half) (bs.take i ++ (new ++ bs.drop (i+n))))) :
    byteBuf (GF := GF) a (DFrac.own (1 : Qp).half) bs ⊢
      byteBuf (a+BitVec.ofNat 64 i) (DFrac.own (1 : Qp).half) ((bs.drop i).take n) ∗
      (∀ new : List (BitVec 8), ⌜new.length = n⌝ -∗
        byteBuf (a+BitVec.ofNat 64 i) (DFrac.own (1 : Qp).half) new -∗
        byteBuf a (DFrac.own (1 : Qp).half) (bs.take i ++ (new ++ bs.drop (i+n)))) := by
  fail_if_success resource_write
  fail_if_success resource_write_smt
  exact fallback

/-- Explicit current limitation: a valid split of one owner into two adjacent
windows is not yet inferred by the assignment planner. The ordinary Iris
proof below checks that this is a limitation, not an invalid request. -/
theorem split_tree_not_yet_planned (a : BitVec 64) (q : DFrac) (xs ys : List (BitVec 8)) :
    byteBuf (GF := GF) a q (xs++ys) ⊢
      (byteBuf a q xs ∗ byteBuf (a+BitVec.ofNat 64 xs.length) q ys) ∗
      ((byteBuf a q xs ∗ byteBuf (a+BitVec.ofNat 64 xs.length) q ys) -∗ byteBuf a q (xs++ys)) := by
  fail_if_success resource_read
  fail_if_success resource_read_smt
  iintro H
  ihave H := (byteBuf_append a q xs ys).1 $$ H
  isplitl [H]
  · iexact H
  · iintro H
    iapply (byteBuf_append a q xs ys).2 $$ H

/- A malicious solver suggests using one owner twice. Reject before replay;
the valid deterministic/normal-solver theorem still establishes this goal. -/
set_option resourcePlanner.solver "Experiments/ResourcePlanner/bad_solver.py" in
theorem corrupt_assignment_rejected (a : BitVec 64) (bs : List (BitVec 8)) (i j n : Nat)
    (firstBound : i+n ≤ bs.length) (secondBound : j+n ≤ bs.length) (F : IProp GF) :
    byteBuf a (DFrac.own (1 : Qp).half) bs ∗
      (F ∗ byteBuf a (DFrac.own (1 : Qp).half) bs) ⊢
      (byteBuf (a+BitVec.ofNat 64 j) (DFrac.own (1 : Qp).half) ((bs.drop j).take n) ∗
        byteBuf (a+BitVec.ofNat 64 i) (DFrac.own (1 : Qp).half) ((bs.drop i).take n)) ∗
      ((byteBuf (a+BitVec.ofNat 64 i) (DFrac.own (1 : Qp).half) ((bs.drop i).take n) ∗
        byteBuf (a+BitVec.ofNat 64 j) (DFrac.own (1 : Qp).half) ((bs.drop j).take n)) -∗
        (byteBuf a (DFrac.own (1 : Qp).half) bs ∗ byteBuf a (DFrac.own (1 : Qp).half) bs) ∗ F) := by
  fail_if_success resource_read_smt
  exact competing a bs i j n firstBound secondBound F

#print axioms competing
#print axioms split_tree_not_yet_planned
end Experiments.ResourcePlanner.Checks
