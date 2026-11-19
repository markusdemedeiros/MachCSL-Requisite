import Experiments.SolverSurvey.Collections
import Xv6.UMemLemmas
import Xv6.ProofMemmove
import Xv6.ProofMemset
import Lean.Util.CollectAxioms

namespace MachCSL.Collections.Checks
open Xv6 Xv6.UMemL

theorem forward (bs olds : List (BitVec 8)) (i : Nat) (b : BitVec 8)
    (hb : bs[i]? = some b) (hl : olds.length = bs.length) :
    (mixF bs olds i).set i b = mixF bs olds (i + 1) := by
  collections_eq [mixF]

theorem backward (bs olds : List (BitVec 8)) (i : Nat) (hi : 1 ≤ i) (b : BitVec 8)
    (hb : bs[i - 1]? = some b) (hl : olds.length = bs.length) (hin : i ≤ bs.length) :
    (mixB bs olds i).set (i - 1) b = mixB bs olds (i - 1) := by
  collections_eq [mixB]

theorem fill (c : BitVec 8) (olds : List (BitVec 8)) (i : Nat) (hi : i < olds.length) :
    (mixS c olds i).set i c = mixS c olds (i + 1) := by
  collections_eq [mixS]

theorem write_inside (M : Nat → List (BitVec 8)) (va : Nat) (bs : List (BitVec 8)) (k off : Nat)
    (hlen : (M k).length = 4096) (hva : va = k * 4096 + off) (hfit : off + bs.length ≤ 4096) :
    umemWrite M va bs k = (M k).take off ++ (bs ++ (M k).drop (off + bs.length)) := by
  collections_eq [umemWrite]

theorem writes_append (M : Nat → List (BitVec 8)) (va : Nat) (bs1 bs2 : List (BitVec 8)) :
    umemWrite M va (bs1 ++ bs2) = umemWrite (umemWrite M va bs1) (va + bs1.length) bs2 := by
  funext k
  collections_eq [umemWrite]

theorem read_append (M : Nat → List (BitVec 8)) (va n1 n2 : Nat) :
    umemRead M va (n1 + n2) = umemRead M va n1 ++ umemRead M (va + n1) n2 := by
  collections_eq [umemRead]

theorem read_take (M : Nat → List (BitVec 8)) (va n m : Nat) (h : m ≤ n) :
    (umemRead M va n).take m = umemRead M va m := by
  collections_eq [umemRead]

-- Bounds and written values remain obligations, not tactic side assumptions.
example : True := by
  fail_if_success
    have wrong_byte : ([0] : List Nat).set 0 1 = [0] := by collections_eq []
  fail_if_success
    have wrong_length : ([0] : List Nat).take 1 = [0, 0] := by collections_eq []
  trivial

open Lean Elab Command in
/-- info: Collection checks: unchanged statements, standard axioms, independent proofs -/
#guard_msgs in
run_cmd do
  let standard := #[``propext, ``Classical.choice, ``Quot.sound]
  let pairs := #[( ``forward, ``Xv6.mixF_set), (``backward, ``Xv6.mixB_set),
    (``fill, ``Xv6.mixS_set), (``write_inside, ``Xv6.UMemL.umemWrite_in),
    (``writes_append, ``Xv6.UMemL.umemWrite_append),
    (``read_append, ``Xv6.UMemL.umemRead_append), (``read_take, ``Xv6.UMemL.umemRead_take)]
  let forbidden := pairs.map Prod.snd
  let env ← getEnv
  for (declaration, original) in pairs do
    let originalInfo ← getConstInfo original
    let newInfo ← getConstInfo declaration
    unless ← liftTermElabM <| Meta.isDefEq originalInfo.type newInfo.type do
      throwError "Changed statement: {declaration} vs {original}"
    let mut pending := #[declaration]
    let mut seen : NameSet := {}
    while !pending.isEmpty do
      let current := pending.back!
      pending := pending.pop
      unless seen.contains current do
        seen := seen.insert current
        if forbidden.contains current then
          throwError "Proof reuses an original result: {declaration}: {current}"
        if let some info := env.find? current then
          pending := pending ++ info.type.getUsedConstants
          if let some value := info.value? then
            pending := pending ++ value.getUsedConstants
    for ax in (← liftCoreM <| collectAxioms declaration) do
      unless standard.contains ax do
        throwError "Unexpected assumption in {declaration}: {ax}"
  logInfo "Collection checks: unchanged statements, standard axioms, independent proofs"

end MachCSL.Collections.Checks
