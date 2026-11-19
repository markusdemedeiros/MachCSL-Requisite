import Experiments.WholeFunction.StackActions

namespace Xv6.WholeFunction.Stack
open MachCSL LeanRV64D

/-- Compile supported stack instructions from the actual Sail AST. The frame
size is a function annotation. Offset and register proofs are checked; a
misaligned/out-of-range cell is still rejected by `Action.Enabled`.
-/
def Action.decode (slots : Nat) (i : instruction) : Option {a : Action // i = a.code} :=
  match i with
  | .ITYPE (imm, .Regidx 2#5, .Regidx 2#5, .ADDI) =>
    if h : imm.signExtend 64 = -(8#64 * BitVec.ofNat 64 slots) then
      some ⟨.push imm slots h, rfl⟩
    else if h : imm.signExtend 64 = 8#64 * BitVec.ofNat 64 slots then
      some ⟨.pop imm slots h, rfl⟩
    else none
  | .STORE (imm, .Regidx rs, .Regidx 2#5, 8) =>
    some ⟨.save imm rs (slots - 1 - imm.toNat / 8), rfl⟩
  | .LOAD (imm, .Regidx 2#5, .Regidx rd, false, 8) =>
    if h : rdOk rd then some ⟨.load imm rd (slots - 1 - imm.toNat / 8) h, rfl⟩ else none
  | _ => none

theorem shape_lookup (cells : List Cell) (sp : BitVec 64) (n i : Nat)
    (shape : cells.map Prod.fst = addresses sp n) (bound : i < n) :
    ∃ c, cells[i]? = some c ∧ c.1 = sp - 8#64 * BitVec.ofNat 64 (i + 1) := by
  have len : cells.length = n := by
    simpa [addresses] using congrArg List.length shape
  have hi : i < cells.length := by omega
  refine ⟨cells[i], List.getElem?_eq_getElem hi, ?_⟩
  have h := congrArg (fun xs => xs[i]?) shape
  simpa [addresses, List.getElem?_map, List.getElem?_range, bound, hi] using h

theorem shape_update (cells : List Cell) (i : Nat) (c : Cell) (value : BitVec 64)
    (lookup : cells[i]? = some c) :
    (cells.set i (c.1, value)).map Prod.fst = cells.map Prod.fst := by
  rw [List.map_set]
  have h : (cells.map Prod.fst)[i]? = some c.1 := by
    simp [List.getElem?_map, lookup]
  exact (List.getElem?_eq_some_iff.mp h).2 ▸
    List.set_getElem_self (List.getElem?_eq_some_iff.mp h).1

theorem Action.next_indices (a : Action) (rvc : Bool) (cpu : CPU) (s t : State)
    (step : a.Next rvc cpu s t) :
    t.ctx.sie = s.ctx.sie ∧ t.ctx.proc = s.ctx.proc := by
  cases a with
  | push imm n offset => obtain ⟨cells, _, rfl⟩ := step; exact ⟨rfl, rfl⟩
  | save imm rs i => obtain ⟨c, _, rfl⟩ := step; exact ⟨rfl, rfl⟩
  | load imm rd i valid => obtain ⟨c, _, rfl⟩ := step; exact ⟨rfl, rfl⟩
  | pop imm n offset => cases step; exact ⟨rfl, rfl⟩

end Xv6.WholeFunction.Stack
