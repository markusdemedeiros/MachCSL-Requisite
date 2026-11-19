import Experiments.WholeFunction.StackCells

/-! Pure cell-list algebra for derived stack frames. A sparse slot/register
map overwrites only saved values; arbitrary padding and every address survive.
These definitions describe expected resources, not another machine evaluator. -/
namespace Xv6.WholeFunction.FrameDerive
open MachCSL

/-- Change a slot's contents while retaining its address. As with `List.set`,
an out-of-bounds write leaves the list unchanged; safety is checked separately. -/
def writeCell (cells : List Stack.Cell) (slot : Nat) (value : BitVec 64) : List Stack.Cell :=
  cells.set slot ((cells[slot]?.getD (0#64, 0#64)).1, value)

/-- Expected saved resources for an arbitrary sparse frame layout. -/
def savedCells (slots : List (Nat × BitVec 5)) (entry : KCtx)
    (cells : List Stack.Cell) : List Stack.Cell :=
  slots.foldl (fun cells item => writeCell cells item.1 (entry.regs item.2)) cells

@[simp] theorem writeCell_length (cells : List Stack.Cell) (slot : Nat) (value : BitVec 64) :
    (writeCell cells slot value).length = cells.length := by
  simp [writeCell]

@[simp] theorem writeCell_shape (cells : List Stack.Cell) (slot : Nat) (value : BitVec 64) :
    (writeCell cells slot value).map Prod.fst = cells.map Prod.fst := by
  induction cells generalizing slot with
  | nil => simp [writeCell]
  | cons c cells ih =>
    cases slot with
    | zero => simp [writeCell]
    | succ slot => simpa [writeCell] using congrArg (List.cons c.1) (ih slot)

theorem writeCell_get_same (cells : List Stack.Cell) (slot : Nat) (c : Stack.Cell)
    (value : BitVec 64) (lookup : cells[slot]? = some c) :
    (writeCell cells slot value)[slot]? = some (c.1, value) := by
  simp [writeCell, lookup, List.getElem?_set_self (List.getElem?_eq_some_iff.mp lookup).1]

theorem writeCell_get_ne (cells : List Stack.Cell) (slot other : Nat)
    (value : BitVec 64) (different : slot ≠ other) :
    (writeCell cells slot value)[other]? = cells[other]? := by
  simp [writeCell, List.getElem?_set_ne different]

@[simp] theorem savedCells_nil (entry : KCtx) (cells : List Stack.Cell) :
    savedCells [] entry cells = cells := rfl

@[simp] theorem savedCells_cons (item : Nat × BitVec 5) (slots : List (Nat × BitVec 5))
    (entry : KCtx) (cells : List Stack.Cell) :
    savedCells (item :: slots) entry cells =
      savedCells slots entry (writeCell cells item.1 (entry.regs item.2)) := rfl

theorem savedCells_append (left right : List (Nat × BitVec 5)) (entry : KCtx)
    (cells : List Stack.Cell) :
    savedCells (left ++ right) entry cells = savedCells right entry (savedCells left entry cells) := by
  simp [savedCells, List.foldl_append]

@[simp] theorem savedCells_length (slots : List (Nat × BitVec 5)) (entry : KCtx)
    (cells : List Stack.Cell) : (savedCells slots entry cells).length = cells.length := by
  induction slots generalizing cells with
  | nil => rfl
  | cons item slots ih => simp [ih]

@[simp] theorem savedCells_shape (slots : List (Nat × BitVec 5)) (entry : KCtx)
    (cells : List Stack.Cell) : (savedCells slots entry cells).map Prod.fst = cells.map Prod.fst := by
  induction slots generalizing cells with
  | nil => rfl
  | cons item slots ih => simp [ih]

/-- Padding is byte-for-byte unchanged, even for a noncontiguous save map. -/
theorem savedCells_get_untouched (slots : List (Nat × BitVec 5)) (entry : KCtx)
    (cells : List Stack.Cell) (slot : Nat) (absent : slot ∉ slots.map Prod.fst) :
    (savedCells slots entry cells)[slot]? = cells[slot]? := by
  induction slots generalizing cells with
  | nil => rfl
  | cons item slots ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at absent
    rw [savedCells_cons, ih _ absent.2, writeCell_get_ne _ _ _ _ (Ne.symm absent.1)]

/-- Unique saved slots contain exactly the corresponding entry register.
No restriction is imposed on unrelated slots or their original values. -/
theorem savedCells_get_saved (slots : List (Nat × BitVec 5)) (entry : KCtx)
    (cells : List Stack.Cell) (slot : Nat) (reg : BitVec 5) (c : Stack.Cell)
    (unique : (slots.map Prod.fst).Nodup) (member : (slot, reg) ∈ slots)
    (lookup : cells[slot]? = some c) :
    (savedCells slots entry cells)[slot]? = some (c.1, entry.regs reg) := by
  induction slots generalizing cells with
  | nil => simp at member
  | cons item slots ih =>
    simp only [List.map_cons, List.nodup_cons] at unique
    rcases List.mem_cons.mp member with equal | member
    · subst item
      rw [savedCells_cons, savedCells_get_untouched _ _ _ _ unique.1]
      exact writeCell_get_same cells slot c _ lookup
    · have different : item.1 ≠ slot := by
        intro equal
        apply unique.1
        rw [equal]
        exact List.mem_map.mpr ⟨(slot, reg), member, rfl⟩
      rw [savedCells_cons]
      apply ih _ unique.2 member
      rw [writeCell_get_ne _ _ _ _ different]
      exact lookup

end Xv6.WholeFunction.FrameDerive
