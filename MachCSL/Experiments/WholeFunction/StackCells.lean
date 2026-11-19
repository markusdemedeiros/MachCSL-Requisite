import Experiments.WholeFunction.Binary
import MachCSL.WpSmodeFrame

/-! A symbolic stack is a list of owned word cells, not one named assertion
per save register. Slot access and reassembly are proved once for arbitrary
lists. The address list is retained explicitly, so popping cannot silently
discard a missing, duplicated or relocated slot.
-/
namespace Xv6.WholeFunction.Stack
open Iris Iris.BI Iris.ProgramLogic MachCSL LeanRV64D

abbrev Cell := BitVec 64 × BitVec 64

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [CurCtx]

def owns (cells : List Cell) : IProp GF := iprop%
  [∗list] c ∈ cells, wordPointsTo c.1 8 (DFrac.own 1) c.2

def vacant (addresses : List (BitVec 64)) : IProp GF := iprop%
  [∗list] a ∈ addresses, ∃ w : BitVec 64, wordPointsTo a 8 (DFrac.own 1) w

def addresses (sp : BitVec 64) (n : Nat) : List (BitVec 64) :=
  (List.range n).map (fun i => sp - 8#64 * BitVec.ofNat 64 (i + 1))

theorem stack_vacant (sp : BitVec 64) (n : Nat) :
    stackOwn (GF := GF) sp n = vacant (addresses sp n) := by
  unfold stackOwn vacant addresses
  rw [BigSepL.bigSepL_map]

theorem vacant_values (addrs : List (BitVec 64)) :
    vacant (GF := GF) addrs ⊢ ∃ cells : List Cell,
      ⌜cells.map Prod.fst = addrs⌝ ∗ owns cells := by
  unfold vacant owns
  induction addrs with
  | nil =>
    iintro _
    iexists ([] : List Cell)
    isplit
    · ipureintro; rfl
    · iapply BigSepL.bigSepL_nil.mpr; itrivial
  | cons a addrs ih =>
    iintro ⟨⟨%w, Hw⟩, Htail⟩
    icases ih $$ Htail with ⟨%cells, %hshape, Hcells⟩
    iexists ((a, w) :: cells)
    isplit
    · ipureintro; simp [hshape]
    · iframe

theorem values_vacant (cells : List Cell) :
    owns (GF := GF) cells ⊢ vacant (cells.map Prod.fst) := by
  unfold owns vacant
  induction cells with
  | nil =>
    simp only [List.map_nil]
    iintro _
    iapply BigSepL.bigSepL_nil.mpr
    itrivial
  | cons c cells ih =>
    simp only [List.map_cons]
    iintro ⟨Hc, Hcells⟩
    isplitl [Hc]
    · iexists c.2; iexact Hc
    · iapply ih $$ Hcells

theorem stack_values (sp : BitVec 64) (n : Nat) :
    stackOwn (GF := GF) sp n ⊢ ∃ cells : List Cell,
      ⌜cells.map Prod.fst = addresses sp n⌝ ∗ owns cells := by
  rw [stack_vacant]
  exact vacant_values _

theorem values_stack (sp : BitVec 64) (n : Nat) (cells : List Cell)
    (shape : cells.map Prod.fst = addresses sp n) :
    owns (GF := GF) cells ⊢ stackOwn sp n := by
  rw [stack_vacant, ← shape]
  exact values_vacant cells

theorem cell_acc (cells : List Cell) (i : Nat) (c : Cell)
    (lookup : cells[i]? = some c) :
    owns (GF := GF) cells ⊢ wordPointsTo c.1 8 (DFrac.own 1) c.2 ∗
      (∀ v : BitVec 64, wordPointsTo c.1 8 (DFrac.own 1) v -∗
        owns (cells.set i (c.1, v))) := by
  unfold owns
  iintro H
  icases BigSepL.bigSepL_lookup_acc lookup |>.mp $$ H with ⟨Hc, Hclose⟩
  iframe Hc
  iintro %v Hv
  iapply Hclose $$ %(c.1, v) Hv

end Xv6.WholeFunction.Stack
