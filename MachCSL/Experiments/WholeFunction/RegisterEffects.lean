import Experiments.WholeFunction.KernelGraph

/-! Checked register effects over the existing action semantics. Masks describe
possible writes, not values or execution. They concern the unpinned register
map; in particular they do not assert that physical tp is invariant on migration.
-/
namespace Xv6.WholeFunction
open MachCSL LeanRV64D

abbrev RegMask := BitVec 32

namespace RegMask

def empty : RegMask := 0#32
def singleton (r : BitVec 5) : RegMask := BitVec.twoPow 32 r.toNat
def union (a b : RegMask) : RegMask := a ||| b
def Contains (mask : RegMask) (r : BitVec 5) : Prop := mask.getLsbD r.toNat = true
def Subset (a b : RegMask) : Prop := ∀ r, a.Contains r → b.Contains r

instance (mask : RegMask) (r : BitVec 5) : Decidable (mask.Contains r) :=
  inferInstanceAs (Decidable (_ = true))
instance (a b : RegMask) : Decidable (a.Subset b) :=
  inferInstanceAs (Decidable (∀ r, a.Contains r → b.Contains r))

@[simp] theorem contains_empty (r : BitVec 5) : ¬ empty.Contains r := by simp [Contains, empty]
@[simp] theorem contains_singleton (rd r : BitVec 5) : (singleton rd).Contains r ↔ r = rd := by
  have bound : rd.toNat < 32 := rd.isLt
  simp [Contains, singleton, BitVec.getLsbD_twoPow, bound, BitVec.toNat_inj, eq_comm]
@[simp] theorem contains_union (a b : RegMask) (r : BitVec 5) :
    (union a b).Contains r ↔ a.Contains r ∨ b.Contains r := by
  simp [Contains, union]

theorem subset_refl (a : RegMask) : a.Subset a := fun _ h => h
theorem subset_trans {a b c : RegMask} (ab : a.Subset b) (bc : b.Subset c) :
    a.Subset c := fun r h => bc r (ab r h)
theorem empty_subset (a : RegMask) : empty.Subset a := fun r h => False.elim (contains_empty r h)
theorem subset_union_left (a b : RegMask) : a.Subset (union a b) :=
  fun r h => (contains_union a b r).2 (Or.inl h)
theorem subset_union_right (a b : RegMask) : b.Subset (union a b) :=
  fun r h => (contains_union a b r).2 (Or.inr h)
theorem union_subset {a b c : RegMask} (ac : a.Subset c) (bc : b.Subset c) :
    (union a b).Subset c := by
  intro r h
  rcases (contains_union a b r).1 h with h | h
  · exact ac r h
  · exact bc r h
@[simp] theorem singleton_subset (rd : BitVec 5) (mask : RegMask) :
    (singleton rd).Subset mask ↔ mask.Contains rd := by
  simp [Subset]

end RegMask

/-- All non-register context fields agree; only the mask's registers may differ.
This is a logical relation on contexts, not an instruction execution relation. -/
structure CtxFrame (writes : RegMask) (before after : KCtx) : Prop where
  shape : after = before.withRegs after.regs
  unchanged : ∀ r, ¬ writes.Contains r → after.regs r = before.regs r

namespace CtxFrame
variable {W V : RegMask} {a b c : KCtx}

theorem refl (W : RegMask) (a : KCtx) : CtxFrame W a a := ⟨rfl, fun _ _ => rfl⟩
theorem lookup (h : CtxFrame W a b) (r : BitVec 5) (outside : ¬ W.Contains r) :
    b.regs r = a.regs r := h.unchanged r outside

theorem weaken (h : CtxFrame W a b) (bound : W.Subset V) : CtxFrame V a b :=
  ⟨h.shape, fun r outside => h.unchanged r (fun inside => outside (bound r inside))⟩

theorem trans (h : CtxFrame W a b) (step : CtxFrame W b c) : CtxFrame W a c := by
  constructor
  · calc c = b.withRegs c.regs := step.shape
         _ = a.withRegs c.regs := by rw [h.shape]; rfl
  · intro r outside
    exact (step.unchanged r outside).trans (h.unchanged r outside)

theorem trans_union (h : CtxFrame W a b) (step : CtxFrame V b c) :
    CtxFrame (RegMask.union W V) a c :=
  (h.weaken (RegMask.subset_union_left W V)).trans
    (step.weaken (RegMask.subset_union_right W V))

theorem symm (h : CtxFrame W a b) : CtxFrame W b a := by
  constructor
  · rw [h.shape]; rfl
  · exact fun r outside => (h.unchanged r outside).symm

theorem indices (h : CtxFrame W a b) : b.sie = a.sie ∧ b.proc = a.proc := by
  rw [h.shape]
  exact ⟨rfl, rfl⟩

theorem of_set (a : KCtx) (rd : BitVec 5) (value : BitVec 64) :
    CtxFrame (RegMask.singleton rd) a (a.setReg rd value) := by
  constructor
  · rfl
  · intro r outside
    have different : r ≠ rd := by simpa using outside
    simp [KCtx.setReg_regs, RegMap.set_apply, different]

theorem set (h : CtxFrame W a b) (rd : BitVec 5) (value : BitVec 64)
    (inside : W.Contains rd) : CtxFrame W a (b.setReg rd value) :=
  h.trans ((of_set b rd value).weaken ((RegMask.singleton_subset rd W).2 inside))

end CtxFrame

/-- Destinations come from the supported action selected by the real decoder. -/
def RegAction.writes : RegAction → RegMask
  | .addi _ rd _ _ | .addiw _ rd _ _ | .andi _ rd _ _ | .srli _ rd _ _
  | .add rd _ _ _ | .sub rd _ _ _ | .subw rd _ _ _ | .addw rd _ _ _
  | .and rd _ _ _ | .lui _ rd _ => RegMask.singleton rd
  | .branch .. | .jump .. | .ret .. => RegMask.empty

/-- Unlike canonical symbolic execution, preservation needs no hart-free
operand assumption: every possible hart value is confined to the destination. -/
theorem RegAction.run_frame (a : RegAction) (rvc : Bool) (cpu : CPU) (s : RegState) :
    CtxFrame a.writes s.ctx (a.run rvc cpu s).ctx := by
  cases a <;> first | exact CtxFrame.of_set _ _ _ | exact CtxFrame.refl _ _

/-- Completeness only for the existing supported action constructors. -/
theorem RegAction.decode_code (a : RegAction) : RegAction.decode a.code = some ⟨a, rfl⟩ := by
  cases a <;> simp [RegAction.code, RegAction.decode, *]

/-- A strict fold over actual row codes. Every row must be classified by the
supplied supported backend; an unknown row rejects the whole derivation. A
client combining register and memory backends supplies their tagged decoder. -/
def deriveRowWrites (decode : instruction → Option RegMask) : List Binary.Row → Option RegMask
  | [] => some RegMask.empty
  | row :: rows => do
    let head ← decode row.code
    let tail ← deriveRowWrites decode rows
    pure (RegMask.union head tail)

/-- Compact effect data accompanied by the strict derivation certificate. -/
structure RowEffects (decode : instruction → Option RegMask) (rows : List Binary.Row) where
  writes : RegMask
  checked : deriveRowWrites decode rows = some writes

/-- A successful derivation certifies every input row, not just rows visited
by one selected path. No control-flow reachability claim is needed. -/
theorem deriveRowWrites_covers {decode : instruction → Option RegMask}
    {rows : List Binary.Row} {W : RegMask} (checked : deriveRowWrites decode rows = some W)
    {row : Binary.Row} (member : row ∈ rows) :
    ∃ mask, decode row.code = some mask ∧ mask.Subset W := by
  induction rows generalizing W with
  | nil => simp at member
  | cons head rows ih =>
    cases hd : decode head.code with
    | none => simp [deriveRowWrites, hd] at checked
    | some headMask =>
      cases ht : deriveRowWrites decode rows with
      | none => simp [deriveRowWrites, hd, ht] at checked
      | some tailMask =>
        have eq : RegMask.union headMask tailMask = W := by
          simpa [deriveRowWrites, hd, ht] using checked
        subst W
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨headMask, hd, RegMask.subset_union_left _ _⟩
        · obtain ⟨mask, decoded, bound⟩ := ih ht member
          exact ⟨mask, decoded, RegMask.subset_trans bound (RegMask.subset_union_right _ _)⟩

theorem deriveRowWrites_contains {decode : instruction → Option RegMask}
    {rows : List Binary.Row} {W mask : RegMask} {row : Binary.Row}
    (checked : deriveRowWrites decode rows = some W) (member : row ∈ rows)
    (decoded : decode row.code = some mask) : mask.Subset W := by
  obtain ⟨mask', found, bound⟩ := deriveRowWrites_covers checked member
  have eq := Option.some.inj (decoded.symm.trans found)
  subst mask'
  exact bound

/-- Unknown register instructions remain unknown; they do not get empty masks. -/
def decodeRegWrites (code : instruction) : Option RegMask :=
  (RegAction.decode code).map (fun decoded => decoded.val.writes)

@[simp] theorem decodeRegWrites_code (action : RegAction) :
    decodeRegWrites action.code = some action.writes := by
  simp only [decodeRegWrites, RegAction.decode_code, Option.map_some]

/-- A caller may conservatively include every register row in a full binary,
without fixing the branch path or CPU used by this particular step. -/
theorem row_run_frame {rows : List Binary.Row} {W : RegMask}
    (checked : deriveRowWrites decodeRegWrites rows = some W)
    (row : Binary.Row) (member : row ∈ rows) (action : RegAction)
    (decoded : row.code = action.code) (cpu : CPU) (s : RegState) :
    CtxFrame W s.ctx (action.run row.rvc cpu s).ctx :=
  (action.run_frame row.rvc cpu s).weaken
    (deriveRowWrites_contains checked member (by rw [decoded, decodeRegWrites_code]))

namespace RegisterEffectsFrontend
open Lean Meta Elab Tactic

/-- Evaluate only the existing strict fold and replay its result definitionally.
Unsupported rows fail before any theorem is installed; no native evaluation
axiom or alternative decoder is involved. The stored mask is a compact literal. -/
elab "derive_effects" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← instantiateMVars (← goal.getType)
    let target := target.consumeMData
    unless target.isAppOfArity ``RowEffects 2 do
      throwError "derive_effects: expected RowEffects decoder rows"
    let args := target.getAppArgs
    let decoder := args[0]!
    let rows := args[1]!
    let computation ← mkAppM ``deriveRowWrites #[decoder, rows]
    if computation.hasFVar || computation.hasMVar then
      throwError "derive_effects: decoder and rows must be closed"
    let computed ← withTransparency .all <| whnf computation
    if computed.isAppOfArity ``Option.none 1 then
      throwError "derive_effects: unsupported row; the strict effect fold returned none"
    unless computed.isAppOfArity ``Option.some 2 do
      throwError "derive_effects: effect computation did not reduce to a closed option"
    let natural ← mkAppM ``BitVec.toNat #[computed.getAppArgs[1]!]
    let natural ← withTransparency .all <| reduce natural
    let some value ← getNatValue? natural
      | throwError "derive_effects: computed mask is not a closed numeral"
    let literal := mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 32) (mkNatLit value)
    let result ← mkAppM ``Option.some #[literal]
    unless ← withTransparency .all <| isDefEq computation result do
      throwError "derive_effects: computed mask did not pass definitional replay"
    let equation ← mkEq computation result
    let checked ← mkAuxTheorem equation (← mkEqRefl computation)
    let certificate ← mkAppM ``RowEffects.mk #[literal, checked]
    goal.assign certificate
    replaceMainGoal []

end RegisterEffectsFrontend

end Xv6.WholeFunction

open Lean in
run_cmd do
  for name in #[``Xv6.WholeFunction.CtxFrame.trans,
      ``Xv6.WholeFunction.CtxFrame.of_set,
      ``Xv6.WholeFunction.RegAction.run_frame,
      ``Xv6.WholeFunction.RegAction.decode_code,
      ``Xv6.WholeFunction.deriveRowWrites_covers,
      ``Xv6.WholeFunction.row_run_frame] do
    let extra := (← collectAxioms name).filter fun a =>
      !(#[``propext, ``Classical.choice, ``Quot.sound]).contains a
    unless extra.isEmpty do throwError "{name}: unexpected axioms {extra}"
  logInfo "Register effects: existing run semantics, all CPUs, standard axioms only."
