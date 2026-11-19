import Experiments.WholeFunction.StackDecode

namespace Xv6.WholeFunction.Stack
open MachCSL

/-- Pure validation of a slot action, independent of saved values or CPU. -/
def Action.FrameSafe (n : Nat) : Action → Prop
  | .save imm _ i | .load imm _ i _ =>
      i < n ∧ imm.signExtend 64 = 8#64 * BitVec.ofNat 64 (n - i - 1)
  | _ => False

instance (n : Nat) (a : Action) : Decidable (a.FrameSafe n) := by
  cases a <;> unfold Action.FrameSafe <;> infer_instance

def Shape (base : BitVec 64) (n : Nat) (s : State) : Prop :=
  s.ctx.sp = base - 8#64 * BitVec.ofNat 64 n ∧
    s.cells.map Prod.fst = addresses base n

theorem slot_offset (base : BitVec 64) (n i : Nat) (bound : i < n) :
    base - 8#64 * BitVec.ofNat 64 (i + 1) =
      (base - 8#64 * BitVec.ofNat 64 n) + 8#64 * BitVec.ofNat 64 (n - i - 1) := by
  have hn : n = (i + 1) + (n - i - 1) := by omega
  have hv : BitVec.ofNat 64 n = BitVec.ofNat 64 (i + 1) + BitVec.ofNat 64 (n - i - 1) := by
    rw [← BitVec.ofNat_add, ← hn]
  rw [hv]
  bv_omega

theorem Action.frame_enabled (a : Action) (base : BitVec 64) (n : Nat) (s : State)
    (safe : a.FrameSafe n) (shape : Shape base n s) : a.Enabled s := by
  cases a with
  | push => exact False.elim safe
  | pop => exact False.elim safe
  | save imm rs i =>
    obtain ⟨c, lookup, addr⟩ := shape_lookup s.cells base n i shape.2 safe.1
    exact ⟨c, lookup, by rw [addr, shape.1, safe.2]; exact slot_offset base n i safe.1⟩
  | load imm rd i valid =>
    obtain ⟨c, lookup, addr⟩ := shape_lookup s.cells base n i shape.2 safe.1
    exact ⟨c, lookup, by rw [addr, shape.1, safe.2]; exact slot_offset base n i safe.1⟩

theorem Action.frame_preserved (a : Action) (base : BitVec 64) (n : Nat)
    (rvc : Bool) (cpu : CPU) (s t : State)
    (safe : a.FrameSafe n) (shape : Shape base n s) (step : a.Next rvc cpu s t) :
    Shape base n t := by
  cases a with
  | push => exact False.elim safe
  | pop => exact False.elim safe
  | save imm rs i =>
    obtain ⟨c, lookup, rfl⟩ := step
    exact ⟨shape.1, (shape_update s.cells i c _ lookup).trans shape.2⟩
  | load imm rd i valid =>
    obtain ⟨c, _, rfl⟩ := step
    exact ⟨(KCtx.setReg_sp _ _ _ valid.2.1).trans shape.1, shape.2⟩

end Xv6.WholeFunction.Stack
