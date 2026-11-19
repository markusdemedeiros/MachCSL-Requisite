import Experiments.WholeFunction.RegisterEffects
import Experiments.WholeFunction.MemoryResidual

/-! Frame preservation for the register/byte-memory body compiler. Stack and
call plans are deliberately absent from the supported leaf interface: their
effects require separate contracts. Algorithm invariants do not carry copies
of unchanged registers or saved stack cells. -/
namespace Xv6.WholeFunction.Memory
open Iris Iris.BI Iris.ProgramLogic MachCSL LeanRV64D

def Op.writes : Op → RegMask
  | .load _ rd _ _ _ => RegMask.singleton rd
  | .store .. => RegMask.empty

theorem Op.run_frame (op : Op) (rvc : Bool) (cpu : CPU) (access : Access)
    (s : State) (buffer : Buffer) (byte : BitVec 8) :
    CtxFrame op.writes s.machine.ctx
      (op.run rvc cpu access s buffer byte).machine.ctx := by
  cases op with
  | load imm rd rs base valid => exact CtxFrame.of_set _ _ _
  | store imm rs rt base value => exact CtxFrame.refl _ _

theorem Op.next_frame (op : Op) (rvc : Bool) (cpu : CPU) (access : Access)
    (s t : State) (step : op.Next rvc cpu access s t) :
    CtxFrame op.writes s.machine.ctx t.machine.ctx := by
  obtain ⟨buffer, byte, _, _, rfl⟩ := step
  exact op.run_frame rvc cpu access s buffer byte

theorem Op.decode_code (op : Op) : Op.decode op.code = some ⟨op, rfl⟩ := by
  cases op <;> simp [Op.decode, Op.code, *]

/-- Metadata/register frame and saved stack cells are independent of the
algorithm's mutable byte buffers. The reference is the body-entry machine. -/
structure BodyFrame (writes : RegMask) (initial : Stack.State) (s : State) : Prop where
  context : CtxFrame writes initial.ctx s.machine.ctx
  cells : s.machine.cells = initial.cells

theorem BodyFrame.refl (writes : RegMask) (s : State) : BodyFrame writes s.machine s :=
  ⟨CtxFrame.refl _ _, rfl⟩

def FramedGood (writes : RegMask) (initial : Stack.State)
    (semantic : State → Prop) (s : State) : Prop :=
  semantic s ∧ BodyFrame writes initial s

/-- Remove the separately certified prologue/epilogue rows by address. This
keeps body suffixes placed after an epilogue, such as STRLEN's empty return. -/
def bodyRows (rows frameRows : List Binary.Row) : List Binary.Row :=
  rows.filter fun row => !(frameRows.any fun frame => frame.pc == row.pc)

/-- Only the ordinary register backend and byte-memory backend are admitted.
Calls, saved-stack actions and other widths remain explicit failures. -/
def decodeWrites (code : instruction) : Option RegMask :=
  match RegAction.decode code with
  | some a => some a.val.writes
  | none => (Op.decode code).map fun a => a.val.writes

theorem decodeWrites_reg (a : RegAction) : decodeWrites a.code = some a.writes := by
  simp [decodeWrites, RegAction.decode_code]

theorem decodeWrites_byte (a : Op) : decodeWrites a.code = some a.writes := by
  cases a <;> simp [decodeWrites, RegAction.decode, Op.code, Op.decode, *]

structure RegLeaf (rows : List Binary.Row) (edge : State → State → Prop) (s : State) where
  row : Binary.Row
  action : RegAction
  member : row ∈ rows
  address : s.machine.pc = row.pc
  decoded : row.code = action.code
  steps : ∀ cpu, edge s (regRun action row.rvc cpu s)

/-- This interface intentionally has no arbitrary `Memory.Plan.full` case.
An actual saved-stack instruction or call cannot acquire an exact body-frame
claim merely because its plan proves some unrelated semantic invariant. -/
inductive LeafPlan (rows : List Binary.Row) (edge : State → State → Prop) (s : State) where
  | reg (plan : RegLeaf rows edge s)
  | byte (plan : BytePlan edge s) (member : plan.row ∈ rows)

def residual_leaf {rows : List Binary.Row} {endpoint : State → Prop} {s : State}
    (good : ResidualGood rows endpoint s)
    (terminal : ∀ t, endpoint t → findReg t.machine.pc rows = none)
    (r : LocatedReg s.machine.pc) (found : findReg s.machine.pc rows = some r) :
    LeafPlan rows (fun _ t => ResidualGood rows endpoint t) s :=
  .reg ⟨r.row, r.action,
    (findMixed_sound 0 _ rows (Symbolic.mixed r)
      (Symbolic.findMixed_of_findReg 0 _ rows r found)).1,
    r.address, r.decoded, fun cpu => residual_reg good terminal r found cpu⟩

theorem BodyFrame.reg {writes : RegMask} {initial : Stack.State} {s : State}
    (frame : BodyFrame writes initial s) (a : RegAction) (rvc : Bool) (cpu : CPU)
    (covered : a.writes.Subset writes) : BodyFrame writes initial (regRun a rvc cpu s) :=
  ⟨frame.context.trans ((a.run_frame rvc cpu s.machine.machine).weaken covered), frame.cells⟩

theorem BodyFrame.byte {writes : RegMask} {initial : Stack.State} {s t : State}
    (frame : BodyFrame writes initial s) (a : Op) (rvc : Bool) (cpu : CPU) (access : Access)
    (covered : a.writes.Subset writes) (step : a.Next rvc cpu access s t) :
    BodyFrame writes initial t :=
  ⟨frame.context.trans ((a.next_frame rvc cpu access s t step).weaken covered),
    (a.next_cells rvc cpu access s t step).trans frame.cells⟩

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
variable [CurCtx] [KernelGeom] [KernelImage GF]

/-- Strengthening is performed once for every supported leaf, independently
of byte values, cursor arithmetic, loop phases or the selected CPU. -/
def LeafPlan.framed {rows : List Binary.Row} {writes : RegMask}
    (checked : deriveRowWrites decodeWrites rows = some writes)
    {initial : Stack.State} {semantic : State → Prop} {s : State}
    (frame : BodyFrame writes initial s) (plan : LeafPlan rows (fun _ t => semantic t) s) :
    Plan (GF := GF) (fun _ t => FramedGood writes initial semantic t) s := by
  cases plan with
  | reg p =>
    refine regPlan p.row p.action s _ p.address p.decoded fun cpu => ⟨p.steps cpu, ?_⟩
    apply frame.reg p.action p.row.rvc cpu
    exact deriveRowWrites_contains checked p.member (p.decoded ▸ decodeWrites_reg p.action)
  | byte p member =>
    refine .byte ⟨p.row, p.action, p.access, p.address, p.decoded, p.enabled, ?_⟩
    intro cpu t step
    refine ⟨p.steps cpu t step, frame.byte p.action p.row.rvc cpu p.access ?_ step⟩
    exact deriveRowWrites_contains checked member (p.decoded ▸ decodeWrites_byte p.action)

/-- Algorithm clients prove only semantic successor facts. Context metadata,
untouched registers, stack cells and WP indices are framed automatically. -/
theorem wp_framed (rows : List Binary.Row) (writes : RegMask)
    (checked : deriveRowWrites decodeWrites rows = some writes)
    (initial : Stack.State) (semantic cut : State → Prop)
    (compile : ∀ s, semantic s → ¬ cut s → LeafPlan rows (fun _ t => semantic t) s)
    (cpu : CPU) (s : State) (entry : FramedGood writes initial semantic s) :
    fullOwn State.machine (payload (GF := GF)) cpu s ∗
      wpNext initial.ctx.sie initial.ctx.proc cpu (fun cpu' => iprop(
        ∀ t, ⌜FramedGood writes initial semantic t⌝ -∗ ⌜cut t⌝ -∗
          fullOwn State.machine (payload (GF := GF)) cpu' t -∗ wpLoop cpu')) ⊢ wpLoop cpu := by
  exact wp_memory initial.ctx.sie initial.ctx.proc
    (FramedGood writes initial semantic) cut (fun _ t => FramedGood writes initial semantic t)
    ⟨fun _ _ _ _ step => step⟩
    (fun _ good => good.2.context.indices)
    (fun s good active => (compile s good.1 active).framed checked good.2)
    cpu s entry

end Xv6.WholeFunction.Memory
