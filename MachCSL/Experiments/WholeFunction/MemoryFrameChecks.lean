import Experiments.WholeFunction.MemoryFrame
import Experiments.WholeFunction.StrlenFrameDefs
import Experiments.WholeFunction.StrncpyBinary

namespace Xv6.WholeFunction.Memory.FrameChecks
open MachCSL LeanRV64D
set_option maxHeartbeats 0

noncomputable def strlenBody := bodyRows Binary.strlen.rows
  (Binary.strlen_000 :: StrlenFrame.saveRows ++ StrlenFrame.returnRows)

theorem actual_body_mask : deriveRowWrites decodeWrites strlenBody = some 0xe400#32 := by
  binary_rfl

/-- The empty-string suffix is after the epilogue, but belongs to the body. -/
theorem retains_empty_suffix :
    (strlenBody.map Binary.Row.pc).contains 0x80000eca#64 = true ∧
    (strlenBody.map Binary.Row.pc).contains 0x80000ecc#64 = true := by
  constructor <;> binary_rfl

theorem actual_load_mask :
    deriveRowWrites decodeWrites [Binary.strlen_008] = some (RegMask.singleton 15#5) := by
  binary_rfl

theorem actual_store_mask :
    deriveRowWrites decodeWrites [Binary.strncpy_01e] = some RegMask.empty := by
  binary_rfl

theorem rejects_stack_push : deriveRowWrites decodeWrites [Binary.strlen_000] = none := by
  binary_rfl

theorem rejects_saved_stack_load : deriveRowWrites decodeWrites [Binary.strlen_020] = none := by
  binary_rfl

noncomputable def callRow : Binary.Row :=
  Binary.rowAt 0x800016d0#64 (by binary_rfl) (by binary_rfl)

theorem rejects_call : deriveRowWrites decodeWrites [callRow] = none := by
  binary_rfl

theorem rejects_unseparated_frame : deriveRowWrites decodeWrites Binary.strlen.rows = none := by
  binary_rfl

theorem rejects_understated_load_mask :
    deriveRowWrites decodeWrites [Binary.strlen_008] ≠ some RegMask.empty := by
  rw [actual_load_mask]
  decide

def readByte : Op := .load 0#12 15#5 10#5 (by decide) (by decide)
def writeByte : Op := .store 0#12 10#5 11#5 (by decide) (by decide)

theorem load_preserves_other_register (cpu : CPU) (s t : State) (access : Access)
    (step : readByte.Next false cpu access s t) (r : BitVec 5) (other : r ≠ 15#5) :
    t.machine.ctx.regs r = s.machine.ctx.regs r := by
  apply (readByte.next_frame false cpu access s t step).lookup r
  simpa [readByte, Op.writes] using other

/-- Stores can update the bytes while preserving the complete context and
saved-cell frame, independent of the selected CPU and buffer position. -/
theorem store_preserves_body_frame (initial : Stack.State) (s t : State)
    (frame : BodyFrame RegMask.empty initial s) (cpu : CPU) (access : Access)
    (step : writeByte.Next false cpu access s t) : BodyFrame RegMask.empty initial t :=
  frame.byte writeByte false cpu access (RegMask.subset_refl _) step

end Xv6.WholeFunction.Memory.FrameChecks

open Lean in
run_cmd do
  let baseline ← collectAxioms ``Xv6.WholeFunction.Memory.wp_memory
  let axioms ← collectAxioms ``Xv6.WholeFunction.Memory.wp_framed
  unless (axioms.filter (!baseline.contains ·)).isEmpty do
    throwError "Framed compiler adds axioms beyond the existing memory compiler"
  for decl in #[``Xv6.WholeFunction.Memory.Op.next_frame,
      ``Xv6.WholeFunction.Memory.FrameChecks.actual_body_mask,
      ``Xv6.WholeFunction.Memory.FrameChecks.store_preserves_body_frame] do
    let extra := (← collectAxioms decl).filter fun ax =>
      ![``propext, ``Quot.sound, ``Classical.choice].contains ax
    unless extra.isEmpty do throwError "Memory frame analysis added axioms: {extra}"
  logInfo "Strict actual-row memory frames: supported leaves only; no new compiler axioms."
