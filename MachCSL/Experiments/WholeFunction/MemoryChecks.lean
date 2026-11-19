import Experiments.WholeFunction.MemoryCompiler
import Experiments.WholeFunction.BinaryCopy

/-! Resource-boundary checks for byte execution. These use actual copyinstr
load/store rows and independently exercise fraction, address, and bounds checks. -/
namespace Xv6.WholeFunction.Memory.Checks
open Iris MachCSL LeanRV64D

def readByte : Op := .load 0#12 13#5 14#5 (by decide) (by decide)
def writeByte : Op := .store 0#12 15#5 13#5 (by decide) (by decide)

theorem actual_read : Binary.copyinstr_0ac.code = readByte.code := by binary_rfl
theorem actual_write : Binary.copyinstr_0b2.code = writeByte.code := by binary_rfl

/-- A wide load is not silently approximated by a byte access. -/
example : Op.decode (.LOAD (0#12, .Regidx 14#5, .Regidx 13#5, true, 8)) = none := rfl
/-- Hart-dependent addressing is rejected by this deliberately restricted engine. -/
example : Op.decode (.LOAD (0#12, .Regidx 4#5, .Regidx 13#5, true, 1)) = none := by decide

def sample (k : KCtx) (fraction : DFrac) : State :=
  ⟨⟨((k.setReg 14#5 0x1000#64).setReg 15#5 0x1000#64).setReg 13#5 0x1234#64,
    0x800017d6#64, []⟩,
    [⟨0x1000#64, fraction, [1#8,2#8]⟩, ⟨0x2000#64, .own 1, [99#8]⟩]⟩

theorem fractional_read (k : KCtx) :
    readByte.Enabled ⟨0,0⟩ (sample k (.own (1 : Qp).half)) := by
  refine ⟨⟨0x1000#64, .own (1 : Qp).half, [1#8,2#8]⟩, 1#8, rfl, rfl, ?_, trivial⟩
  simp [readByte, Op.address, sample, KCtx.rget_ne, KCtx.setReg_regs, RegMap.set_apply]

theorem reject_fractional_store (k : KCtx) :
    ¬ writeByte.Enabled ⟨0,0⟩ (sample k (.own (1 : Qp).half)) := by
  rintro ⟨buffer, byte, found, _, _, permission⟩
  have same : buffer = ⟨0x1000#64, .own (1 : Qp).half, [1#8,2#8]⟩ := by
    simpa [sample] using found.symm
  subst buffer
  change (DFrac.own (1 : Qp).half) = DFrac.own 1 at permission
  have halves := congrArg (fun q : Qp => q.val) (Qp.half_add_half 1)
  rw [DFrac.own.inj permission] at halves
  change (1 : Rat) + 1 = 1 at halves
  grind

theorem reject_out_of_bounds (k : KCtx) :
    ¬ readByte.Enabled ⟨0,2⟩ (sample k (.own 1)) := by
  rintro ⟨buffer, byte, found, lookup, _⟩
  have same : buffer = ⟨0x1000#64, .own 1, [1#8,2#8]⟩ := by
    simpa [sample] using found.symm
  subst buffer
  cases lookup

theorem reject_wrong_address (k : KCtx) :
    ¬ writeByte.Enabled ⟨0,1⟩ (sample k (.own 1)) := by
  rintro ⟨buffer, byte, found, _, address, _⟩
  have same : buffer = ⟨0x1000#64, .own 1, [1#8,2#8]⟩ := by
    simpa [sample] using found.symm
  subst buffer
  simp [writeByte, Op.address, sample, KCtx.rget_ne, KCtx.setReg_regs, RegMap.set_apply] at address

/-- Every byte store frames all other buffer descriptors, including their fractions. -/
theorem untouched_buffer (rvc : Bool) (cpu : CPU) (access : Access) (s t : State)
    (step : writeByte.Next rvc cpu access s t) (other : Nat) (ne : access.buffer ≠ other) :
    t.buffers[other]? = s.buffers[other]? := by
  obtain ⟨buffer, byte, _, _, rfl⟩ := step
  exact List.getElem?_set_ne ne

/-- The actual SB stores only the low byte and preserves the rest of both buffers. -/
theorem exact_store (k : KCtx) (cpu : CPU) (t : State)
    (step : writeByte.Next false cpu ⟨0,0⟩ (sample k (.own 1)) t) :
    t.buffers = [⟨0x1000#64, .own 1, [0x34#8,2#8]⟩, ⟨0x2000#64, .own 1, [99#8]⟩] := by
  obtain ⟨buffer, byte, found, _, rfl⟩ := step
  have same : buffer = ⟨0x1000#64, .own 1, [1#8,2#8]⟩ := by
    simpa [sample] using found.symm
  subst buffer
  simp [writeByte, Op.run, sample, KCtx.rget_ne, KCtx.setReg_regs, RegMap.set_apply]

end Xv6.WholeFunction.Memory.Checks

open Lean in
run_cmd do
  let baseline := (← collectAxioms ``Xv6.WholeFunction.FullPlan.transfer) ++
    (← collectAxioms ``MachCSL.wp_s_lbu) ++ (← collectAxioms ``MachCSL.wp_s_sb) ++
    (← collectAxioms ``MachCSL.wp_s_subw) ++
    (← collectAxioms ``MachCSL.wp_s_addw) ++ (← collectAxioms ``MachCSL.wp_s_branch0)
  for decl in #[``Xv6.WholeFunction.Memory.Op.sound, ``Xv6.WholeFunction.Memory.wp_memory] do
    let axioms ← collectAxioms decl
    let extra := axioms.filter (!baseline.contains ·)
    unless extra.isEmpty do throwError "Memory compiler introduced axioms: {extra}"
    if axioms.contains ``sorryAx then throwError "Memory compiler contains sorryAx"
  logInfo "Guarded memory compiler adds no axioms beyond existing production instruction rules."
