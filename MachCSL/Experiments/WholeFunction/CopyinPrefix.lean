import Experiments.WholeFunction.CopyinChunkFacts
import Experiments.WholeFunction.CopyinClosure
import Experiments.WholeFunction.MemoryPrefix

namespace Xv6.WholeFunction.Copyin
open MachCSL LeanRV64D
set_option maxHeartbeats 0

def atResult (s : State) (r : RegState) : State := ⟨⟨r.ctx,r.pc,s.machine.cells⟩,s.memory⟩

theorem common_result {i : Inputs} {s : State} (h : Common i s) (r : RegState)
    (context : r.ctx = s.machine.ctx.withRegs r.ctx.regs)
    (sp : r.ctx.regs 2#5 = s.machine.ctx.regs 2#5)
    (s11 : r.ctx.regs 27#5 = s.machine.ctx.regs 27#5) : Common i (atResult s r) := by
  have hc := common_reframe h r.ctx.regs r.pc sp s11
  simpa only [atResult,←context] using hc

/-- Compose a generated binary prefix with its semantic continuation. -/
theorem good_of_prefix {i : Inputs} {s : State} {pc : BitVec 64}
    {cut : BitVec 64 → Bool} (entry : s.machine.pc = pc)
    (pre : Symbolic.Prefix Binary.copyin.rows cut ⟨s.machine.ctx, pc⟩
      (fun r => Good i (atResult s r))) : Good i s := by
  obtain ⟨r, certificate, target⟩ := pre
  apply good_prefix (s := s) (t := atResult s r) (cut := cut) rfl rfl _ target
  simpa only [Stack.State.machine, atResult, entry] using certificate

theorem good_of_endpoint_prefix {i : Inputs} {s : State} {pc : BitVec 64}
    {cut : BitVec 64 → Bool} (entry : s.machine.pc = pc)
    (pre : Symbolic.Prefix Binary.copyin.rows cut ⟨s.machine.ctx, pc⟩
      (fun r => Endpoint i (atResult s r))) : Good i s := by
  obtain ⟨r, certificate, target⟩ := pre
  exact good_of_prefix entry ⟨r, certificate, good_of_endpoint target⟩

private theorem page_prefix {i : Inputs} {s : State} {w : BitVec 64}
    (h : Page i s w) (physical : s.machine.ctx.regs 10#5 = pte2pa w)
    (len64 : i.old.length < 2^64) :
    Symbolic.Prefix Binary.copyin.rows (fun pc => pc == 0x800016d0#64)
      ⟨s.machine.ctx,0x800016b8#64⟩ (fun r => MoveCall i (atResult s r) w) := by
  have selected := loop_selected_chunk i s.memory.copied.length s.machine.ctx.regs
    h.registers h.pageReg h.pageBound len64
  have source := loop_physical_source i s.memory.copied.length s.machine.ctx.regs w
    h.registers h.pageReg h.pageBound physical
  have zero : (0#12).signExtend 64 = 0#64 := rfl
  symbolic_prefix 9
  all_goals
    rename_i branch
    simp only [KCtx.setReg_regs, RegMap.set_apply, BitVec.reduceEq, ↓reduceIte,
      BitVec.zero_add, BitVec.add_zero, zero] at branch ⊢
    simp only [branch, ite_true, ite_false, Bool.false_eq_true, ↓reduceIte] at selected
    refine ⟨⟨?_, h.more, ?_, h.leaf, h.readable, h.pageBound, ?_⟩, rfl, ?_, ?_, ?_, ?_⟩
    · apply common_result h.toCommon
      · rfl
      · simp only [KCtx.setReg_regs, RegMap.set_apply, BitVec.reduceEq, ↓reduceIte]
      · simp only [KCtx.setReg_regs, RegMap.set_apply, BitVec.reduceEq, ↓reduceIte]
    · constructor
      all_goals simp only [atResult, KCtx.setReg_regs, RegMap.set_apply, BitVec.reduceEq, ↓reduceIte]
      · exact h.registers.src
      · exact h.registers.remaining
      · exact h.registers.dst
      · exact h.registers.pageSize
      · exact h.registers.root
      · exact h.registers.mask
      · exact h.registers.size
      · exact h.registers.faultMode
    · simp only [atResult, KCtx.setReg_regs, RegMap.set_apply, BitVec.reduceEq, ↓reduceIte]
      exact h.pageReg
    · simp only [atResult, chunk, KCtx.setReg_regs, RegMap.set_apply, BitVec.reduceEq, ↓reduceIte]
      exact selected
    · simp only [atResult, KCtx.setReg_regs, RegMap.set_apply, BitVec.reduceEq, ↓reduceIte]
      exact h.registers.dst
    · simp only [atResult, KCtx.setReg_regs, RegMap.set_apply, BitVec.reduceEq, ↓reduceIte]
      exact source
    · simp only [atResult, chunk, KCtx.setReg_regs, RegMap.set_apply, BitVec.reduceEq, ↓reduceIte]
      rw [selected]
      simpa only [zero, BitVec.add_zero, BitVec.zero_add] using
        chunk_sextw i.src.toNat s.memory.copied.length i.old.length h.more

theorem page_good {i : Inputs} {s : State} {w : BitVec 64}
    (pc : s.machine.pc = 0x800016b8#64)
    (h : Page i s w) (physical : s.machine.ctx.regs 10#5 = pte2pa w)
    (len64 : i.old.length < 2 ^ 64) : Good i s := by
  obtain ⟨r, certificate, target⟩ := page_prefix h physical len64
  exact good_of_endpoint_prefix pc ⟨r, certificate, .move w target⟩

end Xv6.WholeFunction.Copyin
