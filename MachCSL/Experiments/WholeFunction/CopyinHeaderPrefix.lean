import Experiments.WholeFunction.CopyinPrefix

/-! The actual loop header establishes the walkaddr call boundary directly.
No intermediate register-state summary or instruction list is supplied. -/
namespace Xv6.WholeFunction.Copyin
open MachCSL LeanRV64D
set_option maxHeartbeats 0

theorem header_prefix {i : Inputs} {s : State} (h : Header i s) :
    Symbolic.Prefix Binary.copyin.rows (fun pc => pc == 0x800016ea#64)
      ⟨s.machine.ctx, 0x800016e2#64⟩ (fun r => WalkCall i (atResult s r)) := by
  have page : s.machine.ctx.regs 18#5 &&& s.machine.ctx.regs 24#5 =
      BitVec.ofNat 64 ((i.src.toNat + s.memory.copied.length) / 4096 * 4096) := by
    rw [h.registers.src, h.registers.mask]
    exact rounded_source i.src.toNat s.memory.copied.length h.nowrap
  symbolic_prefix 3
  refine ⟨?_, rfl, h.more, h.nowrap, ?_, ?_, ?_, ?_⟩
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
  · simpa [atResult, KCtx.setReg_regs, RegMap.set_apply] using page
  · simpa [atResult, KCtx.setReg_regs, RegMap.set_apply] using h.registers.root
  · simpa [atResult, KCtx.setReg_regs, RegMap.set_apply] using page

theorem header_prefix_good {i : Inputs} {s : State} (h : Header i s) : Good i s := by
  obtain ⟨result, certificate, ready⟩ := header_prefix h
  refine ⟨atResult s result, (fun pc => pc == 0x800016ea#64), rfl, rfl, ?_, .walk ready⟩
  simpa only [atResult, Stack.State.machine, h.pc] using certificate

end Xv6.WholeFunction.Copyin
