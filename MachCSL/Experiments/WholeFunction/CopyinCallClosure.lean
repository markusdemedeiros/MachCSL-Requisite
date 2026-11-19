import Experiments.WholeFunction.CopyinCallFacts
import Experiments.WholeFunction.CopyinJoins

namespace Xv6.WholeFunction.Copyin
open MachCSL LeanRV64D
open Experiments.WholeFunction

theorem walk_call_good {i : Inputs} (valid : Valid i) {s t : State}
    (h : WalkCall i s) (step : WalkNext i (enter s KA.«walkaddr» 0x800016ee#64) t) : Good i t := by
  obtain ⟨R, rfl, saved, result⟩ := step
  have hs := saved_copy_regs saved
  have hc := h.toCommon.enter KA.«walkaddr» 0x800016ee#64
  apply walk_return_good
  · simp only [returnState, enter, KCtx.setReg_regs, RegMap.set_apply, ite_true]
    decide
  · exact hc.withRegs R _ hs
  · exact h.more
  · exact h.nowrap
  · exact (h.registers.of_saved (enter_saved s _ _)).of_saved hs
  · exact hs.page.trans ((enter_saved s _ _).page.trans h.pageReg)
  · exact result
  · have := valid.bound; omega

theorem fault_call_good {i : Inputs} (valid : Valid i) {s t : State}
    (h : FaultCall i s) (step : FaultNext i (enter s KA.«vmfault» 0x800016fc#64) t) : Good i t := by
  have fail := fun zero => FaultNext.failure step
    (show CopyCall.WalkPageResult (enter s KA.«vmfault» 0x800016fc#64).memory.table
      (cursor i (enter s KA.«vmfault» 0x800016fc#64)) 0#64 from
      ⟨fun _ => h.unreadable, fun impossible => False.elim (impossible rfl)⟩) zero
  have success := FaultNext.success step valid.size h.nowrap
    ((enter_regs s _ _ 12#5 (by decide)).trans h.a2)
  obtain ⟨spie, spp, R, memory, rfl, flags, saved, effect, copied, result⟩ := step
  have hs := saved_copy_regs saved
  have hc := h.toCommon.enter KA.«vmfault» 0x800016fc#64
  apply fault_return_good
  · simp only [returnState, enter, KCtx.setReg_regs, RegMap.set_apply, ite_true]
    decide
  · exact hc.faultReturn spie spp R memory hs effect copied flags
  · simpa only [returnState, copied, enter] using h.more
  · simpa only [cursor, returnState, copied, enter] using h.nowrap
  · change LoopRegs i memory.copied.length R
    rw [copied]
    exact (h.registers.of_saved (enter_saved s _ _)).of_saved hs
  · change R 19#5 = BitVec.ofNat 64 ((i.src.toNat + memory.copied.length) / 4096 * 4096)
    rw [copied]
    exact hs.page.trans ((enter_saved s _ _).page.trans h.pageReg)
  · exact fun zero => (fail zero).2.2
  · exact success
  · have := valid.bound; omega

theorem move_call_good {i : Inputs} (valid : Valid i) {s t : State} {w : BitVec 64}
    (h : MoveCall i s w)
    (step : ReadNext i (enter s KA.«memmove» 0x800016d4#64) (chunk i s) t) : Good i t := by
  obtain ⟨R, rfl, saved, _, effect⟩ := step
  have hs := saved_copy_regs saved
  have hc := h.toPage.toCommon.enter KA.«memmove» 0x800016d4#64
  apply move_return_good (d := s.memory.copied.length)
  · simp only [returnState, enter, KCtx.setReg_regs, RegMap.set_apply, ite_true]
    decide
  · exact hc.readReturn R (chunk i s) hs effect (chunk_facts _ _ _ h.more).2.1
  · simp only [returnState, readMemory, Copy.transfer, List.length_append,
      UMemL.umemRead_length, enter, chunk]
  · exact h.more
  · exact (h.registers.of_saved (enter_saved s _ _)).of_saved hs
  · exact hs.count.trans ((enter_saved s _ _).count.trans h.count)
  · exact hs.page.trans ((enter_saved s _ _).page.trans h.pageReg)
  · exact h.pageBound
  · have := valid.bound; omega

end Xv6.WholeFunction.Copyin
