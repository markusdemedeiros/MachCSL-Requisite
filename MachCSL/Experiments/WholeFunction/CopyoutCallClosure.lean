import Experiments.WholeFunction.CopyoutCallFacts
import Experiments.WholeFunction.CopyoutPageJoins

namespace Xv6.WholeFunction.Copyout
open MachCSL LeanRV64D
open Experiments.WholeFunction

theorem walk_call_good {i : Inputs} (valid : Valid i) {s t : State}
    (h : WalkCall i s) (step : WalkNext i (enter s KA.«walkaddr» 0x80001626#64) t) : Good i t := by
  obtain ⟨R, rfl, saved, result⟩ := step
  have hs := Copyin.saved_copy_regs (saved_trans (enter_saved s _ _) saved)
  have hc := h.toCommon.enter KA.«walkaddr» 0x80001626#64
  apply walk_return_good
  · simp only [returnState, enter, KCtx.setReg_regs, RegMap.set_apply, ite_true]
    decide
  · exact hc.withRegs R _ saved
  · exact h.more
  · exact h.nowrap
  · exact (h.registers.of_saved (enter_saved s _ _)).of_saved saved
  · exact hs.count.trans h.pageReg
  · exact h.pageBound
  · exact result

theorem fault_call_good {i : Inputs} (valid : Valid i) {s t : State}
    (h : FaultCall i s) (step : FaultNext i (enter s KA.«vmfault» 0x80001636#64) t) : Good i t := by
  have fail := fun zero => FaultNext.failure step h.unreadable zero
  have success := FaultNext.success step valid.size h.nowrap
    ((enter_regs s _ _ 12#5 (by decide)).trans h.a2)
  obtain ⟨spie, spp, R, memory, rfl, flags, saved, effect, copied, result, wf⟩ := step
  have hs := Copyin.saved_copy_regs (saved_trans (enter_saved s _ _) saved)
  have hc := h.toCommon.enter KA.«vmfault» 0x80001636#64
  apply fault_return_good
  · simp only [returnState, enter, KCtx.setReg_regs, RegMap.set_apply, ite_true]
    decide
  · exact hc.faultReturn spie spp R memory saved effect copied wf flags
  · simpa only [returnState, copied, enter] using h.more
  · simpa only [cursor, returnState, copied, enter] using h.nowrap
  · change LoopRegs i memory.copied.length R
    rw [copied]
    exact (h.registers.of_saved (enter_saved s _ _)).of_saved saved
  · change R 9#5 = BitVec.ofNat 64 ((i.dst.toNat + memory.copied.length) / 4096 * 4096)
    rw [copied]
    exact hs.count.trans h.pageReg
  · simpa only [cursor, returnState, copied, enter] using h.pageBound
  · exact fun zero => (fail zero).2.2
  · exact success

theorem probe_call_good {i : Inputs} (valid : Valid i) {s t : State} {w : BitVec 64}
    (h : ProbeCall i s w) (step : ProbeNext i (enter s KA.«walk» 0x80001644#64) w t) : Good i t := by
  obtain ⟨R, rfl, saved, permission⟩ := step
  have hs := Copyin.saved_copy_regs (saved_trans (enter_saved s _ _) saved)
  have hc := h.toPage.toCommon.enter KA.«walk» 0x80001644#64
  apply probe_return_good
  · rfl
  · refine ⟨hc.withRegs R _ saved, h.more,
      (h.registers.of_saved (enter_saved s _ _)).of_saved saved,
      h.leaf, h.readable, h.pageBound, hs.count.trans h.pageReg, hs.page.trans h.physicalReg⟩
  · exact permission
  · have := valid.bound; omega

theorem move_call_good {i : Inputs} (valid : Valid i) {s t : State} {w : BitVec 64}
    (h : MoveCall i s w)
    (step : WriteNext i (enter s KA.«memmove» 0x80001608#64) (chunk i s) t) : Good i t := by
  obtain ⟨R, rfl, saved, _, effect⟩ := step
  have hs := Copyin.saved_copy_regs (saved_trans (enter_saved s _ _) saved)
  have hc := h.toPage.toCommon.enter KA.«memmove» 0x80001608#64
  have bound := (chunk_facts i.dst.toNat s.memory.copied.length i.bytes.length h.more).2.1
  have len : ((i.bytes.drop s.memory.copied.length).take (chunk i s)).length = chunk i s := by
    simp only [List.length_take, List.length_drop]
    change s.memory.copied.length + chunk i s ≤ i.bytes.length at bound
    omega
  apply move_return_good (d := s.memory.copied.length)
  · simp only [returnState, enter, KCtx.setReg_regs, RegMap.set_apply, ite_true]
    decide
  · exact hc.writeReturn R (chunk i s) saved effect bound
  · change (s.memory.copied ++ (i.bytes.drop s.memory.copied.length).take (chunk i s)).length = _
    rw [List.length_append, len]
    rfl
  · exact h.more
  · exact (h.registers.of_saved (enter_saved s _ _)).of_saved saved
  · exact hs.src.trans h.count
  · exact hs.count.trans h.pageReg
  · exact h.pageBound
  · have := valid.bound; omega

theorem probe_same_leaf {i : Inputs} {s : State} {w v : BitVec 64}
    (h : ProbeCall i s w) (ready : ProbeEnabled i (enter s KA.«walk» 0x80001644#64) v) : v = w := by
  have lookup := ready.lookup
  change Iris.Std.PartialMap.get? s.memory.table.um (vpnOf (s.machine.ctx.regs 11#5)).toNat = some v at lookup
  rw [h.a1, co_vpnOf_toNat _ (by rw [BitVec.toNat_ofNat]; have := h.pageBound; omega),
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := h.pageBound; omega)] at lookup
  have page : cursor i s / 4096 * 4096 / 4096 = cursor i s / 4096 := by omega
  rw [page, h.leaf] at lookup
  exact (Option.some.inj lookup).symm

end Xv6.WholeFunction.Copyout
