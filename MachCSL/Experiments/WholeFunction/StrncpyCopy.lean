import Experiments.WholeFunction.StrncpyModel
import Experiments.WholeFunction.MemoryPrefix

/-! Register prefixes between STRNCPY's semantic memory endpoints. Actual
binary rows determine all actions and intermediate states. -/
namespace Xv6.WholeFunction.Strncpy
open Iris Iris.BI Iris.ProgramLogic MachCSL LeanRV64D Memory StrncpyFacts
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0

theorem initial_good (i : Inputs) (valid : Valid i) : Good i (initial i) := by
  let s := initial i
  have common : Common i s i.old := ⟨rfl⟩
  have source : s.machine.ctx.regs 11#5 = i.src := by
    simp [s, initial, StrncpyFrame.initialMachine, Inputs.src, RegMap.set_apply]
  have count : s.machine.ctx.regs 12#5 = BitVec.ofNat 64 i.n := by
    simp [s, initial, StrncpyFrame.initialMachine, RegMap.set_apply, valid.arg]
  have arg : s.machine.ctx.regs 10#5 = i.dst := by
    simp [s, initial, StrncpyFrame.initialMachine, Inputs.dst, RegMap.set_apply]
  have compare := slt_zero i.n (by have := valid.bound; omega)
  have data : CopyData i i.old 0 := ⟨Nat.zero_le _, by simp, by simp [copied_zero]⟩
  have certified : Symbolic.Prefix bodyRows bodyCuts ⟨s.machine.ctx, 0x80000e2e#64⟩
      (fun r => Endpoint i (atResult s r)) := by
    by_cases zero : i.n = 0
    · symbolic_prefix 6
      all_goals simp_all [RegMap.set_apply, bcond]
      refine ⟨i.old, common.result _, .done rfl ?_⟩
      · exact ⟨valid.dstLength, Or.inl ⟨zero, rfl⟩⟩
    · have positive : 0 < i.n := by omega
      symbolic_prefix 6
      all_goals simp_all [RegMap.set_apply, bcond]
      refine ⟨i.old, common.result _, .read rfl 0 data positive ?_ ?_ ?_ ?_⟩
      all_goals simp [atResult, copyRegs, RegMap.set_apply, source, count, arg,
        addiw_dec i.n positive valid.bound]
      all_goals exact addiw_dec i.n positive valid.bound
  obtain ⟨r, certificate, endpoint⟩ := certified
  refine ⟨atResult s r, bodyCuts, rfl, ?_, endpoint⟩
  simpa only [Memory.residualView, atResult, Stack.State.machine, s, initial,
    StrncpyFrame.initialMachine] using certificate

theorem copy_good {i : Inputs} (valid : Valid i) {s : Memory.State}
    {dst : List (BitVec 8)} (common : Common i s dst)
    (pc : s.machine.pc = 0x80000e48#64) (j : Nat) (b : BitVec 8) (data : Written i dst j b)
    (regs : copyRegs i s.machine.ctx j)
    (cursor : s.machine.ctx.regs 15#5 = i.dst + BitVec.ofNat 64 (j + 1))
    (nextCount : s.machine.ctx.regs 13#5 = BitVec.ofNat 64 (i.n - (j + 1)))
    (padCount : s.machine.ctx.regs 16#5 = BitVec.ofNat 64 (i.n - (j + 1)))
    (value : s.machine.ctx.regs 14#5 = b.setWidth 64) : Good i s := by
  have source := regs.1
  have count := regs.2
  have bound := data.bound
  have compare := slt_zero (i.n - (j + 1)) (by have := valid.bound; omega)
  have certified : Symbolic.Prefix bodyRows bodyCuts ⟨s.machine.ctx, 0x80000e48#64⟩
      (fun r => Endpoint i (atResult s r)) := by
    by_cases nul : b = 0#8
    · subst b
      by_cases last : j + 1 = i.n
      · symbolic_prefix 8
        all_goals simp_all [RegMap.set_apply, bcond]
        refine ⟨dst, common.result _, .done rfl ?_⟩
        · exact (last ▸ data.pad).finished valid
      · have active : j + 1 < i.n := by omega
        have positive : 0 < i.n - (j + 1) := by omega
        symbolic_prefix 8
        all_goals simp_all [RegMap.set_apply, bcond]
        refine ⟨dst, common.result _, .padWrite rfl j (j + 1) data.pad active ?_ ?_⟩
        · simpa [atResult, RegMap.set_apply, cursor, count] using pad_w i.dst i.n j bound valid.bound
        · simp [atResult, RegMap.set_apply, cursor, BitVec.ofNat_add, BitVec.add_assoc]
    · by_cases last : j + 1 = i.n
      · symbolic_prefix 8
        all_goals simp_all [RegMap.set_apply, bcond, byte_zero]
        refine ⟨dst, common.result _, .done rfl ?_⟩
        · exact (last ▸ data.more nul).finish valid
      · have active : j + 1 < i.n := by omega
        have positive : 0 < i.n - (j + 1) := by omega
        have countBound : i.n - (j + 1) < 2 ^ 31 := by have := valid.bound; omega
        symbolic_prefix 8
        all_goals simp_all [RegMap.set_apply, bcond, byte_zero]
        refine ⟨dst, common.result _, .read rfl (j + 1) (data.more nul) active ?_ ?_ ?_ ?_⟩
        all_goals simp [atResult, copyRegs, RegMap.set_apply, source, nextCount, cursor,
          BitVec.ofNat_add, BitVec.add_assoc, addiw_dec (i.n - (j + 1)) positive countBound,
          Nat.sub_sub]
        all_goals
          have dec := addiw_dec (i.n - (j + 1)) positive countBound
          rw [Nat.sub_sub] at dec
          exact dec
  obtain ⟨r, certificate, endpoint⟩ := certified
  refine ⟨atResult s r, bodyCuts, rfl, ?_, endpoint⟩
  simpa only [Memory.residualView, atResult, Stack.State.machine, pc] using certificate

end Xv6.WholeFunction.Strncpy
