import Experiments.WholeFunction.StrncpyModel
import Experiments.WholeFunction.MemoryPrefix

/-! One semantic join for the padding loop. The shared prefix compiler reads
SUBW, the conditional branch, and the cursor increment from the actual binary.
Only the next byte-write or return invariant is supplied here. -/
namespace Xv6.WholeFunction.Strncpy
open MachCSL LeanRV64D StrncpyFacts
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 8192

theorem pad_good {i : Inputs} (valid : Valid i) {s : Memory.State}
    {dst : List (BitVec 8)} (h : Common i s dst)
    (pc : s.machine.pc = 0x80000e5c#64) (k j : Nat) (data : PadData i dst k j)
    (endValue : (s.machine.ctx.regs 15#5).extractLsb' 0 32 =
      (i.dst + BitVec.ofNat 64 i.n).extractLsb' 0 32)
    (cursor : s.machine.ctx.regs 14#5 = i.dst + BitVec.ofNat 64 j) : Good i s := by
  have difference : ((s.machine.ctx.regs 15#5).extractLsb' 0 32 -
      (s.machine.ctx.regs 14#5).extractLsb' 0 32).signExtend 64 = BitVec.ofNat 64 (i.n-j) := by
    rw [cursor]
    exact subw_pad _ i.dst i.n j data.bound valid.bound endValue
  have bound : i.n - j < 2 ^ 63 := by have := valid.bound; omega
  have certified : Symbolic.Prefix bodyRows bodyCuts ⟨s.machine.ctx, 0x80000e5c#64⟩
      (fun r => Endpoint i (atResult s r)) := by
    by_cases done : j = i.n
    · have zero : i.n - j = 0 := by omega
      symbolic_prefix 3
      all_goals simp_all [RegMap.set_apply, bcond, slt_zero (i.n-j) bound]
      refine ⟨dst, h.result _, .done rfl ?_⟩
      · exact data.finished valid
    · have active : j < i.n := by have := data.bound; omega
      have positive : 0 < i.n - j := by omega
      symbolic_prefix 3
      all_goals simp_all [RegMap.set_apply, bcond, slt_zero (i.n-j) bound]
      refine ⟨dst, h.result _, .padWrite rfl k j data active ?_ ?_⟩
      · simpa [atResult, RegMap.set_apply] using endValue
      · simp [atResult, RegMap.set_apply, cursor, BitVec.ofNat_add, BitVec.add_assoc]
  obtain ⟨r, certificate, endpoint⟩ := certified
  refine ⟨atResult s r, bodyCuts, rfl, ?_, endpoint⟩
  simpa only [Memory.residualView, atResult, Stack.State.machine, pc] using certificate

end Xv6.WholeFunction.Strncpy
