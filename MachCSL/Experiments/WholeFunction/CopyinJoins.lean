import Experiments.WholeFunction.CopyinHeaderPrefix

namespace Xv6.WholeFunction.Copyin
open MachCSL LeanRV64D
set_option maxHeartbeats 0

private theorem walk_prefix {i : Inputs} {s : State}
    (pc : s.machine.pc = 0x800016ee#64)
    (hc : Common i s) (more : s.memory.copied.length < i.old.length)
    (nowrap : cursor i s < 2 ^ 64) (regs : LoopRegs i s.memory.copied.length s.machine.ctx.regs)
    (page : s.machine.ctx.regs 19#5 = BitVec.ofNat 64 (cursor i s / 4096 * 4096))
    (result : CopyCall.WalkPageResult s.memory.table (cursor i s) (s.machine.ctx.regs 10#5))
    (len64 : i.old.length < 2 ^ 64) :
    Symbolic.Prefix Binary.copyin.rows (fun p => p == 0x800016b8#64 || p == 0x800016f8#64)
      ⟨s.machine.ctx, 0x800016ee#64⟩ (fun r => (∃ w, PageReady i (atResult s r) w) ∨ FaultCall i (atResult s r)) := by
  symbolic_prefix 5
  all_goals simp only [BitVec.reduceSignExtend, BitVec.reduceAdd]
  · rename_i branch
    have nonzero : s.machine.ctx.regs 10#5 ≠ 0#64 := by simpa [bcond] using branch
    obtain ⟨w, leaf, readable, physical, bound⟩ := result.nonzero nonzero
    exact Or.inl ⟨w, ⟨⟨common_result hc _ rfl rfl rfl,
      more, regs, leaf, readable, bound, page⟩, rfl, physical⟩⟩
  · rename_i branch
    have zero : s.machine.ctx.regs 10#5 = 0#64 := by simpa [bcond] using branch
    apply Or.inr
    refine ⟨?_, rfl, more, nowrap, ?_, ?_, result.zero zero, ?_, ?_, ?_, ?_⟩
    · apply common_result hc
      · rfl
      · simp only [KCtx.setReg_regs, RegMap.set_apply, BitVec.reduceEq, ↓reduceIte]
      · simp only [KCtx.setReg_regs, RegMap.set_apply, BitVec.reduceEq, ↓reduceIte]
    · constructor
      all_goals simp only [atResult, KCtx.setReg_regs, RegMap.set_apply, BitVec.reduceEq, ↓reduceIte]
      · exact regs.src
      · exact regs.remaining
      · exact regs.dst
      · exact regs.pageSize
      · exact regs.root
      · exact regs.mask
      · exact regs.size
      · exact regs.faultMode
    · simp only [atResult, KCtx.setReg_regs, RegMap.set_apply, BitVec.reduceEq, ↓reduceIte]
      exact page
    · simp only [atResult, KCtx.setReg_regs, RegMap.set_apply, BitVec.reduceEq, ↓reduceIte, BitVec.zero_add]
      exact regs.root
    · simp only [atResult, KCtx.setReg_regs, RegMap.set_apply, BitVec.reduceEq, ↓reduceIte, BitVec.zero_add]
      exact regs.size
    · simp only [atResult, KCtx.setReg_regs, RegMap.set_apply, BitVec.reduceEq, ↓reduceIte, BitVec.zero_add]
      exact page
    · simp only [atResult, KCtx.setReg_regs, RegMap.set_apply, BitVec.reduceEq, ↓reduceIte, BitVec.zero_add]
      exact regs.faultMode

private theorem fault_prefix {i : Inputs} {s : State}
    (pc : s.machine.pc = 0x800016fc#64)
    (hc : Common i s) (more : s.memory.copied.length < i.old.length)
    (nowrap : cursor i s < 2 ^ 64) (regs : LoopRegs i s.memory.copied.length s.machine.ctx.regs)
    (page : s.machine.ctx.regs 19#5 = BitVec.ofNat 64 (cursor i s / 4096 * 4096))
    (failure : s.machine.ctx.regs 10#5 = 0#64 → ¬ uvaRmapped s.memory.table (cursor i s))
    (success : s.machine.ctx.regs 10#5 ≠ 0#64 → ∃ w,
      Iris.Std.PartialMap.get? s.memory.table.um (cursor i s / 4096) = some w ∧ pteVU w ∧
      s.machine.ctx.regs 10#5 = pte2pa w ∧ cursor i s / 4096 * 4096 < 2 ^ 38)
    (len64 : i.old.length < 2 ^ 64) :
    Symbolic.Prefix Binary.copyin.rows (fun p => p == 0x800016b8#64 || p == 0x80001704#64)
      ⟨s.machine.ctx, 0x800016fc#64⟩ (fun r => (∃ w, PageReady i (atResult s r) w) ∨ Exit i (atResult s r)) := by
  symbolic_prefix 3
  all_goals simp only [BitVec.reduceSignExtend, BitVec.reduceAdd]
  · rename_i branch
    have nonzero : s.machine.ctx.regs 10#5 ≠ 0#64 := by simpa [bcond] using branch
    obtain ⟨w, leaf, readable, physical, bound⟩ := success nonzero
    exact Or.inl ⟨w, ⟨⟨common_result hc _ rfl rfl rfl,
      more, regs, leaf, readable, bound, page⟩, rfl, physical⟩⟩
  · rename_i branch
    have zero : s.machine.ctx.regs 10#5 = 0#64 := by simpa [bcond] using branch
    apply Or.inr
    refine ⟨?_, rfl, Or.inr ⟨?_, s.memory.copied.length, more, ?_⟩⟩
    · apply common_result hc
      · rfl
      · simp only [KCtx.setReg_regs, RegMap.set_apply, BitVec.reduceEq, ↓reduceIte]
      · simp only [KCtx.setReg_regs, RegMap.set_apply, BitVec.reduceEq, ↓reduceIte]
    · rfl
    · rw [wrapped_toNat i.src s.memory.copied.length nowrap]
      exact failure zero

private theorem move_prefix {i : Inputs} {s : State} (pc : s.machine.pc = 0x800016d4#64)
    (hc : Common i s) (d : Nat)
    (copied : s.memory.copied.length = d + chunkSize i.src.toNat d i.old.length)
    (more : d < i.old.length) (regs : LoopRegs i d s.machine.ctx.regs)
    (count : s.machine.ctx.regs 9#5 = BitVec.ofNat 64 (chunkSize i.src.toNat d i.old.length))
    (page : s.machine.ctx.regs 19#5 = BitVec.ofNat 64 ((i.src.toNat + d) / 4096 * 4096))
    (pageBound : (i.src.toNat + d) / 4096 * 4096 < 2 ^ 38)
    (len64 : i.old.length < 2 ^ 64) :
    Symbolic.Prefix Binary.copyin.rows (fun p => p == 0x800016e2#64 || p == 0x80001704#64)
      ⟨s.machine.ctx, 0x800016d4#64⟩ (fun r => Header i (atResult s r) ∨ Exit i (atResult s r)) := by
  obtain ⟨_, bound, _, _, hcase⟩ := chunk_facts i.src.toNat d i.old.length more
  obtain ⟨_, destination, rem⟩ := chunk_register_updates i.src i.dst d
    (chunkSize i.src.toNat d i.old.length) i.old.length bound len64
  have remaining : s.machine.ctx.regs 20#5 - s.machine.ctx.regs 9#5 =
      BitVec.ofNat 64 (i.old.length - (d + chunkSize i.src.toNat d i.old.length)) := by
    rw [regs.remaining, count, rem]
  symbolic_prefix 5
  all_goals simp only [BitVec.reduceSignExtend, BitVec.reduceAdd]
  · rename_i branch
    simp only [KCtx.setReg_regs, RegMap.set_apply, BitVec.reduceEq, ↓reduceIte] at branch
    have zero : BitVec.ofNat 64 (i.old.length - (d + chunkSize i.src.toNat d i.old.length)) = 0#64 := by
      simpa only [bcond, beq_iff_eq, remaining] using branch
    have done : d + chunkSize i.src.toNat d i.old.length = i.old.length := by
      have hn := congrArg BitVec.toNat zero
      simp only [BitVec.toNat_ofNat, BitVec.toNat_zero] at hn
      omega
    apply Or.inr
    refine ⟨?_, rfl, Or.inl ⟨?_, copied.trans done⟩⟩
    · apply common_result hc
      · rfl
      · simp only [KCtx.setReg_regs, RegMap.set_apply, BitVec.reduceEq, ↓reduceIte]
      · simp only [KCtx.setReg_regs, RegMap.set_apply, BitVec.reduceEq, ↓reduceIte]
    · rfl
  · rename_i branch
    simp only [KCtx.setReg_regs, RegMap.set_apply, BitVec.reduceEq, ↓reduceIte] at branch
    have nonzero : BitVec.ofNat 64 (i.old.length - (d + chunkSize i.src.toNat d i.old.length)) ≠ 0#64 := by
      simpa only [bcond, beq_iff_eq, remaining] using branch
    have continuing : d + chunkSize i.src.toNat d i.old.length < i.old.length := by
      have notdone : d + chunkSize i.src.toNat d i.old.length ≠ i.old.length := by
        intro he
        apply nonzero
        rw [he, Nat.sub_self]
      omega
    obtain ⟨_, small, align⟩ := next_cursor i.src.toNat d i.old.length more pageBound continuing
    have advance : (i.src.toNat + d) / 4096 * 4096 + 4096 =
        i.src.toNat + (d + chunkSize i.src.toNat d i.old.length) := by omega
    apply Or.inl
    refine ⟨?_, rfl, ?_, ?_, Or.inr ?_, ?_⟩
    · apply common_result hc
      · rfl
      · simp only [KCtx.setReg_regs, RegMap.set_apply, BitVec.reduceEq, ↓reduceIte]
      · simp only [KCtx.setReg_regs, RegMap.set_apply, BitVec.reduceEq, ↓reduceIte]
    · simpa only [atResult, copied] using continuing
    · change i.src.toNat + s.memory.copied.length < 2^64
      rw [copied]
      omega
    · simpa only [atResult, copied] using align
    · constructor
      all_goals simp only [atResult, KCtx.setReg_regs, RegMap.set_apply, BitVec.reduceEq, ↓reduceIte, copied]
      · rw [page, regs.pageSize, ← BitVec.ofNat_add, advance]
      · exact remaining
      · rw [regs.dst, count, destination]
      · exact regs.pageSize
      · exact regs.root
      · exact regs.mask
      · exact regs.size
      · exact regs.faultMode

theorem walk_return_good {i : Inputs} {s : State}
    (pc : s.machine.pc = 0x800016ee#64)
    (hc : Common i s) (more : s.memory.copied.length < i.old.length)
    (nowrap : cursor i s < 2 ^ 64) (regs : LoopRegs i s.memory.copied.length s.machine.ctx.regs)
    (page : s.machine.ctx.regs 19#5 = BitVec.ofNat 64 (cursor i s / 4096 * 4096))
    (result : CopyCall.WalkPageResult s.memory.table (cursor i s) (s.machine.ctx.regs 10#5))
    (len64 : i.old.length < 2 ^ 64) : Good i s := by
  obtain ⟨r, certificate, target⟩ := walk_prefix pc hc more nowrap regs page result len64
  apply good_of_prefix pc ⟨r, certificate, ?_⟩
  rcases target with ⟨w, h⟩ | h
  · exact page_good h.pc h.toPage h.physical len64
  · exact good_of_endpoint (.fault h)

theorem fault_return_good {i : Inputs} {s : State}
    (pc : s.machine.pc = 0x800016fc#64)
    (hc : Common i s) (more : s.memory.copied.length < i.old.length)
    (nowrap : cursor i s < 2 ^ 64) (regs : LoopRegs i s.memory.copied.length s.machine.ctx.regs)
    (page : s.machine.ctx.regs 19#5 = BitVec.ofNat 64 (cursor i s / 4096 * 4096))
    (failure : s.machine.ctx.regs 10#5 = 0#64 → ¬ uvaRmapped s.memory.table (cursor i s))
    (success : s.machine.ctx.regs 10#5 ≠ 0#64 → ∃ w,
      Iris.Std.PartialMap.get? s.memory.table.um (cursor i s / 4096) = some w ∧ pteVU w ∧
      s.machine.ctx.regs 10#5 = pte2pa w ∧ cursor i s / 4096 * 4096 < 2 ^ 38)
    (len64 : i.old.length < 2 ^ 64) : Good i s := by
  obtain ⟨r, certificate, target⟩ := fault_prefix pc hc more nowrap regs page failure success len64
  apply good_of_prefix pc ⟨r, certificate, ?_⟩
  rcases target with ⟨w, h⟩ | h
  · exact page_good h.pc h.toPage h.physical len64
  · exact good_of_endpoint (.done h)

theorem move_return_good {i : Inputs} {s : State} (pc : s.machine.pc = 0x800016d4#64)
    (hc : Common i s) (d : Nat)
    (copied : s.memory.copied.length = d + chunkSize i.src.toNat d i.old.length)
    (more : d < i.old.length) (regs : LoopRegs i d s.machine.ctx.regs)
    (count : s.machine.ctx.regs 9#5 = BitVec.ofNat 64 (chunkSize i.src.toNat d i.old.length))
    (page : s.machine.ctx.regs 19#5 = BitVec.ofNat 64 ((i.src.toNat + d) / 4096 * 4096))
    (pageBound : (i.src.toNat + d) / 4096 * 4096 < 2 ^ 38)
    (len64 : i.old.length < 2 ^ 64) : Good i s := by
  obtain ⟨r, certificate, target⟩ := move_prefix pc hc d copied more regs count page pageBound len64
  apply good_of_prefix pc ⟨r, certificate, ?_⟩
  rcases target with h | h
  · exact header_prefix_good h
  · exact good_of_endpoint (.done h)

end Xv6.WholeFunction.Copyin
