import Experiments.WholeFunction.CopyinClosure

namespace Xv6.WholeFunction.Copyin
open MachCSL LeanRV64D
open Experiments.WholeFunction

theorem SavedCopyRegs.trans {R S T : RegMap} (h : SavedCopyRegs R S) (k : SavedCopyRegs S T) :
    SavedCopyRegs R T :=
  ⟨k.sp.trans h.sp, k.count.trans h.count, k.src.trans h.src, k.page.trans h.page,
    k.remaining.trans h.remaining, k.dst.trans h.dst, k.pageSize.trans h.pageSize,
    k.root.trans h.root, k.mask.trans h.mask, k.size.trans h.size,
    k.faultMode.trans h.faultMode, k.s11.trans h.s11⟩

theorem LoopRegs.of_saved {i : Inputs} {d : Nat} {R R' : RegMap}
    (h : LoopRegs i d R) (saved : SavedCopyRegs R R') : LoopRegs i d R' :=
  ⟨saved.src.trans h.src, saved.remaining.trans h.remaining, saved.dst.trans h.dst,
    saved.pageSize.trans h.pageSize, saved.root.trans h.root, saved.mask.trans h.mask,
    saved.size.trans h.size, saved.faultMode.trans h.faultMode⟩

theorem Common.withRegs {i : Inputs} {s : State} (h : Common i s)
    (R : RegMap) (pc : BitVec 64) (saved : SavedCopyRegs s.machine.ctx.regs R) :
    Common i ⟨⟨s.machine.ctx.withRegs R, pc, s.machine.cells⟩, s.memory⟩ :=
  common_reframe h R pc saved.sp saved.s11

theorem Common.indices {i : Inputs} {s : State} (h : Common i s) :
    s.machine.ctx.sie = i.entry.sie ∧ s.machine.ctx.proc = i.entry.proc :=
  ⟨by simpa using congrArg KCtx.sie h.context, by simpa using congrArg KCtx.proc h.context⟩

theorem Common.avail {i : Inputs} {s : State} (h : Common i s) :
    s.machine.ctx.avail = i.entry.avail - 12 := by
  simpa using congrArg KCtx.avail h.context

theorem Common.noff {i : Inputs} {s : State} (h : Common i s) :
    s.machine.ctx.noff = i.entry.noff := by simpa using congrArg KCtx.noff h.context

theorem Common.locks {i : Inputs} {s : State} (h : Common i s) :
    s.machine.ctx.locks = i.entry.locks := by simpa using congrArg KCtx.locks h.context

theorem Common.table_root {i : Inputs} {s : State} (h : Common i s) :
    s.memory.table.root = i.table.root :=
  (Copy.trace_certificate h.trace).extension.1.1

theorem Common.faultReturn {i : Inputs} {s : State} (h : Common i s)
    (spie spp : Bool) (R : RegMap) (memory : Copy.State)
    (saved : SavedCopyRegs s.machine.ctx.regs R)
    (step : Copy.Step .read i.size i.src s.memory memory)
    (copied : memory.copied = s.memory.copied)
    (flags : s.machine.ctx.sie = false → spie = s.machine.ctx.spie ∧ spp = s.machine.ctx.spp) :
    Common i (returnState s ((s.machine.ctx.withSpie spie spp).withRegs R) memory) := by
  refine ⟨.snoc h.trace step, ?_, h.cells, saved.sp.trans h.sp, saved.s11.trans h.s11,
    context_withSpie i.entry s.machine.ctx 12 spie spp R h.context, ?_⟩
  · simpa only [returnState, copied] using h.bound
  · exact flags_after_call i.entry s.machine.ctx spie spp h.indices.1 h.flags flags

theorem Common.readReturn {i : Inputs} {s : State} (h : Common i s)
    (R : RegMap) (n : Nat) (saved : SavedCopyRegs s.machine.ctx.regs R)
    (step : Copy.Step .read i.size i.src s.memory (readMemory i s n))
    (bound : s.memory.copied.length + n ≤ i.old.length) :
    Common i (returnState s (s.machine.ctx.withRegs R) (readMemory i s n)) := by
  refine ⟨.snoc h.trace step, ?_, h.cells, saved.sp.trans h.sp, saved.s11.trans h.s11,
    context_withRegs i.entry s.machine.ctx 12 R h.context, h.flags⟩
  simpa only [returnState, readMemory, Copy.transfer, List.length_append, UMemL.umemRead_length] using bound

/-- Canonical JAL update: the only caller register overwritten is ra. -/
def enter (s : State) (target ra : BitVec 64) : State :=
  ⟨⟨s.machine.ctx.setReg 1#5 ra, target, s.machine.cells⟩, s.memory⟩

theorem enter_saved (s : State) (target ra : BitVec 64) :
    SavedCopyRegs s.machine.ctx.regs (enter s target ra).machine.ctx.regs := by
  constructor <;> simp [enter, KCtx.setReg_regs, RegMap.set_apply]

theorem enter_regs (s : State) (target ra : BitVec 64) (r : BitVec 5) (hr : r ≠ 1#5) :
    (enter s target ra).machine.ctx.regs r = s.machine.ctx.regs r := by
  simp [enter, KCtx.setReg_regs, RegMap.set_apply, hr]

theorem Common.enter {i : Inputs} {s : State} (h : Common i s) (target ra : BitVec 64) :
    Common i (enter s target ra) :=
  h.withRegs _ _ (enter_saved s target ra)

theorem walk_ready {i : Inputs} {s : State} (valid : Valid i) (h : WalkCall i s) :
    WalkEnabled i (enter s KA.«walkaddr» 0x800016ee#64) := by
  constructor
  · rfl
  · change 10 ≤ s.machine.ctx.avail
    rw [h.toCommon.avail]
    have := valid.stack
    omega
  · have root := h.toCommon.table_root
    simpa only [enter, KCtx.setReg_regs, RegMap.set_apply, BitVec.reduceEq, ↓reduceIte, root] using h.a0
  · exact h.nowrap
  · simpa only [cursor, enter, KCtx.setReg_regs, RegMap.set_apply, BitVec.reduceEq, ↓reduceIte] using h.a1

theorem fault_ready {i : Inputs} {s : State} (valid : Valid i) (h : FaultCall i s) :
    FaultEnabled i (enter s KA.«vmfault» 0x800016fc#64) := by
  constructor
  · rfl
  · change s.machine.ctx.noff + 1 < 2 ^ 31
    rw [h.toCommon.noff]
    exact valid.noff
  · change vmfaultSlots ≤ s.machine.ctx.avail
    rw [h.toCommon.avail]
    have := valid.stack
    unfold vmfaultSlots
    omega
  · change "kmem" ∉ s.machine.ctx.locks
    rw [h.toCommon.locks]
    exact valid.lock
  · have root := h.toCommon.table_root
    simpa only [enter, KCtx.setReg_regs, RegMap.set_apply, BitVec.reduceEq, ↓reduceIte, root] using h.a0
  · simpa only [cursor, enter, KCtx.setReg_regs, RegMap.set_apply, BitVec.reduceEq, ↓reduceIte] using h.a1
  · exact valid.size
  · exact h.toCommon.indices.2

theorem move_length {i : Inputs} {s : State} {w : BitVec 64} (h : MoveCall i s w) :
    readLength (enter s KA.«memmove» 0x800016d4#64) = chunk i s := by
  have hn := (chunk_facts i.src.toNat s.memory.copied.length i.old.length h.more).2.2.2.1
  change ((s.machine.ctx.regs.set 1#5 0x800016d4#64) 12#5).toNat = chunk i s
  simp only [RegMap.set_apply, BitVec.reduceEq, ↓reduceIte, h.a2, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by unfold chunk; omega)

theorem move_ready {i : Inputs} {s : State} {w : BitVec 64} (valid : Valid i) (h : MoveCall i s w) :
    ∃ w', ReadEnabled i (enter s KA.«memmove» 0x800016d4#64)
      (readLength (enter s KA.«memmove» 0x800016d4#64)) w' := by
  rw [move_length h]
  obtain ⟨positive, bound, fit, _, _⟩ := chunk_facts i.src.toNat s.memory.copied.length i.old.length h.more
  refine ⟨w, ?_⟩
  constructor
  · rfl
  · change 2 ≤ s.machine.ctx.avail
    rw [h.toPage.toCommon.avail]
    have := valid.stack
    omega
  · exact h.leaf
  · exact fit
  · exact positive
  · exact bound
  · exact page_readable_chunk s.memory.table i.src s.memory.copied.length (chunk i s) w
      h.leaf h.readable fit h.pageBound
  · simpa only [cursor, enter, KCtx.setReg_regs, RegMap.set_apply, BitVec.reduceEq, ↓reduceIte] using h.a1
  · simpa only [enter, KCtx.setReg_regs, RegMap.set_apply, BitVec.reduceEq, ↓reduceIte] using h.a0
  · simpa only [enter, KCtx.setReg_regs, RegMap.set_apply, BitVec.reduceEq, ↓reduceIte] using h.a2

end Xv6.WholeFunction.Copyin
