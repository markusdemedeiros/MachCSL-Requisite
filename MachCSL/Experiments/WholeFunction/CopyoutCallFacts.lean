import Experiments.WholeFunction.CopyoutInvariant
import Experiments.WholeFunction.CopyoutCallRegistry
import Experiments.WholeFunction.CopyinPageFacts

namespace Xv6.WholeFunction.Copyout
open MachCSL LeanRV64D
open Iris.Std (get?)
open Experiments.WholeFunction

theorem saved_trans {R S T : RegMap} (h : calleeSaved R S) (k : calleeSaved S T) :
    calleeSaved R T := by
  simp only [calleeSaved] at *
  rcases h with ⟨h2,h8,h9,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27⟩
  rcases k with ⟨k2,k8,k9,k18,k19,k20,k21,k22,k23,k24,k25,k26,k27⟩
  exact ⟨k2.trans h2,k8.trans h8,k9.trans h9,k18.trans h18,k19.trans h19,
    k20.trans h20,k21.trans h21,k22.trans h22,k23.trans h23,k24.trans h24,
    k25.trans h25,k26.trans h26,k27.trans h27⟩

theorem LoopRegs.of_saved {i : Inputs} {d : Nat} {R R' : RegMap}
    (h : LoopRegs i d R) (saved : calleeSaved R R') : LoopRegs i d R' := by
  obtain ⟨_,_,_,_,_,s20,s21,s22,s23,s24,s25,s26,s27⟩ := saved
  exact ⟨s20.trans h.dst,s21.trans h.remaining,s22.trans h.src,s23.trans h.root,
    s24.trans h.pageSize,s25.trans h.maxva,s26.trans h.mask,s27.trans h.size⟩

theorem Common.withRegs {i : Inputs} {s : State} (h : Common i s)
    (R : RegMap) (pc : BitVec 64) (saved : calleeSaved s.machine.ctx.regs R) :
    Common i ⟨⟨s.machine.ctx.withRegs R, pc, s.machine.cells⟩, s.memory⟩ := by
  exact ⟨h.run,h.wf,h.frame,saved.1.trans h.sp,
    Copyin.context_withRegs i.entry s.machine.ctx 14 R h.context,h.flags⟩

theorem Common.avail {i : Inputs} {s : State} (h : Common i s) :
    s.machine.ctx.avail = i.entry.avail - 14 := by
  simpa using congrArg KCtx.avail h.context
theorem Common.noff {i : Inputs} {s : State} (h : Common i s) :
    s.machine.ctx.noff = i.entry.noff := by simpa using congrArg KCtx.noff h.context
theorem Common.locks {i : Inputs} {s : State} (h : Common i s) :
    s.machine.ctx.locks = i.entry.locks := by simpa using congrArg KCtx.locks h.context
theorem Common.table_root {i : Inputs} {s : State} (h : Common i s) :
    s.memory.table.root = i.table.root :=
  (Copy.trace_certificate (Copy.write_run_certificate h.run).1).extension.1.1

theorem Common.faultReturn {i : Inputs} {s : State} (h : Common i s)
    (spie spp : Bool) (R : RegMap) (memory : Copy.State)
    (saved : calleeSaved s.machine.ctx.regs R)
    (step : Copy.Step .write i.size i.dst s.memory memory)
    (copied : memory.copied = s.memory.copied) (wf : uptWf memory.table)
    (flags : s.machine.ctx.sie = false → spie = s.machine.ctx.spie ∧ spp = s.machine.ctx.spp) :
    Common i (returnState s ((s.machine.ctx.withSpie spie spp).withRegs R) memory) := by
  refine ⟨?_,wf,h.frame,saved.1.trans h.sp,
    Copyin.context_withSpie i.entry s.machine.ctx 14 spie spp R h.context,?_⟩
  · cases step with
    | fault Q ke ext lend => exact .fault h.run Q ke ext lend
    | chunk bs positive page mapped access read =>
      have len := congrArg List.length copied
      simp only [Copy.transfer,List.length_append] at len
      omega
  · exact Copyin.flags_after_call i.entry s.machine.ctx spie spp h.indices.1 h.flags flags

theorem Common.writeReturn {i : Inputs} {s : State} (h : Common i s)
    (R : RegMap) (n : Nat) (saved : calleeSaved s.machine.ctx.regs R)
    (step : Copy.Step .write i.size i.dst s.memory (writeMemory i s n))
    (bound : s.memory.copied.length + n ≤ i.bytes.length) :
    Common i (returnState s (s.machine.ctx.withRegs R) (writeMemory i s n)) := by
  have len : ((i.bytes.drop s.memory.copied.length).take n).length = n := by
    simp only [List.length_take,List.length_drop]; omega
  refine ⟨.chunk h.run _ step ?_ ?_,h.wf,h.frame,saved.1.trans h.sp,
    Copyin.context_withRegs i.entry s.machine.ctx 14 R h.context,h.flags⟩
  · simpa only [len] using bound
  · rw [len]

/-- Canonical JAL update: the only caller register overwritten is ra. -/
def enter (s : State) (target ra : BitVec 64) : State :=
  ⟨⟨s.machine.ctx.setReg 1#5 ra, target, s.machine.cells⟩, s.memory⟩

theorem enter_saved (s : State) (target ra : BitVec 64) :
    calleeSaved s.machine.ctx.regs (enter s target ra).machine.ctx.regs := by
  simp [calleeSaved, enter, KCtx.setReg_regs, RegMap.set_apply]

theorem enter_regs (s : State) (target ra : BitVec 64) (r : BitVec 5) (hr : r ≠ 1#5) :
    (enter s target ra).machine.ctx.regs r = s.machine.ctx.regs r := by
  simp [enter, KCtx.setReg_regs, RegMap.set_apply, hr]

theorem Common.enter {i : Inputs} {s : State} (h : Common i s) (target ra : BitVec 64) :
    Common i (enter s target ra) :=
  h.withRegs _ _ (enter_saved s target ra)

theorem walk_ready {i : Inputs} {s : State} (valid : Valid i) (h : WalkCall i s) :
    WalkEnabled i (enter s KA.«walkaddr» 0x80001626#64) := by
  change WalkEnabled i (enter s KA.«walkaddr» 0x80001626#64)
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
    FaultEnabled i (enter s KA.«vmfault» 0x80001636#64) := by
  change FaultEnabled i (enter s KA.«vmfault» 0x80001636#64)
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
    writeLength (enter s KA.«memmove» 0x80001608#64) = chunk i s := by
  have hn := (chunk_facts i.dst.toNat s.memory.copied.length i.bytes.length h.more).2.2.2.1
  change ((s.machine.ctx.regs.set 1#5 0x80001608#64) 12#5).toNat = chunk i s
  simp only [RegMap.set_apply, BitVec.reduceEq, ↓reduceIte, h.a2, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by unfold chunk; omega)

theorem move_ready {i : Inputs} {s : State} {w : BitVec 64} (valid : Valid i) (h : MoveCall i s w) :
    ∃ w', WriteEnabled i (enter s KA.«memmove» 0x80001608#64)
      (writeLength (enter s KA.«memmove» 0x80001608#64)) w' := by
  change ∃ w', WriteEnabled i (enter s KA.«memmove» 0x80001608#64)
    (writeLength (enter s KA.«memmove» 0x80001608#64)) w'
  rw [move_length h]
  obtain ⟨positive, bound, fit, _, _⟩ := chunk_facts i.dst.toNat s.memory.copied.length i.bytes.length h.more
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
  · exact page_writable_chunk s.memory.table i.dst s.memory.copied.length (chunk i s) w
      h.leaf h.readable h.writable fit h.pageBound
  · simpa only [cursor, enter, KCtx.setReg_regs, RegMap.set_apply, BitVec.reduceEq, ↓reduceIte] using h.a1
  · simpa only [cursor, enter, KCtx.setReg_regs, RegMap.set_apply, BitVec.reduceEq, ↓reduceIte] using h.a0
  · simpa only [enter, KCtx.setReg_regs, RegMap.set_apply, BitVec.reduceEq, ↓reduceIte] using h.a2


theorem probe_ready {i : Inputs} {s : State} {w : BitVec 64}
    (valid : Valid i) (h : ProbeCall i s w) :
    ∃ w', ProbeEnabled i (enter s KA.«walk» 0x80001644#64) w' := by
  change ∃ w', ProbeEnabled i (enter s KA.«walk» 0x80001644#64) w'
  refine ⟨w, ?_⟩
  constructor
  · rfl
  · change 8 ≤ s.machine.ctx.avail
    rw [h.toPage.toCommon.avail]
    have := valid.stack
    omega
  · have root := h.toPage.toCommon.table_root
    simpa only [enter,KCtx.setReg_regs,RegMap.set_apply,BitVec.reduceEq,↓reduceIte,root] using h.a0
  · change (s.machine.ctx.regs 11#5).toNat < 2^38
    rw [h.a1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := h.pageBound; omega)]
    exact h.pageBound
  · simpa only [enter,KCtx.setReg_regs,RegMap.set_apply,BitVec.reduceEq,↓reduceIte] using h.a2
  · change Iris.Std.PartialMap.get? s.memory.table.um (vpnOf (s.machine.ctx.regs 11#5)).toNat = some w
    rw [h.a1, co_vpnOf_toNat _ (by rw [BitVec.toNat_ofNat]; have := h.pageBound; omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := h.pageBound; omega)]
    simpa using h.leaf
  · change jumpPc 0x80001644#64 = 0x80001644#64
    decide

theorem endpoint_notMixed {i : Inputs} {s : State} (h : Endpoint i s) (active : ¬ BodyExit s) :
    findMixed 14 s.machine.pc Binary.copyout.rows = none := by
  cases h with
  | walk h => rw [h.pc]; binary_rfl
  | fault h => rw [h.pc]; binary_rfl
  | probe w h => rw [h.pc]; binary_rfl
  | move w h => rw [h.pc]; binary_rfl
  | done h => exact False.elim (active h.pc)

/-- The page information retained after a successful fault. -/
theorem FaultNext.success {i : Inputs} {s t : State}
    (hn : FaultNext i s t) (size : i.size.toNat ≤ 2 ^ 38)
    (bound : cursor i s < 2 ^ 64)
    (address : s.machine.ctx.regs 12#5 = BitVec.ofNat 64 (cursor i s / 4096 * 4096))
    (nonzero : t.machine.ctx.regs 10#5 ≠ 0#64) :
    ∃ w, get? t.memory.table.um (cursor i t / 4096) = some w ∧ pteVU w ∧
      t.machine.ctx.regs 10#5 = pte2pa w ∧ cursor i t / 4096 * 4096 < 2 ^ 38 := by
  obtain ⟨spie, spp, R', memory, rfl, flags, saved, step, copied, result, wf⟩ := hn
  change R' 10#5 ≠ 0#64 at nonzero
  have cur : cursor i (returnState s ((s.machine.ctx.withSpie spie spp).withRegs R') memory) =
      cursor i s := by simp only [cursor, returnState, copied]
  rw [cur]
  dsimp only [returnState, KCtx.withRegs]
  rcases result with ⟨zero, _⟩ | ⟨r, ret, valid, below, absent, table⟩
  · exact False.elim (nonzero zero)
  · have pageNat : (BitVec.ofNat 64 (cursor i s / 4096 * 4096)).toNat =
        cursor i s / 4096 * 4096 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [address, pageNat] at below
    have vpn : (vpnOf (s.machine.ctx.regs 12#5)).toNat = cursor i s / 4096 := by
      rw [address, co_vpnOf_toNat _ (by omega), pageNat]
      omega
    refine ⟨leafOf (BitVec.extractLsb' 12 44 r) (PTE_W ||| PTE_U ||| PTE_R), ?_,
      Copyin.fresh_leaf_readable r, ret.trans (Copyin.fresh_leaf_address r valid).symm, by omega⟩
    rw [table, vpn]
    exact Iris.Std.LawfulPartialMap.get?_insert_eq rfl

/-- A failed fault leaves the prior walk failure valid in the returned table. -/
theorem FaultNext.failure {i : Inputs} {s t : State}
    (hn : FaultNext i s t)
    (unreadable : ¬ uvaRmapped s.memory.table (cursor i s))
    (zero : t.machine.ctx.regs 10#5 = 0#64) :
    t.memory.table = s.memory.table ∧ cursor i t = cursor i s ∧
      ¬ uvaRmapped t.memory.table (cursor i t) := by
  obtain ⟨spie, spp, R', memory, rfl, flags, saved, step, copied, result, wf⟩ := hn
  have cur : cursor i (returnState s ((s.machine.ctx.withSpie spie spp).withRegs R') memory) =
      cursor i s := by simp only [cursor, returnState, copied]
  change R' 10#5 = 0#64 at zero
  rw [cur]
  dsimp only [returnState]
  rcases result with ⟨_, table⟩ | ⟨r, ret, valid, _⟩
  · exact ⟨table, rfl, by rw [table]; exact unreadable⟩
  · exact False.elim (PtRun.pageValid_ne_zero r valid (ret.symm.trans zero))


end Xv6.WholeFunction.Copyout

open Lean in
run_cmd do
  for decl in #[``Xv6.WholeFunction.Copyout.walk_ready,
      ``Xv6.WholeFunction.Copyout.Common.faultReturn,
      ``Xv6.WholeFunction.Copyout.Common.writeReturn,
      ``Xv6.WholeFunction.Copyout.FaultNext.success,
      ``Xv6.WholeFunction.Copyout.FaultNext.failure] do
    let axs ← collectAxioms decl
    unless axs.all (fun a => #[``propext, ``Classical.choice, ``Quot.sound].contains a) do
      throwError "{decl}: unexpected axioms {axs}"
