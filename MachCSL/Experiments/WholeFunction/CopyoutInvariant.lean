import Experiments.WholeFunction.CopyoutPure
import Experiments.WholeFunction.CopyoutFrameDefs
import Experiments.WholeFunction.Residual

namespace Xv6.WholeFunction.Copyout
open MachCSL LeanRV64D
namespace C
export Experiments.WholeFunction.Copy (WriteRun write_run_certificate write_run_contract initial)
end C

structure LoopRegs (i : Inputs) (d : Nat) (R : RegMap) : Prop where
  dst : R 20#5 = BitVec.ofNat 64 (i.dst.toNat + d)
  remaining : R 21#5 = BitVec.ofNat 64 (i.bytes.length - d)
  src : R 22#5 = i.src + BitVec.ofNat 64 d
  root : R 23#5 = pageAddr i.table.root
  pageSize : R 24#5 = 4096#64
  maxva : R 25#5 = 0x3fffffffff#64
  mask : R 26#5 = 0xfffffffffffff000#64
  size : R 27#5 = i.size

/-- Algorithm history, current page-table validity and the saved ABI frame.
No instruction-prefix register equations are stored in this invariant. -/
structure Common (i : Inputs) (s : State) : Prop where
  run : C.WriteRun i.size i.dst i.bytes i.table i.image i.lend s.memory
  wf : uptWf s.memory.table
  frame : CopyoutFrame.Frame i.entry s.machine.cells
  sp : s.machine.ctx.regs 2#5 = i.entry.sp - 112#64
  context : s.machine.ctx =
    ((i.entry.withSpie s.machine.ctx.spie s.machine.ctx.spp).pushed 14).withRegs s.machine.ctx.regs
  flags : i.entry.sie = false →
    s.machine.ctx.spie = i.entry.spie ∧ s.machine.ctx.spp = i.entry.spp

theorem Common.bound {i : Inputs} {s : State} (h : Common i s) :
    s.memory.copied.length ≤ i.bytes.length := (C.write_run_certificate h.run).2.1

theorem Common.indices {i : Inputs} {s : State} (h : Common i s) :
    s.machine.ctx.sie = i.entry.sie ∧ s.machine.ctx.proc = i.entry.proc :=
  ⟨by simpa using congrArg KCtx.sie h.context, by simpa using congrArg KCtx.proc h.context⟩

theorem Common.reframe {i : Inputs} {s : State} (h : Common i s)
    (R : RegMap) (pc : BitVec 64) (sp : R 2#5 = s.machine.ctx.regs 2#5) :
    Common i ⟨⟨s.machine.ctx.withRegs R, pc, s.machine.cells⟩, s.memory⟩ := by
  refine ⟨h.run, h.wf, h.frame, sp.trans h.sp, ?_, h.flags⟩
  exact (congrArg (fun k : KCtx => k.withRegs R) h.context).trans (KCtx.withRegs_withRegs _ _ _)

def atResult (s : State) (r : RegState) : State := ⟨⟨r.ctx, r.pc, s.machine.cells⟩, s.memory⟩

theorem common_result {i : Inputs} {s : State} (h : Common i s) (r : RegState)
    (context : r.ctx = s.machine.ctx.withRegs r.ctx.regs)
    (sp : r.ctx.regs 2#5 = s.machine.ctx.regs 2#5) : Common i (atResult s r) := by
  have hc := h.reframe r.ctx.regs r.pc sp
  simpa only [atResult, ← context] using hc

structure Header (i : Inputs) (s : State) : Prop extends Common i s where
  pc : s.machine.pc = 0x80001616#64
  more : s.memory.copied.length < i.bytes.length
  nowrap : cursor i s < 2 ^ 64
  registers : LoopRegs i s.memory.copied.length s.machine.ctx.regs

structure Page (i : Inputs) (s : State) (w : BitVec 64) : Prop extends Common i s where
  more : s.memory.copied.length < i.bytes.length
  registers : LoopRegs i s.memory.copied.length s.machine.ctx.regs
  leaf : Iris.Std.PartialMap.get? s.memory.table.um (cursor i s / 4096) = some w
  readable : pteVU w
  pageBound : cursor i s / 4096 * 4096 < 2 ^ 38
  pageReg : s.machine.ctx.regs 9#5 = BitVec.ofNat 64 (cursor i s / 4096 * 4096)
  physicalReg : s.machine.ctx.regs 19#5 = pte2pa w

def chunk (i : Inputs) (s : State) : Nat := chunkSize i.dst.toNat s.memory.copied.length i.bytes.length

structure WalkCall (i : Inputs) (s : State) : Prop extends Common i s where
  pc : s.machine.pc = 0x80001622#64
  more : s.memory.copied.length < i.bytes.length
  nowrap : cursor i s < 2 ^ 64
  registers : LoopRegs i s.memory.copied.length s.machine.ctx.regs
  pageReg : s.machine.ctx.regs 9#5 = BitVec.ofNat 64 (cursor i s / 4096 * 4096)
  pageBound : cursor i s / 4096 * 4096 < 2 ^ 38
  a0 : s.machine.ctx.regs 10#5 = pageAddr i.table.root
  a1 : s.machine.ctx.regs 11#5 = BitVec.ofNat 64 (cursor i s / 4096 * 4096)

structure FaultCall (i : Inputs) (s : State) : Prop extends Common i s where
  pc : s.machine.pc = 0x80001632#64
  more : s.memory.copied.length < i.bytes.length
  nowrap : cursor i s < 2 ^ 64
  registers : LoopRegs i s.memory.copied.length s.machine.ctx.regs
  pageReg : s.machine.ctx.regs 9#5 = BitVec.ofNat 64 (cursor i s / 4096 * 4096)
  pageBound : cursor i s / 4096 * 4096 < 2 ^ 38
  unreadable : ¬ uvaRmapped s.memory.table (cursor i s)
  a0 : s.machine.ctx.regs 10#5 = pageAddr i.table.root
  a1 : s.machine.ctx.regs 11#5 = i.size
  a2 : s.machine.ctx.regs 12#5 = BitVec.ofNat 64 (cursor i s / 4096 * 4096)
  a3 : s.machine.ctx.regs 13#5 = 0#64

structure ProbeCall (i : Inputs) (s : State) (w : BitVec 64) : Prop extends Page i s w where
  pc : s.machine.pc = 0x80001640#64
  a0 : s.machine.ctx.regs 10#5 = pageAddr i.table.root
  a1 : s.machine.ctx.regs 11#5 = BitVec.ofNat 64 (cursor i s / 4096 * 4096)
  a2 : s.machine.ctx.regs 12#5 = 0#64

structure MoveCall (i : Inputs) (s : State) (w : BitVec 64) : Prop extends Page i s w where
  pc : s.machine.pc = 0x80001604#64
  writable : w &&& PTE_W ≠ 0#64
  count : s.machine.ctx.regs 18#5 = BitVec.ofNat 64 (chunk i s)
  a0 : s.machine.ctx.regs 10#5 = pte2pa w + BitVec.ofNat 64 (cursor i s % 4096)
  a1 : s.machine.ctx.regs 11#5 = i.src + BitVec.ofNat 64 s.memory.copied.length
  a2 : s.machine.ctx.regs 12#5 = BitVec.ofNat 64 (chunk i s)

structure Exit (i : Inputs) (s : State) : Prop extends Common i s where
  pc : s.machine.pc = 0x80001662#64
  status : (s.machine.ctx.regs 10#5 = 0#64 ∧ s.memory.copied.length = i.bytes.length) ∨
    (s.machine.ctx.regs 10#5 = -1#64 ∧ s.memory.copied.length < i.bytes.length ∧
      ¬ uvaWmapped s.memory.table (i.dst + BitVec.ofNat 64 s.memory.copied.length).toNat)

theorem Exit.post {i : Inputs} {s : State} (h : Exit i s) :
    Post i (s.machine.ctx.regs 10#5) s.memory := C.write_run_contract h.run h.status

inductive Endpoint (i : Inputs) : State → Prop
  | walk {s} : WalkCall i s → Endpoint i s
  | fault {s} : FaultCall i s → Endpoint i s
  | probe (w) {s} : ProbeCall i s w → Endpoint i s
  | move (w) {s} : MoveCall i s w → Endpoint i s
  | done {s} : Exit i s → Endpoint i s

theorem Endpoint.common {i : Inputs} {s : State} (h : Endpoint i s) : Common i s := by
  cases h with
  | walk h => exact h.toCommon
  | fault h => exact h.toCommon
  | probe w h => exact h.toPage.toCommon
  | move w h => exact h.toPage.toCommon
  | done h => exact h.toCommon

def residualView : Residual.View State (Effect.State × List (BitVec 64 × BitVec 64)) where
  machine := fun s => s.machine.machine
  resources := fun s => (s.memory, s.machine.cells)
  ext := by
    rintro ⟨⟨sk, sp, sc⟩, sm⟩ ⟨⟨tk, tp, tc⟩, tm⟩ data machine
    simp only [Prod.mk.injEq] at data
    simp only [Stack.State.machine, RegState.mk.injEq] at machine
    obtain ⟨rfl, rfl⟩ := data
    obtain ⟨rfl, rfl⟩ := machine
    rfl

abbrev Good (i : Inputs) := Residual.Good residualView Binary.copyout.rows (Endpoint i)

theorem good_indices {i : Inputs} {s : State} (h : Good i s) :
    s.machine.ctx.sie = i.entry.sie ∧ s.machine.ctx.proc = i.entry.proc :=
  Residual.indices h (fun _ e => e.common.indices)

/-- The semantic loop update; arithmetic facts are shared with COPYIN. -/
def updateRegs (R : RegMap) : RegMap :=
  ((R.set 21#5 (R 21#5 - R 18#5)).set 22#5 (R 22#5 + R 18#5)).set 20#5 (R 9#5 + R 24#5)

theorem update_loop (i : Inputs) (d : Nat) (R : RegMap)
    (regs : LoopRegs i d R) (more : d < i.bytes.length) (len64 : i.bytes.length < 2 ^ 64)
    (count : R 18#5 = BitVec.ofNat 64 (chunkSize i.dst.toNat d i.bytes.length))
    (page : R 9#5 = BitVec.ofNat 64 ((i.dst.toNat + d) / 4096 * 4096))
    (continuing : d + chunkSize i.dst.toNat d i.bytes.length < i.bytes.length) :
    LoopRegs i (d + chunkSize i.dst.toNat d i.bytes.length) (updateRegs R) := by
  obtain ⟨_, bound, _, _, cases⟩ := chunk_facts i.dst.toNat d i.bytes.length more
  have he : (i.dst.toNat + d) / 4096 * 4096 + 4096 =
      i.dst.toNat + (d + chunkSize i.dst.toNat d i.bytes.length) := by omega
  obtain ⟨_, hsrc, hrem⟩ := chunk_register_updates i.dst i.src d
    (chunkSize i.dst.toNat d i.bytes.length) i.bytes.length bound len64
  constructor
  · simp only [updateRegs, RegMap.set_apply, BitVec.reduceEq, ↓reduceIte]
    rw [page, regs.pageSize, ← BitVec.ofNat_add, he]
  · simp only [updateRegs, RegMap.set_apply, BitVec.reduceEq, ↓reduceIte]
    rw [regs.remaining, count, hrem]
  · simp only [updateRegs, RegMap.set_apply, BitVec.reduceEq, ↓reduceIte]
    rw [regs.src, count, hsrc]
  all_goals simpa only [updateRegs, RegMap.set_apply, BitVec.reduceEq, ↓reduceIte] using
    (by first | exact regs.root | exact regs.pageSize | exact regs.maxva | exact regs.mask | exact regs.size)

end Xv6.WholeFunction.Copyout
