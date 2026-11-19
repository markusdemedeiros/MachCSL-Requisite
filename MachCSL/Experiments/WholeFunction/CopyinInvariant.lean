import Experiments.WholeFunction.CopyinModel
import Experiments.WholeFunction.CopyinPure
import Experiments.WholeFunction.KernelSymbolic
import Experiments.WholeFunction.StackValueWp

namespace Xv6.WholeFunction.Copyin
open MachCSL LeanRV64D
namespace C
export Experiments.WholeFunction.Copy (Trace initial CopyinPost copyin_contract transfer)
end C

/-- The persistent loop-register annotation. Temporary/caller-saved
registers are deliberately absent, so callee summaries preserve this directly. -/
structure LoopRegs (i : Inputs) (d : Nat) (R : RegMap) : Prop where
  src : R 18#5 = BitVec.ofNat 64 (i.src.toNat + d)
  remaining : R 20#5 = BitVec.ofNat 64 (i.old.length - d)
  dst : R 21#5 = i.dst + BitVec.ofNat 64 d
  pageSize : R 22#5 = 4096#64
  root : R 23#5 = pageAddr i.table.root
  mask : R 24#5 = 0xFFFFFFFFFFFFF000#64
  size : R 25#5 = i.size
  faultMode : R 26#5 = 1#64

structure Common (i : Inputs) (s : State) : Prop where
  trace : C.Trace .read i.size i.src (C.initial i.table i.image i.lend) s.memory
  bound : s.memory.copied.length ≤ i.old.length
  cells : s.machine.cells = StackValues.frameCells i.entry
  sp : s.machine.ctx.sp = i.entry.sp - 96#64
  s11 : s.machine.ctx.regs 27#5 = i.entry.regs 27#5
  context : s.machine.ctx =
    ((i.entry.withSpie s.machine.ctx.spie s.machine.ctx.spp).pushed 12).withRegs s.machine.ctx.regs
  flags : i.entry.sie = false →
    s.machine.ctx.spie = i.entry.spie ∧ s.machine.ctx.spp = i.entry.spp

/-- Only loop/call cutpoints carry handwritten domain facts. Intermediate
register states are supplied by the symbolic row evaluator. -/
structure Header (i : Inputs) (s : State) : Prop extends Common i s where
  pc : s.machine.pc = 0x800016e2#64
  more : s.memory.copied.length < i.old.length
  nowrap : i.src.toNat + s.memory.copied.length < 2 ^ 64
  aligned : s.memory.copied.length = 0 ∨ (i.src.toNat + s.memory.copied.length) % 4096 = 0
  registers : LoopRegs i s.memory.copied.length s.machine.ctx.regs

structure Page (i : Inputs) (s : State) (w : BitVec 64) : Prop extends Common i s where
  more : s.memory.copied.length < i.old.length
  registers : LoopRegs i s.memory.copied.length s.machine.ctx.regs
  leaf : Iris.Std.PartialMap.get? s.memory.table.um
    ((i.src.toNat + s.memory.copied.length) / 4096) = some w
  readable : pteVU w
  pageBound : (i.src.toNat + s.memory.copied.length) / 4096 * 4096 < 2 ^ 38
  pageReg : s.machine.ctx.regs 19#5 =
    BitVec.ofNat 64 ((i.src.toNat + s.memory.copied.length) / 4096 * 4096)

structure PageReady (i : Inputs) (s : State) (w : BitVec 64) : Prop extends Page i s w where
  pc : s.machine.pc = 0x800016b8#64
  physical : s.machine.ctx.regs 10#5 = pte2pa w

def chunk (i : Inputs) (s : State) : Nat :=
  chunkSize i.src.toNat s.memory.copied.length i.old.length

structure MoveCall (i : Inputs) (s : State) (w : BitVec 64) : Prop extends Page i s w where
  pc : s.machine.pc = 0x800016d0#64
  count : s.machine.ctx.regs 9#5 = BitVec.ofNat 64 (chunk i s)
  a0 : s.machine.ctx.regs 10#5 = i.dst + BitVec.ofNat 64 s.memory.copied.length
  a1 : s.machine.ctx.regs 11#5 = pte2pa w + BitVec.ofNat 64
    ((i.src.toNat + s.memory.copied.length) % 4096)
  a2 : s.machine.ctx.regs 12#5 = BitVec.ofNat 64 (chunk i s)

structure WalkCall (i : Inputs) (s : State) : Prop extends Common i s where
  pc : s.machine.pc = 0x800016ea#64
  more : s.memory.copied.length < i.old.length
  nowrap : i.src.toNat + s.memory.copied.length < 2 ^ 64
  registers : LoopRegs i s.memory.copied.length s.machine.ctx.regs
  pageReg : s.machine.ctx.regs 19#5 =
    BitVec.ofNat 64 ((i.src.toNat + s.memory.copied.length) / 4096 * 4096)
  a0 : s.machine.ctx.regs 10#5 = pageAddr i.table.root
  a1 : s.machine.ctx.regs 11#5 =
    BitVec.ofNat 64 ((i.src.toNat + s.memory.copied.length) / 4096 * 4096)

structure FaultCall (i : Inputs) (s : State) : Prop extends Common i s where
  pc : s.machine.pc = 0x800016f8#64
  more : s.memory.copied.length < i.old.length
  nowrap : i.src.toNat + s.memory.copied.length < 2 ^ 64
  registers : LoopRegs i s.memory.copied.length s.machine.ctx.regs
  pageReg : s.machine.ctx.regs 19#5 =
    BitVec.ofNat 64 ((i.src.toNat + s.memory.copied.length) / 4096 * 4096)
  unreadable : ¬ uvaRmapped s.memory.table (i.src.toNat + s.memory.copied.length)
  a0 : s.machine.ctx.regs 10#5 = pageAddr i.table.root
  a1 : s.machine.ctx.regs 11#5 = i.size
  a2 : s.machine.ctx.regs 12#5 =
    BitVec.ofNat 64 ((i.src.toNat + s.memory.copied.length) / 4096 * 4096)
  a3 : s.machine.ctx.regs 13#5 = 1#64

/-- Return classification agrees with both original contract arms. -/
structure Exit (i : Inputs) (s : State) : Prop extends Common i s where
  pc : s.machine.pc = 0x80001704#64
  status : (s.machine.ctx.regs 10#5 = 0#64 ∧ s.memory.copied.length = i.old.length) ∨
    (s.machine.ctx.regs 10#5 = -1#64 ∧ ∃ e, e < i.old.length ∧
      ¬ uvaRmapped s.memory.table (i.src + BitVec.ofNat 64 e).toNat)

theorem exit_post (i : Inputs) (s : State) (h : Exit i s) :
    C.CopyinPost i.size i.src (s.machine.ctx.regs 10#5) i.table i.image i.old s.memory :=
  C.copyin_contract i.old h.trace h.bound h.status

inductive Endpoint (i : Inputs) (s : State) : Prop
  | walk : WalkCall i s → Endpoint i s
  | fault : FaultCall i s → Endpoint i s
  | move (w : BitVec 64) : MoveCall i s w → Endpoint i s
  | done : Exit i s → Endpoint i s

theorem Endpoint.common {i : Inputs} {s : State} (h : Endpoint i s) : Common i s := by
  cases h with
  | walk h => exact h.toCommon
  | fault h => exact h.toCommon
  | move w h => exact h.toPage.toCommon
  | done h => exact h.toCommon

/-- Intermediate machine states are generated symbolic prefixes whose
remaining certificate ends at one of the semantic call/exit boundaries.
No register equations are enumerated for intermediate PCs. -/
def Good (i : Inputs) (s : State) : Prop :=
  ∃ t : State, ∃ cut : BitVec 64 → Bool,
    s.memory = t.memory ∧ s.machine.cells = t.machine.cells ∧
    Symbolic.Certificate Binary.copyin.rows cut s.machine.machine ⟨t.machine.machine, .cut⟩ ∧
    Endpoint i t

theorem good_of_endpoint {i : Inputs} {s : State} (h : Endpoint i s) : Good i s :=
  ⟨s, (fun _ => true), rfl, rfl, .stop _ rfl, h⟩

theorem good_indices {i : Inputs} {s : State} (h : Good i s) :
    s.machine.ctx.sie = i.entry.sie ∧ s.machine.ctx.proc = i.entry.proc := by
  obtain ⟨t, cut, _, _, cert, endpoint⟩ := h
  have hc := endpoint.common.context
  have he := cert.indices
  dsimp only [Stack.State.machine] at he
  exact ⟨he.1.symm.trans (by simpa using congrArg KCtx.sie hc),
    he.2.symm.trans (by simpa using congrArg KCtx.proc hc)⟩

theorem page_chunk (i : Inputs) (s : State) (w : BitVec 64) (h : Page i s w) :
    C.Trace .read i.size i.src (C.initial i.table i.image i.lend)
      (C.transfer .read i.src s.memory (readChunk i.src s.memory (chunk i s))) := by
  obtain ⟨hp, _, hfit, _, _⟩ := chunk_facts i.src.toNat s.memory.copied.length i.old.length h.more
  exact readChunk_trace h.trace (chunk i s) w hp h.leaf h.readable hfit h.pageBound

end Xv6.WholeFunction.Copyin
