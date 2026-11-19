import Experiments.WholeFunction.CopyRuns
import Experiments.WholeFunction.KernelStackGraph

namespace Xv6.WholeFunction.Copyout
open Iris Iris.BI Iris.ProgramLogic MachCSL
namespace Effect
export Experiments.WholeFunction.Copy (Image State)
end Effect

/-- Public inputs; the source buffer is preserved at its original fraction. -/
structure Inputs where
  entry : KCtx
  table : UPtd
  image : Effect.Image
  bytes : List (BitVec 8)
  fraction : DFrac
  lend : Nat

def Inputs.src (i : Inputs) : BitVec 64 := i.entry.regs 13#5
def Inputs.dst (i : Inputs) : BitVec 64 := i.entry.regs 12#5
def Inputs.size (i : Inputs) : BitVec 64 := i.entry.regs 11#5

structure Valid (i : Inputs) : Prop where
  noff : i.entry.noff + 1 < 2 ^ 31
  stack : 52 ≤ i.entry.avail
  lock : "kmem" ∉ i.entry.locks
  root : i.entry.regs 10#5 = pageAddr i.table.root
  size : i.size.toNat ≤ 2 ^ 38
  length : i.entry.regs 14#5 = BitVec.ofNat 64 i.bytes.length
  bound : i.bytes.length < 2 ^ 63

structure State where
  machine : Stack.State
  memory : Effect.State

def State.withMachine (s : State) (m : Stack.State) : State := ⟨m, s.memory⟩
def State.withMemory (s : State) (m : Effect.State) : State := ⟨s.machine, m⟩
def cursor (i : Inputs) (s : State) : Nat := i.dst.toNat + s.memory.copied.length

/-- Exact pure component of the public COPYOUT return; the source buffer is
preserved separately by payload ownership. -/
def Post (i : Inputs) (ret : BitVec 64) (m : Effect.State) : Prop :=
  i.table.extSz i.size m.table ∧
    ((ret = 0#64 ∧ m.image = umemWrite (viewFaulted i.table m.table i.image) i.dst.toNat i.bytes ∧
        umMapped m.table i.dst.toNat i.bytes.length ∧ uvaWprefix m.table i.dst i.bytes.length) ∨
     (ret = -1#64 ∧ ∃ d, d < i.bytes.length ∧
        m.image = umemWrite (viewFaulted i.table m.table i.image) i.dst.toNat (i.bytes.take d) ∧
        umMapped m.table i.dst.toNat d ∧ uvaWprefix m.table i.dst d ∧
        ¬ uvaWmapped i.table (i.dst + BitVec.ofNat 64 d).toNat))

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
variable [Xv6G GF] [WchG GF] [CurCtx]

def payload (i : Inputs) (γl : GName) (γk : KmemNames) (s : State) : IProp GF := iprop%
  isLock γl kmemLockAddr "kmem" (kmemRes γk) ∗ kallocAvail γk none ∗
  procPtAt s.memory.table s.memory.image ∗ byteBuf i.src i.fraction i.bytes ∗
  actLend i.entry.proc s.memory.lend

end Xv6.WholeFunction.Copyout
