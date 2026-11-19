import Experiments.WholeFunction.CopyControl
import Experiments.WholeFunction.KernelStackGraph

namespace Xv6.WholeFunction.Copyin
open Iris Iris.BI Iris.ProgramLogic MachCSL
namespace Effect
export Experiments.WholeFunction.Copy (Image State buffer)
end Effect

/-- Fixed public inputs. Registers and memory remain symbolic. -/
structure Inputs where
  entry : KCtx
  table : UPtd
  image : Effect.Image
  old : List (BitVec 8)
  lend : Nat

def Inputs.src (i : Inputs) : BitVec 64 := i.entry.regs 13#5
def Inputs.dst (i : Inputs) : BitVec 64 := i.entry.regs 12#5
def Inputs.size (i : Inputs) : BitVec 64 := i.entry.regs 11#5

structure Valid (i : Inputs) : Prop where
  noff : i.entry.noff + 1 < 2 ^ 31
  stack : 50 ≤ i.entry.avail
  lock : "kmem" ∉ i.entry.locks
  root : i.entry.regs 10#5 = pageAddr i.table.root
  size : i.size.toNat ≤ 2 ^ 38
  length : i.entry.regs 14#5 = BitVec.ofNat 64 i.old.length
  bound : i.old.length < 2 ^ 63

/-- The machine footprint and the process-image effect state. Phase witnesses
belong to the pure invariant, rather than duplicating owned resources. -/
structure State where
  machine : Stack.State
  memory : Effect.State

def State.withMachine (s : State) (m : Stack.State) : State := ⟨m, s.memory⟩
def State.withMemory (s : State) (m : Effect.State) : State := ⟨s.machine, m⟩

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
variable [Xv6G GF] [WchG GF] [CurCtx]

def payload (i : Inputs) (γl : GName) (γk : KmemNames) (s : State) : IProp GF := iprop%
  isLock γl kmemLockAddr "kmem" (kmemRes γk) ∗ kallocAvail γk none ∗
  procPtAt s.memory.table s.memory.image ∗
  byteBuf i.dst (DFrac.own 1) (Effect.buffer s.memory i.old) ∗
  actLend i.entry.proc s.memory.lend

end Xv6.WholeFunction.Copyin
