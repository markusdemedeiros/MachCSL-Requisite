import Experiments.WholeFunction.CopyoutCalls
import Experiments.WholeFunction.CopyoutModel

namespace Xv6.WholeFunction.Copyout
open Iris Iris.BI Iris.ProgramLogic MachCSL
open Iris.Std (get?)
open Experiments.WholeFunction

def writeLength (s : State) : Nat := (s.machine.ctx.regs 12#5).toNat
def BodyExit (s : State) : Prop := s.machine.pc = 0x80001662#64

/-- Return from a callee, retaining the caller's saved stack cells. -/
def returnState (s : State) (k : KCtx) (memory : Copy.State) : State :=
  ⟨⟨k, jumpPc (s.machine.ctx.regs 1#5), s.machine.cells⟩, memory⟩

structure WalkEnabled (i : Inputs) (s : State) : Prop where
  pc : s.machine.pc = KA.«walkaddr»
  stack : 10 ≤ s.machine.ctx.avail
  root : s.machine.ctx.regs 10#5 = pageAddr s.memory.table.root
  bound : cursor i s < 2 ^ 64
  address : s.machine.ctx.regs 11#5 = BitVec.ofNat 64 (cursor i s / 4096 * 4096)

def WalkNext (i : Inputs) (s t : State) : Prop :=
  ∃ R', t = returnState s (s.machine.ctx.withRegs R') s.memory ∧
    calleeSaved s.machine.ctx.regs R' ∧
    CopyCall.WalkPageResult s.memory.table (cursor i s) (R' 10#5)

theorem WalkNext.cells {i : Inputs} {s t : State} (h : WalkNext i s t) :
    t.machine.cells = s.machine.cells := by obtain ⟨R', rfl, _⟩ := h; rfl

theorem WalkNext.indices {i : Inputs} {s t : State} (h : WalkNext i s t) :
    t.machine.ctx.sie = s.machine.ctx.sie ∧ t.machine.ctx.proc = s.machine.ctx.proc := by
  obtain ⟨R', rfl, _⟩ := h
  exact ⟨rfl, rfl⟩

structure FaultEnabled (i : Inputs) (s : State) : Prop where
  pc : s.machine.pc = KA.«vmfault»
  noff : s.machine.ctx.noff + 1 < 2 ^ 31
  stack : vmfaultSlots ≤ s.machine.ctx.avail
  lock : "kmem" ∉ s.machine.ctx.locks
  root : s.machine.ctx.regs 10#5 = pageAddr s.memory.table.root
  sizeArg : s.machine.ctx.regs 11#5 = i.size
  size : i.size.toNat ≤ 2 ^ 38
  proc : s.machine.ctx.proc = i.entry.proc

def FaultNext (i : Inputs) (s t : State) : Prop :=
  ∃ spie spp R' memory,
    t = returnState s ((s.machine.ctx.withSpie spie spp).withRegs R') memory ∧
    (s.machine.ctx.sie = false → spie = s.machine.ctx.spie ∧ spp = s.machine.ctx.spp) ∧
    calleeSaved s.machine.ctx.regs R' ∧
    Copy.Step .write i.size i.dst s.memory memory ∧ memory.copied = s.memory.copied ∧
    CopyCall.FaultResult s.memory.table i.size (s.machine.ctx.regs 12#5) (R' 10#5) memory.table ∧ uptWf memory.table

theorem FaultNext.cells {i : Inputs} {s t : State} (h : FaultNext i s t) :
    t.machine.cells = s.machine.cells := by obtain ⟨_, _, _, _, rfl, _⟩ := h; rfl

theorem FaultNext.indices {i : Inputs} {s t : State} (h : FaultNext i s t) :
    t.machine.ctx.sie = s.machine.ctx.sie ∧ t.machine.ctx.proc = s.machine.ctx.proc := by
  obtain ⟨_, _, _, _, rfl, _⟩ := h
  exact ⟨rfl, rfl⟩

structure WriteEnabled (i : Inputs) (s : State) (n : Nat) (w : BitVec 64) : Prop where
  pc : s.machine.pc = KA.«memmove»
  stack : 2 ≤ s.machine.ctx.avail
  lookup : get? s.memory.table.um (cursor i s / 4096) = some w
  fit : cursor i s % 4096 + n ≤ 4096
  positive : 0 < n
  bound : s.memory.copied.length + n ≤ i.bytes.length
  access : ∀ j, j < n → uvaWmapped s.memory.table
    (i.dst + BitVec.ofNat 64 (s.memory.copied.length + j)).toNat
  srcArg : s.machine.ctx.regs 11#5 = i.src + BitVec.ofNat 64 s.memory.copied.length
  dstArg : s.machine.ctx.regs 10#5 = pte2pa w + BitVec.ofNat 64 (cursor i s % 4096)
  lenArg : s.machine.ctx.regs 12#5 = BitVec.ofNat 64 n

def writeMemory (i : Inputs) (s : State) (n : Nat) : Copy.State :=
  Copy.transfer .write i.dst s.memory ((i.bytes.drop s.memory.copied.length).take n)

def WriteNext (i : Inputs) (s : State) (n : Nat) (t : State) : Prop :=
  ∃ R', t = returnState s (s.machine.ctx.withRegs R') (writeMemory i s n) ∧
    calleeSaved s.machine.ctx.regs R' ∧ R' 10#5 = s.machine.ctx.regs 10#5 ∧
    Copy.Step .write i.size i.dst s.memory (writeMemory i s n)

theorem WriteNext.cells {i : Inputs} {s t : State} {n : Nat} (h : WriteNext i s n t) :
    t.machine.cells = s.machine.cells := by obtain ⟨_, rfl, _⟩ := h; rfl

theorem WriteNext.indices {i : Inputs} {s t : State} {n : Nat} (h : WriteNext i s n t) :
    t.machine.ctx.sie = s.machine.ctx.sie ∧ t.machine.ctx.proc = s.machine.ctx.proc := by
  obtain ⟨_, rfl, _⟩ := h
  exact ⟨rfl, rfl⟩


structure ProbeEnabled (_i : Inputs) (s : State) (w : BitVec 64) : Prop where
  pc : s.machine.pc = KA.«walk»
  stack : 8 ≤ s.machine.ctx.avail
  root : s.machine.ctx.regs 10#5 = pageAddr s.memory.table.root
  address : (s.machine.ctx.regs 11#5).toNat < 2 ^ 38
  alloc : s.machine.ctx.regs 12#5 = 0#64
  lookup : get? s.memory.table.um (vpnOf (s.machine.ctx.regs 11#5)).toNat = some w
  returnPC : jumpPc (s.machine.ctx.regs 1#5) = 0x80001644#64

def probeReturnState (s : State) (k : KCtx) : State :=
  ⟨⟨k, 0x80001646#64, s.machine.cells⟩, s.memory⟩

def ProbeNext (_i : Inputs) (s : State) (w : BitVec 64) (t : State) : Prop :=
  ∃ R', t = probeReturnState s (s.machine.ctx.withRegs R') ∧
    calleeSaved s.machine.ctx.regs R' ∧ R' 15#5 &&& PTE_W = w &&& PTE_W

theorem ProbeNext.cells {i : Inputs} {s t : State} {w : BitVec 64} (h : ProbeNext i s w t) :
    t.machine.cells = s.machine.cells := by obtain ⟨_, rfl, _⟩ := h; rfl

theorem ProbeNext.indices {i : Inputs} {s t : State} {w : BitVec 64} (h : ProbeNext i s w t) :
    t.machine.ctx.sie = s.machine.ctx.sie ∧ t.machine.ctx.proc = s.machine.ctx.proc := by
  obtain ⟨_, rfl, _⟩ := h
  exact ⟨rfl, rfl⟩

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [WchG GF] [CurCtx]

theorem probe_spec (W : WALK_NOALLOC) (i : Inputs) (γl : GName) (γk : KmemNames)
    (s : State) (w : BitVec 64) (ready : ProbeEnabled i s w) :
    CalleeSpec State.machine (payload (GF := GF) i γl γk) (ProbeNext i s w) s := by
  intro cpu
  unfold callOwn payload
  iintro ⟨⟨Hk, Hpc, #Hlk, #Hav, HP, Hsrc, Hlend⟩, Hexit⟩
  rw [ready.pc]
  iapply CopyCall.walk_load W cpu s.machine.ctx s.memory.table s.memory.image w
    ready.stack ready.root ready.address ready.alloc ready.lookup ready.returnPC
    $$ [$Hk $Hpc $HP Hsrc Hlend Hexit]
  iapply wpNext_intro_pin
  iintro %cpu' %hpin %R' Hk Hpc HP %result
  ihave Hexit := wpNext_at _ _ _ cpu' _ hpin $$ Hexit
  iapply Hexit $$ %(probeReturnState s (s.machine.ctx.withRegs R'))
    %(show ProbeNext i s w _ from ⟨R', rfl, result⟩) [Hk Hpc HP Hsrc Hlend]
  dsimp only [probeReturnState]
  iframe Hk Hpc HP Hsrc Hlend
  iframe #

theorem walk_spec (WA : WALKADDR) (i : Inputs) (γl : GName) (γk : KmemNames)
    (s : State) (ready : WalkEnabled i s) :
    CalleeSpec State.machine (payload (GF := GF) i γl γk) (WalkNext i s) s := by
  intro cpu
  unfold callOwn payload
  iintro ⟨⟨Hk, Hpc, #Hlk, #Hav, HP, Hdst, Hlend⟩, Hexit⟩
  rw [ready.pc]
  iapply CopyCall.walkaddr_page WA cpu s.machine.ctx s.memory.table s.memory.image
    (cursor i s) ready.bound ready.stack ready.root ready.address
    $$ [$Hk $Hpc $HP Hdst Hlend Hexit]
  iapply wpNext_intro_pin
  iintro %cpu' %hpin %R' Hk Hpc HP %result
  ihave Hexit := wpNext_at _ _ _ cpu' _ hpin $$ Hexit
  iapply Hexit $$ %(returnState s (s.machine.ctx.withRegs R') s.memory)
    %(show WalkNext i s _ from ⟨R', rfl, result⟩) [Hk Hpc HP Hdst Hlend]
  dsimp only [returnState]
  iframe Hk Hpc HP Hdst Hlend
  iframe #

theorem fault_spec (VF : VMFAULT) (i : Inputs) (γl : GName) (γk : KmemNames)
    (s : State) (ready : FaultEnabled i s) :
    CalleeSpec State.machine (payload (GF := GF) i γl γk) (FaultNext i s) s := by
  intro cpu
  unfold callOwn payload
  iintro ⟨⟨Hk, Hpc, #Hlk, #Hav, HP, Hdst, Hlend⟩, Hexit⟩
  rw [ready.pc, ← ready.proc]
  iapply CopyCall.fault VF cpu s.machine.ctx γl γk s.memory i.dst ready.noff ready.stack
    ready.lock ready.root (by rw [ready.sizeArg]; exact ready.size)
    $$ [$Hk $Hpc $Hlk $Hav $HP $Hlend Hdst Hexit]
  iapply wpNext_intro_pin
  iintro %cpu' %hpin %spie %spp %R' %memory %flags Hk Hpc Hlend HP %step %copied %result %saved
  rw [ready.sizeArg] at step result
  have step := CopyCall.fault_step_write step copied
  icases UMemL.procPtAt_wf memory.table memory.image $$ HP with ⟨HP, %wf⟩
  ihave Hexit := wpNext_at _ _ _ cpu' _ hpin $$ Hexit
  iapply Hexit $$ %(returnState s ((s.machine.ctx.withSpie spie spp).withRegs R') memory)
    %(show FaultNext i s _ from ⟨spie, spp, R', memory, rfl, flags, saved, step, copied, result, wf⟩)
    [Hk Hpc HP Hdst Hlend]
  dsimp only [returnState]
  iframe Hk Hpc HP Hdst Hlend
  iframe #

theorem write_spec (MM : MEMMOVE) (i : Inputs) (γl : GName) (γk : KmemNames)
    (s : State) (n : Nat) (w : BitVec 64) (ready : WriteEnabled i s n w) :
    CalleeSpec State.machine (payload (GF := GF) i γl γk) (WriteNext i s n) s := by
  intro cpu
  unfold callOwn payload
  iintro ⟨⟨Hk, Hpc, #Hlk, #Hav, HP, Hdst, Hlend⟩, Hexit⟩
  rw [ready.pc]
  iapply CopyCall.write_chunk MM cpu s.machine.ctx s.memory i.size i.dst w i.src i.fraction i.bytes n
    ready.lookup ready.fit ready.positive ready.bound ready.access ready.stack
    ready.srcArg ready.dstArg ready.lenArg $$ [$Hk $Hpc $HP $Hdst Hlend Hexit]
  iapply wpNext_intro_pin
  iintro %cpu' %hpin %R' Hk Hpc HP Hdst %step %result
  ihave Hexit := wpNext_at _ _ _ cpu' _ hpin $$ Hexit
  iapply Hexit $$ %(returnState s (s.machine.ctx.withRegs R') (writeMemory i s n))
    %(show WriteNext i s n _ from ⟨R', rfl, result.1, result.2, step⟩) [Hk Hpc HP Hdst Hlend]
  dsimp only [returnState, writeMemory, Copy.transfer, Copy.imageAfter, cursor]
  iframe Hk Hpc HP Hdst Hlend
  iframe #

end Xv6.WholeFunction.Copyout

/-- info: 'Xv6.WholeFunction.Copyout.walk_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Xv6.WholeFunction.Copyout.walk_spec
/-- info: 'Xv6.WholeFunction.Copyout.fault_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Xv6.WholeFunction.Copyout.fault_spec
/-- info: 'Xv6.WholeFunction.Copyout.write_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Xv6.WholeFunction.Copyout.write_spec
open Lean in
run_cmd do
  let baseline ← collectAxioms ``MachCSL.wp_s_ld
  let axs ← collectAxioms ``Xv6.WholeFunction.Copyout.probe_spec
  let extra := axs.filter fun ax => !baseline.contains ax
  unless extra.isEmpty do throwError "probe_spec adds axioms {extra}"
