import Experiments.WholeFunction.CopyCalls
import Experiments.WholeFunction.CopyinModel
import Experiments.WholeFunction.KernelCalls

/-! Callee adapters and branch facts for the whole-copy compiler. All spatial
rules are applications of the original public callee contracts. No instruction
or loop-body proof from ProofCopyin is imported. -/
namespace Xv6.WholeFunction.CopyCall
open Iris Iris.BI Iris.ProgramLogic MachCSL
open Iris.Std (get?)

-- The production counterpart uses native bv_decide for this mask. Keep the
-- compiler's new call certificates kernel checked using bit-projection lemmas.
private theorem tfLeaf_not_vu_checked (ppn : BitVec 44) : ¬ pteVU (tfLeaf ppn) := by
  intro h
  apply h.2
  change tfLeaf ppn &&& BitVec.twoPow 64 4 = 0#64
  rw [BitVec.and_twoPow]
  simp [tfLeaf, leafOf, PTE_R, PTE_W]

private theorem um_of_leaves_vu_checked (P : UPtd) (k : Nat) (w : BitVec 64)
    (hl : get? P.leaves k = some w) (hvu : pteVU w) : get? P.um k = some w := by
  unfold UPtd.leaves at hl
  by_cases h1 : trampVpn.toNat = k
  · rw [Iris.Std.LawfulPartialMap.get?_insert_eq h1] at hl
    cases hl
    exact absurd hvu (by unfold pteVU; decide : ¬ pteVU trampLeaf)
  · rw [Iris.Std.LawfulPartialMap.get?_insert_ne h1] at hl
    by_cases h2 : tfVpn.toNat = k
    · rw [Iris.Std.LawfulPartialMap.get?_insert_eq h2] at hl
      cases hl
      exact absurd hvu (tfLeaf_not_vu_checked _)
    · rw [Iris.Std.LawfulPartialMap.get?_insert_ne h2] at hl
      exact hl

/-- The logical information needed after walking the page containing `cursor`.
The zero result refutes readability at that byte; a nonzero result identifies
the precise owned user page and the physical page address. -/
structure WalkPageResult (P : UPtd) (cursor : Nat) (ret : BitVec 64) : Prop where
  zero : ret = 0#64 → ¬ uvaRmapped P cursor
  nonzero : ret ≠ 0#64 → ∃ w,
    get? P.um (cursor / 4096) = some w ∧ pteVU w ∧
    ret = pte2pa w ∧ cursor / 4096 * 4096 < 2 ^ 38

theorem walk_page_result (P : UPtd) (cursor : Nat) (ret : BitVec 64)
    (wf : uptWf P) (bound : cursor < 2 ^ 64)
    (result : walkaddrRet P.leaves (BitVec.ofNat 64 (cursor / 4096 * 4096)) ret) :
    WalkPageResult P cursor ret := by
  constructor
  · intro zero
    rcases result with ⟨_, why⟩ | ⟨w, lookup, vu, _, page⟩
    · exact ci_fault_leaf P P cursor (UMemL.ext_refl P) wf bound why
    · have um := um_of_leaves_vu_checked P _ w lookup vu
      exact False.elim (PtRun.pageValid_ne_zero _ (wf.1 _ w um).2.2 (page.symm.trans zero))
  · intro nonzero
    rcases result with ⟨zero, _⟩ | ⟨w, lookup, vu, below, page⟩
    · exact False.elim (nonzero zero)
    · have natPage : (BitVec.ofNat 64 (cursor / 4096 * 4096)).toNat = cursor / 4096 * 4096 := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have vpn : (vpnOf (BitVec.ofNat 64 (cursor / 4096 * 4096))).toNat = cursor / 4096 := by
        rw [co_vpnOf_toNat _ (by omega), natPage]
        omega
      have um := um_of_leaves_vu_checked P _ w lookup vu
      rw [vpn] at um
      exact ⟨w, um, vu, page, by omega⟩

/-- Failure remains a witness about any earlier table extended by the current
one, as required by COPYIN's original failure postcondition. -/
theorem WalkPageResult.zero_at_entry {P Q : UPtd} {cursor : Nat} {ret : BitVec 64}
    (result : WalkPageResult Q cursor ret) (extension : P.ext Q) (zero : ret = 0#64) :
    ¬ uvaRmapped P cursor := fun readable =>
  result.zero zero (UMemL.uvaRmapped_mono extension readable)

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]

/-- WALKADDR registered at the process-image level. Page ownership is framed
through the tree-only public specification and reassembled before returning.
No registers, flags, or image contents are silently strengthened. -/
theorem walkaddr_user (WA : WALKADDR) (cpu : CPU) (k : KCtx)
    (P : UPtd) (M : Nat → List (BitVec 8))
    (stack : 10 ≤ k.avail) (root : k.regs 10#5 = pageAddr P.root) :
    kctx cpu k ∗ pcIs cpu KA.«walkaddr» ∗ procPtAt P M ∗
    wpNext k.sie k.proc cpu (fun cpu' => iprop(∀ R' : RegMap,
      kctx cpu' (k.withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗ procPtAt P M -∗
      ⌜uptWf P ∧ calleeSaved k.regs R' ∧ walkaddrRet P.leaves (k.regs 11#5) (R' 10#5)⌝ -∗
      wpLoop cpu')) ⊢ wpLoop (GF := GF) cpu := by
  iintro ⟨Hk, Hpc, HP, Hexit⟩
  icases UMemL.procPtAt_elim P M $$ HP with ⟨%wf, ⟨%t, %tree, Htree⟩, Hpages⟩
  have root' : k.regs 10#5 = pageAddr t.base := by rw [tree.1]; exact root
  iapply co_walkaddr_call WA cpu k (DFrac.own 1) t P.leaves stack root' tree.2
    $$ [$Hk $Hpc $Htree Hpages Hexit]
  iapply wpNext_intro_pin
  iintro %cpu' %hpin %R' Hk Hpc Htree %result
  ihave HP := UMemL.procPtAt_intro' P M t tree wf $$ [$Htree $Hpages]
  ihave Hexit := wpNext_at k.sie k.proc cpu cpu' _ hpin $$ Hexit
  iapply Hexit $$ %R' Hk Hpc HP %⟨wf, result⟩

/-- The page-aligned call interface used by the copy loop's generated call
node. It returns branch facts about the cursor without a separate per-loop
walkaddr adapter. -/
theorem walkaddr_page (WA : WALKADDR) (cpu : CPU) (k : KCtx)
    (P : UPtd) (M : Nat → List (BitVec 8)) (cursor : Nat)
    (bound : cursor < 2 ^ 64) (stack : 10 ≤ k.avail)
    (root : k.regs 10#5 = pageAddr P.root)
    (address : k.regs 11#5 = BitVec.ofNat 64 (cursor / 4096 * 4096)) :
    kctx cpu k ∗ pcIs cpu KA.«walkaddr» ∗ procPtAt P M ∗
    wpNext k.sie k.proc cpu (fun cpu' => iprop(∀ R' : RegMap,
      kctx cpu' (k.withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗ procPtAt P M -∗
      ⌜calleeSaved k.regs R' ∧ WalkPageResult P cursor (R' 10#5)⌝ -∗
      wpLoop cpu')) ⊢ wpLoop (GF := GF) cpu := by
  iintro ⟨Hk, Hpc, HP, Hexit⟩
  iapply walkaddr_user WA cpu k P M stack root $$ [$Hk $Hpc $HP Hexit]
  iapply wpNext_intro_pin
  iintro %cpu' %hpin %R' Hk Hpc HP %result
  obtain ⟨wf, saved, walked⟩ := result
  rw [address] at walked
  ihave Hexit := wpNext_at k.sie k.proc cpu cpu' _ hpin $$ Hexit
  iapply Hexit $$ %R' Hk Hpc HP %⟨saved, walk_page_result P cursor _ wf bound walked⟩

end Xv6.WholeFunction.CopyCall

/-- info: 'Xv6.WholeFunction.CopyCall.walkaddr_page' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Xv6.WholeFunction.CopyCall.walkaddr_page

namespace Xv6.WholeFunction.Copyin
open Iris Iris.BI Iris.ProgramLogic MachCSL
open Iris.Std (get?)
open Experiments.WholeFunction

/-- Return from a callee, retaining the caller's saved stack cells. -/
def returnState (s : State) (k : KCtx) (memory : Copy.State) : State :=
  ⟨⟨k, jumpPc (s.machine.ctx.regs 1#5), s.machine.cells⟩, memory⟩

def cursor (i : Inputs) (s : State) : Nat := i.src.toNat + s.memory.copied.length

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
    Copy.Step .read i.size i.src s.memory memory ∧ memory.copied = s.memory.copied ∧
    CopyCall.FaultResult s.memory.table i.size (s.machine.ctx.regs 12#5) (R' 10#5) memory.table

theorem FaultNext.cells {i : Inputs} {s t : State} (h : FaultNext i s t) :
    t.machine.cells = s.machine.cells := by obtain ⟨_, _, _, _, rfl, _⟩ := h; rfl

theorem FaultNext.indices {i : Inputs} {s t : State} (h : FaultNext i s t) :
    t.machine.ctx.sie = s.machine.ctx.sie ∧ t.machine.ctx.proc = s.machine.ctx.proc := by
  obtain ⟨_, _, _, _, rfl, _⟩ := h
  exact ⟨rfl, rfl⟩

structure ReadEnabled (i : Inputs) (s : State) (n : Nat) (w : BitVec 64) : Prop where
  pc : s.machine.pc = KA.«memmove»
  stack : 2 ≤ s.machine.ctx.avail
  lookup : get? s.memory.table.um (cursor i s / 4096) = some w
  fit : cursor i s % 4096 + n ≤ 4096
  positive : 0 < n
  bound : s.memory.copied.length + n ≤ i.old.length
  access : ∀ j, j < n → uvaRmapped s.memory.table
    (i.src + BitVec.ofNat 64 (s.memory.copied.length + j)).toNat
  srcArg : s.machine.ctx.regs 11#5 = pte2pa w + BitVec.ofNat 64 (cursor i s % 4096)
  dstArg : s.machine.ctx.regs 10#5 = i.dst + BitVec.ofNat 64 s.memory.copied.length
  lenArg : s.machine.ctx.regs 12#5 = BitVec.ofNat 64 n

def readMemory (i : Inputs) (s : State) (n : Nat) : Copy.State :=
  Copy.transfer .read i.src s.memory (umemRead s.memory.image (cursor i s) n)

def ReadNext (i : Inputs) (s : State) (n : Nat) (t : State) : Prop :=
  ∃ R', t = returnState s (s.machine.ctx.withRegs R') (readMemory i s n) ∧
    calleeSaved s.machine.ctx.regs R' ∧ R' 10#5 = s.machine.ctx.regs 10#5 ∧
    Copy.Step .read i.size i.src s.memory (readMemory i s n)

theorem ReadNext.cells {i : Inputs} {s t : State} {n : Nat} (h : ReadNext i s n t) :
    t.machine.cells = s.machine.cells := by obtain ⟨_, rfl, _⟩ := h; rfl

theorem ReadNext.indices {i : Inputs} {s t : State} {n : Nat} (h : ReadNext i s n t) :
    t.machine.ctx.sie = s.machine.ctx.sie ∧ t.machine.ctx.proc = s.machine.ctx.proc := by
  obtain ⟨_, rfl, _⟩ := h
  exact ⟨rfl, rfl⟩

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [WchG GF] [CurCtx]

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
  iapply CopyCall.fault VF cpu s.machine.ctx γl γk s.memory i.src ready.noff ready.stack
    ready.lock ready.root (by rw [ready.sizeArg]; exact ready.size)
    $$ [$Hk $Hpc $Hlk $Hav $HP $Hlend Hdst Hexit]
  iapply wpNext_intro_pin
  iintro %cpu' %hpin %spie %spp %R' %memory %flags Hk Hpc Hlend HP %step %copied %result %saved
  rw [ready.sizeArg] at step result
  have buffer_eq : Copy.buffer memory i.old = Copy.buffer s.memory i.old := by
    unfold Copy.buffer; rw [copied]
  rw [← buffer_eq]
  ihave Hexit := wpNext_at _ _ _ cpu' _ hpin $$ Hexit
  iapply Hexit $$ %(returnState s ((s.machine.ctx.withSpie spie spp).withRegs R') memory)
    %(show FaultNext i s _ from ⟨spie, spp, R', memory, rfl, flags, saved, step, copied, result⟩)
    [Hk Hpc HP Hdst Hlend]
  dsimp only [returnState]
  iframe Hk Hpc HP Hdst Hlend
  iframe #

theorem read_spec (MM : MEMMOVE) (i : Inputs) (γl : GName) (γk : KmemNames)
    (s : State) (n : Nat) (w : BitVec 64) (ready : ReadEnabled i s n w) :
    CalleeSpec State.machine (payload (GF := GF) i γl γk) (ReadNext i s n) s := by
  intro cpu
  unfold callOwn payload
  iintro ⟨⟨Hk, Hpc, #Hlk, #Hav, HP, Hdst, Hlend⟩, Hexit⟩
  rw [ready.pc]
  iapply CopyCall.read_chunk MM cpu s.machine.ctx s.memory i.size i.src w i.dst i.old n
    ready.lookup ready.fit ready.positive ready.bound ready.access ready.stack
    ready.srcArg ready.dstArg ready.lenArg $$ [$Hk $Hpc $HP $Hdst Hlend Hexit]
  iapply wpNext_intro_pin
  iintro %cpu' %hpin %R' Hk Hpc HP Hdst %step %result
  ihave Hexit := wpNext_at _ _ _ cpu' _ hpin $$ Hexit
  iapply Hexit $$ %(returnState s (s.machine.ctx.withRegs R') (readMemory i s n))
    %(show ReadNext i s n _ from ⟨R', rfl, result.1, result.2, step⟩) [Hk Hpc HP Hdst Hlend]
  dsimp only [returnState, readMemory, Copy.transfer, Copy.imageAfter, cursor]
  iframe Hk Hpc HP Hdst Hlend
  iframe #

end Xv6.WholeFunction.Copyin

/-- info: 'Xv6.WholeFunction.Copyin.walk_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Xv6.WholeFunction.Copyin.walk_spec
/-- info: 'Xv6.WholeFunction.Copyin.fault_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Xv6.WholeFunction.Copyin.fault_spec
/-- info: 'Xv6.WholeFunction.Copyin.read_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Xv6.WholeFunction.Copyin.read_spec
