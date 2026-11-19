import Xv6.CopyLemmas
import Xv6.UMemLemmas
import Experiments.WholeFunction.CopyContracts

/-! Reusable spatial call actions for the copy compiler. This is a MEMMOVE
contract adapter over an abstract process image and a destination window;
there are no copyin PCs, loop-body instructions, or loop invariants here.
It does not prove COPYIN: automatic stack, call dispatch and cutpoint compilation
remain necessary before the original proof can be deleted.
-/
namespace Xv6.WholeFunction
open Iris Iris.BI Iris.ProgramLogic MachCSL
open Iris.Std (get?)

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]

/-- Borrow a page-contained logical read as physical bytes; returning the same
bytes restores the process image, including its page-table ownership. -/
theorem user_read_window (P : UPtd) (M : Nat → List (BitVec 8))
    (va n : Nat) (w : BitVec 64)
    (lookup : get? P.um (va / 4096) = some w)
    (fit : va % 4096 + n ≤ 4096) :
    procPtAt P M ⊢@{IProp GF}
      byteBuf (pte2pa w + BitVec.ofNat 64 (va % 4096)) (DFrac.own 1) (umemRead M va n) ∗
      (byteBuf (pte2pa w + BitVec.ofNat 64 (va % 4096)) (DFrac.own 1) (umemRead M va n)
        -∗ procPtAt P M) := by
  iintro HP
  icases UMemL.procPtAt_elim P M $$ HP with ⟨%hwf, ⟨%t, %ht, Htree⟩, Hpages⟩
  icases UMemL.umPages_acc P M (va / 4096) w lookup $$ Hpages
    with ⟨%hlen, Hpage, Hclose⟩
  have hread : umemRead M va n = ((M (va / 4096)).drop (va % 4096)).take n :=
    UMemL.umemRead_in M va n (va / 4096) (va % 4096) hlen (by omega) fit
  icases UMemL.byteBuf_split_td (pte2pa w) (DFrac.own 1) (M (va / 4096))
    (va % 4096) n (by omega) $$ Hpage with ⟨Hprefix, Hbytes, Hsuffix⟩
  rw [← hread]
  isplitl [Hbytes]
  · iexact Hbytes
  · iintro Hbytes
    ihave Hpage := UMemL.byteBuf_join_td (pte2pa w) (DFrac.own 1) (M (va / 4096))
      (umemRead M va n) (va % 4096) n (by omega) (UMemL.umemRead_length M va n)
      $$ [$Hprefix $Hbytes $Hsuffix]
    have hrestore : (M (va / 4096)).take (va % 4096) ++
        (umemRead M va n ++ (M (va / 4096)).drop (va % 4096 + n)) = M (va / 4096) := by
      rw [hread, ← List.drop_drop, List.take_append_drop, List.take_append_drop]
    rw [hrestore]
    ihave Hpages := Hclose $$ %hlen Hpage
    iapply UMemL.procPtAt_intro' P M t ht hwf $$ [$Htree $Hpages]

/-- Writable destination window. The returned value is arbitrary but has the
same length, so neighboring spatial resources can be reassembled unchanged. -/
theorem destination_window (dst : BitVec 64) (old : List (BitVec 8)) (off n : Nat)
    (bound : off + n ≤ old.length) :
    byteBuf dst (DFrac.own 1) old ⊢@{IProp GF}
      byteBuf (dst + BitVec.ofNat 64 off) (DFrac.own 1) ((old.drop off).take n) ∗
      (∀ new : List (BitVec 8), ⌜new.length = n⌝ -∗
        byteBuf (dst + BitVec.ofNat 64 off) (DFrac.own 1) new -∗
        byteBuf dst (DFrac.own 1) (old.take off ++ (new ++ old.drop (off + n)))) := by
  iintro Hdst
  icases UMemL.byteBuf_split_td dst (DFrac.own 1) old off n bound $$ Hdst
    with ⟨Hprefix, Hbytes, Hsuffix⟩
  isplitl [Hbytes]
  · iexact Hbytes
  · iintro %new %hlen Hbytes
    iapply UMemL.byteBuf_join_td dst (DFrac.own 1) old new off n bound hlen
      $$ [$Hprefix $Hbytes $Hsuffix]

/-- Registered call effect: MEMMOVE copies a logical process-image window
into a kernel buffer while restoring the source process resources. Interrupt
and hart migration behavior is exactly that of the original callee contract.
This adapter can serve any caller, not just the copyin loop. -/
theorem memmove_from_user (MM : MEMMOVE) (cpu : CPU) (k : KCtx)
    (P : UPtd) (M : Nat → List (BitVec 8)) (w dst : BitVec 64)
    (old : List (BitVec 8)) (va off n : Nat)
    (lookup : get? P.um (va / 4096) = some w) (fit : va % 4096 + n ≤ 4096)
    (bound : off + n ≤ old.length) (stack : 2 ≤ k.avail)
    (srcArg : k.regs 11#5 = pte2pa w + BitVec.ofNat 64 (va % 4096))
    (dstArg : k.regs 10#5 = dst + BitVec.ofNat 64 off)
    (lenArg : k.regs 12#5 = BitVec.ofNat 64 n) :
    kctx cpu k ∗ pcIs cpu KA.«memmove» ∗ procPtAt P M ∗ byteBuf dst (DFrac.own 1) old ∗
    wpNext k.sie k.proc cpu (fun cpu' => iprop(∀ R' : RegMap,
      kctx cpu' (k.withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
      procPtAt P M -∗
      byteBuf dst (DFrac.own 1) (old.take off ++ (umemRead M va n ++ old.drop (off + n))) -∗
      ⌜calleeSaved k.regs R' ∧ R' 10#5 = k.regs 10#5⌝ -∗ wpLoop cpu'))
      ⊢ wpLoop (GF := GF) cpu := by
  iintro ⟨Hk, Hpc, HP, Hdst, Hexit⟩
  icases user_read_window P M va n w lookup fit $$ HP with ⟨Hsrc, HsrcClose⟩
  icases destination_window dst old off n bound $$ Hdst with ⟨Hdst, HdstClose⟩
  have hlen : ((old.drop off).take n).length = n := by
    simp only [List.length_take, List.length_drop]; omega
  iapply co_memmove_call MM cpu k (umemRead M va n) ((old.drop off).take n)
    n (DFrac.own 1) stack lenArg (by omega) (UMemL.umemRead_length M va n) hlen
    $$ [- $Hk $Hpc]
  rw [srcArg, dstArg]
  iframe Hsrc Hdst
  iapply wpNext_intro_pin
  iintro %cpu' %hpin %R' Hk Hpc Hsrc Hdst %hpost
  ihave HP := HsrcClose $$ Hsrc
  ihave Hdst := HdstClose $$ %(umemRead M va n) %(UMemL.umemRead_length M va n) Hdst
  ihave Hexit := wpNext_at k.sie k.proc cpu cpu' _ hpin $$ Hexit
  iapply Hexit $$ %R' Hk Hpc HP Hdst %hpost

namespace CopyCall
open Experiments.WholeFunction.Copy

/-- The call action produces the same local effect used by the whole-copy
trace theorem. Its spatial postcondition owns the updated buffer, rather than
assuming that an abstract trace can manufacture ownership. Lend resources
are unchanged by this action and can be framed by its caller. -/
theorem read_chunk (MM : MEMMOVE) (cpu : CPU) (k : KCtx)
    (s : State) (sz a w dst : BitVec 64) (old : List (BitVec 8)) (n : Nat)
    (lookup : get? s.table.um ((a.toNat + s.copied.length) / 4096) = some w)
    (fit : (a.toNat + s.copied.length) % 4096 + n ≤ 4096)
    (positive : 0 < n) (bound : s.copied.length + n ≤ old.length)
    (access : ∀ j, j < n → uvaRmapped s.table (a + BitVec.ofNat 64 (s.copied.length + j)).toNat)
    (stack : 2 ≤ k.avail)
    (srcArg : k.regs 11#5 = pte2pa w + BitVec.ofNat 64 ((a.toNat + s.copied.length) % 4096))
    (dstArg : k.regs 10#5 = dst + BitVec.ofNat 64 s.copied.length)
    (lenArg : k.regs 12#5 = BitVec.ofNat 64 n) :
    let after := transfer .read a s (umemRead s.image (a.toNat + s.copied.length) n)
    kctx cpu k ∗ pcIs cpu KA.«memmove» ∗ procPtAt s.table s.image ∗
    byteBuf dst (DFrac.own 1) (buffer s old) ∗
    wpNext k.sie k.proc cpu (fun cpu' => iprop(∀ R' : RegMap,
      kctx cpu' (k.withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
      procPtAt after.table after.image -∗ byteBuf dst (DFrac.own 1) (buffer after old) -∗
      ⌜Step .read sz a s after⌝ -∗
      ⌜calleeSaved k.regs R' ∧ R' 10#5 = k.regs 10#5⌝ -∗ wpLoop cpu'))
      ⊢ wpLoop (GF := GF) cpu := by
  dsimp only
  let chunk := umemRead s.image (a.toNat + s.copied.length) n
  have hlen : chunk.length = n := UMemL.umemRead_length _ _ _
  have hstep : Step .read sz a s (transfer .read a s chunk) := by
    apply Step.chunk
    · omega
    · simpa only [hlen] using fit
    · simpa only [hlen] using UMemL.umMapped_page fit (by rw [lookup]; rfl)
    · simpa only [hlen, permission] using access
    · intro _; rw [hlen]
  have hbound : s.copied.length + n ≤ (buffer s old).length := by
    simp only [buffer, List.length_append, List.length_drop]; omega
  have htake : (buffer s old).take s.copied.length = s.copied :=
    List.take_left' rfl
  have hdrop : (buffer s old).drop (s.copied.length + n) = old.drop (s.copied.length + n) := by
    unfold buffer
    rw [← List.drop_drop, List.drop_left' rfl, List.drop_drop]
  have hbuffer : (buffer s old).take s.copied.length ++
      (chunk ++ (buffer s old).drop (s.copied.length + n)) = buffer (transfer .read a s chunk) old := by
    rw [htake, hdrop]
    simp only [buffer, transfer, List.length_append, hlen, List.append_assoc]
  iintro ⟨Hk, Hpc, HP, Hdst, Hexit⟩
  iapply memmove_from_user MM cpu k s.table s.image w dst (buffer s old)
    (a.toNat + s.copied.length) s.copied.length n lookup fit hbound stack srcArg dstArg lenArg
    $$ [$Hk $Hpc $HP $Hdst Hexit]
  iapply wpNext_intro_pin
  iintro %cpu' %hpin %R' Hk Hpc HP Hdst %hpost
  rw [hbuffer]
  simp only [transfer, imageAfter]
  ihave Hexit := wpNext_at k.sie k.proc cpu cpu' _ hpin $$ Hexit
  iapply Hexit $$ %R' Hk Hpc HP Hdst %hstep %hpost

end CopyCall

end Xv6.WholeFunction

/-! VMFAULT as an abstract, spatial copy-machine action. This is a reusable
callee boundary, not a proof of copyin's binary. The allocation lend and the
zeroed image come from VMFAULT's actual spatial contract. -/
namespace Xv6.WholeFunction.CopyCall
open Iris Iris.BI Iris.ProgramLogic MachCSL
open Iris.Std (get?)
open Experiments.WholeFunction.Copy

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [WchG GF] [CurCtx]

def FaultResult (P : UPtd) (sz va ret : BitVec 64) (Q : UPtd) : Prop :=
  (ret = 0#64 ∧ Q = P) ∨
  (∃ r : BitVec 64, ret = r ∧ pageValid r ∧ va.toNat < sz.toNat ∧
    get? P.um (vpnOf va).toNat = none ∧
    Q = P.insertLeaf (vpnOf va).toNat r (PTE_W ||| PTE_U ||| PTE_R))

/-- Both failed and successful faults advance the abstract effect machine.
A failed allocation may still advance the lend; its table/image stay fixed.
The effect's zeroing equation is proved from the callee's returned ownership.
-/
theorem fault (VF : VMFAULT) (cpu : CPU) (k : KCtx)
    (γl : GName) (γk : KmemNames) (s : State) (a : BitVec 64)
    (noff : k.noff + 1 < 2 ^ 31) (stack : vmfaultSlots ≤ k.avail)
    (lock : "kmem" ∉ k.locks) (root : k.regs 10#5 = pageAddr s.table.root)
    (size : (k.regs 11#5).toNat ≤ 2 ^ 38) :
    kctx cpu k ∗ pcIs cpu KA.«vmfault» ∗ isLock γl kmemLockAddr "kmem" (kmemRes γk) ∗
    kallocAvail γk none ∗ procPtAt s.table s.image ∗ actLend k.proc s.lend ∗
    wpNext k.sie k.proc cpu (fun cpu' => iprop(∀ (spie spp : Bool) (R' : RegMap) (after : State),
      ⌜k.sie = false → spie = k.spie ∧ spp = k.spp⌝ -∗
      kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
      actLend k.proc after.lend -∗ procPtAt after.table after.image -∗
      ⌜Step .read (k.regs 11#5) a s after⌝ -∗
      ⌜after.copied = s.copied⌝ -∗
      ⌜FaultResult s.table (k.regs 11#5) (k.regs 12#5) (R' 10#5) after.table⌝ -∗
      ⌜calleeSaved k.regs R'⌝ -∗ wpLoop cpu'))
      ⊢ wpLoop (GF := GF) cpu := by
  iintro ⟨Hk, Hpc, Hlock, Havail, HP, Hlend, Hexit⟩
  iapply co_vmfault_call VF cpu k γl γk s.table s.image noff stack lock root size s.lend
    $$ [$Hk $Hpc $Hlock $Havail $HP $Hlend Hexit]
  iapply wpNext_intro_pin
  iintro %cpu' %hpin %spie %spp %R' %hsp Hk Hpc ⟨%ke, %hke, Hlend⟩ Hresult %hcs
  ihave Hexit := wpNext_at k.sie k.proc cpu cpu' _ hpin $$ Hexit
  icases Hresult with ⟨Hfailed | Hsuccess⟩
  · icases Hfailed with ⟨%hzero, HP⟩
    have hstep : Step .read (k.regs 11#5) a s (extend s s.table ke) :=
      .fault s s.table ke (UMemL.extSz_refl _ _) hke
    have hresult : FaultResult s.table (k.regs 11#5) (k.regs 12#5) (R' 10#5) s.table :=
      Or.inl ⟨hzero, rfl⟩
    ihave Hexit := Hexit $$ %spie %spp %R' %(extend s s.table ke) %hsp Hk Hpc
    simp only [extend, UMemL.viewFaulted_self]
    simp only [extend, UMemL.viewFaulted_self] at hstep
    iapply Hexit $$ Hlend HP %hstep %True.intro %hresult %hcs
  · icases Hsuccess with ⟨%r, ⟨%hret, %hvalid, %hva, %hnone⟩, HP⟩
    let Q := s.table.insertLeaf (vpnOf (k.regs 12#5)).toNat r (PTE_W ||| PTE_U ||| PTE_R)
    have hext : s.table.extSz (k.regs 11#5) Q := by
      apply UMemL.extSz_insertLeaf _ _ _ _ hnone
      rw [co_vpnOf_toNat _ (by omega)]
      omega
    have hstep : Step .read (k.regs 11#5) a s (extend s Q ke) := .fault s Q ke hext hke
    have himage : viewFaulted s.table Q s.image =
        viewZero s.image (vpnOf (k.regs 12#5)).toNat := by
      rw [UMemL.viewFaulted_insertLeaf _ _ _ _ _ _ (UMemL.ext_refl _) hnone,
        UMemL.viewFaulted_self]
    have hresult : FaultResult s.table (k.regs 11#5) (k.regs 12#5) (R' 10#5) Q :=
      Or.inr ⟨r, hret, hvalid, hva, hnone, rfl⟩
    ihave Hexit := Hexit $$ %spie %spp %R' %(extend s Q ke) %hsp Hk Hpc
    simp only [extend, himage]
    simp only [extend, himage] at hstep
    iapply Hexit $$ Hlend HP %hstep %True.intro %hresult %hcs

end Xv6.WholeFunction.CopyCall

/-- info: 'Xv6.WholeFunction.memmove_from_user' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Xv6.WholeFunction.memmove_from_user

/-- info: 'Xv6.WholeFunction.CopyCall.read_chunk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Xv6.WholeFunction.CopyCall.read_chunk

/-- info: 'Xv6.WholeFunction.CopyCall.fault' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Xv6.WholeFunction.CopyCall.fault

