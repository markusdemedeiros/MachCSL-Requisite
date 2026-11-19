import Experiments.WholeFunction.CopyCallRegistry
import Experiments.WholeFunction.BinaryCopy
import Xv6.SpecWalk

/-! Spatial effects for writes and the page-table permission probe. These
adapters consume the original public callee contracts. -/
namespace Xv6.WholeFunction
open Iris Iris.BI Iris.ProgramLogic MachCSL
open Iris.Std (get?)
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]

/-- Borrow a writable logical page window and close it with the new bytes. -/
theorem user_write_window (P : UPtd) (M : Nat → List (BitVec 8))
    (va : Nat) (bs : List (BitVec 8)) (w : BitVec 64)
    (lookup : get? P.um (va / 4096) = some w)
    (fit : va % 4096 + bs.length ≤ 4096) :
    procPtAt P M ⊢@{IProp GF}
      byteBuf (pte2pa w + BitVec.ofNat 64 (va % 4096)) (DFrac.own 1)
        (umemRead M va bs.length) ∗
      (byteBuf (pte2pa w + BitVec.ofNat 64 (va % 4096)) (DFrac.own 1) bs
        -∗ procPtAt P (umemWrite M va bs)) := by
  iintro HP
  icases UMemL.procPtAt_elim P M $$ HP with ⟨%wf, ⟨%t, %tree, Htree⟩, Hpages⟩
  icases UMemL.umPages_upd P M (umemWrite M va bs) (va / 4096) w lookup
    (fun j v _ ne len => UMemL.umemWrite_off M va bs (va / 4096) (va % 4096)
      (by omega) fit j ne len) $$ Hpages with ⟨%len, Hpage, Hclose⟩
  have read : umemRead M va bs.length = ((M (va / 4096)).drop (va % 4096)).take bs.length :=
    UMemL.umemRead_in M va bs.length (va / 4096) (va % 4096) len (by omega) fit
  icases UMemL.byteBuf_split_td (pte2pa w) (DFrac.own 1) (M (va / 4096))
    (va % 4096) bs.length (by omega) $$ Hpage with ⟨Hpre, Hbytes, Hpost⟩
  rw [← read]
  isplitl [Hbytes]
  · iexact Hbytes
  · iintro Hbytes
    ihave Hpage := UMemL.byteBuf_join_td (pte2pa w) (DFrac.own 1) (M (va / 4096))
      bs (va % 4096) bs.length (by omega) rfl $$ [$Hpre $Hbytes $Hpost]
    rw [← UMemL.umemWrite_in M va bs (va / 4096) (va % 4096) len (by omega) fit]
    ihave Hpages := Hclose $$ %(by rw [UMemL.umemWrite_length]; exact len) Hpage
    iapply UMemL.procPtAt_intro' P (umemWrite M va bs) t tree wf $$ [$Htree $Hpages]

/-- Fractional kernel-source ownership is returned unchanged. -/
theorem source_window (src : BitVec 64) (dq : DFrac) (bs : List (BitVec 8)) (off n : Nat)
    (bound : off + n ≤ bs.length) :
    byteBuf src dq bs ⊢@{IProp GF}
      byteBuf (src + BitVec.ofNat 64 off) dq ((bs.drop off).take n) ∗
      (byteBuf (src + BitVec.ofNat 64 off) dq ((bs.drop off).take n) -∗ byteBuf src dq bs) := by
  iintro Hsrc
  icases UMemL.byteBuf_split_td src dq bs off n bound $$ Hsrc with ⟨Hpre, Hbytes, Hpost⟩
  isplitl [Hbytes]
  · iexact Hbytes
  · iintro Hbytes
    have len : ((bs.drop off).take n).length = n := by
      simp only [List.length_take, List.length_drop]; omega
    ihave Hsrc := UMemL.byteBuf_join_td src dq bs ((bs.drop off).take n) off n bound len
      $$ [$Hpre $Hbytes $Hpost]
    rw [← List.drop_drop, List.take_append_drop, List.take_append_drop]
    iexact Hsrc

theorem memmove_to_user (MM : MEMMOVE) (cpu : CPU) (k : KCtx)
    (P : UPtd) (M : Nat → List (BitVec 8)) (w src : BitVec 64) (dq : DFrac)
    (bs : List (BitVec 8)) (va off n : Nat)
    (lookup : get? P.um (va / 4096) = some w) (fit : va % 4096 + n ≤ 4096)
    (bound : off + n ≤ bs.length) (stack : 2 ≤ k.avail)
    (srcArg : k.regs 11#5 = src + BitVec.ofNat 64 off)
    (dstArg : k.regs 10#5 = pte2pa w + BitVec.ofNat 64 (va % 4096))
    (lenArg : k.regs 12#5 = BitVec.ofNat 64 n) :
    kctx cpu k ∗ pcIs cpu KA.«memmove» ∗ procPtAt P M ∗ byteBuf src dq bs ∗
    wpNext k.sie k.proc cpu (fun cpu' => iprop(∀ R' : RegMap,
      kctx cpu' (k.withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
      procPtAt P (umemWrite M va ((bs.drop off).take n)) -∗ byteBuf src dq bs -∗
      ⌜calleeSaved k.regs R' ∧ R' 10#5 = k.regs 10#5⌝ -∗ wpLoop cpu'))
      ⊢ wpLoop (GF := GF) cpu := by
  have len : ((bs.drop off).take n).length = n := by
    simp only [List.length_take, List.length_drop]; omega
  iintro ⟨Hk, Hpc, HP, Hsrc, Hexit⟩
  icases user_write_window P M va ((bs.drop off).take n) w lookup (by omega)
    $$ HP with ⟨Hdst, Hclose⟩
  rw [len]
  icases source_window src dq bs off n bound $$ Hsrc with ⟨Hsrc, HsrcClose⟩
  iapply co_memmove_call MM cpu k ((bs.drop off).take n) (umemRead M va n)
    n dq stack lenArg (by omega) len (UMemL.umemRead_length M va n) $$ [- $Hk $Hpc]
  rw [srcArg, dstArg]
  iframe Hsrc Hdst
  iapply wpNext_intro_pin
  iintro %cpu' %hpin %R' Hk Hpc Hsrc Hdst %result
  ihave HP := Hclose $$ Hdst
  ihave Hsrc := HsrcClose $$ Hsrc
  ihave Hexit := wpNext_at k.sie k.proc cpu cpu' _ hpin $$ Hexit
  iapply Hexit $$ %R' Hk Hpc HP Hsrc %result

namespace CopyCall
open Experiments.WholeFunction.Copy

theorem write_chunk (MM : MEMMOVE) (cpu : CPU) (k : KCtx)
    (s : State) (sz a w src : BitVec 64) (dq : DFrac) (bs : List (BitVec 8)) (n : Nat)
    (lookup : get? s.table.um ((a.toNat + s.copied.length) / 4096) = some w)
    (fit : (a.toNat + s.copied.length) % 4096 + n ≤ 4096)
    (positive : 0 < n) (bound : s.copied.length + n ≤ bs.length)
    (access : ∀ j, j < n → uvaWmapped s.table (a + BitVec.ofNat 64 (s.copied.length + j)).toNat)
    (stack : 2 ≤ k.avail)
    (srcArg : k.regs 11#5 = src + BitVec.ofNat 64 s.copied.length)
    (dstArg : k.regs 10#5 = pte2pa w + BitVec.ofNat 64 ((a.toNat + s.copied.length) % 4096))
    (lenArg : k.regs 12#5 = BitVec.ofNat 64 n) :
    let after := transfer .write a s ((bs.drop s.copied.length).take n)
    kctx cpu k ∗ pcIs cpu KA.«memmove» ∗ procPtAt s.table s.image ∗ byteBuf src dq bs ∗
    wpNext k.sie k.proc cpu (fun cpu' => iprop(∀ R' : RegMap,
      kctx cpu' (k.withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
      procPtAt after.table after.image -∗ byteBuf src dq bs -∗
      ⌜Step .write sz a s after⌝ -∗
      ⌜calleeSaved k.regs R' ∧ R' 10#5 = k.regs 10#5⌝ -∗ wpLoop cpu'))
      ⊢ wpLoop (GF := GF) cpu := by
  dsimp only
  have len : ((bs.drop s.copied.length).take n).length = n := by
    simp only [List.length_take, List.length_drop]; omega
  have step : Step .write sz a s (transfer .write a s ((bs.drop s.copied.length).take n)) := by
    apply Step.chunk
    · omega
    · simpa only [len] using fit
    · simpa only [len] using UMemL.umMapped_page fit (by rw [lookup]; rfl)
    · simpa only [len, permission] using access
    · intro h; cases h
  iintro ⟨Hk, Hpc, HP, Hsrc, Hexit⟩
  iapply memmove_to_user MM cpu k s.table s.image w src dq bs
    (a.toNat + s.copied.length) s.copied.length n lookup fit bound stack srcArg dstArg lenArg
    $$ [$Hk $Hpc $HP $Hsrc Hexit]
  iapply wpNext_intro_pin
  iintro %cpu' %hpin %R' Hk Hpc HP Hsrc %result
  ihave Hexit := wpNext_at k.sie k.proc cpu cpu' _ hpin $$ Hexit
  simp only [transfer, imageAfter]
  iapply Hexit $$ %R' Hk Hpc HP Hsrc %step %result

theorem fault_step_write {sz a : BitVec 64} {s t : State}
    (h : Step .read sz a s t) (same : t.copied = s.copied) : Step .write sz a s t := by
  cases h with
  | fault Q ke ext lend => exact .fault s Q ke ext lend
  | chunk bs positive page mapped access read =>
    have len := congrArg List.length same
    simp only [transfer, List.length_append] at len
    omega

private theorem pteAD_write_checked (w v : BitVec 64) (h : pteAD w v) :
    v &&& PTE_W = w &&& PTE_W := by
  obtain ⟨a, d, rfl⟩ := h
  change pteSetAD w a d &&& BitVec.twoPow 64 2 = w &&& BitVec.twoPow 64 2
  rw [BitVec.and_twoPow, BitVec.and_twoPow]
  simp [pteSetAD, Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange',
    Sail.BitVec.extractLsb, BitVec.extractLsb, LeanRV64D.Functions._update_PTE_Flags_A, LeanRV64D.Functions._update_PTE_Flags_D]

/-- The walker returns a pointer into the owned tree. Consume the actual
following load while that tree is open, then restore the whole process image.
The hardware PTE can differ in A/D bits, so only its write bit is identified. -/
theorem walk_load (W : WALK_NOALLOC) (cpu : CPU) (k : KCtx)
    (P : UPtd) (M : Image) (w : BitVec 64)
    (stack : 8 ≤ k.avail) (root : k.regs 10#5 = pageAddr P.root)
    (address : (k.regs 11#5).toNat < 2 ^ 38) (alloc : k.regs 12#5 = 0#64)
    (lookup : get? P.um (vpnOf (k.regs 11#5)).toNat = some w)
    (returnPC : jumpPc (k.regs 1#5) = 0x80001644#64) :
    kctx cpu k ∗ pcIs cpu KA.«walk» ∗ procPtAt P M ∗
    wpNext k.sie k.proc cpu (fun cpu' => iprop(∀ R' : RegMap,
      kctx cpu' (k.withRegs R') -∗ pcIs cpu' 0x80001646#64 -∗ procPtAt P M -∗
      ⌜calleeSaved k.regs R' ∧ R' 15#5 &&& PTE_W = w &&& PTE_W⌝ -∗ wpLoop cpu'))
      ⊢ wpLoop (GF := GF) cpu := by
  iintro ⟨Hk, Hpc, HP, Hexit⟩
  icases kctx_kernelText _ _ $$ Hk with ⟨#Htext, Hk⟩
  icases UMemL.procPtAt_elim P M $$ HP with ⟨%wf, ⟨%t, %tree, Htree⟩, Hpages⟩
  have root' : k.regs 10#5 = pageAddr t.base := by rw [tree.1]; exact root
  have rule := W.wp_walk_noalloc (hlc := hlc) (GF := GF) cpu k (DFrac.own 1) t
    stack root' address alloc tree.2.1
  unfold wp_walk_noalloc_body at rule
  simp only [walkAddr] at rule
  iapply rule $$ [$Hk $Hpc $Htree Hpages Hexit]
  iapply wpNext_intro_pin
  iintro %cpu' %hpin %R Hk Hpc Htree %result
  obtain ⟨saved, walked⟩ := result
  have leaf := UMemL.leaves_of_um P wf _ w lookup
  obtain ⟨complete, slot, ad⟩ := UMemL.ptRep_leaf t P.leaves _ w tree.2 leaf
  have ptr : R 10#5 = pteAddr (t.slot 2 (vpnOf (k.regs 11#5))).1
      (vpnIdx (vpnOf (k.regs 11#5)) 0) := by
    rcases walked with ⟨_, bad⟩ | ⟨_, good⟩
    · exact (bad complete).elim
    · exact good
  icases PtRun.ptreeOwn_leaf_acc 2 (DFrac.own 1) t _ complete $$ Htree with ⟨Hcell, Hclose⟩
  rw [returnPC]
  k_step_gen (wp_s_ld cpu' _ 0x80001644#64 true 0#12 15#5 10#5 (by decide) (by decide)
      (DFrac.own 1) (t.entAt 2 (vpnOf (k.regs 11#5))))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [ptr] next cpu'' pin2
  iintro Hk Hpc Hcell
  ihave Htree := Hclose $$ %(t.entAt 2 (vpnOf (k.regs 11#5))) Hcell
  rw [UMemL.setLeaf_self]
  ihave HP := UMemL.procPtAt_intro' P M t tree wf $$ [$Htree $Hpages]
  have pin : k.sie = false ∨ k.proc = 0#64 → cpu'' = cpu := fun h => (pin2 h).trans (hpin h)
  ihave Hexit := wpNext_at k.sie k.proc cpu cpu'' _ pin $$ Hexit
  have saved' : calleeSaved k.regs (R.set 15#5 (t.entAt 2 (vpnOf (k.regs 11#5)))) := by
    simpa only [calleeSaved, RegMap.set_apply, BitVec.reduceEq, ite_false] using saved
  have write : (R.set 15#5 (t.entAt 2 (vpnOf (k.regs 11#5)))) 15#5 &&& PTE_W = w &&& PTE_W := by
    simpa only [RegMap.set_apply, ite_true] using pteAD_write_checked w _ ad
  k_norm_g
  iapply Hexit $$ %(R.set 15#5 (t.entAt 2 (vpnOf (k.regs 11#5)))) Hk Hpc HP %⟨saved', write⟩

end CopyCall
end Xv6.WholeFunction

/-- info: 'Xv6.WholeFunction.CopyCall.write_chunk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Xv6.WholeFunction.CopyCall.write_chunk
open Lean in
run_cmd do
  let baseline ← collectAxioms ``MachCSL.wp_s_ld
  let axs ← collectAxioms ``Xv6.WholeFunction.CopyCall.walk_load
  let extra := axs.filter fun ax => !baseline.contains ax
  unless extra.isEmpty do throwError "walk_load adds axioms {extra}"
