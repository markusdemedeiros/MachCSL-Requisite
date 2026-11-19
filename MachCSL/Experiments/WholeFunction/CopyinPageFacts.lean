import Experiments.WholeFunction.CopyCallRegistry

/-! Pure joins after copy-family calls. These facts connect the callee result
relations to page-ready and failure invariants without instruction proofs. -/
namespace Xv6.WholeFunction.Copyin
open MachCSL LeanRV64D
open Iris.Std (get?)
open Experiments.WholeFunction

theorem fresh_leaf_readable (r : BitVec 64) :
    pteVU (leafOf (BitVec.extractLsb' 12 44 r) (PTE_W ||| PTE_U ||| PTE_R)) := by
  constructor
  · intro bad
    have h := congrArg (fun v : BitVec 64 => v.getLsbD 0) bad
    simp [leafOf, PTE_V, PTE_W, PTE_U, PTE_R] at h
  · intro bad
    have h := congrArg (fun v : BitVec 64 => v.getLsbD 4) bad
    simp [leafOf, PTE_W, PTE_U, PTE_R] at h

/-- Kernel-checked address decoding for the fresh leaf. The proof uses the
allocator's alignment/range facts directly rather than native bv_decide. -/
theorem fresh_leaf_address (r : BitVec 64) (valid : pageValid r) :
    pte2pa (leafOf (BitVec.extractLsb' 12 44 r) (PTE_W ||| PTE_U ||| PTE_R)) = r := by
  have aligned := congrArg BitVec.toNat valid.1
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat] at aligned
  have align : r.toNat % 4096 = 0 := by
    change r.toNat &&& (2^12-1) = 0 at aligned
    simpa only [Nat.and_two_pow_sub_one_eq_mod] using aligned
  have small := valid.2.2
  simp only [BitVec.ult, decide_eq_true_eq, physTop, BitVec.toNat_ofNat] at small
  unfold pte2pa leafOf
  rw [BitVec.ushiftRight_or_distrib, BitVec.ushiftRight_or_distrib]
  simp only [PTE_W, PTE_U, PTE_R, BitVec.reduceOr]
  rw [show (22#64 >>> 10) = 0#64 from rfl, show (1#64 >>> 10) = 0#64 from rfl]
  simp only [BitVec.or_zero]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_setWidth,
    BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.reducePow]
  rw [Nat.mod_eq_of_lt (by omega : r.toNat / 4096 < 17592186044416)]
  rw [Nat.mod_eq_of_lt (by omega : r.toNat / 4096 < 18446744073709551616)]
  rw [Nat.mod_eq_of_lt (by omega : r.toNat / 4096 * 1024 < 18446744073709551616)]
  omega

/-- The page information retained after a successful fault. -/
theorem FaultNext.success {i : Inputs} {s t : State}
    (hn : FaultNext i s t) (size : i.size.toNat ≤ 2 ^ 38)
    (bound : cursor i s < 2 ^ 64)
    (address : s.machine.ctx.regs 12#5 = BitVec.ofNat 64 (cursor i s / 4096 * 4096))
    (nonzero : t.machine.ctx.regs 10#5 ≠ 0#64) :
    ∃ w, get? t.memory.table.um (cursor i t / 4096) = some w ∧ pteVU w ∧
      t.machine.ctx.regs 10#5 = pte2pa w ∧ cursor i t / 4096 * 4096 < 2 ^ 38 := by
  obtain ⟨spie, spp, R', memory, rfl, flags, saved, step, copied, result⟩ := hn
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
      fresh_leaf_readable r, ret.trans (fresh_leaf_address r valid).symm, by omega⟩
    rw [table, vpn]
    exact Iris.Std.LawfulPartialMap.get?_insert_eq rfl

/-- A failed fault leaves the prior walk failure valid in the returned table. -/
theorem FaultNext.failure {i : Inputs} {s t : State}
    (hn : FaultNext i s t)
    (walked : CopyCall.WalkPageResult s.memory.table (cursor i s) 0#64)
    (zero : t.machine.ctx.regs 10#5 = 0#64) :
    t.memory.table = s.memory.table ∧ cursor i t = cursor i s ∧
      ¬ uvaRmapped t.memory.table (cursor i t) := by
  obtain ⟨spie, spp, R', memory, rfl, flags, saved, step, copied, result⟩ := hn
  have cur : cursor i (returnState s ((s.machine.ctx.withSpie spie spp).withRegs R') memory) =
      cursor i s := by simp only [cursor, returnState, copied]
  change R' 10#5 = 0#64 at zero
  rw [cur]
  dsimp only [returnState]
  rcases result with ⟨_, table⟩ | ⟨r, ret, valid, _⟩
  · exact ⟨table, rfl, by rw [table]; exact walked.zero rfl⟩
  · exact False.elim (PtRun.pageValid_ne_zero r valid (ret.symm.trans zero))

theorem FaultNext.failure_entry {i : Inputs} {s t : State}
    (hn : FaultNext i s t)
    (walked : CopyCall.WalkPageResult s.memory.table (cursor i s) 0#64)
    (trace : Copy.Trace .read i.size i.src (Copy.initial i.table i.image i.lend) s.memory)
    (zero : t.machine.ctx.regs 10#5 = 0#64) :
    ¬ uvaRmapped i.table (cursor i s) :=
  walked.zero_at_entry (Copy.trace_certificate trace).extension.1 rfl

/-- Exactly the saved registers used by the page/chunk loop annotations. -/
structure SavedCopyRegs (R R' : RegMap) : Prop where
  sp : R' 2#5 = R 2#5
  count : R' 9#5 = R 9#5
  src : R' 18#5 = R 18#5
  page : R' 19#5 = R 19#5
  remaining : R' 20#5 = R 20#5
  dst : R' 21#5 = R 21#5
  pageSize : R' 22#5 = R 22#5
  root : R' 23#5 = R 23#5
  mask : R' 24#5 = R 24#5
  size : R' 25#5 = R 25#5
  faultMode : R' 26#5 = R 26#5
  s11 : R' 27#5 = R 27#5

theorem saved_copy_regs {R R' : RegMap} (h : calleeSaved R R') : SavedCopyRegs R R' := by
  rcases h with ⟨sp, _, count, src, page, remaining, dst, pageSize, root, mask, size, mode, s11⟩
  exact ⟨sp, count, src, page, remaining, dst, pageSize, root, mask, size, mode, s11⟩

theorem WalkNext.saved {i : Inputs} {s t : State} (h : WalkNext i s t) :
    SavedCopyRegs s.machine.ctx.regs t.machine.ctx.regs := by
  obtain ⟨R', rfl, saved, _⟩ := h
  exact saved_copy_regs saved

theorem FaultNext.saved {i : Inputs} {s t : State} (h : FaultNext i s t) :
    SavedCopyRegs s.machine.ctx.regs t.machine.ctx.regs := by
  obtain ⟨spie, spp, R', memory, rfl, flags, saved, _⟩ := h
  exact saved_copy_regs saved

theorem ReadNext.saved {i : Inputs} {s t : State} {n : Nat} (h : ReadNext i s n t) :
    SavedCopyRegs s.machine.ctx.regs t.machine.ctx.regs := by
  obtain ⟨R', rfl, saved, _⟩ := h
  exact saved_copy_regs saved

theorem context_withRegs (entry k : KCtx) (slots : Nat) (R : RegMap)
    (context : k = ((entry.withSpie k.spie k.spp).pushed slots).withRegs k.regs) :
    k.withRegs R = ((entry.withSpie k.spie k.spp).pushed slots).withRegs R := by
  exact (congrArg (fun c : KCtx => c.withRegs R) context).trans (KCtx.withRegs_withRegs _ _ _)

theorem context_withSpie (entry k : KCtx) (slots : Nat) (spie spp : Bool) (R : RegMap)
    (context : k = ((entry.withSpie k.spie k.spp).pushed slots).withRegs k.regs) :
    (k.withSpie spie spp).withRegs R = ((entry.withSpie spie spp).pushed slots).withRegs R := by
  rw [context]
  simp only [KCtx.withSpie_withRegs, KCtx.withSpie_pushed,
    KCtx.withSpie_twice, KCtx.withRegs_withRegs]

theorem flags_after_call (entry k : KCtx) (spie spp : Bool)
    (sie : k.sie = entry.sie)
    (before : entry.sie = false → k.spie = entry.spie ∧ k.spp = entry.spp)
    (after : k.sie = false → spie = k.spie ∧ spp = k.spp) :
    entry.sie = false → spie = entry.spie ∧ spp = entry.spp := by
  intro off
  have h1 := before off
  have h2 := after (sie.trans off)
  exact ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

end Xv6.WholeFunction.Copyin

/-- info: 'Xv6.WholeFunction.Copyin.FaultNext.success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Xv6.WholeFunction.Copyin.FaultNext.success
