import Experiments.WholeFunction.CopyoutInvariant
import Experiments.WholeFunction.CopyoutBlockFacts
import Experiments.WholeFunction.CopyoutCallRegistry

namespace Xv6.WholeFunction.Copyout
open MachCSL LeanRV64D

/-- Loop annotations mention only the contiguous saved-register range s4--s11. -/
theorem LoopRegs.of_preserves {i : Inputs} {d : Nat} {R R' : RegMap}
    (h : LoopRegs i d R) (same : ∀ r : BitVec 5, 20 ≤ r.toNat → r.toNat ≤ 27 → R' r = R r) :
    LoopRegs i d R' :=
  ⟨(same _ (by decide) (by decide)).trans h.dst,
    (same _ (by decide) (by decide)).trans h.remaining,
    (same _ (by decide) (by decide)).trans h.src,
    (same _ (by decide) (by decide)).trans h.root,
    (same _ (by decide) (by decide)).trans h.pageSize,
    (same _ (by decide) (by decide)).trans h.maxva,
    (same _ (by decide) (by decide)).trans h.mask,
    (same _ (by decide) (by decide)).trans h.size⟩

private theorem high_ne (r : BitVec 5) (h : 20 ≤ r.toNat) (n : BitVec 5)
    (low : n.toNat < 20) : r ≠ n := fun eq => by subst r; omega

theorem good_result {i : Inputs} (s : State) (r : RegState)
    (cert : Symbolic.Certificate Binary.copyout.rows bodyCuts s.machine.machine ⟨r, .cut⟩)
    (endpoint : Endpoint i (atResult s r)) : Good i s :=
  ⟨atResult s r, bodyCuts, rfl, cert, endpoint⟩

theorem header_result_endpoint {i : Inputs} {s : State} (h : Header i s) :
    Endpoint i (atResult s (headerResult s.machine.ctx)) := by
  have common := common_result h.toCommon _ (header_context _)
    (header_preserves _ _ (by decide) (by decide) (by decide))
  have regs := h.registers.of_preserves (fun r lo _ => header_preserves _ r
    (high_ne r lo _ (by decide)) (high_ne r lo _ (by decide)) (high_ne r lo _ (by decide)))
  have high := tooHigh_iff s.machine.ctx i.dst.toNat s.memory.copied.length
    h.registers.dst h.registers.mask h.registers.maxva h.nowrap
  cases branch : tooHigh s.machine.ctx with
  | true =>
    refine .done ⟨common, ?_, Or.inr ⟨?_, h.more, ?_⟩⟩
    · simp only [atResult, headerResult, branch, ↓reduceIte]
    · simp [atResult, headerResult, branch, KCtx.setReg_regs, RegMap.set_apply]
    · change ¬ uvaWmapped s.memory.table (i.dst + BitVec.ofNat 64 s.memory.copied.length).toNat
      rw [wrapped_toNat _ _ h.nowrap]
      exact not_writable_max h.wf (high.mp branch)
  | false =>
    have below : cursor i s < 2 ^ 38 := by
      have hn : ¬ 2 ^ 38 ≤ cursor i s := fun hn => by have := high.mpr hn; simp [branch] at this
      omega
    have page : s.machine.ctx.regs 20#5 &&& s.machine.ctx.regs 26#5 =
        BitVec.ofNat 64 (cursor i s / 4096 * 4096) := by
      rw [h.registers.dst, h.registers.mask]
      exact rounded_source _ _ h.nowrap
    obtain ⟨pageReg, a0, a1⟩ := header_values s.machine.ctx branch
    exact .walk ⟨common, by simp only [atResult, headerResult, branch, Bool.false_eq_true, ↓reduceIte],
      h.more, h.nowrap, regs, pageReg.trans page, by change cursor i s / 4096 * 4096 < 2 ^ 38; omega,
      a0.trans h.registers.root, a1.trans page⟩

theorem good_of_header {i : Inputs} {s : State} (h : Header i s) : Good i s := by
  apply good_result s (headerResult s.machine.ctx) _ (header_result_endpoint h)
  simpa only [Stack.State.machine, h.pc] using header_certificate s.machine.ctx

theorem page_move {i : Inputs} {s : State} {w : BitVec 64} (h : Page i s w)
    (writable : w &&& PTE_W ≠ 0#64) (len64 : i.bytes.length < 2 ^ 64) :
    MoveCall i (atResult s (pageResult s.machine.ctx)) w := by
  have common := common_result h.toCommon _ (page_context _)
    (page_preserves _ _ (by decide) (by decide) (by decide) (by decide))
  have regs := h.registers.of_preserves (fun r lo _ => page_preserves _ r
    (high_ne r lo _ (by decide)) (high_ne r lo _ (by decide))
    (high_ne r lo _ (by decide)) (high_ne r lo _ (by decide)))
  obtain ⟨count, a0, a1, a2⟩ := page_chunk_values s.machine.ctx i.dst.toNat s.memory.copied.length
    i.bytes.length (i.src + BitVec.ofNat 64 s.memory.copied.length) (pte2pa w)
    h.registers.dst h.pageReg h.registers.pageSize h.registers.remaining h.registers.src
    h.physicalReg h.pageBound h.more len64
  exact ⟨⟨common, h.more, regs, h.leaf, h.readable, h.pageBound,
      (page_preserves _ _ (by decide) (by decide) (by decide) (by decide)).trans h.pageReg,
      (page_preserves _ _ (by decide) (by decide) (by decide) (by decide)).trans h.physicalReg⟩,
    rfl, writable, count, a0, a1, a2⟩

/-- A generated prefix may finish at another residual proof. Only its register
state changes; COPYOUT's memory, lend and saved frame stay in the same view. -/
theorem good_prefix {i : Inputs} (s : State) (cut : BitVec 64 → Bool)
    (pre : Symbolic.Prefix Binary.copyout.rows cut s.machine.machine
      (fun r => Good i (atResult s r))) : Good i s := by
  obtain ⟨r, cert, good⟩ := pre
  exact Residual.prepend (v := residualView) (s := s) (t := atResult s r) rfl cert good

theorem good_endpoint {i : Inputs} {s : State} (h : Endpoint i s) : Good i s :=
  Residual.at_endpoint residualView Binary.copyout.rows (Endpoint i) s h

theorem probe_return_good {i : Inputs} {s : State} {w : BitVec 64}
    (pc : s.machine.pc = 0x80001646#64) (h : Page i s w)
    (permission : s.machine.ctx.regs 15#5 &&& PTE_W = w &&& PTE_W)
    (len64 : i.bytes.length < 2 ^ 64) : Good i s := by
  have common := common_result h.toCommon ⟨permissionCtx s.machine.ctx, 0x8000164a#64⟩
    (permission_context _) (permission_preserves _ _ (by decide))
  have regs := h.registers.of_preserves (fun r lo _ => permission_preserves _ r (high_ne r lo _ (by decide)))
  apply good_prefix s (fun pc => pc == 0x8000164a#64 || pc == 0x80001662#64)
  rw [show s.machine.machine = ⟨s.machine.ctx, 0x80001646#64⟩ from by
    simp only [Stack.State.machine, pc]]
  symbolic_prefix 4
  · rename_i branch
    change Good i (atResult s ⟨(permissionCtx s.machine.ctx).setReg 10#5 (0#64 + -1#64), 0x80001662#64⟩)
    have ro : w &&& PTE_W = 0#64 := permission.symm.trans ((readonly_iff _).mp branch)
    have hc := common_result h.toCommon ⟨(permissionCtx s.machine.ctx).setReg 10#5 (0#64 + -1#64), 0x80001662#64⟩
      rfl (by simp [permissionCtx, KCtx.setReg_regs, RegMap.set_apply])
    apply good_endpoint
    refine .done ⟨hc, rfl, Or.inr ⟨?_, h.more, ?_⟩⟩
    · simp [atResult, KCtx.setReg_regs, RegMap.set_apply]
    · change ¬ uvaWmapped s.memory.table (i.dst + BitVec.ofNat 64 s.memory.copied.length).toNat
      rw [wrapped_toNat _ _ (by have := h.pageBound; unfold cursor at this; omega)]
      exact not_writable_of_leaf h.leaf ro
  · rename_i branch
    change Good i (atResult s ⟨permissionCtx s.machine.ctx, 0x8000164a#64⟩)
    have writable : w &&& PTE_W ≠ 0#64 := fun ro =>
      branch ((readonly_iff s.machine.ctx).mpr (permission.trans ro))
    have page : Page i (atResult s ⟨permissionCtx s.machine.ctx, 0x8000164a#64⟩) w :=
      ⟨common, h.more, regs, h.leaf, h.readable, h.pageBound,
        (permission_preserves _ _ (by decide)).trans h.pageReg,
        (permission_preserves _ _ (by decide)).trans h.physicalReg⟩
    apply good_result _ _ (page_certificate _)
    exact .move w (page_move page writable len64)

theorem movedCtx_regs (k : KCtx) : (movedCtx k).regs = updateRegs k.regs := rfl

theorem move_return_good {i : Inputs} {s : State} (pc : s.machine.pc = 0x80001608#64)
    (hc : Common i s) (d : Nat)
    (copied : s.memory.copied.length = d + chunkSize i.dst.toNat d i.bytes.length)
    (more : d < i.bytes.length) (regs : LoopRegs i d s.machine.ctx.regs)
    (count : s.machine.ctx.regs 18#5 = BitVec.ofNat 64 (chunkSize i.dst.toNat d i.bytes.length))
    (page : s.machine.ctx.regs 9#5 = BitVec.ofNat 64 ((i.dst.toNat + d) / 4096 * 4096))
    (pageBound : (i.dst.toNat + d) / 4096 * 4096 < 2 ^ 38)
    (len64 : i.bytes.length < 2 ^ 64) : Good i s := by
  have moved := common_result hc ⟨movedCtx s.machine.ctx, 0x80001616#64⟩ (movedCtx_context _)
    (movedCtx_preserves _ _ (by decide) (by decide) (by decide))
  have bound := (chunk_facts i.dst.toNat d i.bytes.length more).2.1
  have finished := moveDone_iff s.machine.ctx d (chunkSize i.dst.toNat d i.bytes.length)
    i.bytes.length regs.remaining count bound len64
  apply good_prefix s (fun pc => pc == 0x80001616#64 || pc == 0x80001662#64)
  rw [show s.machine.machine = ⟨s.machine.ctx, 0x80001608#64⟩ from by
    simp only [Stack.State.machine, pc]]
  symbolic_prefix 6
  · rename_i branch
    change Good i (atResult s ⟨(movedCtx s.machine.ctx).setReg 10#5 0#64, 0x80001662#64⟩)
    have hf := common_result hc ⟨(movedCtx s.machine.ctx).setReg 10#5 0#64, 0x80001662#64⟩ rfl
      (by simpa only [KCtx.setReg_regs, RegMap.set_apply, BitVec.reduceEq, ↓reduceIte] using
        movedCtx_preserves s.machine.ctx 2#5 (by decide) (by decide) (by decide))
    apply good_endpoint
    exact .done ⟨hf, rfl, Or.inl ⟨by simp [atResult, KCtx.setReg_regs, RegMap.set_apply],
      copied.trans (finished.mp branch)⟩⟩
  · rename_i branch
    change Good i (atResult s ⟨movedCtx s.machine.ctx, 0x80001616#64⟩)
    have continuing : d + chunkSize i.dst.toNat d i.bytes.length < i.bytes.length := by
      have hn : d + chunkSize i.dst.toNat d i.bytes.length ≠ i.bytes.length :=
        fun eq => branch (finished.mpr eq)
      omega
    obtain ⟨_, small, _⟩ := next_cursor i.dst.toNat d i.bytes.length more pageBound continuing
    have hr : LoopRegs i s.memory.copied.length (movedCtx s.machine.ctx).regs := by
      rw [copied, movedCtx_regs]
      exact update_loop i d s.machine.ctx.regs regs more len64 count page continuing
    apply good_of_header
    exact ⟨moved, rfl, by simpa only [atResult, copied] using continuing,
      by change i.dst.toNat + s.memory.copied.length < 2 ^ 64; rw [copied]; omega, hr⟩

end Xv6.WholeFunction.Copyout
