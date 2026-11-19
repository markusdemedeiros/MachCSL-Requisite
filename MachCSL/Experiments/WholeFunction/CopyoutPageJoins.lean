import Experiments.WholeFunction.CopyoutJoins

namespace Xv6.WholeFunction.Copyout
open MachCSL LeanRV64D

private theorem high_ne (r : BitVec 5) (h : 20 ≤ r.toNat) (n : BitVec 5)
    (low : n.toNat < 20) : r ≠ n := fun eq => by subst r; omega

theorem prepared_probe {i : Inputs} {s : State} {w : BitVec 64}
    (hc : Common i s) (more : s.memory.copied.length < i.bytes.length)
    (regs : LoopRegs i s.memory.copied.length s.machine.ctx.regs)
    (page : s.machine.ctx.regs 9#5 = BitVec.ofNat 64 (cursor i s / 4096 * 4096))
    (leaf : Iris.Std.PartialMap.get? s.memory.table.um (cursor i s / 4096) = some w)
    (readable : pteVU w) (physical : s.machine.ctx.regs 10#5 = pte2pa w)
    (bound : cursor i s / 4096 * 4096 < 2 ^ 38) :
    ProbeCall i (atResult s ⟨walkArgs (savePhysical s.machine.ctx), 0x80001640#64⟩) w := by
  have common := common_result hc ⟨walkArgs (savePhysical s.machine.ctx), 0x80001640#64⟩ rfl
    (by simp [walkArgs, savePhysical, KCtx.setReg_regs, RegMap.set_apply])
  have registers := regs.of_preserves (fun r lo _ =>
    (walkArgs_preserves _ r (high_ne r lo _ (by decide)) (high_ne r lo _ (by decide))
      (high_ne r lo _ (by decide))).trans (savedPhysical_preserves _ r (high_ne r lo _ (by decide))))
  obtain ⟨a0,a1,a2⟩ := walkArgs_values (savePhysical s.machine.ctx)
  refine ⟨⟨common,more,registers,leaf,readable,bound,?_,?_⟩,rfl,?_,?_,a2⟩
  · exact ((walkArgs_preserves _ _ (by decide) (by decide) (by decide)).trans
      (savedPhysical_preserves _ _ (by decide))).trans page
  · exact (walkArgs_preserves _ _ (by decide) (by decide) (by decide)).trans
      ((savedPhysical_value _).trans physical)
  · exact a0.trans ((savedPhysical_preserves _ _ (by decide)).trans regs.root)
  · exact a1.trans ((savedPhysical_preserves _ _ (by decide)).trans page)

theorem walk_return_good {i : Inputs} {s : State}
    (pc : s.machine.pc = 0x80001626#64)
    (hc : Common i s) (more : s.memory.copied.length < i.bytes.length)
    (nowrap : cursor i s < 2 ^ 64) (regs : LoopRegs i s.memory.copied.length s.machine.ctx.regs)
    (page : s.machine.ctx.regs 9#5 = BitVec.ofNat 64 (cursor i s / 4096 * 4096))
    (pageBound : cursor i s / 4096 * 4096 < 2 ^ 38)
    (result : CopyCall.WalkPageResult s.memory.table (cursor i s) (s.machine.ctx.regs 10#5)) :
    Good i s := by
  apply good_prefix s bodyCuts
  rw [show s.machine.machine = ⟨s.machine.ctx, 0x80001626#64⟩ from by
    simp only [Stack.State.machine, pc]]
  symbolic_prefix 7
  · rename_i branch
    change Good i (atResult s ⟨walkArgs (savePhysical s.machine.ctx), 0x80001640#64⟩)
    obtain ⟨w,leaf,readable,physical,bound⟩ := result.nonzero ((nonzero_iff _).mp branch)
    exact good_endpoint (.probe w (prepared_probe hc more regs page leaf readable physical bound))
  · rename_i branch
    change Good i (atResult s ⟨faultArgs (savePhysical s.machine.ctx), 0x80001632#64⟩)
    have zeroRet : s.machine.ctx.regs 10#5 = 0#64 := by
      simpa [nonzero, bcond, KCtx.setReg_regs, RegMap.set_apply] using branch
    have common := common_result hc ⟨faultArgs (savePhysical s.machine.ctx),0x80001632#64⟩ rfl
      (by simp [faultArgs,savePhysical,KCtx.setReg_regs,RegMap.set_apply])
    have registers := regs.of_preserves (fun r lo _ =>
      (faultArgs_preserves _ r (high_ne r lo _ (by decide)) (high_ne r lo _ (by decide))
        (high_ne r lo _ (by decide)) (high_ne r lo _ (by decide))).trans
        (savedPhysical_preserves _ r (high_ne r lo _ (by decide))))
    obtain ⟨a0,a1,a2,a3⟩ := faultArgs_values (savePhysical s.machine.ctx)
    apply good_endpoint
    refine .fault ⟨common,rfl,more,nowrap,registers,?_,pageBound,result.zero zeroRet,?_,?_,?_,a3⟩
    · exact ((faultArgs_preserves _ _ (by decide) (by decide) (by decide) (by decide)).trans
        (savedPhysical_preserves _ _ (by decide))).trans page
    · exact a0.trans ((savedPhysical_preserves _ _ (by decide)).trans regs.root)
    · exact a1.trans ((savedPhysical_preserves _ _ (by decide)).trans regs.size)
    · exact a2.trans ((savedPhysical_preserves _ _ (by decide)).trans page)

theorem fault_return_good {i : Inputs} {s : State}
    (pc : s.machine.pc = 0x80001636#64)
    (hc : Common i s) (more : s.memory.copied.length < i.bytes.length)
    (nowrap : cursor i s < 2 ^ 64) (regs : LoopRegs i s.memory.copied.length s.machine.ctx.regs)
    (page : s.machine.ctx.regs 9#5 = BitVec.ofNat 64 (cursor i s / 4096 * 4096))
    (pageBound : cursor i s / 4096 * 4096 < 2 ^ 38)
    (failure : s.machine.ctx.regs 10#5 = 0#64 → ¬ uvaRmapped s.memory.table (cursor i s))
    (success : s.machine.ctx.regs 10#5 ≠ 0#64 → ∃ w,
      Iris.Std.PartialMap.get? s.memory.table.um (cursor i s / 4096) = some w ∧ pteVU w ∧
      s.machine.ctx.regs 10#5 = pte2pa w ∧ cursor i s / 4096 * 4096 < 2 ^ 38) :
    Good i s := by
  apply good_prefix s bodyCuts
  rw [show s.machine.machine = ⟨s.machine.ctx, 0x80001636#64⟩ from by
    simp only [Stack.State.machine, pc]]
  symbolic_prefix 6
  · rename_i branch
    change Good i (atResult s ⟨(savePhysical s.machine.ctx).setReg 10#5 (0#64 + -1#64), 0x80001662#64⟩)
    have common := common_result hc
      ⟨(savePhysical s.machine.ctx).setReg 10#5 (0#64 + -1#64),0x80001662#64⟩ rfl
      (by simp [savePhysical,KCtx.setReg_regs,RegMap.set_apply])
    apply good_endpoint
    refine .done ⟨common,rfl,Or.inr ⟨?_,more,?_⟩⟩
    · simp [atResult,KCtx.setReg_regs,RegMap.set_apply]
    · change ¬ uvaWmapped s.memory.table (i.dst + BitVec.ofNat 64 s.memory.copied.length).toNat
      rw [wrapped_toNat _ _ nowrap]
      exact not_writable_of_unreadable (failure ((zero_iff _).mp branch))
  · rename_i branch
    change Good i (atResult s ⟨walkArgs (savePhysical s.machine.ctx), 0x80001640#64⟩)
    obtain ⟨w,leaf,readable,physical,bound⟩ := success (fun eq => branch ((zero_iff _).mpr eq))
    exact good_endpoint (.probe w (prepared_probe hc more regs page leaf readable physical bound))

end Xv6.WholeFunction.Copyout

open Lean in
run_cmd do
  for decl in #[``Xv6.WholeFunction.Copyout.walk_return_good,
      ``Xv6.WholeFunction.Copyout.fault_return_good,
      ``Xv6.WholeFunction.Copyout.probe_return_good,
      ``Xv6.WholeFunction.Copyout.move_return_good] do
    let axs ← collectAxioms decl
    unless axs.all (fun a => #[``propext, ``Classical.choice, ``Quot.sound].contains a) do
      throwError "{decl}: unexpected axioms {axs}"
