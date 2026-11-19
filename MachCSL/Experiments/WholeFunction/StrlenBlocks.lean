import Experiments.WholeFunction.StrlenModel
import Experiments.WholeFunction.AffineTransport

/-! Semantic joins consume the universally replayed, generated affine table.
Only zero-byte exits need a local prefix proof for the C-string result. -/
namespace Xv6.WholeFunction.Strlen
open MachCSL LeanRV64D
set_option linter.unusedSimpArgs false

private theorem good_of_prefix {i : Inputs} {s : Memory.State} {start : RegState}
    (certified : Symbolic.Prefix bodyRows Affine.scanCut start
      (fun r => Endpoint i (atResult s r))) : Good i (atResult s start) := by
  obtain ⟨r, certificate, endpoint⟩ := certified
  exact ⟨atResult s r, Affine.scanCut, rfl, certificate, endpoint⟩

theorem first_good {i : Inputs} (valid : Valid i) {s : Memory.State} (h : Common i s)
    (arg : s.machine.ctx.regs 10#5 = i.base)
    (b : BitVec 8) (lookup : i.bytes[0]? = some b) :
    Good i (atResult s (Affine.readResult Affine.firstByte s.machine.ctx b)) := by
  apply good_of_prefix
  have zero := cstrAt_zero valid.terminated (Nat.zero_le i.length) lookup
  by_cases hb : b = 0#8
  · have hn : i.length = 0 := (zero.mp hb).symm
    dsimp only [Affine.readResult, Affine.firstByte, Memory.Op.run, Stack.State.machine]
    symbolic_prefix 5
    all_goals simp_all [bcond, byte_zero]
    refine .done ⟨h.result _, rfl, ?_⟩
    simp [atResult, RegMap.set_apply, hn]
  · have hn : 0 < i.length := by have := mt zero.mpr hb; omega
    obtain ⟨r, certificate, pc, invariant⟩ :=
      Affine.entry_body_checked s.machine.ctx i.base arg b hb
    exact ⟨r, certificate, .scan 1 ⟨h.result _, pc, invariant, by omega, hn⟩⟩

theorem loop_good {i : Inputs} (valid : Valid i) {s : Memory.State} (h : Common i s)
    (j : Nat) (positive : 1 ≤ j) (bound : j ≤ i.length)
    (invariant : Affine.Holds Affine.inferred i.base j s.machine.ctx)
    (b : BitVec 8) (lookup : i.bytes[j]? = some b) :
    Good i (atResult s (Affine.readResult Affine.scanByte s.machine.ctx b)) := by
  apply good_of_prefix
  have zero := cstrAt_zero valid.terminated bound lookup
  by_cases hb : b = 0#8
  · have hj : j = i.length := zero.mp hb
    dsimp only [Affine.readResult, Affine.scanByte, Memory.Op.run, Stack.State.machine]
    symbolic_prefix 4
    all_goals simp_all [bcond, byte_zero]
    refine .done ⟨h.result _, rfl, ?_⟩
    simp [Affine.Holds, Affine.inferred, Affine.Rule.value] at invariant
    simpa [atResult, RegMap.set_apply, invariant.1, invariant.2.1, hj] using
      subw_len i.base i.length valid.bound
  · have hj : j < i.length := by have := mt zero.mpr hb; omega
    obtain ⟨r, certificate, pc, inferred⟩ :=
      Affine.step_body_checked s.machine.ctx i.base j invariant b hb
    exact ⟨r, certificate, .scan (j+1) ⟨h.result _, pc, inferred, by omega, by omega⟩⟩

end Xv6.WholeFunction.Strlen
