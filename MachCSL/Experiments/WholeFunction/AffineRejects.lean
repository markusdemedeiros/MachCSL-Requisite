import Experiments.WholeFunction.AffineTransport

/-! Certified counterexamples, rather than solver timeouts: the same actual
binary prefixes refute a wrong initial index, wrong stride, and a nonmodular
address claim at wraparound. -/
namespace Xv6.WholeFunction.Affine
open MachCSL LeanRV64D
set_option linter.unusedSimpArgs false

theorem reject_initial_zero (k : KCtx) :
    Symbolic.Prefix Binary.strlen.rows scanCut (firstRead (k.withRegs (sampleRegs 0 3)))
      (fun result => ¬ Holds inferred 0#64 0 result.ctx) := by
  obtain ⟨result, certificate, _, invariant⟩ := entry_checked
    (k.withRegs (sampleRegs 0 3)) 0#64 (by simp [sampleRegs]) 1#8 (by decide)
  refine ⟨result, certificate, ?_⟩
  simp_all [Holds, inferred, Rule.value]

theorem reject_stride_two (k : KCtx) :
    Symbolic.Prefix Binary.strlen.rows scanCut (firstRead (k.withRegs (sampleRegs 0 3)))
      (fun first => Symbolic.Prefix Binary.strlen.rows scanCut (nextRead first.ctx)
        (fun second => ¬ Holds inferred 0#64 3 second.ctx)) := by
  obtain ⟨first, entry, _, invariant⟩ := entry_checked
    (k.withRegs (sampleRegs 0 3)) 0#64 (by simp [sampleRegs]) 1#8 (by decide)
  obtain ⟨second, step, _, invariant⟩ := step_checked first.ctx 0#64 1 invariant 1#8 (by decide)
  refine ⟨first, entry, second, step, ?_⟩
  simp_all [Holds, inferred, Rule.value]

theorem reject_nonmodular_address (k : KCtx) :
    Symbolic.Prefix Binary.strlen.rows scanCut
      (firstRead (k.withRegs (sampleRegs (2^64-1) 3)))
      (fun result => (scanByte.action.address result.ctx).toNat ≠ (2^64-1) + 1) := by
  obtain ⟨result, certificate, _, invariant⟩ := entry_checked
    (k.withRegs (sampleRegs (2^64-1) 3)) (BitVec.ofNat 64 (2^64-1))
    (by simp [sampleRegs]) 1#8 (by decide)
  refine ⟨result, certificate, ?_⟩
  change (scanByte.action.address result.ctx).toNat ≠ (2^64-1) + 1
  rw [read_address result.ctx _ 1 invariant]
  decide

/-- Neither an ordinary loop row nor the empty-string suffix may disappear
when the checked certificate is rebased onto the frame-filtered body. -/
theorem reject_missing_loop_row :
    filterCheck Binary.strlen.rows bodyRegion
      (fun row => bodyKeep row && row.pc != 0x80000eb0#64) = false := by binary_rfl

theorem reject_missing_empty_suffix :
    filterCheck Binary.strlen.rows bodyRegion
      (fun row => bodyKeep row && row.pc != 0x80000ecc#64) = false := by binary_rfl

open Lean in
run_cmd do
  for decl in #[``reject_initial_zero, ``reject_stride_two, ``reject_nonmodular_address,
      ``reject_missing_loop_row, ``reject_missing_empty_suffix] do
    let axioms ← collectAxioms decl
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Affine counterexample introduced axioms: {axioms}"

end Xv6.WholeFunction.Affine
