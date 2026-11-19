import Experiments.WholeFunction.AffineSamples
import Experiments.WholeFunction.AffineCandidates
import Experiments.SolverSurvey.SmtSlice

/-! Samples and solver models have no proof authority. These universal
obligations accept the generated table only after checking the actual binary
entry and backedge, for arbitrary registers, pointers, counters and bytes. -/
namespace Xv6.WholeFunction.Affine
open MachCSL LeanRV64D
set_option linter.unusedSimpArgs false

theorem byte_zero (b : BitVec 8) : b.setWidth 64 = 0#64 ↔ b = 0#8 := by
  constructor
  · intro h
    have := congrArg (BitVec.setWidth 8) h
    simpa using this
  · intro h; subst b; rfl

theorem entry_checked (k : KCtx) (base : BitVec 64)
    (anchor : k.regs 10#5 = base) (byte : BitVec 8) (nonzero : byte ≠ 0#8) :
    Symbolic.Prefix Binary.strlen.rows scanCut (readResult firstByte k byte)
      (fun result => result.pc = 0x80000eb8#64 ∧ Holds inferred base 1 result.ctx) := by
  dsimp only [readResult, firstByte, Memory.Op.run, Stack.State.machine]
  symbolic_prefix 8
  all_goals simp_all [bcond, byte_zero, Holds, inferred, Rule.value,
    KCtx.setReg_regs, RegMap.set_apply, BitVec.ofNat_add, BitVec.add_assoc]

theorem step_checked (k : KCtx) (base : BitVec 64) (j : Nat)
    (invariant : Holds inferred base j k) (byte : BitVec 8) (nonzero : byte ≠ 0#8) :
    Symbolic.Prefix Binary.strlen.rows scanCut (readResult scanByte k byte)
      (fun result => result.pc = 0x80000eb8#64 ∧ Holds inferred base (j+1) result.ctx) := by
  dsimp only [readResult, scanByte, Memory.Op.run, Stack.State.machine]
  symbolic_prefix 8
  all_goals simp_all [bcond, byte_zero, Holds, inferred, Rule.value,
    KCtx.setReg_regs, RegMap.set_apply, BitVec.ofNat_add, BitVec.add_assoc]

/-- The generated register table proves the actual load's address obligation.
The client need not name the cursor register or its off-by-one convention. -/
theorem read_address (k : KCtx) (base : BitVec 64) (j : Nat)
    (invariant : Holds inferred base j k) :
    scanByte.action.address k = base + BitVec.ofNat 64 j := by
  simp [Holds, inferred, Rule.value] at invariant
  simp_all [scanByte, Memory.Op.address, KCtx.rget_eq]
  all_goals bv_smt

open Lean in
run_cmd do
  for decl in #[``entry_checked, ``step_checked, ``read_address] do
    let axioms ← collectAxioms decl
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Affine replay introduced axioms: {axioms}"

end Xv6.WholeFunction.Affine
