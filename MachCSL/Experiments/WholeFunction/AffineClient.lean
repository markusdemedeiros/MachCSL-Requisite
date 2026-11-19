import Experiments.WholeFunction.AffineReplay

/-! A resource-aware consumer of the discovered relation. The statement names
the semantic byte index, but no cursor register or register offset. -/
namespace Xv6.WholeFunction.Affine
open MachCSL

theorem scan_enabled (s : Memory.State) (base : BitVec 64) (fraction : Iris.DFrac)
    (bytes : List (BitVec 8)) (j : Nat) (byte : BitVec 8)
    (buffers : s.buffers = [⟨base,fraction,bytes⟩])
    (lookup : bytes[j]? = some byte)
    (invariant : Holds inferred base j s.machine.ctx) :
    scanByte.action.Enabled ⟨0,j⟩ s := by
  refine ⟨⟨base,fraction,bytes⟩, byte, ?_, lookup, ?_, ?_⟩
  · simp [buffers]
  · exact read_address s.machine.ctx base j invariant
  · simp [scanByte, Memory.Op.canAccess]

open Lean in
run_cmd do
  let axioms ← collectAxioms ``scan_enabled
  unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
    throwError "Affine client introduced axioms: {axioms}"
  let forbidden := #[`Xv6.WholeFunction.Strlen.Scan,
    `Xv6.WholeFunction.Strlen.loop_good, `Xv6.WholeFunction.Copyin.LoopRegs,
    `Xv6.strlen_proof]
  for name in forbidden do
    if (← getEnv).contains name then throwError "Handwritten invariant imported: {name}"

end Xv6.WholeFunction.Affine
