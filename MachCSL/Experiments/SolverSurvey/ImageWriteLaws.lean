import Experiments.WholeFunction.CopyRuns
import Lean.Util.CollectAxioms

/-! Local call results preserve the existing write-run invariant. These laws
consume checked effect steps; they do not replace the machine/callee boundary.
No global image equation is supplied by a caller. -/
namespace Experiments.WholeFunction.Copy
open Xv6

/-- A checked effect which copied no bytes is a fault transition. A positive
write cannot silently pass through this interface as an allocation. -/
theorem write_run_fault_step {sz a : BitVec 64} {src : List (BitVec 8)}
    {P : UPtd} {M : Image} {ke : Nat} {s t : State}
    (h : WriteRun sz a src P M ke s) (hs : Step .write sz a s t)
    (copied : t.copied = s.copied) : WriteRun sz a src P M ke t := by
  cases hs with
  | fault Q ke' he hk => exact .fault h Q ke' he hk
  | chunk bs positive page mapped access read =>
    have hc := congrArg List.length copied
    simp only [transfer, List.length_append] at hc
    omega

/-- A source slice that fits has its requested length; truncating `take`
does not excuse an out-of-bounds copy request. -/
theorem transfer_slice_length {src : List (BitVec 8)} {s : State} {a : BitVec 64} {n : Nat}
    (bound : s.copied.length + n ≤ src.length) :
    (transfer .write a s ((src.drop s.copied.length).take n)).copied.length =
      s.copied.length + n := by
  simp only [transfer, List.length_append, List.length_take, List.length_drop]
  omega

/-- A registered chunk call selects its input at the current source cursor.
The run invariant and exact cursor progress follow without separate prefix,
image, page-map or byte-permission reconstruction. -/
theorem write_run_slice_step {sz a : BitVec 64} {src : List (BitVec 8)}
    {P : UPtd} {M : Image} {ke n : Nat} {s : State}
    (h : WriteRun sz a src P M ke s)
    (hs : Step .write sz a s (transfer .write a s ((src.drop s.copied.length).take n)))
    (bound : s.copied.length + n ≤ src.length) :
    WriteRun sz a src P M ke (transfer .write a s ((src.drop s.copied.length).take n)) ∧
      (transfer .write a s ((src.drop s.copied.length).take n)).copied.length =
        s.copied.length + n := by
  have hn : ((src.drop s.copied.length).take n).length = n := by
    simp only [List.length_take, List.length_drop]
    omega
  refine ⟨.chunk h _ hs ?_ ?_, transfer_slice_length bound⟩
  · simpa only [hn] using bound
  · rw [hn]

/-- info: 'Experiments.WholeFunction.Copy.write_run_fault_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms write_run_fault_step

/-- info: 'Experiments.WholeFunction.Copy.write_run_slice_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms write_run_slice_step

end Experiments.WholeFunction.Copy
