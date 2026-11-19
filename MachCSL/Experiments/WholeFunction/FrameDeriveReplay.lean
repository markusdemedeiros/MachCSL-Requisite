import Experiments.WholeFunction.FrameDeriveChecks

/-! Independently replay the kernel checks of each generated certificate and
its private helper proofs. This measures checking separately from frontend
metadata computation and simplification. Existing imported backend theorems
remain the shared trust baseline. -/
open Lean in
run_cmd do
  let environment ← getEnv
  for root in #[``Xv6.WholeFunction.FrameDerive.Checks.strncpy,
      ``Xv6.WholeFunction.FrameDerive.Checks.copyin,
      ``Xv6.WholeFunction.FrameDerive.Checks.copyout,
      ``Xv6.WholeFunction.FrameDerive.Checks.consoleread,
      ``Xv6.WholeFunction.FrameDerive.Checks.kexec] do
    let mut count : Nat := 0
    let start ← IO.monoNanosNow
    for (name, declaration) in environment.constants.toList do
      if root.isPrefixOf name then
        if let some value := declaration.value? true then
          match Kernel.check environment {} value with
          | .ok _ => count := count + 1
          | .error error => throwError "Kernel replay failed for {name}: {error.toMessageData (← getOptions)}"
    let elapsed ← IO.monoNanosNow
    logInfo m!"{root}: replayed {count} generated declarations in {(elapsed-start)/1000000} ms"

namespace Xv6.WholeFunction.FrameDerive.Checks
open MachCSL

private theorem padding (layout : FrameCompiler.Layout) (saved : List (Nat × BitVec 5))
    (body : BitVec 64) (entry : KCtx) (values : Fin layout.slots → BitVec 64)
    (slot : Nat) (outside : slot ∉ saved.map Prod.fst) :
    (savedState layout saved body entry values).cells[slot]? =
      (rawCells entry layout.slots values)[slot]? :=
  savedCells_get_untouched saved entry (rawCells entry layout.slots values) slot outside

/-- Actual unused COPYOUT padding can contain any original word. -/
example (entry : KCtx) (values : Fin 14 → BitVec 64) :
    (savedState copyout.layout copyout.saved copyout.body entry values).cells[13]? =
      (rawCells entry 14 values)[13]? :=
  padding copyout.layout copyout.saved copyout.body entry values 13 (by
    change 13 ∉ [0,1,2,3,4,5,6,7,8,9,10,11,12]
    decide)

/-- The interior hole in CONSOLEREAD is retained, not compacted away. -/
example (entry : KCtx) (values : Fin 12 → BitVec 64) :
    (savedState consoleread.layout consoleread.saved consoleread.body entry values).cells[6]? =
      (rawCells entry 12 values)[6]? :=
  padding consoleread.layout consoleread.saved consoleread.body entry values 6 (by
    change 6 ∉ [0,1,2,3,4,5,7,8]
    decide)

/-- The largest mixed-width fixture also retains its last scratch slot. -/
example (entry : KCtx) (values : Fin 68 → BitVec 64) :
    (savedState kexec.layout kexec.saved kexec.body entry values).cells[67]? =
      (rawCells entry 68 values)[67]? :=
  padding kexec.layout kexec.saved kexec.body entry values 67 (by
    change 67 ∉ [0,1,2,3]
    decide)

end Xv6.WholeFunction.FrameDerive.Checks
