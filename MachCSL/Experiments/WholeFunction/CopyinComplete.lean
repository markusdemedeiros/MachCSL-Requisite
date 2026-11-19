import Experiments.WholeFunction.CopyinRegistryClient

/-! Stable public export of the complete binary-driven COPYIN proof. All call
lookup, witnessed return dispatch and body composition use the shared finite
registry; this module contains no second body implementation. -/
namespace Xv6.WholeFunction.Copyin

theorem compiled_copyin (WA : WALKADDR) (VF : VMFAULT) (MM : MEMMOVE) : COPYIN :=
  RegistryClient.compiled_copyin WA VF MM

end Xv6.WholeFunction.Copyin

open Lean in
run_cmd do
  let expected ← collectAxioms ``Xv6.WholeFunction.Copyin.RegistryClient.compiled_copyin
  let actual ← collectAxioms ``Xv6.WholeFunction.Copyin.compiled_copyin
  unless actual == expected do throwError "COPYIN public export changed the axiom set"
  if actual.contains ``sorryAx then throwError "COPYIN public export contains sorryAx"
  logInfo m!"COPYIN finite-registry public export: {actual.size} unchanged axioms."
