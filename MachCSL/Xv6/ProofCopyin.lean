/-
The unchanged COPYIN interface, derived from the complete binary-driven
function proof. Its only semantic parameters are the public walkaddr,
vmfault, and memmove contracts.
-/
import Experiments.WholeFunction.CopyinComplete

namespace Xv6

/-- Copy from user memory through the complete compiled function certificate. -/
theorem copyin_proof (WA : WALKADDR) (VF : VMFAULT) (MM : MEMMOVE) : COPYIN :=
  WholeFunction.Copyin.compiled_copyin WA VF MM

end Xv6
