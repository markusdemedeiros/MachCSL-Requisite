/-
The unchanged COPYOUT interface, derived from the complete binary-driven
function proof. Its semantic parameters are the public walkaddr, vmfault,
nonallocating walk, and memmove contracts.
-/
import Experiments.WholeFunction.CopyoutComplete

namespace Xv6

/-- Copy into user memory through the complete compiled function certificate. -/
theorem copyout_proof (WA : WALKADDR) (VF : VMFAULT) (W : WALK_NOALLOC) (MM : MEMMOVE) : COPYOUT :=
  WholeFunction.Copyout.compiled_copyout WA VF W MM

end Xv6
