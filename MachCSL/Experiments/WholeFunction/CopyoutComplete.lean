import Experiments.WholeFunction.CopyoutRegistryClient

namespace Xv6.WholeFunction.Copyout

/-- Stable public export; the implementation uses witnessed finite call
registries, declarative sites and the shared actual-binary dispatcher. -/
theorem compiled_copyout (WA : WALKADDR) (VF : VMFAULT) (W : WALK_NOALLOC) (MM : MEMMOVE) : COPYOUT :=
  Registered.compiled_copyout WA VF W MM

end Xv6.WholeFunction.Copyout
