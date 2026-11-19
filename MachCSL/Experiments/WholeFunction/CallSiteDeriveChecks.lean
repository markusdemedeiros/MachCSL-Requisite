import Experiments.WholeFunction.KernelCallSites
import Experiments.WholeFunction.BinaryCopy

namespace Xv6.WholeFunction.CallSiteDeriveChecks
open MachCSL LeanRV64D

noncomputable def walk : CallSite Binary.copyout.rows
    0x80001640#64 KA.«walk» 0x80001644#64 := by checked_callsite
noncomputable def move : CallSite Binary.copyin.rows
    0x800016d0#64 KA.«memmove» 0x800016d4#64 := by checked_callsite

example : True := by
  fail_if_success
    have wrongTarget : CallSite Binary.copyout.rows
        0x80001640#64 KA.«memmove» 0x80001644#64 := by checked_callsite
  fail_if_success
    have wrongReturn : CallSite Binary.copyout.rows
        0x80001640#64 KA.«walk» 0x80001646#64 := by checked_callsite
  fail_if_success
    have notACall : CallSite Binary.copyout.rows
        0x80001644#64 KA.«walk» 0x80001646#64 := by checked_callsite
  trivial

open Lean in
run_cmd do
  for decl in #[``walk, ``move] do
    let axs ← collectAxioms decl
    unless axs.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Generated call descriptor introduced axioms: {axs}"

end Xv6.WholeFunction.CallSiteDeriveChecks
