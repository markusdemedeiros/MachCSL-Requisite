import Experiments.WholeFunction.CopyoutRegistryClient

/-! Rejection properties for the finite call registry. These are theorems
about the actual binary and actual enabled witnesses, rather than examples
that merely restate a constructor. -/
namespace Xv6.WholeFunction.Copyout.Registered.Checks
open MachCSL

/-- The actual PTE load is not a JAL and cannot be registered as a callsite. -/
theorem wrong_pc (target ret : BitVec 64) :
    ¬ Nonempty (CallSite Binary.copyout.rows 0x80001644#64 target ret) := by
  rintro ⟨site⟩
  have none : findCall 0x80001644#64 Binary.copyout.rows = none := by binary_rfl
  have found := site.found
  rw [none] at found
  cases found

/-- An ABI-compatible callee cannot be substituted at the wrong target. -/
theorem wrong_target :
    ¬ Nonempty (CallSite Binary.copyout.rows 0x80001622#64 KA.«memmove» 0x80001626#64) := by
  rintro ⟨site⟩
  have impossible := walkSite.unique_target site
  contradiction

/-- The descriptor's hardware return address is constrained independently
of the semantic continuation supplied by the callee summary. -/
theorem wrong_return :
    ¬ Nonempty (CallSite Binary.copyout.rows 0x80001640#64 KA.«walk» 0x80001646#64) := by
  rintro ⟨site⟩
  have impossible := probeSite.unique_return site
  contradiction

/-- The enabled leaf remains attached to the return relation. A forged leaf
cannot alter the permission-check result after the actual load. -/
theorem probe_witness_retained {i : Inputs} {s t : State} {leaf : BitVec 64}
    (pc : s.machine.pc = KA.«walk»)
    (lookup : Iris.Std.PartialMap.get? s.memory.table.um (vpnOf (s.machine.ctx.regs 11#5)).toNat = some leaf)
    (step : (registry i).Next s t) : ProbeNext i s leaf t := by
  obtain ⟨w,enabled,result⟩ := (registry i).next_at 2 pc step
  change ProbeEnabled i s w at enabled
  have same := Option.some.inj (enabled.lookup.symm.trans lookup)
  subst w
  exact result

theorem wrong_probe_witness {i : Inputs} {s : State} {leaf forged : BitVec 64}
    (lookup : Iris.Std.PartialMap.get? s.memory.table.um (vpnOf (s.machine.ctx.regs 11#5)).toNat = some leaf)
    (different : forged ≠ leaf) : ¬ (probeFamily i).Enabled forged s := by
  intro enabled
  exact different (Option.some.inj (enabled.lookup.symm.trans lookup))

/-- The registered probe legitimately continues after its load, two bytes
beyond the JAL's hardware return address. -/
theorem probe_continuation {i : Inputs} {s t : State}
    (pc : s.machine.pc = KA.«walk») (step : (registry i).Next s t) :
    t.machine.pc = 0x80001646#64 := by
  obtain ⟨w,enabled,result⟩ := (registry i).next_at 2 pc step
  change ProbeNext i s w t at result
  obtain ⟨R,rfl,_⟩ := result
  rfl

end Xv6.WholeFunction.Copyout.Registered.Checks

open Lean in
run_cmd do
  for name in #[``Xv6.WholeFunction.CallSite.entry_eq,
      ``Xv6.WholeFunction.CalleeRegistry.spec,
      ``Xv6.WholeFunction.AnnotatedSite.ready,
      ``Xv6.WholeFunction.AnnotatedSite.closed,
      ``Xv6.WholeFunction.Copyout.Registered.Checks.wrong_pc,
      ``Xv6.WholeFunction.Copyout.Registered.Checks.wrong_target,
      ``Xv6.WholeFunction.Copyout.Registered.Checks.wrong_return,
      ``Xv6.WholeFunction.Copyout.Registered.Checks.probe_witness_retained,
      ``Xv6.WholeFunction.Copyout.Registered.Checks.wrong_probe_witness,
      ``Xv6.WholeFunction.Copyout.Registered.Checks.probe_continuation] do
    let axs ← collectAxioms name
    unless axs.all (fun a => #[``propext, ``Classical.choice, ``Quot.sound].contains a) do
      throwError "{name}: unexpected axioms {axs}"
