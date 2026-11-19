import Experiments.WholeFunction.KernelChecks
import Experiments.WholeFunction.KernelCycle
import Experiments.WholeFunction.KernelStackGraph

/-! The production Sail/kernel rules already depend on native bv_decide
axioms. These checks enforce that the compiler adds no axioms beyond the
union of its existing instruction-rule dependencies. -/
open Lean in
run_cmd do
  let rules := #[``MachCSL.wp_s_addi, ``MachCSL.wp_s_addiw, ``MachCSL.wp_s_add, ``MachCSL.wp_s_sub,
    ``MachCSL.wp_s_and, ``MachCSL.wp_s_andi, ``MachCSL.wp_s_srli, ``MachCSL.wp_s_lui, ``MachCSL.wp_s_branch,
    ``MachCSL.wp_s_subw, ``MachCSL.wp_s_addw, ``MachCSL.wp_s_branch0,
    ``MachCSL.wp_s_j, ``MachCSL.wp_s_ret, ``MachCSL.wp_s_push, ``MachCSL.wp_s_pop,
    ``MachCSL.wp_s_ld, ``MachCSL.wp_s_sd]
  let mut baseline : Array Name := #[]
  for rule in rules do
    for ax in ← collectAxioms rule do
      if !baseline.contains ax then baseline := baseline.push ax
  let checks := #[``Xv6.WholeFunction.RegAction.sound,
    ``Xv6.WholeFunction.reg_graph_transfer, ``Xv6.WholeFunction.wp_reg_graph,
    ``Xv6.WholeFunction.copyin_zero_compiled, ``Xv6.WholeFunction.panic_loop_compiled,
    ``Xv6.WholeFunction.MixedAction.sound, ``Xv6.WholeFunction.mixed_graph_transfer,
    ``Xv6.WholeFunction.wp_mixed_graph]
  for decl in checks do
    let axioms ← collectAxioms decl
    let extra := axioms.filter fun a => !baseline.contains a
    unless extra.isEmpty do throwError "{decl}: new axioms {extra}"
    if axioms.contains ``sorryAx then throwError "{decl}: contains sorryAx"
  logInfo m!"Eight compiler/actual-binary theorems add no axioms beyond {baseline.size} production-rule axioms."
