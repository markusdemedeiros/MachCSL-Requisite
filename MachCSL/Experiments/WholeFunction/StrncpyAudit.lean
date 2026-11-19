import Experiments.WholeFunction.StrncpyComplete
import Lean.Util.CollectAxioms

/-! Check the unchanged public type and reject new axiom dependencies. The
baseline is the existing instruction rules and arithmetic lemmas, never the
old STRNCPY proof or the new compiler itself. -/
example : Xv6.STRNCPY := Xv6.WholeFunction.Strncpy.compiled_strncpy

open Lean in
run_cmd do
  let mut baseline : Array Name := #[]
  for decl in #[``MachCSL.wp_s_addi, ``MachCSL.wp_s_addiw,
      ``MachCSL.wp_s_add, ``MachCSL.wp_s_sub, ``MachCSL.wp_s_and,
      ``MachCSL.wp_s_andi, ``MachCSL.wp_s_srli, ``MachCSL.wp_s_lui,
      ``MachCSL.wp_s_branch, ``MachCSL.wp_s_j, ``MachCSL.wp_s_ret,
      ``MachCSL.wp_s_push, ``MachCSL.wp_s_pop, ``MachCSL.wp_s_ld,
      ``MachCSL.wp_s_sd, ``MachCSL.wp_s_lbu, ``MachCSL.wp_s_sb,
      ``MachCSL.wp_s_subw, ``MachCSL.wp_s_addw, ``MachCSL.wp_s_branch0,
      ``Xv6.fw_ext32, ``Xv6.extractLsb'_ofNat64,
      ``MachCSL.signExtend_ofNat32, ``MachCSL.toInt_ofNat] do
    for ax in ← collectAxioms decl do
      if !baseline.contains ax then baseline := baseline.push ax
  let axioms ← collectAxioms ``Xv6.WholeFunction.Strncpy.compiled_strncpy
  let extra := axioms.filter fun ax => !baseline.contains ax
  unless extra.isEmpty do throwError "STRNCPY adds axioms: {extra}"
  if axioms.contains ``sorryAx then throwError "STRNCPY contains sorryAx"
  let env ← getEnv
  if env.contains `Xv6.strncpy_proof then
    throwError "Old STRNCPY proof is in the import closure"
  logInfo m!"Unconditional STRNCPY checked: {axioms.size} axioms, all in the existing production-rule/arithmetic baseline ({baseline.size}). Old strncpy_proof absent."

#check Xv6.WholeFunction.Strncpy.compiled_strncpy
