import Experiments.WholeFunction.StrlenComplete

open Lean in
run_cmd do
  let rules := #[``Xv6.WholeFunction.MixedAction.sound, ``MachCSL.wp_s_push,
    ``MachCSL.wp_s_lbu, ``MachCSL.wp_s_subw]
  let mut baseline : Array Name := #[]
  for rule in rules do
    for ax in ← collectAxioms rule do
      if !baseline.contains ax then baseline := baseline.push ax
  for decl in #[``Xv6.WholeFunction.StrlenFrame.wp_prologue,
      ``Xv6.WholeFunction.StrlenFrame.wp_return,
      ``Xv6.WholeFunction.Strlen.compile,
      ``Xv6.WholeFunction.Strlen.compiled_strlen] do
    let axioms ← collectAxioms decl
    let extra := axioms.filter fun a => !baseline.contains a
    unless extra.isEmpty do throwError "{decl}: new axioms {extra}"
    if axioms.contains ``sorryAx then throwError "{decl}: contains sorryAx"
  for decl in #[``Xv6.WholeFunction.Strlen.effects,
      ``Xv6.WholeFunction.Strlen.writes_accepted,
      ``Xv6.WholeFunction.Strlen.first_good, ``Xv6.WholeFunction.Strlen.loop_good,
      ``Xv6.WholeFunction.Affine.entry_body_checked,
      ``Xv6.WholeFunction.Affine.step_body_checked,
      ``Xv6.WholeFunction.Strlen.compile] do
    let extra := (← collectAxioms decl).filter fun a =>
      !(#[``propext, ``Classical.choice, ``Quot.sound]).contains a
    unless extra.isEmpty do throwError "Pure STRLEN certificate {decl}: unexpected axioms {extra}"
  let forbidden := #[`Xv6.strlen_proof, `Xv6.strlen_iter, `Xv6.strlen_loop,
    `Xv6.subw_len, `Xv6.cstrAt_of_nonul]
  let env ← getEnv
  let mut seen : Std.HashSet Name := {}
  let mut todo := #[``Xv6.WholeFunction.Strlen.compiled_strlen]
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    unless seen.contains name do
      seen := seen.insert name
      if forbidden.contains name then throwError "Old STRLEN proof dependency: {name}"
      if let some info := env.find? name then
        todo := todo ++ info.type.getUsedConstants
        if let some value := info.value? then todo := todo ++ value.getUsedConstants
  logInfo m!"Complete compiled STRLEN: no old proof/iteration dependencies; no axioms beyond {baseline.size} inherited instruction-rule axioms."
