import Experiments.SolverSurvey.BlockChecks
import Experiments.SolverSurvey.BlockMachine
import Experiments.SolverSurvey.BlockPhase
import Experiments.SolverSurvey.BlockBridge

namespace Experiments.SolverSurvey.Block
open Fixture
open Xv6.WholeFunction Xv6.WholeFunction.Copyin MachCSL

/-- The machine-level solver postcondition is attached to the checked
execution certificate for the real decoded copyin prefix. -/
theorem page_compiled (k : KCtx)
    (page : k.regs 19#5 = k.regs 18#5 &&& 0xFFFFFFFFFFFFF000#64)
    (size : k.regs 22#5 = 4096#64) :
    Symbolic.Certificate Binary.copyin.rows bodyCuts
      ⟨k, 0x800016b8#64⟩ ⟨pageResult k, .cut⟩ ∧ PageABI k (pageResult k).ctx :=
  ⟨page_certificate k, page_machine k page size⟩

open Lean in
private partial def dependencies (env : Environment) (todo : List Name)
    (seen : NameSet := {}) : NameSet :=
  match todo with
  | [] => seen
  | name :: todo =>
    if seen.contains name then dependencies env todo seen else
    let seen := seen.insert name
    match env.find? name with
    | none => dependencies env todo seen
    | some info =>
      let uses := info.type.getUsedConstants ++
        ((info.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]
      dependencies env (uses.toList ++ todo) seen

open Lean in
run_cmd do
  let standard := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``Fixture.page_certificate, ``page_count, ``moved_done, ``moved_done_variant] do
    let axioms ← collectAxioms decl
    unless axioms.all (standard.contains ·) do
      throwError "Kernel-replayed block theorem has unexpected axioms: {decl}: {axioms}"
  for decl in #[``page_machine, ``page_chunk_values_vc, ``page_chunk_values_bridge, ``page_compiled] do
    let axioms ← collectAxioms decl
    let extra := axioms.filter (!standard.contains ·)
    for ax in extra do
      let some info := (← getEnv).find? ax | throwError "missing axiom {ax}"
      let args := info.type.getAppArgs
      unless info.type.isAppOfArity ``Eq 3 && args[0]! == mkConst ``Bool &&
          args[1]!.isAppOfArity ``Std.Tactic.BVDecide.Reflect.verifyBVExpr 2 &&
          args[2]! == mkConst ``Bool.true && !info.type.hasFVar && !info.type.hasMVar do
        throwError "Unexpected native-certificate axiom: {ax}: {info.type}"
    logInfo m!"{decl}: {extra.size} closed native BV verifier facts, no other new axioms"
  let prohibited := #["page_certificate", "page_symbolic", "walk_symbolic", "fault_symbolic",
    "move_symbolic", "page_values", "page_chunk_values", "loop_selected_chunk",
    "loop_page_remaining", "selected_chunk", "loop_source_offset", "loop_physical_source",
    "source_offset", "page_remaining", "chunk_sextw", "sextw_small_checked", "move_remaining",
    "moveDone_iff", "update_loop", "page_chunk", "page_nowrap", "chunk_facts"]
  for decl in #[``Fixture.page_certificate, ``page_compiled, ``page_machine,
      ``page_chunk_values_vc, ``page_chunk_values_bridge, ``page_count, ``moved_done] do
    let used := dependencies (← getEnv) [decl]
    for suffix in prohibited do
      let name := (s!"Xv6.WholeFunction.Copyin.{suffix}").toName
      if used.contains name then throwError "{decl} reused prohibited old proof {name}"
  logInfo "Block VCs do not reuse the previous page/chunk/move proof chain."

end Experiments.SolverSurvey.Block
