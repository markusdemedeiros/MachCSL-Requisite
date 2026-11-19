import Experiments.WholeFunction.MemoryPrefix
import Experiments.WholeFunction.StrlenBinary
import Experiments.WholeFunction.StrncpyBinary

namespace Xv6.WholeFunction.Symbolic
open MachCSL
set_option maxHeartbeats 0

private def cuts (pc : BitVec 64) : Bool :=
  pc == 0x80000eb8#64 || pc == 0x80000ebe#64 || pc == 0x80000ec2#64

theorem first_frontier (k : KCtx) : Prefix Binary.strlen.rows cuts ⟨k, 0x80000eae#64⟩
    (fun r => r.pc = 0x80000ec2#64 ∨ r.pc = 0x80000eb8#64) := by
  symbolic_prefix 5 <;> first | exact Or.inl rfl | exact Or.inr rfl

theorem loop_frontier (k : KCtx) : Prefix Binary.strlen.rows cuts ⟨k, 0x80000ebc#64⟩
    (fun r => r.pc = 0x80000ebe#64 ∨ r.pc = 0x80000eb8#64) := by
  symbolic_prefix 4 <;> first | exact Or.inl rfl | exact Or.inr rfl

/-- The SUBW result stays symbolic through the actual signed branch. Reducing
the whole branch condition instead of exposing its head caused recursion
failure here; this regression runs at the ordinary checker depth limit. -/
theorem word_branch_frontier (s : Stack.State) :
    Prefix Binary.strncpy.rows
      (fun pc => pc == 0x80000e58#64 || pc == 0x80000e64#64)
      ⟨s.ctx, 0x80000e5c#64⟩
      (fun r => r.ctx.regs 13#5 =
          ((s.ctx.regs 15#5).extractLsb' 0 32 -
            (s.ctx.regs 14#5).extractLsb' 0 32).signExtend 64 ∧
        (r.pc = 0x80000e58#64 ∨ r.pc = 0x80000e64#64)) := by
  symbolic_prefix 3
  all_goals constructor
  all_goals first
    | simp [RegMap.set_apply]
    | exact Or.inl rfl
    | exact Or.inr rfl

example (k : KCtx) : True := by
  fail_if_success
    have bad : Prefix Binary.strlen.rows cuts ⟨k, 0x80000eae#64⟩ (fun _ => True) := by
      symbolic_prefix 0 <;> trivial
  -- The LBU is a genuine unsupported boundary, never a silent fallthrough.
  fail_if_success
    have bad : Prefix Binary.strlen.rows cuts ⟨k, 0x80000eaa#64⟩ (fun _ => True) := by
      symbolic_prefix 5 <;> trivial
  fail_if_success
    have bad : Prefix Binary.strlen.rows cuts ⟨k, 0x1234#64⟩ (fun _ => True) := by
      symbolic_prefix 5 <;> trivial
  -- Even after successful execution, the caller must prove the semantic post.
  fail_if_success
    have bad : Prefix Binary.strlen.rows cuts ⟨k, 0x80000ebc#64⟩
        (fun r => r.pc = 0x1234#64) := by
      symbolic_prefix 4 <;> rfl
  trivial

noncomputable def hartRead : Binary.Row :=
  Binary.rowAt (KA.«cpuid» + 8#64) (by binary_rfl) (by binary_rfl)

example (k : KCtx) : True := by
  fail_if_success
    have bad : Prefix [hartRead] (fun _ => false) ⟨k, KA.«cpuid» + 8#64⟩
        (fun _ => True) := by
      symbolic_prefix 1 <;> trivial
  trivial

end Xv6.WholeFunction.Symbolic

open Lean in
run_cmd do
  for decl in #[``Xv6.WholeFunction.Symbolic.Prefix.step,
      ``Xv6.WholeFunction.Symbolic.first_frontier,
      ``Xv6.WholeFunction.Symbolic.loop_frontier,
      ``Xv6.WholeFunction.Symbolic.word_branch_frontier] do
    let axioms ← collectAxioms decl
    let extra := axioms.filter fun ax =>
      ![``propext, ``Quot.sound, ``Classical.choice].contains ax
    unless extra.isEmpty do throwError "Prefix certificate added axioms: {extra}"
  logInfo "Actual branch frontiers checked; rejected exhausted, unsupported, missing, wrong-post and hart-dependent paths."
