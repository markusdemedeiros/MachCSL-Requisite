import Experiments.WholeFunction.MemoryPrefixChecks
import Experiments.WholeFunction.StrncpyBinary

/-! Lookup metadata imported from another checked module can be reused, while
tables, cutpoints and semantic postconditions retain their own obligations. -/
namespace Xv6.WholeFunction.Symbolic.CacheChecks
open MachCSL
set_option symbolicPrefix.traceCache true

private def cuts (pc : BitVec 64) : Bool :=
  pc == 0x80000eb8#64 || pc == 0x80000ec2#64

theorem imported_metadata (k : KCtx) : Prefix Binary.strlen.rows cuts ⟨k, 0x80000eae#64⟩
    (fun r => r.pc = 0x80000ec2#64 ∨ r.pc = 0x80000eb8#64) := by
  symbolic_prefix 5 <;> first | exact Or.inl rfl | exact Or.inr rfl

/-- Only instruction metadata is shared; a new stopping condition still
changes execution and the endpoint the client must justify. -/
theorem different_cut (k : KCtx) :
    Prefix Binary.strlen.rows (fun pc => pc == 0x80000eca#64 || pc == 0x80000eb0#64)
      ⟨k, 0x80000eae#64⟩ (fun r => r.pc = 0x80000eca#64 ∨ r.pc = 0x80000eb0#64) := by
  symbolic_prefix 1 <;> first | exact Or.inl rfl | exact Or.inr rfl

example (k : KCtx) : True := by
  -- The same PC with another actual binary table must not hit old evidence.
  fail_if_success
    have bad : Prefix Binary.strncpy.rows cuts ⟨k, 0x80000eae#64⟩ (fun _ => True) := by
      symbolic_prefix 5 <;> trivial
  -- The first instruction is present, but all of its successor rows are
  -- missing. Cached evidence for the complete table cannot fill those gaps.
  fail_if_success
    have bad : Prefix [Binary.strlen_00c] cuts ⟨k, 0x80000eae#64⟩ (fun _ => True) := by
      symbolic_prefix 5 <;> trivial
  -- Reused instruction evidence cannot establish a false semantic post.
  fail_if_success
    have bad : Prefix Binary.strlen.rows cuts ⟨k, 0x80000eae#64⟩
        (fun r => r.pc = 0x1234#64) := by
      symbolic_prefix 5 <;> rfl
  trivial

end Xv6.WholeFunction.Symbolic.CacheChecks

open Lean in
run_cmd do
  for decl in #[``Xv6.WholeFunction.Symbolic.CacheChecks.imported_metadata,
      ``Xv6.WholeFunction.Symbolic.CacheChecks.different_cut] do
    let extra := (← collectAxioms decl).filter fun ax =>
      ![``propext, ``Quot.sound, ``Classical.choice].contains ax
    unless extra.isEmpty do throwError "Cached prefix added axioms: {extra}"
  logInfo "Imported lookup metadata replayed; changed-table and wrong-post goals rejected."
