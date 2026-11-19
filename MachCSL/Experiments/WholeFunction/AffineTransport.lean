import Experiments.WholeFunction.AffineReplay
import Experiments.WholeFunction.MemoryFrame

/-! Reuse a checked prefix after removing separately verified frame rows.
Filtering preserves every lookup reachable inside a checked control-flow
region. No register invariant is repeated or supplied to this transport. -/
namespace Xv6.WholeFunction.Affine
open MachCSL LeanRV64D
set_option linter.unusedSimpArgs false

private theorem found_member (pc : BitVec 64) (rows : List Binary.Row)
    (r : LocatedReg pc) (found : findReg pc rows = some r) : r.row ∈ rows := by
  induction rows with
  | nil => simp [findReg] at found
  | cons row rows ih =>
    simp only [findReg] at found
    split at found
    · rename_i address
      cases decoded : RegAction.decode row.code with
      | none => simp [decoded] at found
      | some action =>
        simp only [decoded, Option.map_some, Option.some.injEq] at found
        cases found
        exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih found)

private theorem found_filter (keep : Binary.Row → Bool) (pc : BitVec 64)
    (rows : List Binary.Row) (r : LocatedReg pc)
    (found : findReg pc rows = some r) (retained : keep r.row = true) :
    findReg pc (rows.filter keep) = some r := by
  induction rows with
  | nil => simp [findReg] at found
  | cons row rows ih =>
    simp only [findReg] at found
    split at found
    · rename_i address
      cases decoded : RegAction.decode row.code with
      | none => simp [decoded] at found
      | some action =>
        simp only [decoded, Option.map_some, Option.some.injEq] at found
        cases found
        simp [List.filter_cons, retained, findReg, address, decoded]
    · rename_i address
      by_cases kept : keep row = true
      · simp only [List.filter_cons, kept, ↓reduceIte, findReg, address]
        exact ih found
      · simpa [List.filter_cons, kept] using ih found

def flowClosed (region : BitVec 64 → Bool) (row : Binary.Row) : Bool :=
  match row.flow with
  | .next p | .jump p => region p
  | .branch p q => region p && region q
  | _ => false

private theorem run_region (region : BitVec 64 → Bool) (s : RegState)
    (r : LocatedReg s.pc) (closed : flowClosed region r.row = true) :
    region (r.action.run r.row.rvc Symbolic.canonical s).pc = true := by
  have address := r.address
  have decoded := r.decoded
  have zero : (regidx.Regidx 0#5 == regidx.Regidx 0#5) = true := by decide
  cases width : r.row.rvc <;> cases action : r.action <;>
    simp_all [flowClosed, Binary.Row.flow, Binary.Row.next,
      RegAction.code, RegAction.run, instrLen]
  all_goals split <;> simp_all

/-- A finite, executable check of the register-step graph. Unsupported byte
and frame rows are boundaries, so their successors impose no obligation. -/
def filterCheck (rows : List Binary.Row) (region : BitVec 64 → Bool)
    (keep : Binary.Row → Bool) : Bool :=
  rows.all fun row => !region row.pc || !(RegAction.decode row.code).isSome ||
    (keep row && flowClosed region row)

/-- Generic certificate transport. This checks lookup preservation and graph
closure once for the finite binary table, independently of client data. -/
theorem certificate_filter {rows : List Binary.Row} {region : BitVec 64 → Bool}
    {keep : Binary.Row → Bool} (checked : filterCheck rows region keep = true)
    {cut : BitVec 64 → Bool} {start : RegState} {result : Symbolic.Result}
    (certificate : Symbolic.Certificate rows cut start result)
    (inside : region start.pc = true) :
    Symbolic.Certificate (rows.filter keep) cut start result := by
  have properties (s : RegState) (r : LocatedReg s.pc)
      (found : findReg s.pc rows = some r) (inside : region s.pc = true) :
      keep r.row = true ∧ flowClosed region r.row = true := by
    have member := found_member s.pc rows r found
    have h := List.all_eq_true.mp checked r.row member
    have decodes : (RegAction.decode r.row.code).isSome = true := by
      rw [r.decoded, RegAction.decode_code]
      rfl
    simpa only [← r.address, inside, decodes, Bool.not_true, Bool.false_or,
      Bool.and_eq_true] using h
  induction certificate with
  | stop s hit => exact .stop s hit
  | ret s r found free returned =>
    exact .ret s r (found_filter keep s.pc rows r found (properties s r found inside).1) free returned
  | step s r result found free tail ih =>
    obtain ⟨kept, closed⟩ := properties s r found inside
    exact .step s r result (found_filter keep s.pc rows r found kept) free
      (ih (run_region region s r closed))

theorem prefix_filter {rows : List Binary.Row} {region : BitVec 64 → Bool}
    {keep : Binary.Row → Bool} (checked : filterCheck rows region keep = true)
    {cut : BitVec 64 → Bool} {start : RegState} {post : RegState → Prop}
    (certified : Symbolic.Prefix rows cut start post) (inside : region start.pc = true) :
    Symbolic.Prefix (rows.filter keep) cut start post := by
  obtain ⟨result, certificate, done⟩ := certified
  exact ⟨result, certificate_filter checked certificate inside, done⟩

noncomputable def bodyKeep (row : Binary.Row) : Bool :=
  !((Binary.strlen_000 :: (Binary.strlen.rows.drop 1).take 3 ++
    (Binary.strlen.rows.drop 12).take 4).any fun frame => frame.pc == row.pc)

noncomputable def bodyRows : List Binary.Row := Binary.strlen.rows.filter bodyKeep

noncomputable def bodyRegion (pc : BitVec 64) : Bool :=
  Binary.memberPc bodyRows pc || pc == 0x80000ec2#64

set_option maxHeartbeats 800000 in
theorem body_filter_checked : filterCheck Binary.strlen.rows bodyRegion bodyKeep = true := by
  binary_rfl

theorem bodyRows_eq : bodyRows = Memory.bodyRows Binary.strlen.rows
    (Binary.strlen_000 :: (Binary.strlen.rows.drop 1).take 3 ++
      (Binary.strlen.rows.drop 12).take 4) := rfl

theorem entry_body_checked (k : KCtx) (base : BitVec 64)
    (anchor : k.regs 10#5 = base) (byte : BitVec 8) (nonzero : byte ≠ 0#8) :
    Symbolic.Prefix bodyRows scanCut (readResult firstByte k byte)
      (fun result => result.pc = 0x80000eb8#64 ∧ Holds inferred base 1 result.ctx) := by
  exact prefix_filter body_filter_checked (entry_checked k base anchor byte nonzero) (by binary_rfl)

theorem step_body_checked (k : KCtx) (base : BitVec 64) (j : Nat)
    (invariant : Holds inferred base j k) (byte : BitVec 8) (nonzero : byte ≠ 0#8) :
    Symbolic.Prefix bodyRows scanCut (readResult scanByte k byte)
      (fun result => result.pc = 0x80000eb8#64 ∧ Holds inferred base (j+1) result.ctx) := by
  exact prefix_filter body_filter_checked (step_checked k base j invariant byte nonzero) (by binary_rfl)

open Lean in
run_cmd do
  for decl in #[``certificate_filter, ``entry_body_checked, ``step_body_checked] do
    let axioms ← collectAxioms decl
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Affine row transport introduced axioms: {axioms}"

end Xv6.WholeFunction.Affine
