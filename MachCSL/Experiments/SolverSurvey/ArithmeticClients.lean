import Experiments.SolverSurvey.SmtSlice
import Xv6.CopyLemmas

namespace Experiments.SmtSlice.Clients
open Xv6
set_option smtSlice.trace true

/-- The source-page remainder, directly from the machine expression. -/
theorem page_remainder (a : Nat) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 (a / 4096 * 4096) + (-BitVec.ofNat 64 a + 4096#64)
      = BitVec.ofNat 64 (4096 - a % 4096) := by
  bv_smt

/-- Address normalization does not depend on the normalizer's association. -/
theorem source_offset (A d : Nat) (h : A + d < 2 ^ 64) :
    BitVec.ofNat 64 A + BitVec.ofNat 64 d + -BitVec.ofNat 64 ((A + d) / 4096 * 4096)
      = BitVec.ofNat 64 ((A + d) % 4096) := by
  bv_smt

theorem source_offset_associated (A d : Nat) (h : A + d < 2 ^ 64) :
    BitVec.ofNat 64 A + (BitVec.ofNat 64 d + -BitVec.ofNat 64 ((A + d) / 4096 * 4096))
      = BitVec.ofNat 64 ((A + d) % 4096) := by
  bv_smt

/-- A positive count decremented by the actual all-ones immediate. -/
theorem positive_count (m : Nat) (h : 0 < m) :
    BitVec.ofNat 64 m + 18446744073709551615#64 = BitVec.ofNat 64 (m - 1) := by
  bv_smt

end Experiments.SmtSlice.Clients

open Lean in
run_cmd do
  for decl in #[``Experiments.SmtSlice.Clients.page_remainder,
      ``Experiments.SmtSlice.Clients.source_offset,
      ``Experiments.SmtSlice.Clients.source_offset_associated,
      ``Experiments.SmtSlice.Clients.positive_count] do
    let axioms ← collectAxioms decl
    unless axioms.all (#[``propext, ``Quot.sound, ``Classical.choice].contains ·) do
      throwError "Unexpected axioms: {axioms}"
