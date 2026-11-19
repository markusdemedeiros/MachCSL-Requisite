import Experiments.SolverSurvey.BlockFixture
import Experiments.SolverSurvey.SmtSlice
import Experiments.SolverSurvey.SolverCache

/-! An experimental VC normalizer for semantic assertions about the actual
symbolic block outputs. This module supplies no previous block-correctness
theorems: definitions of register updates are unfolded and the resulting
arithmetic obligations are sent to independently checked solver backends. -/
namespace Experiments.SolverSurvey.Block
open Fixture
open Xv6.WholeFunction.Copyin MachCSL LeanRV64D

macro "block_normalize" : tactic =>
  `(tactic| simp_all only [pageResult, pageTail, pageSelected, pagePrefix,
    pageBranch, pageCandidate, movedCtx, moveDone, chunkSize,
    KCtx.setReg_regs, RegMap.set_apply, BitVec.reduceEq, ↓reduceIte,
    BitVec.zero_add, BitVec.add_zero, bcond, Bool.not_eq_true', Bool.not_eq_false,
    beq_iff_eq, Nat.min_def])

end Experiments.SolverSurvey.Block
