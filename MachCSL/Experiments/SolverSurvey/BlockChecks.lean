import Experiments.SolverSurvey.BlockNormalize

namespace Experiments.SolverSurvey.Block
open Fixture
open Xv6 Xv6.WholeFunction.Copyin MachCSL LeanRV64D
set_option smtSlice.trace true

/-- The branch-selected count directly from the actual page-ready block. -/
theorem page_count (k : KCtx) (a d len : Nat)
    (src : k.regs 18#5 = BitVec.ofNat 64 (a + d))
    (page : k.regs 19#5 = BitVec.ofNat 64 ((a + d) / 4096 * 4096))
    (size : k.regs 22#5 = 4096#64)
    (remaining : k.regs 20#5 = BitVec.ofNat 64 (len - d))
    (pageBound : (a + d) / 4096 * 4096 < 2 ^ 38) (len64 : len < 2 ^ 64) :
    (pageResult k).ctx.regs 9#5 = BitVec.ofNat 64 (chunkSize a d len) := by
  block_normalize
  split <;> block_normalize <;> split <;>
    simp only [BitVec.ult, decide_eq_true_eq, decide_eq_false_iff_not] at * <;> bv_smt

/-- The post-memmove completion test, without its handwritten helper chain. -/
theorem moved_done (k : KCtx) (d n len : Nat)
    (remaining : k.regs 20#5 = BitVec.ofNat 64 (len - d))
    (count : k.regs 9#5 = BitVec.ofNat 64 n)
    (bound : d + n ≤ len) (len64 : len < 2 ^ 64) :
    moveDone k = true ↔ d + n = len := by
  block_normalize
  bv_smt

/-- Equivalent input arithmetic and disconnected register noise need no new
rewrite sequence or helper lemma. The same VC route proves the variant. -/
theorem moved_done_variant (k : KCtx) (d n len a b : Nat)
    (remaining : k.regs 20#5 = BitVec.ofNat 64 len - BitVec.ofNat 64 d)
    (count : k.regs 9#5 = BitVec.ofNat 64 n)
    (noise : (k.regs 31#5).toNat = a - b)
    (bound : n + d ≤ len) (len64 : len < 2 ^ 64) :
    moveDone k = true ↔ n + d = len := by
  block_normalize
  bv_smt

end Experiments.SolverSurvey.Block
