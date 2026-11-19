import Experiments.SolverSurvey.BlockNormalize

namespace Experiments.SolverSurvey.Block
open Fixture
open Xv6 Xv6.WholeFunction.Copyin MachCSL LeanRV64D

/-- Semantic machine-level postcondition for the entire page-ready prefix:
the ABI arguments and selected chunk, rather than individual instructions. -/
def PageABI (before after : KCtx) : Prop :=
  let room := 4096#64 - (before.regs 18#5 &&& 4095#64)
  let count := if (before.regs 20#5).ult room then before.regs 20#5 else room
  after.regs 9#5 = count ∧
  after.regs 10#5 = before.regs 21#5 ∧
  after.regs 11#5 = before.regs 10#5 + (before.regs 18#5 &&& 4095#64) ∧
  after.regs 12#5 = count

theorem page_machine (k : KCtx)
    (page : k.regs 19#5 = k.regs 18#5 &&& 0xFFFFFFFFFFFFF000#64)
    (size : k.regs 22#5 = 4096#64) : PageABI k (pageResult k).ctx := by
  unfold PageABI
  block_normalize
  split <;> block_normalize <;> solver_bv

#solver_stats

end Experiments.SolverSurvey.Block
