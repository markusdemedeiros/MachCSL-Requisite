import Experiments.SolverSurvey.BlockMachine

namespace Experiments.SolverSurvey.Block
open Fixture
open Xv6 Xv6.WholeFunction.Copyin MachCSL LeanRV64D

-- These use the same successful normalizer/solver path as page_machine.
-- Changing a semantic premise must not silently preserve its certificate.
example (k : KCtx)
    (page : k.regs 19#5 = k.regs 18#5 &&& 0xFFFFFFFFFFFFF000#64)
    (size : k.regs 22#5 = 8192#64) : True := by
  fail_if_success
    have bad : PageABI k (pageResult k).ctx := by
      unfold PageABI
      block_normalize
      split <;> block_normalize <;> solver_bv
  trivial

example (k : KCtx) (size : k.regs 22#5 = 4096#64) : True := by
  fail_if_success
    have bad : PageABI k (pageResult k).ctx := by
      unfold PageABI
      block_normalize
      split <;> block_normalize <;> solver_bv
  trivial

-- Off-by-one mutation of the actual physical-source ABI argument.
example (k : KCtx)
    (page : k.regs 19#5 = k.regs 18#5 &&& 0xFFFFFFFFFFFFF000#64)
    (size : k.regs 22#5 = 4096#64) : True := by
  fail_if_success
    have bad : (pageResult k).ctx.regs 11#5 =
        k.regs 10#5 + (k.regs 18#5 &&& 4095#64) + 1#64 := by
      block_normalize
      split <;> block_normalize <;> solver_bv
  trivial

end Experiments.SolverSurvey.Block
