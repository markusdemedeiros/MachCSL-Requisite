import Experiments.SolverSurvey.BlockNormalize

namespace Experiments.SolverSurvey.Block
open Fixture
open Xv6 Xv6.WholeFunction.Copyin MachCSL LeanRV64D
set_option smtSlice.trace true

theorem sext_small_bv (x : BitVec 64) (small : x.ult 2147483648#64 = true) :
    (x.extractLsb' 0 32).signExtend 64 = x := by
  solver_bv

theorem sext_small (x : BitVec 64) (small : x.toNat < 2 ^ 31) :
    (x.extractLsb' 0 32).signExtend 64 = x := by
  apply sext_small_bv
  simpa only [BitVec.ult, BitVec.reduceToNat, decide_eq_true_eq] using small

macro "block_arithmetic" : tactic =>
  `(tactic| (try simp only [BitVec.ult, decide_eq_true_eq,
    decide_eq_false_iff_not] at *) <;> bv_smt)

/-- Exact original natural-indexed page postcondition, on the actual block
result. No previous page-values, chunk-selection, offset, or sext lemmas
are used: the only reusable lemma is the solver-certified word conversion. -/
theorem page_chunk_values_vc (i : Inputs) (d : Nat) (k : KCtx) (w : BitVec 64)
    (regs : LoopRegs i d k.regs)
    (page : k.regs 19#5 = BitVec.ofNat 64 ((i.src.toNat + d) / 4096 * 4096))
    (pageBound : (i.src.toNat + d) / 4096 * 4096 < 2 ^ 38)
    (physical : k.regs 10#5 = pte2pa w) (more : d < i.old.length)
    (len64 : i.old.length < 2 ^ 64) :
    (pageResult k).ctx.regs 9#5 = BitVec.ofNat 64 (chunkSize i.src.toNat d i.old.length) ∧
    (pageResult k).ctx.regs 10#5 = i.dst + BitVec.ofNat 64 d ∧
    (pageResult k).ctx.regs 11#5 = pte2pa w + BitVec.ofNat 64 ((i.src.toNat + d) % 4096) ∧
    (pageResult k).ctx.regs 12#5 = BitVec.ofNat 64 (chunkSize i.src.toNat d i.old.length) := by
  cases regs
  block_normalize
  split <;> block_normalize
  all_goals repeat' constructor
  all_goals try split
  all_goals first
    | rw [sext_small _ (by block_arithmetic)] <;> block_arithmetic
    | block_arithmetic

#solver_stats

end Experiments.SolverSurvey.Block
