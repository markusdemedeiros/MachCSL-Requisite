import Experiments.WholeFunction.MemoryCompiler
import Experiments.WholeFunction.Residual

/-! A shared pure frontend for memory clients: semantic endpoints separated
by certified register prefixes. Buffer/stack ownership is unchanged across a
prefix, so every ordinary row uses one generic plan constructor. -/
namespace Xv6.WholeFunction.Memory
open MachCSL

def residualView : Residual.View State (List Buffer × List Stack.Cell) where
  machine := fun s => s.machine.machine
  resources := fun s => (s.buffers, s.machine.cells)
  ext := by
    rintro ⟨⟨sk, sp, sc⟩, sb⟩ ⟨⟨tk, tp, tc⟩, tb⟩ data machine
    simp only [Prod.mk.injEq] at data
    simp only [Stack.State.machine, RegState.mk.injEq] at machine
    obtain ⟨rfl, rfl⟩ := data
    obtain ⟨rfl, rfl⟩ := machine
    rfl

abbrev ResidualGood (rows : List Binary.Row) (endpoint : State → Prop) :=
  Residual.Good residualView rows endpoint

theorem residual_reg {rows : List Binary.Row} {endpoint : State → Prop} {s : State}
    (h : ResidualGood rows endpoint s)
    (terminal : ∀ t, endpoint t → findReg t.machine.pc rows = none)
    (r : LocatedReg s.machine.pc) (found : findReg s.machine.pc rows = some r) (cpu : CPU) :
    ResidualGood rows endpoint (regRun r.action r.row.rvc cpu s) :=
  Residual.advance h terminal r found cpu rfl rfl

variable {hlc : Iris.HasLC} {GF : Iris.BundledGFunctors} [MachGS hlc GF]
variable [CurCtx] [KernelGeom] [KernelImage GF]

/-- All ordinary program instructions are selected from the checked table;
clients author only endpoint invariants and memory/scalar semantic joins. -/
def residual_regPlan {rows : List Binary.Row} {endpoint : State → Prop} {s : State}
    (h : ResidualGood rows endpoint s)
    (terminal : ∀ t, endpoint t → findReg t.machine.pc rows = none)
    (r : LocatedReg s.machine.pc) (found : findReg s.machine.pc rows = some r) :
    Plan (GF := GF) (fun _ t => ResidualGood rows endpoint t) s :=
  regPlan r.row r.action s _ r.address r.decoded (residual_reg h terminal r found)

end Xv6.WholeFunction.Memory
