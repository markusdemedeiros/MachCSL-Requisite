import Experiments.WholeFunction.KernelGraph

/-! A complete cyclic region from the actual xv6 binary: panic's terminal
self-loop. This checks the compiler's unbounded guarded composition, rather
than a bounded interpreter or a per-iteration spatial adapter. -/
namespace Xv6.WholeFunction
open Iris Iris.BI Iris.ProgramLogic MachCSL LeanRV64D
noncomputable section
attribute [local semireducible] LeanRV64D.Functions.hartSupports LeanRV64D.Functions.currentlyEnabled

private def loopPc : BitVec 64 := KA.«panic» + 0x26#64
private def loopRow : Binary.Row := Binary.rowAt loopPc (by binary_rfl) (by binary_rfl)

/-- Complete contiguous binary region with a checked direct self-edge. -/
def panicRegion : Binary.Function :=
  ⟨loopPc, loopPc + 2#64, [loopRow], by binary_rfl, by binary_rfl⟩

private def located : LocatedReg loopPc := ⟨loopRow, .jump 0#21, rfl, by rfl⟩
private theorem loop_lookup : findReg loopPc panicRegion.rows = some located := by rfl

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
variable [CurCtx] [KernelGeom] [KernelImage GF]

/-- The whole divergent machine region is safe, at arbitrary interrupt state,
with no termination/fuel premise and no per-iteration spatial proof. -/
theorem panic_loop_compiled (cpu : CPU) (k : KCtx) :
    regOwn (GF := GF) cpu ⟨k, loopPc⟩ ⊢ wpLoop cpu := by
  let initial : RegState := ⟨k, loopPc⟩
  let inv (s : RegState) := s = initial
  have closed : ∀ s s', inv s → RegEdge panicRegion.rows s s' → inv s' := by
    intro s s' hi he
    dsimp only [inv] at hi
    subst s
    obtain ⟨r, hr, c, rfl⟩ := he
    have hr' : r = located := by
      simpa only [initial, loop_lookup, Option.some.injEq] using hr.symm
    subst r
    simp [inv, located, RegAction.run, initial]
  iintro Hstate
  iapply wp_reg_graph panicRegion.rows inv closed cpu initial rfl $$ [$Hstate]
  iapply wpNext_intro_pin
  iintro %cpu' %_ %s' %hi %hc _
  have hs : s' = initial := hi
  subst s'
  have hf : False := by simpa [RegCut, initial, loop_lookup] using hc
  exact hf.elim

end
end Xv6.WholeFunction

#print axioms Xv6.WholeFunction.panic_loop_compiled
