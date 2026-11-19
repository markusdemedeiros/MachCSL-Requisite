import Experiments.WholeFunction.CopyoutJoins
import Experiments.WholeFunction.CopyoutExit

/-! The actual setup block initializes the semantic loop invariant. Fresh
stack padding is universally quantified; page-table validity comes from the
public resource, not an extra assumption in COPYOUT. -/
namespace Xv6.WholeFunction.Copyout
open MachCSL LeanRV64D
open Experiments.WholeFunction

theorem initial_common (i : Inputs) (cells : List Stack.Cell)
    (frame : CopyoutFrame.Frame i.entry cells) (wf : uptWf i.table) :
    Common i (initialBody i cells) := by
  refine ⟨.start, wf, frame, ?_, ?_, ?_⟩
  · simp [initialBody, CopyoutFrame.initialMachine, KCtx.setReg_regs,
      KCtx.push_regs, RegMap.set_apply, KCtx.sp]
  · rfl
  · intro _; exact ⟨rfl, rfl⟩

def setupState (s : State) : State := atResult s (setupResult s.machine.ctx)

theorem setup_common (i : Inputs) (cells : List Stack.Cell)
    (frame : CopyoutFrame.Frame i.entry cells) (wf : uptWf i.table) :
    Common i (setupState (initialBody i cells)) :=
  common_result (initial_common i cells frame wf) _ (setup_context _) (setup_sp _)

theorem setup_header (i : Inputs) (valid : Valid i) (positive : 0 < i.bytes.length)
    (cells : List Stack.Cell) (frame : CopyoutFrame.Frame i.entry cells) (wf : uptWf i.table) :
    Header i (setupState (initialBody i cells)) := by
  refine ⟨setup_common i cells frame wf, rfl, ?_, ?_, ?_⟩
  · exact positive
  · simpa only [cursor, setupState, atResult, initialBody, Copy.initial,
      List.length_nil, Nat.add_zero] using i.dst.isLt
  · have regs := setup_values (initialBody i cells).machine.ctx
    dsimp only [initialBody, CopyoutFrame.initialMachine] at regs
    simp only [KCtx.setReg_regs, KCtx.push_regs, RegMap.set_apply,
      BitVec.reduceEq, ↓reduceIte] at regs
    rcases regs with ⟨dst, remaining, src, root, pagesize, maxva, mask, size⟩
    change LoopRegs i 0 (setupCtx ((i.entry.push 14).setReg 8#5 i.entry.sp)).regs
    refine ⟨?_, ?_, ?_, ?_, pagesize, maxva, mask, size⟩
    · simpa [Inputs.dst] using dst
    · simpa only [Nat.sub_zero, valid.length] using remaining
    · simpa [Inputs.src] using src
    · exact root.trans valid.root

theorem initial_good (i : Inputs) (valid : Valid i) (positive : 0 < i.bytes.length)
    (cells : List Stack.Cell) (frame : CopyoutFrame.Frame i.entry cells) (wf : uptWf i.table) :
    Good i (initialBody i cells) := by
  apply Residual.prepend (v := residualView) (s := initialBody i cells)
    (t := setupState (initialBody i cells)) rfl
    (setup_certificate (initialBody i cells).machine.ctx)
  exact good_of_header (setup_header i valid positive cells frame wf)

end Xv6.WholeFunction.Copyout
