import Experiments.WholeFunction.CopyinInvariant
import Experiments.WholeFunction.CopyinDispatch
import Experiments.WholeFunction.CopyinExit
import Experiments.WholeFunction.CopyinPageFacts

namespace Xv6.WholeFunction.Copyin
open MachCSL LeanRV64D

theorem state_eq_of_parts (s t : State) (memory : s.memory = t.memory)
    (cells : s.machine.cells = t.machine.cells) (machine : s.machine.machine = t.machine.machine) :
    s = t := by
  cases s with
  | mk sm mem =>
    cases t with
    | mk tm mem' =>
      cases sm with
      | mk sk sp sc =>
        cases tm with
        | mk tk tp tc =>
          simp only [Stack.State.machine, RegState.mk.injEq] at machine
          obtain ⟨hk, hp⟩ := machine
          cases memory; cases cells; cases hk; cases hp
          rfl

theorem good_prefix {i : Inputs} {s t : State} {cut : BitVec 64 → Bool}
    (memory : s.memory = t.memory) (cells : s.machine.cells = t.machine.cells)
    (pre : Symbolic.Certificate Binary.copyin.rows cut s.machine.machine ⟨t.machine.machine, .cut⟩)
    (ht : Good i t) : Good i s := by
  obtain ⟨goal, finalCut, hm, hc, cert, endpoint⟩ := ht
  exact ⟨goal, finalCut, memory.trans hm, cells.trans hc, pre.append rfl cert, endpoint⟩

theorem endpoint_notMixed {i : Inputs} {s : State} (h : Endpoint i s) (active : ¬ BodyExit s) :
    findMixed 12 s.machine.pc Binary.copyin.rows = none := by
  cases h with
  | walk h => rw [h.pc]; binary_rfl
  | fault h => rw [h.pc]; binary_rfl
  | move w h => rw [h.pc]; binary_rfl
  | done h => exact False.elim (active h.pc)

theorem good_ordinary {i : Inputs} {s : State} (h : Good i s) (active : ¬ BodyExit s)
    (r : LocatedMixed s.machine.pc)
    (found : findMixed 12 s.machine.pc Binary.copyin.rows = some r)
    (cpu : CPU) (t : Stack.State) (step : r.action.Next r.row.rvc cpu s.machine t) :
    Good i (s.withMachine t) := by
  obtain ⟨goal, cut, hm, hc, cert, endpoint⟩ := h
  rcases cert.cut_cases rfl with he | ⟨r', hf, free, tail⟩
  · have hs := state_eq_of_parts s goal hm hc he
    subst goal
    rw [endpoint_notMixed endpoint active] at found
    cases found
  · have same := Symbolic.findMixed_of_findReg 12 s.machine.pc Binary.copyin.rows r' hf
    rw [found] at same
    cases Option.some.inj same
    change t = ⟨(r'.action.run r'.row.rvc cpu s.machine.machine).ctx,
      (r'.action.run r'.row.rvc cpu s.machine.machine).pc, s.machine.cells⟩ at step
    subst t
    have he := Symbolic.run_independent r'.action r'.row.rvc s.machine.machine cpu free
    refine ⟨goal, cut, hm, hc, ?_, endpoint⟩
    change Symbolic.Certificate Binary.copyin.rows cut
      (r'.action.run r'.row.rvc cpu s.machine.machine) ⟨goal.machine.machine, .cut⟩
    rw [he]
    exact tail

/-- Calls cannot occur in the middle of a register certificate: the actual
decoder lookup forces the current state to be its annotated endpoint. -/
theorem good_call_endpoint {i : Inputs} {s : State} (h : Good i s)
    (notMixed : findMixed 12 s.machine.pc Binary.copyin.rows = none) : Endpoint i s := by
  obtain ⟨goal, cut, hm, hc, cert, endpoint⟩ := h
  rcases cert.cut_cases rfl with he | ⟨r, found, _, _⟩
  · have hs := state_eq_of_parts s goal hm hc he
    exact hs.symm ▸ endpoint
  · have hm := Symbolic.findMixed_of_findReg 12 s.machine.pc Binary.copyin.rows r found
    rw [notMixed] at hm
    cases hm

theorem good_at_exit {i : Inputs} {s : State} (h : Good i s) (done : BodyExit s) : Exit i s := by
  obtain ⟨goal, cut, hm, hc, cert, endpoint⟩ := h
  rcases cert.cut_cases rfl with he | ⟨r, found, _, _⟩
  · have hs := state_eq_of_parts s goal hm hc he
    subst goal
    cases endpoint with
    | done h => exact h
    | walk h => have hh := done.symm.trans h.pc; contradiction
    | fault h => have hh := done.symm.trans h.pc; contradiction
    | move w h => have hh := done.symm.trans h.pc; contradiction
  · have none : findReg s.machine.pc Binary.copyin.rows = none := by rw [done]; binary_rfl
    dsimp only [Stack.State.machine] at found
    rw [none] at found
    cases found

theorem good_exit_result {i : Inputs} {s : State} (h : Good i s) (done : BodyExit s) :
    BodyResult i s := by
  have h := good_at_exit h done
  exact ⟨h.pc, h.cells, h.context, h.sp, h.s11, h.flags, exit_post i s h,
    (Experiments.WholeFunction.Copy.trace_read h.trace).1,
    (Experiments.WholeFunction.Copy.trace_certificate h.trace).lend⟩

theorem common_reframe {i : Inputs} {s : State} (h : Common i s) (R : RegMap) (pc : BitVec 64)
    (sp : R 2#5 = s.machine.ctx.regs 2#5) (s11 : R 27#5 = s.machine.ctx.regs 27#5) :
    Common i ⟨⟨s.machine.ctx.withRegs R, pc, s.machine.cells⟩, s.memory⟩ := by
  refine ⟨h.trace, h.bound, h.cells, ?_, s11.trans h.s11, ?_, h.flags⟩
  · exact sp.trans h.sp
  · exact context_withRegs i.entry s.machine.ctx 12 R h.context

end Xv6.WholeFunction.Copyin
