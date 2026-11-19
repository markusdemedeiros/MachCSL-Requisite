import Experiments.WholeFunction.CopyoutCallFacts
import Experiments.WholeFunction.CopyoutExit

namespace Xv6.WholeFunction.Copyout
open MachCSL

/-- Semantic endpoints are real calls or the shared stack-restore boundary. -/
theorem endpoint_notReg {i : Inputs} {s : State} (h : Endpoint i s) :
    findReg s.machine.pc Binary.copyout.rows = none := by
  cases h with
  | walk h => rw [h.pc]; binary_rfl
  | fault h => rw [h.pc]; binary_rfl
  | probe w h => rw [h.pc]; binary_rfl
  | move w h => rw [h.pc]; binary_rfl
  | done h => rw [h.pc]; binary_rfl

theorem good_ordinary {i : Inputs} {s : State} (h : Good i s) (active : ¬ BodyExit s)
    (r : LocatedMixed s.machine.pc)
    (found : findMixed 14 s.machine.pc Binary.copyout.rows = some r)
    (cpu : CPU) (t : Stack.State) (step : r.action.Next r.row.rvc cpu s.machine t) :
    Good i (s.withMachine t) := by
  rcases Residual.decode_or_endpoint h with he | ⟨r', found'⟩
  · rw [endpoint_notMixed he active] at found
    cases found
  · have mixed := Symbolic.findMixed_of_findReg 14 s.machine.pc Binary.copyout.rows r' found'
    rw [found] at mixed
    cases Option.some.inj mixed
    change t = ⟨(r'.action.run r'.row.rvc cpu s.machine.machine).ctx,
      (r'.action.run r'.row.rvc cpu s.machine.machine).pc, s.machine.cells⟩ at step
    subst t
    exact Residual.advance h (fun _ he => endpoint_notReg he) r' found' cpu rfl rfl

theorem good_call_endpoint {i : Inputs} {s : State} (h : Good i s)
    (notMixed : findMixed 14 s.machine.pc Binary.copyout.rows = none) : Endpoint i s := by
  rcases Residual.decode_or_endpoint h with he | ⟨r, found⟩
  · exact he
  · have mixed := Symbolic.findMixed_of_findReg 14 s.machine.pc Binary.copyout.rows r found
    rw [notMixed] at mixed
    cases mixed

theorem good_at_exit {i : Inputs} {s : State} (h : Good i s) (done : BodyExit s) : Exit i s := by
  have endpoint := Residual.endpoint_of_no_decode h (by change findReg s.machine.pc _ = none; rw [done]; binary_rfl)
  cases endpoint with
  | done h => exact h
  | walk h => have hh := done.symm.trans h.pc; contradiction
  | fault h => have hh := done.symm.trans h.pc; contradiction
  | probe w h => have hh := done.symm.trans h.pc; contradiction
  | move w h => have hh := done.symm.trans h.pc; contradiction

theorem good_exit_result {i : Inputs} {s : State} (h : Good i s) (done : BodyExit s) : BodyResult i s := by
  have exit := good_at_exit h done
  exact ⟨exit.pc, exit.frame, exit.context, exit.sp, exit.flags, exit.post,
    (Experiments.WholeFunction.Copy.trace_certificate (C.write_run_certificate exit.run).1).lend⟩

end Xv6.WholeFunction.Copyout
