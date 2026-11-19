import Experiments.WholeFunction.StrlenFacts
import Experiments.WholeFunction.StrlenFrame
import Experiments.WholeFunction.MemoryFrame
import Experiments.WholeFunction.FrameEffects
import Experiments.WholeFunction.AffineClient

/-! A pure invariant for the actual STRLEN body. Only byte accesses and return are annotated. A generated affine invariant justifies the exact accessed byte,
including the zero terminator; the entire fractional buffer is preserved. -/
namespace Xv6.WholeFunction.Strlen
open Iris Iris.BI Iris.ProgramLogic MachCSL LeanRV64D

/-- Remove only the separately compiled frame rows. The empty-string suffix
following the epilogue remains part of every body analysis. -/
noncomputable def bodyRows : List Binary.Row :=
  Memory.bodyRows Binary.strlen.rows
    (Binary.strlen_000 :: StrlenFrame.saveRows ++ StrlenFrame.returnRows)

set_option maxHeartbeats 0 in
noncomputable def effects : RowEffects Memory.decodeWrites bodyRows := by derive_effects

noncomputable abbrev writes : RegMask := effects.writes

theorem writes_checked : deriveRowWrites Memory.decodeWrites bodyRows = some writes := effects.checked

theorem writes_accepted : FrameEffects.Accepts FrameContract.layout writes := by decide

theorem first_member : Binary.strlen_008 ∈ bodyRows := by
  unfold bodyRows Memory.bodyRows
  apply List.mem_filter.mpr
  exact ⟨by simp [Binary.strlen], by decide⟩

theorem scan_member : Binary.strlen_016 ∈ bodyRows := by
  unfold bodyRows Memory.bodyRows
  apply List.mem_filter.mpr
  exact ⟨by simp [Binary.strlen], by decide⟩

structure Inputs where
  entry : KCtx
  bytes : List (BitVec 8)
  fraction : DFrac
  length : Nat

def Inputs.base (i : Inputs) : BitVec 64 := i.entry.regs 10#5

def Inputs.buffer (i : Inputs) : Memory.Buffer := ⟨i.base, i.fraction, i.bytes⟩

structure Valid (i : Inputs) : Prop where
  terminated : cstrAt i.bytes i.length
  bound : i.length < 2 ^ 31

def initial (i : Inputs) : Memory.State := ⟨StrlenFrame.initialMachine i.entry, [i.buffer]⟩

structure Common (i : Inputs) (s : Memory.State) : Prop where
  buffers : s.buffers = [i.buffer]

structure First (i : Inputs) (s : Memory.State) : Prop extends Common i s where
  pc : s.machine.pc = 0x80000eaa#64
  arg : s.machine.ctx.regs 10#5 = i.base

structure Scan (i : Inputs) (s : Memory.State) (j : Nat) : Prop extends Common i s where
  pc : s.machine.pc = 0x80000eb8#64
  invariant : Affine.Holds Affine.inferred i.base j s.machine.ctx
  positive : 1 ≤ j
  bound : j ≤ i.length

structure Done (i : Inputs) (s : Memory.State) : Prop extends Common i s where
  pc : s.machine.pc = 0x80000ec2#64
  result : s.machine.ctx.regs 10#5 = BitVec.ofNat 64 i.length

inductive Endpoint (i : Inputs) : Memory.State → Prop
  | first {s} : First i s → Endpoint i s
  | scan (j) {s} : Scan i s j → Endpoint i s
  | done {s} : Done i s → Endpoint i s

theorem Endpoint.common {i : Inputs} {s : Memory.State} (h : Endpoint i s) : Common i s := by
  cases h with
  | first h => exact h.toCommon
  | scan j h => exact h.toCommon
  | done h => exact h.toCommon

abbrev Good (i : Inputs) := Memory.ResidualGood bodyRows (Endpoint i)

def Exit (s : Memory.State) : Prop := s.machine.pc = 0x80000ec2#64

set_option maxHeartbeats 0 in
theorem endpoint_terminal (i : Inputs) (s : Memory.State) (h : Endpoint i s) :
    findReg s.machine.pc bodyRows = none := by
  cases h with
  | first h => rw [h.pc]; binary_rfl
  | scan j h => rw [h.pc]; binary_rfl
  | done h => rw [h.pc]; binary_rfl

theorem initial_good (i : Inputs) : Good i (initial i) := by
  apply Residual.at_endpoint
  refine .first ⟨⟨rfl⟩, rfl, ?_⟩
  simp [initial, StrlenFrame.initialMachine, Inputs.base, RegMap.set_apply]

set_option maxHeartbeats 0 in
theorem good_done {i : Inputs} {s : Memory.State} (h : Good i s) (exit : Exit s) : Done i s := by
  have terminal : findReg s.machine.pc bodyRows = none := by rw [exit]; binary_rfl
  have endpoint := Residual.endpoint_of_no_decode h terminal
  cases endpoint with
  | done h => exact h
  | first h => have := h.pc; simp_all [Exit]
  | scan j h => have := h.pc; simp_all [Exit]

def atResult (s : Memory.State) (r : RegState) : Memory.State :=
  ⟨⟨r.ctx, r.pc, s.machine.cells⟩, s.buffers⟩

theorem Common.result {i : Inputs} {s : Memory.State} (h : Common i s) (r : RegState) : Common i (atResult s r) :=
  ⟨h.buffers⟩

end Xv6.WholeFunction.Strlen
