import Experiments.WholeFunction.StrlenBlocks

/-! Byte actions and loop register relations are derived from actual rows.
The client supplies the C-string byte index and consumes checked replay. -/
namespace Xv6.WholeFunction.Strlen
open MachCSL LeanRV64D Memory
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0

noncomputable def compile (i : Inputs) (valid : Valid i) (s : Memory.State)
    (good : Good i s) (active : ¬ Exit s) : LeafPlan bodyRows (fun _ t => Good i t) s := by
  apply Classical.choice
  rcases Residual.decode_or_endpoint good with endpoint | ⟨r, found⟩
  · cases endpoint with
    | first h =>
      obtain ⟨b, lookup, _⟩ := cstrAt_read valid.terminated (Nat.zero_le i.length)
      refine ⟨.byte ⟨Affine.firstByte.row, Affine.firstByte.action, ⟨0,0⟩,
        h.pc, Affine.firstByte.decoded, ?_, ?_⟩ first_member⟩
      · refine ⟨i.buffer, b, ?_, lookup, ?_, trivial⟩
        · simp [h.buffers]
        · simp [Affine.firstByte, Op.address, KCtx.rget_ne, h.arg, Inputs.buffer]
      · intro cpu t hn
        obtain ⟨buffer, byte, found, read, rfl⟩ := hn
        have eq : buffer = i.buffer := by simpa [h.buffers] using found.symm
        subst buffer
        have certified := first_good valid h.toCommon h.arg byte read
        rw [← Affine.firstByte.width]
        simpa only [atResult, Affine.readResult, Affine.firstByte, Op.run,
          Stack.State.machine, h.pc] using certified
    | scan j h =>
      obtain ⟨b, lookup, _⟩ := cstrAt_read valid.terminated h.bound
      refine ⟨.byte ⟨Affine.scanByte.row, Affine.scanByte.action, ⟨0,j⟩,
        h.pc, Affine.scanByte.decoded, ?_, ?_⟩ scan_member⟩
      · exact Affine.scan_enabled s i.base i.fraction i.bytes j b h.buffers lookup h.invariant
      · intro cpu t hn
        obtain ⟨buffer, byte, found, read, rfl⟩ := hn
        have eq : buffer = i.buffer := by simpa [h.buffers] using found.symm
        subst buffer
        have certified := loop_good valid h.toCommon j h.positive h.bound h.invariant byte read
        rw [← Affine.scanByte.width]
        simpa only [atResult, Affine.readResult, Affine.scanByte, Op.run,
          Stack.State.machine, h.pc] using certified
    | done h => exact (active h.pc).elim
  · exact ⟨residual_leaf good (endpoint_terminal i) r found⟩

end Xv6.WholeFunction.Strlen
