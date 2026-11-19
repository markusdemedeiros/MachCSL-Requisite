import Experiments.WholeFunction.StrncpyCopy
import Experiments.WholeFunction.StrncpyPad
import Experiments.WholeFunction.MemoryCompiler

/-! Three byte-memory endpoints; every register/control instruction is selected
from the actual binary by the shared residual-prefix compiler. -/
namespace Xv6.WholeFunction.Strncpy
open Iris Iris.BI Iris.ProgramLogic MachCSL LeanRV64D Memory StrncpyFacts
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
variable [CurCtx] [KernelGeom] [KernelImage GF]

noncomputable def compile (i : Inputs) (valid : Valid i) (s : Memory.State)
    (good : Good i s) (active : ¬Exit s) : LeafPlan bodyRows (fun _ t => Good i t) s := by
  apply Classical.choice
  rcases Residual.decode_or_endpoint good with endpoint | ⟨r, found⟩
  · obtain ⟨dst, h⟩ := endpoint
    cases h.control with
    | read pc j data live regs cursor nextCount padCount =>
      have js : j < i.source.length := by have := valid.srcLength; omega
      let b := i.source[j]
      have lookup : i.source[j]? = some b := List.getElem?_eq_getElem js
      have member : Binary.strncpy_01a ∈ bodyRows := by
        apply List.mem_filter.mpr
        constructor
        · simp [Binary.strncpy]
        · binary_rfl
      refine ⟨.byte ⟨Binary.strncpy_01a, .load 0 14 11 (by decide) (by decide), ⟨1,j⟩,
        pc, (by binary_rfl), ?_, ?_⟩ member⟩
      · refine ⟨i.srcBuffer, b, ?_, lookup, ?_, trivial⟩
        · simp [h.buffers, Inputs.buffers]
        · simp [Op.address, KCtx.rget_ne, regs.1, Inputs.srcBuffer]
      · intro cpu t hn
        obtain ⟨buffer, byte, found, read, rfl⟩ := hn
        have eq : buffer = i.srcBuffer := by simpa [h.buffers, Inputs.buffers] using found.symm
        subst buffer
        rw [(show Binary.strncpy_01a.rvc = false from by binary_rfl)]
        change Good i ⟨⟨s.machine.ctx.setReg 14#5 (byte.setWidth 64), s.machine.pc + 4, s.machine.cells⟩, s.buffers⟩
        apply Residual.at_endpoint
        refine ⟨dst, ⟨h.buffers⟩, ?_⟩
        exact .write (by simp [pc]) j data live (by simpa [copyRegs, RegMap.set_apply] using regs)
          (by simp [RegMap.set_apply, cursor]) (by simp [RegMap.set_apply, nextCount])
          (by simp [RegMap.set_apply, padCount]) byte read (by simp [RegMap.set_apply])
    | write pc j data live regs cursor nextCount padCount b lookup value =>
      have jd : j < dst.length := by rw [data.length valid]; exact live
      let old := dst[j]
      have readOld : dst[j]? = some old := List.getElem?_eq_getElem jd
      have member : Binary.strncpy_01e ∈ bodyRows := by
        apply List.mem_filter.mpr
        constructor
        · simp [Binary.strncpy]
        · binary_rfl
      refine ⟨.byte ⟨Binary.strncpy_01e, .store 4095 15 14 (by decide) (by decide), ⟨0,j⟩,
        pc, (by binary_rfl), ?_, ?_⟩ member⟩
      · refine ⟨i.dstBuffer dst, old, ?_, readOld, ?_, rfl⟩
        · simp [h.buffers, Inputs.buffers]
        · simp [Op.address, KCtx.rget_ne, cursor, Inputs.dstBuffer, BitVec.ofNat_add, BitVec.add_assoc]
      · intro cpu t hn
        obtain ⟨buffer, byte, found, read, rfl⟩ := hn
        have eq : buffer = i.dstBuffer dst := by simpa [h.buffers, Inputs.buffers] using found.symm
        subst buffer
        rw [(show Binary.strncpy_01e.rvc = false from by binary_rfl)]
        change Good i ⟨⟨s.machine.ctx, s.machine.pc + 4, s.machine.cells⟩,
          s.buffers.set 0 {i.dstBuffer dst with bytes := dst.set j ((s.machine.ctx.rget cpu 14#5).extractLsb' 0 8)}⟩
        rw [KCtx.rget_ne cpu _ 14#5 (by decide) (by decide), value, byte_extract]
        apply copy_good valid (s := ⟨⟨s.machine.ctx, s.machine.pc + 4, s.machine.cells⟩,
          s.buffers.set 0 {i.dstBuffer dst with bytes := dst.set j b}⟩) (dst := dst.set j b) ⟨?_⟩
          (by simp [pc]) j b ?_ regs cursor nextCount padCount value
        · simp [h.buffers, Inputs.buffers, Inputs.dstBuffer]
        · refine ⟨live, data.nonzero, lookup, ?_⟩
          rw [data.content]
          exact copied_set i.source i.old j b (by have := valid.dstLength; omega) lookup
    | padWrite pc k j data live endValue cursor =>
      have member : Binary.strncpy_032 ∈ bodyRows := by
        apply List.mem_filter.mpr
        constructor
        · simp [Binary.strncpy]
        · binary_rfl
      refine ⟨.byte ⟨Binary.strncpy_032, .store 4095 14 0 (by decide) (by decide), ⟨0,j⟩,
        pc, (by binary_rfl), ?_, ?_⟩ member⟩
      · have hj : j < dst.length := by rw [data.length valid]; exact live
        refine ⟨i.dstBuffer dst, dst[j], ?_, List.getElem?_eq_getElem hj, ?_, rfl⟩
        · simp [h.buffers, Inputs.buffers]
        · simp [Op.address, KCtx.rget_ne, cursor, Inputs.dstBuffer]
          bv_omega
      · intro cpu t hn
        obtain ⟨buffer, byte, found, read, rfl⟩ := hn
        have eq : buffer = i.dstBuffer dst := by simpa [h.buffers, Inputs.buffers] using found.symm
        subst buffer
        rw [(show Binary.strncpy_032.rvc = false from by binary_rfl)]
        change Good i ⟨⟨s.machine.ctx, s.machine.pc + 4, s.machine.cells⟩,
          s.buffers.set 0 {i.dstBuffer dst with bytes := dst.set j ((s.machine.ctx.rget cpu 0#5).extractLsb' 0 8)}⟩
        simp only [KCtx.rget_zero, BitVec.reduceExtractLsb']
        have hk := data.lower
        have hn := data.nulBound
        have hs := valid.srcLength
        have hd := valid.dstLength
        have updated : PadData i (dst.set j 0#8) k (j + 1) := by
          refine ⟨data.nulBound, by omega, by omega, data.nonzero, data.nul, ?_⟩
          rw [data.content]
          exact padded_set i.source i.old k j (by omega) (by omega) (by omega)
        apply pad_good valid (s := ⟨⟨s.machine.ctx, s.machine.pc + 4, s.machine.cells⟩,
          s.buffers.set 0 {i.dstBuffer dst with bytes := dst.set j 0#8}⟩) (dst := dst.set j 0#8) ⟨?_⟩
          (by simp [pc]) k (j + 1) updated endValue cursor
        simp [h.buffers, Inputs.buffers, Inputs.dstBuffer]
    | done pc _ => exact (active pc).elim
  · exact ⟨residual_leaf good (endpoint_terminal i) r found⟩

end Xv6.WholeFunction.Strncpy
