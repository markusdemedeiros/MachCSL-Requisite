import Experiments.WholeFunction.KernelGraph
import Experiments.WholeFunction.BinaryCopy
import Experiments.WholeFunction.KernelSymbolic
import Experiments.WholeFunction.StrlenBinary
import Experiments.WholeFunction.StrncpyBinary

/-! Actual-binary checks for the uniform register/control compiler. The full
copyin table is supplied unchanged; its stack prologue, loads and calls remain
explicit spatial boundaries. This is not a replacement for COPYIN. -/
namespace Xv6.WholeFunction
open Iris Iris.BI Iris.ProgramLogic MachCSL LeanRV64D

set_option maxHeartbeats 0
noncomputable section
attribute [local semireducible] LeanRV64D.Functions.hartSupports LeanRV64D.Functions.currentlyEnabled

/-- The expected decoded branch is a test oracle; production compilation uses
`RegAction.decode`, not this constructor. -/
private def entryRow : LocatedReg 0x80001688#64 :=
  ⟨Binary.copyin_000, .branch 152#13 14#5 0#5 (by decide) .BEQ, rfl, by rfl⟩
private def zeroRow : LocatedReg 0x80001720#64 :=
  ⟨Binary.copyin_098, .addi 0#12 10#5 0#5 (by decide), rfl, by rfl⟩
private def returnRow : LocatedReg 0x80001722#64 :=
  ⟨Binary.copyin_09a, .ret 1#5, rfl, by rfl⟩

private theorem entry_lookup : findReg 0x80001688#64 Binary.copyin.rows = some entryRow := by rfl
private theorem zero_lookup : findReg 0x80001720#64 Binary.copyin.rows = some zeroRow := by rfl
private theorem return_lookup : findReg 0x80001722#64 Binary.copyin.rows = some returnRow := by rfl

/-- Fail closed: the unsupported stack allocation is a cutpoint, rather than
an ordinary register update that would lose stack ownership. -/
example : findReg 0x8000168a#64 Binary.copyin.rows = none := by rfl
/-- Calls are cutpoints until a callee contract is registered. -/
example : RegAction.decode (instruction.JAL (4#21, .Regidx 1#5)) = none := by rfl
/-- No instruction outside the function's checked partition is synthesized. -/
example : findReg 0#64 Binary.copyin.rows = none := by rfl
/-- Mutating an immediate changes the symbolic result and fails correspondence. -/
example : Binary.copyin_098.code ≠ (RegAction.addi 1#12 10#5 0#5 (by decide)).code := by intro h; cases h

/-- The formerly separate scalar endpoints are ordinary decoded rows. -/
example : (RegAction.decode Binary.strlen_01c.code).isSome = true ∧
    (RegAction.decode Binary.strncpy_00e.code).isSome = true ∧
    (RegAction.decode Binary.strncpy_028.code).isSome = true ∧
    (RegAction.decode Binary.strncpy_02c.code).isSome = true ∧
    (RegAction.decode Binary.strncpy_036.code).isSome = true ∧
    (RegAction.decode Binary.strncpy_03a.code).isSome = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> binary_rfl

/-- Word arithmetic still cannot write x0, sp, or tp through this backend. -/
example : RegAction.decode (.RTYPEW (.Regidx 12#5, .Regidx 13#5, .Regidx 0#5, .SUBW)) = none ∧
    RegAction.decode (.RTYPEW (.Regidx 12#5, .Regidx 13#5, .Regidx 2#5, .ADDW)) = none ∧
    RegAction.decode (.RTYPEW (.Regidx 12#5, .Regidx 13#5, .Regidx 4#5, .SUBW)) = none := by decide

/-- Generalizing the branch does not invent a rule for two zero operands. -/
example : RegAction.decode (.BTYPE (4#13, .Regidx 0#5, .Regidx 0#5, .BEQ)) = none := by decide

/-- Other word operations remain explicit unsupported boundaries. -/
example : RegAction.decode (.RTYPEW (.Regidx 12#5, .Regidx 13#5, .Regidx 10#5, .SLLW)) = none := rfl

/-- Hart-dependent reads remain excluded from fixed-state symbolic prefixes. -/
example : Symbolic.hartFree (.subw 10#5 4#5 12#5 (by decide)) = false ∧
    Symbolic.hartFree (.addw 10#5 12#5 4#5 (by decide)) = false ∧
    Symbolic.hartFree (.branch 4#13 0#5 4#5 (by decide) .BLT) = false := by decide

/-- The actual subtraction must not be silently compiled as addition. -/
example : Binary.strlen_01c.code ≠ (RegAction.addw 10#5 13#5 10#5 (by decide)).code := by
  have decoded : Binary.strlen_01c.code = (RegAction.subw 10#5 13#5 10#5 (by decide)).code := by binary_rfl
  rw [decoded]
  intro wrong
  cases wrong

private def z0 (k : KCtx) : RegState := ⟨k, 0x80001688#64⟩
private def z1 (k : KCtx) : RegState := ⟨k, 0x80001720#64⟩
private def z2 (k : KCtx) : RegState := ⟨k.setReg 10#5 0#64, 0x80001722#64⟩
private def z3 (k : KCtx) : RegState := ⟨k.setReg 10#5 0#64, jumpPc (k.regs 1#5)⟩
private def zeroInv (k : KCtx) (s : RegState) : Prop := s = z0 k ∨ s = z1 k ∨ s = z2 k ∨ s = z3 k

private theorem zero_preserved (k : KCtx) (hz : k.regs 14#5 = 0#64)
    (hout : findReg (jumpPc (k.regs 1#5)) Binary.copyin.rows = none)
    (s s' : RegState) (hi : zeroInv k s) (he : RegEdge Binary.copyin.rows s s') : zeroInv k s' := by
  obtain ⟨r, hr, c, rfl⟩ := he
  rcases hi with rfl | rfl | rfl | rfl
  · have hr' : r = entryRow := by simpa only [z0, entry_lookup, Option.some.injEq] using hr.symm
    subst r
    right; left
    simp [entryRow, RegAction.run, z0, z1, KCtx.rget_eq, hz, bcond]
  · have hr' : r = zeroRow := by simpa only [z1, zero_lookup, Option.some.injEq] using hr.symm
    subst r
    right; right; left
    simp [zeroRow, RegAction.run, z1, z2, KCtx.rget_eq,
      show Binary.copyin_098.rvc = true from rfl, instrLen]
  · have hr' : r = returnRow := by simpa only [z2, return_lookup, Option.some.injEq] using hr.symm
    subst r
    right; right; right
    simp [returnRow, RegAction.run, z2, z3, KCtx.rget_eq, KCtx.setReg, RegMap.set]
  · simp only [z3, hout] at hr
    cases hr

private theorem zero_exit (k : KCtx) (s : RegState) (hi : zeroInv k s)
    (hc : RegCut Binary.copyin.rows s) : s = z3 k := by
  rcases hi with rfl | rfl | rfl | h
  · simp only [RegCut, z0, entry_lookup] at hc; cases hc
  · simp only [RegCut, z1, zero_lookup] at hc; cases hc
  · simp only [RegCut, z2, return_lookup] at hc; cases hc
  · exact h

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
variable [CurCtx] [KernelGeom] [KernelImage GF]

/-- The complete zero-length copyin machine path, from entry branch through
return, compiled by the whole-table engine. No per-instruction spatial proof
occurs here. The test keeps the caller return outside this function's rows. -/
theorem copyin_zero_compiled (cpu : CPU) (k : KCtx) (hz : k.regs 14#5 = 0#64)
    (hout : findReg (jumpPc (k.regs 1#5)) Binary.copyin.rows = none) :
    regOwn (GF := GF) cpu (z0 k) ∗ wpNext k.sie k.proc cpu (fun cpu' => iprop(
      regOwn cpu' (z3 k) -∗ wpLoop cpu')) ⊢ wpLoop cpu := by
  iintro ⟨Hstate, Hexit⟩
  iapply wp_reg_graph Binary.copyin.rows (zeroInv k) (zero_preserved k hz hout)
    cpu (z0 k) (Or.inl rfl) $$ [$Hstate Hexit]
  iapply wpNext_intro_pin
  iintro %cpu' %hp %s' %hi %hc Hstate
  have hs := zero_exit k s' hi hc
  subst s'
  dsimp only [z0] at hp
  ihave Hexit := wpNext_at k.sie k.proc cpu cpu' _ hp $$ Hexit
  iapply Hexit $$ Hstate

end
end Xv6.WholeFunction

#print axioms Xv6.WholeFunction.copyin_zero_compiled
