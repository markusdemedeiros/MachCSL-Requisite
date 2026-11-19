import Experiments.WholeFunction.KernelLinear
import Experiments.WholeFunction.StackValues

/-! Actual value-sensitive copyin prologue WP. All thirteen save-body rows
are selected from the binary, composed by the generic finite-row backend,
and discharged by the shared symbolic value certificate. The initial push
is included by the final theorem. This is a prologue, not full COPYIN.
-/
namespace Xv6.WholeFunction.StackValues
open Iris Iris.BI Iris.ProgramLogic MachCSL LeanRV64D

theorem rowRun_of_linear {slots : Nat} {rows : List Binary.Row} {s t : Stack.State}
    (h : Linear.RowRun slots rows s t) : RowRun slots rows s t := by
  induction h with
  | nil => exact .nil _
  | cons row a cpu hd hp hn _ ih => exact .cons row a cpu hd hp hn ih

theorem copyin_row_supported (row : Binary.Row) (mem : row ∈ copyinSaveRows)
    (a : {a : MixedAction // row.code = a.code})
    (hd : MixedAction.decode 12 row.code = some a) : supported a.val := by
  have hm : some (row.rvc, a.val) ∈ copyinSaveRows.map (fun row =>
      (MixedAction.decode 12 row.code).map (fun a => (row.rvc, a.val))) :=
    List.mem_map.mpr ⟨row, mem, by rw [hd]; rfl⟩
  rw [copyinProgram_binary] at hm
  obtain ⟨pair, hp, he⟩ := List.mem_map.mp hm
  cases Option.some.inj he
  exact copyinProgram_safe _ hp

theorem supported_next_pc (a : MixedAction) (rvc : Bool) (cpu : CPU) (s t : Stack.State)
    (hs : supported a) (hn : a.Next rvc cpu s t) : t.pc = s.pc + instrLen rvc := by
  rw [next_eq_eval a rvc cpu s t hs hn]
  cases a with
  | reg a => cases a <;> first | rfl | exact False.elim hs
  | stack a => cases a <;> first | rfl | exact False.elim hs

theorem copyin_safe [CurCtx] [KernelGeom] (base : BitVec 64) (s : Stack.State)
    (shape : Stack.Shape base 12 s) (pc : s.pc = 0x8000168c#64) :
    Linear.Safe 12 copyinSaveRows s := by
  apply Linear.safe_of_invariant 12 copyinSaveRows (Stack.Shape base 12)
    0x8000168c#64 0x800016a6#64 (by binary_rfl) _ s shape pc
  intro row mem
  have checked := List.all_eq_true.mp copyinSaveRows_checked row mem
  cases hd : MixedAction.decode 12 row.code with
  | none => simp [frameRows, hd] at checked
  | some a =>
    have safe : a.val.FrameSafe 12 := by
      rw [hd] at checked
      exact of_decide_eq_true checked
    refine ⟨a, rfl, ?_, ?_⟩
    · intro s hs _
      cases ha : a.val with
      | reg => trivial
      | stack act =>
        rw [ha] at safe
        exact act.frame_enabled base 12 s safe hs
    · intro cpu s t hs hp hn
      refine ⟨?_, ?_⟩
      · cases ha : a.val with
        | reg act =>
          rw [ha] at hn
          cases hn
          exact ⟨(act.run_sp ..).trans hs.1, hs.2⟩
        | stack act =>
          rw [ha] at safe hn
          exact act.frame_preserved base 12 row.rvc cpu s t safe hs hn
      · rw [supported_next_pc a.val row.rvc cpu s t (copyin_row_supported row mem a hd) hn, hp]
        unfold Binary.Row.next
        cases row.rvc <;> rfl

def saveResult (k : KCtx) (cells : List Stack.Cell) : Stack.State :=
  ⟨k.setReg 8#5 (k.sp + 96#64), 0x800016a6#64, savedCells k cells⟩

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
variable [CurCtx] [KernelGeom] [KernelImage GF]

/-- This returns actual ownership of all twelve correctly saved values,
not a pure trace premise or a frame-shape-only postcondition. -/
theorem wp_copyin_save_values (base : BitVec 64) (cpu : CPU) (k : KCtx)
    (cells : List Stack.Cell) (shape : Stack.Shape base 12 ⟨k, 0x8000168c#64, cells⟩) :
    mixedOwn (GF := GF) cpu ⟨k, 0x8000168c#64, cells⟩ ∗
      wpNext k.sie k.proc cpu (fun cpu' => iprop(
        mixedOwn cpu' (saveResult k cells) -∗ wpLoop cpu')) ⊢ wpLoop cpu := by
  have len : cells.length = 12 := by
    simpa [Stack.addresses] using congrArg List.length shape.2
  iintro ⟨Hstate, Hexit⟩
  iapply Linear.wp_rows 12 copyinSaveRows cpu _ (copyin_safe base _ shape rfl) $$ [$Hstate Hexit]
  iapply wpNext_mono _ _ _ _ _ $$ Hexit
  iintro %cpu' Hexit %t %hr Hstate
  have he := copyin_binary_values k cells len t (rowRun_of_linear hr)
  change t = saveResult k cells at he
  rw [he]
  iapply Hexit $$ Hstate

def frameCells (k : KCtx) : List Stack.Cell :=
  List.zipWith (fun addr reg => (addr, k.regs reg)) (Stack.addresses k.sp 12) saveRegisters

theorem savedCells_shape (k : KCtx) (cells : List Stack.Cell)
    (shape : cells.map Prod.fst = Stack.addresses k.sp 12) : savedCells k cells = frameCells k := by
  unfold savedCells frameCells
  rw [← List.zipWith_map_left (f := Prod.fst)
    (g := fun (addr : BitVec 64) (reg : BitVec 5) => (addr, k.regs reg)), shape]

theorem savedCells_push (k : KCtx) (cells : List Stack.Cell) :
    savedCells (k.push 12) cells = savedCells k cells := by
  have regs : saveRegisters.map (k.push 12).regs = saveRegisters.map k.regs := by
    simp [saveRegisters, KCtx.push_regs, RegMap.set]
  unfold savedCells
  rw [← List.zipWith_map_right (f := (k.push 12).regs)
      (g := fun (c : Stack.Cell) (v : BitVec 64) => (c.1, v)),
    ← List.zipWith_map_right (f := k.regs)
      (g := fun (c : Stack.Cell) (v : BitVec 64) => (c.1, v)), regs]

def prologueResult (k : KCtx) : Stack.State :=
  ⟨(k.push 12).setReg 8#5 k.sp, 0x800016a6#64, frameCells k⟩

/-- Complete fourteen-instruction actual copyin prologue: push, twelve SDs,
and ADDI s0. The post owns entry ra,s0,s1,s2,...,s10 at their original frame
addresses, SP=entrySP-96, and s0=entrySP, for arbitrary entry values/harts. -/
theorem wp_copyin_prologue_values (cpu : CPU) (k : KCtx) (available : 12 ≤ k.avail) :
    kernelText (GF := GF) ∗ kctx cpu k ∗ pcIs cpu 0x8000168a#64 ∗
      wpNext k.sie k.proc cpu (fun cpu' => iprop(
        mixedOwn cpu' (prologueResult k) -∗ wpLoop cpu')) ⊢ wpLoop cpu := by
  iintro ⟨#HT, HK, HPC, Hexit⟩
  have hpc : Binary.copyin_002.pc = 0x8000168a#64 := by binary_rfl
  have hrvc : Binary.copyin_002.rvc = true := by binary_rfl
  have hcode : Binary.copyin_002.code = instruction.ITYPE
      (4000#12, .Regidx 2#5, .Regidx 2#5, .ADDI) := by binary_rfl
  have code := Binary.copyin_002.instr (GF := GF)
  rw [hpc, hrvc, hcode] at code
  ihave #HI := code $$ HT
  iapply wp_s_push cpu k 0x8000168a#64 true 4000#12 12 available (by decide)
    $$ [$HI $HK $HPC Hexit]
  inext
  iapply wpNext_intro_pin
  iintro %cpu' %hpin HK HPC Hframe
  icases Stack.stack_values k.sp 12 $$ Hframe with ⟨%cells, %hshape, Hcells⟩
  have shape : Stack.Shape k.sp 12 ⟨k.push 12, 0x8000168c#64, cells⟩ :=
    ⟨KCtx.push_sp k 12, hshape⟩
  have result : saveResult (k.push 12) cells = prologueResult k := by
    unfold saveResult prologueResult
    rw [savedCells_push, savedCells_shape k cells hshape, KCtx.push_sp]
    simp only [BitVec.reduceMul, BitVec.sub_add_cancel]
  iapply wp_copyin_save_values k.sp cpu' (k.push 12) cells shape $$ [HT HK HPC Hcells Hexit]
  isplitl [HK HPC Hcells]
  · unfold mixedOwn regOwn Stack.State.machine
    simp only [instrLen, BitVec.reduceAdd]
    iframe HT HK HPC Hcells
  · rw [result]
    simp only [KCtx.push_sie, KCtx.push_proc]
    iapply wpNext_shift k.sie k.proc cpu cpu' _ hpin $$ Hexit

#print axioms wp_copyin_save_values
#print axioms wp_copyin_prologue_values

open Lean in
run_cmd do
  let rules := #[``MachCSL.wp_s_addi, ``MachCSL.wp_s_addiw, ``MachCSL.wp_s_add, ``MachCSL.wp_s_sub,
    ``MachCSL.wp_s_and, ``MachCSL.wp_s_lui, ``MachCSL.wp_s_branch,
    ``MachCSL.wp_s_j, ``MachCSL.wp_s_ret, ``MachCSL.wp_s_push, ``MachCSL.wp_s_pop,
    ``MachCSL.wp_s_ld, ``MachCSL.wp_s_sd]
  let mut baseline : Array Name := #[]
  for rule in rules do
    for ax in ← collectAxioms rule do
      if !baseline.contains ax then baseline := baseline.push ax
  for decl in #[``wp_copyin_save_values, ``wp_copyin_prologue_values] do
    let axioms ← collectAxioms decl
    let extra := axioms.filter fun ax => !baseline.contains ax
    unless extra.isEmpty do throwError "{decl}: new axioms {extra}"
    if axioms.contains ``sorryAx then throwError "{decl}: contains sorryAx"
  logInfo m!"Both actual copyin value WPs add no axioms beyond {baseline.size} production-rule axioms."

end Xv6.WholeFunction.StackValues
