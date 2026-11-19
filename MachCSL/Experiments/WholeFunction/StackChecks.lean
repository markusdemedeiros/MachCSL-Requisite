import Experiments.WholeFunction.StackShape
import Experiments.WholeFunction.KernelStackGraph
import Experiments.WholeFunction.BinaryCopy

/-! Actual copyin save-region integration. This checks spatial execution of
all twelve saves and the frame-pointer instruction, with symbolic values and
arbitrary interrupt state. Its invariant retains frame shape, NOT a relation
between saved values and entry registers; it cannot replace `frameCi` yet.
-/
namespace Xv6.WholeFunction
open Iris Iris.BI Iris.ProgramLogic MachCSL

def MixedAction.FrameSafe (n : Nat) : MixedAction → Prop
  | .reg _ => True
  | .stack a => a.FrameSafe n

instance (n : Nat) (a : MixedAction) : Decidable (a.FrameSafe n) := by
  cases a <;> unfold MixedAction.FrameSafe <;> infer_instance

def frameRows (n : Nat) (rows : List Binary.Row) : Bool := rows.all fun row =>
  match MixedAction.decode n row.code with
  | none => false
  | some a => decide (a.val.FrameSafe n)

theorem frameRows_lookup (n : Nat) (rows : List Binary.Row) (pc : BitVec 64)
    (checked : frameRows n rows = true) (r : LocatedMixed pc)
    (found : findMixed n pc rows = some r) : r.action.FrameSafe n := by
  obtain ⟨mem, decoded⟩ := findMixed_sound n pc rows r found
  have h := List.all_eq_true.mp checked r.row mem
  rw [decoded] at h
  exact of_decide_eq_true h

theorem frame_ready (n : Nat) (rows : List Binary.Row) (checked : frameRows n rows = true)
    (base : BitVec 64) (s : Stack.State) (shape : Stack.Shape base n s) :
    MixedReady n rows s := by
  intro r found
  have safe := frameRows_lookup n rows s.pc checked r found
  cases ha : r.action with
  | reg a => trivial
  | stack a =>
    rw [ha] at safe
    exact a.frame_enabled base n s safe shape

theorem frame_preserved (n : Nat) (rows : List Binary.Row) (checked : frameRows n rows = true)
    (base : BitVec 64) (s t : Stack.State) (shape : Stack.Shape base n s)
    (edge : MixedEdge n rows s t) : Stack.Shape base n t := by
  obtain ⟨r, found, cpu, step⟩ := edge
  have safe := frameRows_lookup n rows s.pc checked r found
  cases ha : r.action with
  | reg a =>
    rw [ha] at step
    cases step
    exact ⟨(a.run_sp ..).trans shape.1, shape.2⟩
  | stack a =>
    rw [ha] at step safe
    exact a.frame_preserved base n r.row.rvc cpu s t safe shape step

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
variable [CurCtx] [KernelGeom] [KernelImage GF]

theorem wp_frame_rows (n : Nat) (rows : List Binary.Row) (checked : frameRows n rows = true)
    (base : BitVec 64) (cpu : CPU) (s : Stack.State) (shape : Stack.Shape base n s) :
    mixedOwn (GF := GF) cpu s ∗ wpNext s.ctx.sie s.ctx.proc cpu (fun cpu' => iprop(
      ∀ t, ⌜Stack.Shape base n t⌝ -∗ ⌜MixedCut n rows t⌝ -∗ mixedOwn cpu' t -∗ wpLoop cpu'))
      ⊢ wpLoop cpu :=
  wp_mixed_graph n rows (Stack.Shape base n)
    (frame_ready n rows checked base) (frame_preserved n rows checked base) cpu s shape

noncomputable def copyinSaveRows : List Binary.Row := Binary.copyin.rows.drop 2 |>.take 13

set_option maxHeartbeats 0 in
theorem copyinSaveRows_checked : frameRows 12 copyinSaveRows = true := by
  binary_rfl

set_option maxHeartbeats 0 in
example : copyinSaveRows.length = 13 := by binary_rfl

/-- Actual entry of the twelve-save body. This theorem preserves every owned
word through the decoded operations. The return continuation deliberately
requires only the proven shape/cut facts, not an unproved ABI value relation.
-/
theorem wp_copyin_save_region (base : BitVec 64) (cpu : CPU) (k : KCtx)
    (cells : List Stack.Cell) (shape : Stack.Shape base 12 ⟨k, 0x8000168c#64, cells⟩) :
    mixedOwn (GF := GF) cpu ⟨k, 0x8000168c#64, cells⟩ ∗
      wpNext k.sie k.proc cpu (fun cpu' => iprop(
        ∀ t, ⌜Stack.Shape base 12 t⌝ -∗ ⌜MixedCut 12 copyinSaveRows t⌝ -∗
          mixedOwn cpu' t -∗ wpLoop cpu')) ⊢ wpLoop cpu :=
  wp_frame_rows 12 copyinSaveRows copyinSaveRows_checked base cpu _ shape

/-- Include the actual stack-allocation instruction. This checks the complete
fourteen-instruction prologue, but still exposes only shape at its boundary.
The full saved-register value certificate is a separate pure obligation.
-/
theorem wp_copyin_prologue_region (cpu : CPU) (k : KCtx) (available : 12 ≤ k.avail) :
    kernelText (GF := GF) ∗ kctx cpu k ∗ pcIs cpu 0x8000168a#64 ∗
      wpNext k.sie k.proc cpu (fun cpu' => iprop(
        ∀ t, ⌜Stack.Shape k.sp 12 t⌝ -∗ ⌜MixedCut 12 copyinSaveRows t⌝ -∗
          mixedOwn cpu' t -∗ wpLoop cpu')) ⊢ wpLoop cpu := by
  iintro ⟨#HT, HK, HPC, Hexit⟩
  have hpc : Binary.copyin_002.pc = 0x8000168a#64 := by binary_rfl
  have hrvc : Binary.copyin_002.rvc = true := by binary_rfl
  have hcode : Binary.copyin_002.code = LeanRV64D.instruction.ITYPE
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
  iapply wp_copyin_save_region k.sp cpu' (k.push 12) cells shape
    $$ [HT HK HPC Hcells Hexit]
  isplitl [HK HPC Hcells]
  · unfold mixedOwn regOwn Stack.State.machine
    simp only [instrLen, BitVec.reduceAdd]
    iframe HT HK HPC Hcells
  · simp only [KCtx.push_sie, KCtx.push_proc]
    iapply wpNext_shift k.sie k.proc cpu cpu' _ hpin $$ Hexit

-- A shifted slot annotation must not validate the binary save layout.
set_option maxHeartbeats 0 in
example : frameRows 11 copyinSaveRows = false := by binary_rfl

#print axioms wp_copyin_save_region
#print axioms wp_copyin_prologue_region

end Xv6.WholeFunction
