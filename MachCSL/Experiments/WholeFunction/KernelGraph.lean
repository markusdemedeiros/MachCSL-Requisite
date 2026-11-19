import Experiments.WholeFunction.KernelDecode

/-! Whole binary register/control regions. All supported rows are compiled
uniformly, all branch successors are retained, and cyclic composition is by
`wp_control_flow`. A memory, stack or call row is an explicit cutpoint; the
continuation must provide its actual contract. No missing row is skipped. -/
namespace Xv6.WholeFunction
open Iris Iris.BI Iris.ProgramLogic MachCSL LeanRV64D

structure LocatedReg (pc : BitVec 64) where
  row : Binary.Row
  action : RegAction
  address : pc = row.pc
  decoded : row.code = action.code

def findReg (pc : BitVec 64) : List Binary.Row → Option (LocatedReg pc)
  | [] => none
  | row :: rest =>
    if hp : pc = row.pc then
      (RegAction.decode row.code).map (fun a => ⟨row, a.val, hp, a.property⟩)
    else findReg pc rest

/-- This edge is generated from the full instruction partition. The target
includes the result of a branch decision; neither branch is assumed taken. -/
def RegEdge (rows : List Binary.Row) (s s' : RegState) : Prop :=
  ∃ r, findReg s.pc rows = some r ∧ ∃ cpu, s' = r.action.run r.row.rvc cpu s

def RegCut (rows : List Binary.Row) (s : RegState) : Prop :=
  findReg s.pc rows = none

theorem RegAction.run_sie (a : RegAction) (rvc : Bool) (cpu : CPU) (s : RegState) :
    (a.run rvc cpu s).ctx.sie = s.ctx.sie := by cases a <;> rfl

theorem RegAction.run_proc (a : RegAction) (rvc : Bool) (cpu : CPU) (s : RegState) :
    (a.run rvc cpu s).ctx.proc = s.ctx.proc := by cases a <;> rfl

/-- Every supported register/control action preserves the stack pointer;
SP writes are delegated to the owned-stack backend. -/
theorem RegAction.run_sp (a : RegAction) (rvc : Bool) (cpu : CPU) (s : RegState) :
    (a.run rvc cpu s).ctx.sp = s.ctx.sp := by
  cases a with
  | addi imm rd rs valid => exact KCtx.setReg_sp _ _ _ valid.2.1
  | addiw imm rd rs valid => exact KCtx.setReg_sp _ _ _ valid.2.1
  | andi imm rd rs valid => exact KCtx.setReg_sp _ _ _ valid.2.1
  | srli shamt rd rs valid => exact KCtx.setReg_sp _ _ _ valid.2.1
  | add rd rs rt valid => exact KCtx.setReg_sp _ _ _ valid.2.1
  | sub rd rs rt valid => exact KCtx.setReg_sp _ _ _ valid.2.1
  | subw rd rs rt valid => exact KCtx.setReg_sp _ _ _ valid.2.1
  | addw rd rs rt valid => exact KCtx.setReg_sp _ _ _ valid.2.1
  | and rd rs rt valid => exact KCtx.setReg_sp _ _ _ valid.2.1
  | lui imm rd valid => exact KCtx.setReg_sp _ _ _ valid.2.1
  | branch => rfl
  | jump => rfl
  | ret => rfl

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
variable [CurCtx] [KernelGeom] [KernelImage GF]

/-- Backend selection needs only a successful generated lookup, not a WP
certificate supplied separately for each program counter. -/
theorem reg_graph_transfer (rows : List Binary.Row) (s : RegState)
    (sie : Bool) (proc : BitVec 64) (hsie : s.ctx.sie = sie) (hproc : s.ctx.proc = proc)
    (hcut : ¬ RegCut rows s) :
    Transfer (regOwn (GF := GF)) sie proc (RegEdge rows) s := by
  unfold RegCut at hcut
  cases hfind : findReg s.pc rows with
  | none => exact False.elim (hcut hfind)
  | some r =>
    apply r.action.transfer r.row s r.address r.decoded sie proc hsie hproc
    intro cpu
    exact ⟨r, hfind, cpu, rfl⟩

/-- Compile the entire supported region of an actual function. Pure invariant
preservation is the only function-specific certificate. In particular, the
compiler never asks for a hand-written spatial proof for each loop body. -/
theorem wp_reg_graph (rows : List Binary.Row) (inv : RegState → Prop)
    (preserved : ∀ s s', inv s → RegEdge rows s s' → inv s')
    (cpu : CPU) (s : RegState) (entry : inv s) :
    regOwn (GF := GF) cpu s ∗ wpNext s.ctx.sie s.ctx.proc cpu (fun cpu' => iprop(
      ∀ s', ⌜inv s'⌝ -∗ ⌜RegCut rows s'⌝ -∗ regOwn cpu' s' -∗ wpLoop cpu'))
      ⊢ wpLoop cpu := by
  let good (s' : RegState) := s'.ctx.sie = s.ctx.sie ∧ s'.ctx.proc = s.ctx.proc ∧ inv s'
  have closed : Closed good (RegCut rows) (RegEdge rows) := by
    constructor
    intro a b ha _ he
    obtain ⟨r, _, c, rfl⟩ := he
    exact ⟨(RegAction.run_sie ..).trans ha.1,
      (RegAction.run_proc ..).trans ha.2.1,
      preserved a _ ha.2.2 ⟨r, by assumption, c, rfl⟩⟩
  iintro ⟨Hstate, Hexit⟩
  iapply wp_control_flow (regOwn (GF := GF)) s.ctx.sie s.ctx.proc closed
    (fun a ha hc => reg_graph_transfer rows a _ _ ha.1 ha.2.1 hc)
    cpu s (show good s from ⟨rfl, rfl, entry⟩) $$ [$Hstate Hexit]
  iapply wpNext_intro_pin
  iintro %cpu' %hp %s' %hg %hc Hstate
  ihave Hexit := wpNext_at _ _ _ cpu' _ hp $$ Hexit
  iapply Hexit $$ %s' %hg.2.2 %hc Hstate

end Xv6.WholeFunction
