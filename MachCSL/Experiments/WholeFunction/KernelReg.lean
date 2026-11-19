import Experiments.WholeFunction.Binary
import Experiments.WholeFunction.ControlFlow

/-! A symbolic register/control backend for whole-CFG composition. The action
interpreter is proved once against production instruction rules. Binary rows
then select actions by checked equality; clients do not supply per-PC WPs.
Memory ownership and callee contracts remain separate backend extensions. -/
namespace Xv6.WholeFunction
open Iris Iris.BI Iris.ProgramLogic MachCSL LeanRV64D

inductive RegAction where
  | addi (imm : BitVec 12) (rd rs : BitVec 5) (valid : rdOk rd)
  | addiw (imm : BitVec 12) (rd rs : BitVec 5) (valid : rdOk rd)
  | andi (imm : BitVec 12) (rd rs : BitVec 5) (valid : rdOk rd)
  | srli (shamt : BitVec 6) (rd rs : BitVec 5) (valid : rdOk rd)
  | add (rd rs rt : BitVec 5) (valid : rdOk rd)
  | sub (rd rs rt : BitVec 5) (valid : rdOk rd)
  | subw (rd rs rt : BitVec 5) (valid : rdOk rd)
  | addw (rd rs rt : BitVec 5) (valid : rdOk rd)
  | and (rd rs rt : BitVec 5) (valid : rdOk rd)
  | lui (imm : BitVec 20) (rd : BitVec 5) (valid : rdOk rd)
  | branch (imm : BitVec 13) (rs rt : BitVec 5) (valid : rs ≠ 0#5 ∨ rt ≠ 0#5) (op : bop)
  | jump (imm : BitVec 21)
  | ret (rs : BitVec 5)

def RegAction.code : RegAction → instruction
  | .addi imm rd rs _ => .ITYPE (imm, .Regidx rs, .Regidx rd, .ADDI)
  | .addiw imm rd rs _ => .ADDIW (imm, .Regidx rs, .Regidx rd)
  | .andi imm rd rs _ => .ITYPE (imm, .Regidx rs, .Regidx rd, .ANDI)
  | .srli shamt rd rs _ => .SHIFTIOP (shamt, .Regidx rs, .Regidx rd, .SRLI)
  | .add rd rs rt _ => .RTYPE (.Regidx rt, .Regidx rs, .Regidx rd, .ADD)
  | .sub rd rs rt _ => .RTYPE (.Regidx rt, .Regidx rs, .Regidx rd, .SUB)
  | .subw rd rs rt _ => .RTYPEW (.Regidx rt, .Regidx rs, .Regidx rd, .SUBW)
  | .addw rd rs rt _ => .RTYPEW (.Regidx rt, .Regidx rs, .Regidx rd, .ADDW)
  | .and rd rs rt _ => .RTYPE (.Regidx rt, .Regidx rs, .Regidx rd, .AND)
  | .lui imm rd _ => .UTYPE (imm, .Regidx rd, .LUI)
  | .branch imm rs rt _ op => .BTYPE (imm, .Regidx rt, .Regidx rs, op)
  | .jump imm => .JAL (imm, .Regidx 0#5)
  | .ret rs => .JALR (0#12, .Regidx rs, .Regidx 0#5)

structure RegState where
  ctx : KCtx
  pc : BitVec 64

/-- Hart-dependent reads (notably tp) remain universally quantified in the
edge relation; migration is never replaced by a fixed-hart assumption. -/
def RegAction.run (a : RegAction) (rvc : Bool) (cpu : CPU) (s : RegState) : RegState :=
  let k := s.ctx
  let npc := s.pc + instrLen rvc
  match a with
  | .addi imm rd rs _ => ⟨k.setReg rd (k.rget cpu rs + imm.signExtend 64), npc⟩
  | .addiw imm rd rs _ => ⟨k.setReg rd ((k.rget cpu rs + imm.signExtend 64).extractLsb' 0 32 |>.signExtend 64), npc⟩
  | .andi imm rd rs _ => ⟨k.setReg rd (k.rget cpu rs &&& imm.signExtend 64), npc⟩
  | .srli shamt rd rs _ => ⟨k.setReg rd (k.rget cpu rs >>> shamt.toNat), npc⟩
  | .add rd rs rt _ => ⟨k.setReg rd (k.rget cpu rs + k.rget cpu rt), npc⟩
  | .sub rd rs rt _ => ⟨k.setReg rd (k.rget cpu rs - k.rget cpu rt), npc⟩
  | .subw rd rs rt _ => ⟨k.setReg rd ((k.rget cpu rs).extractLsb' 0 32 -
      (k.rget cpu rt).extractLsb' 0 32 |>.signExtend 64), npc⟩
  | .addw rd rs rt _ => ⟨k.setReg rd ((k.rget cpu rs).extractLsb' 0 32 +
      (k.rget cpu rt).extractLsb' 0 32 |>.signExtend 64), npc⟩
  | .and rd rs rt _ => ⟨k.setReg rd (k.rget cpu rs &&& k.rget cpu rt), npc⟩
  | .lui imm rd _ => ⟨k.setReg rd ((imm ++ 0#12).signExtend 64), npc⟩
  | .branch imm rs rt _ op => ⟨k, if bcond op (k.rget cpu rs) (k.rget cpu rt)
      then s.pc + imm.signExtend 64 else npc⟩
  | .jump imm => ⟨k, s.pc + imm.signExtend 64⟩
  | .ret rs => ⟨k, jumpPc (k.rget cpu rs)⟩

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
variable [CurCtx] [KernelGeom] [KernelImage GF]

/-- Soundness is against the existing Sail-derived kernel rules, including
interrupts/migration and all their resource invariants. -/
theorem RegAction.sound (a : RegAction) (rvc : Bool) (cpu : CPU) (s : RegState) :
    instr (GF := GF) s.pc rvc a.code ∗ kctx cpu s.ctx ∗ pcIs cpu s.pc ∗
    ▷ wpNext s.ctx.sie s.ctx.proc cpu (fun cpu' =>
      iprop(kctx cpu' (a.run rvc cpu' s).ctx -∗
        pcIs cpu' (a.run rvc cpu' s).pc -∗ wpLoop cpu')) ⊢ wpLoop cpu := by
  cases a with
  | addi imm rd rs valid => exact wp_s_addi cpu s.ctx s.pc rvc imm rd rs valid
  | addiw imm rd rs valid => exact wp_s_addiw cpu s.ctx s.pc rvc imm rd rs valid
  | andi imm rd rs valid => exact wp_s_andi cpu s.ctx s.pc rvc imm rd rs valid
  | srli shamt rd rs valid => exact wp_s_srli cpu s.ctx s.pc rvc shamt rd rs valid
  | add rd rs rt valid => exact wp_s_add cpu s.ctx s.pc rvc rd rs rt valid
  | sub rd rs rt valid => exact wp_s_sub cpu s.ctx s.pc rvc rd rs rt valid
  | subw rd rs rt valid => exact wp_s_subw cpu s.ctx s.pc rvc rd rs rt valid
  | addw rd rs rt valid => exact wp_s_addw cpu s.ctx s.pc rvc rd rs rt valid
  | and rd rs rt valid => exact wp_s_and cpu s.ctx s.pc rvc rd rs rt valid
  | lui imm rd valid => exact wp_s_lui cpu s.ctx s.pc rvc imm rd valid
  | branch imm rs rt valid op =>
    by_cases left : rs = 0#5
    · subst rs
      have right : rt ≠ 0#5 := valid.resolve_left (by simp)
      simpa only [RegAction.code, RegAction.run, KCtx.rget_zero] using
        (wp_s_branch0 cpu s.ctx s.pc rvc imm rt right op)
    · exact wp_s_branch cpu s.ctx s.pc rvc imm rs rt left op
  | jump imm => exact wp_s_j cpu s.ctx s.pc rvc imm
  | ret rs => exact wp_s_ret cpu s.ctx s.pc rvc rs

/-- Production ownership, with arbitrary client resources framed by the
whole-CFG theorem rather than copied into the machine state. -/
def regOwn (cpu : CPU) (s : RegState) : IProp GF :=
  iprop(kernelText ∗ kctx cpu s.ctx ∗ pcIs cpu s.pc)

/-- One row's generated transfer theorem. It is uniform in row address,
register values, interrupt state and the chosen global CFG relation. -/
theorem RegAction.transfer (a : RegAction) (row : Binary.Row) (s : RegState)
    (hpc : s.pc = row.pc) (hcode : row.code = a.code)
    (sie : Bool) (proc : BitVec 64) (hsie : s.ctx.sie = sie) (hproc : s.ctx.proc = proc)
    (edge : RegState → RegState → Prop)
    (hedge : ∀ cpu, edge s (a.run row.rvc cpu s)) :
    Transfer (regOwn (GF := GF)) sie proc edge s := by
  intro cpu
  unfold regOwn
  iintro ⟨⟨#HT, HK, HPC⟩, Hnext⟩
  ihave #HI := row.instr (GF := GF) $$ HT
  rw [← hpc, hcode]
  iapply a.sound row.rvc cpu s $$ [$HI $HK $HPC Hnext]
  inext
  rw [hsie, hproc]
  iapply wpNext_intro_pin
  iintro %cpu' %hpin HK HPC
  ihave Hnext := wpNext_at _ _ _ cpu' _ hpin $$ Hnext
  iapply Hnext $$ %(a.run row.rvc cpu' s) %(hedge cpu') [HT HK HPC]
  iframe HT HK HPC

/-- Lift the proved register action to an abstract state carrying arbitrary
spatial data. The data obligation is a resource entailment, never a whole WP;
register-only transfers normally satisfy it by reflexivity. -/
theorem RegAction.transfer_frame {S : Type} (machine : S → RegState)
    (payload : S → IProp GF) (a : RegAction) (row : Binary.Row) (s : S)
    (target : CPU → S)
    (hpc : (machine s).pc = row.pc) (hcode : row.code = a.code)
    (hrun : ∀ cpu, machine (target cpu) = a.run row.rvc cpu (machine s))
    (hframe : ∀ cpu, payload s ⊢ payload (target cpu))
    (sie : Bool) (proc : BitVec 64)
    (hsie : (machine s).ctx.sie = sie) (hproc : (machine s).ctx.proc = proc)
    (edge : S → S → Prop) (hedge : ∀ cpu, edge s (target cpu)) :
    Transfer (fun cpu s => iprop(regOwn cpu (machine s) ∗ payload s)) sie proc edge s := by
  intro cpu
  unfold regOwn
  iintro ⟨⟨⟨#HT, HK, HPC⟩, HF⟩, Hnext⟩
  ihave #HI := row.instr (GF := GF) $$ HT
  rw [← hpc, hcode]
  iapply a.sound row.rvc cpu (machine s) $$ [$HI $HK $HPC Hnext HF]
  inext
  rw [hsie, hproc]
  iapply wpNext_intro_pin
  iintro %cpu' %hpin HK HPC
  ihave Hnext := wpNext_at _ _ _ cpu' _ hpin $$ Hnext
  iapply Hnext $$ %(target cpu') %(hedge cpu') [HT HK HPC HF]
  dsimp only
  rw [hrun]
  iframe HT HK HPC
  iapply hframe cpu' $$ HF

end Xv6.WholeFunction
