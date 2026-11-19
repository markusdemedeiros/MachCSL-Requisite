import Experiments.WholeFunction.MemoryActions

/-! Extensible guarded compilation: established register/stack/call plans,
and resource-aware byte instructions share one CFG importer. No unguarded
callee assumption is used as a progressing byte step. -/
namespace Xv6.WholeFunction.Memory
open Iris Iris.BI Iris.ProgramLogic MachCSL LeanRV64D

structure Located (A : Type) (code : A → instruction) (pc : BitVec 64) where
  row : Binary.Row
  action : A
  address : pc = row.pc
  decoded : row.code = code action

def findAction {A : Type} (code : A → instruction)
    (decode : (i : instruction) → Option {a : A // i = code a})
    (pc : BitVec 64) : List Binary.Row → Option (Located A code pc)
  | [] => none
  | row :: rest =>
    if h : pc = row.pc then (decode row.code).map (fun a => ⟨row, a.val, h, a.property⟩)
    else findAction code decode pc rest

abbrev findByte := findAction Op.code Op.decode

def regRun (op : RegAction) (rvc : Bool) (cpu : CPU) (s : State) : State :=
  let r := op.run rvc cpu s.machine.machine
  s.withMachine ⟨r.ctx, r.pc, s.machine.cells⟩

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
variable [CurCtx] [KernelGeom] [KernelImage GF]

theorem Op.transfer (op : Op) (row : Binary.Row) (a : Access) (s : State)
    (edge : State → State → Prop) (address : s.machine.pc = row.pc)
    (decoded : row.code = op.code) (enabled : op.Enabled a s)
    (steps : ∀ cpu t, op.Next row.rvc cpu a s t → edge s t)
    (sie : Bool) (proc : BitVec 64)
    (hsie : s.machine.ctx.sie = sie) (hproc : s.machine.ctx.proc = proc) :
    Transfer (fullOwn State.machine (payload (GF := GF))) sie proc edge s := by
  intro cpu
  unfold fullOwn mixedOwn regOwn Stack.State.machine payload
  iintro ⟨⟨⟨⟨#HT, HK, HPC⟩, Hcells⟩, Hbuffers⟩, Hnext⟩
  ihave #HI := row.instr (GF := GF) $$ HT
  rw [← address, decoded]
  iapply op.sound row.rvc a cpu s enabled $$ [$HI $HK $HPC $Hbuffers Hcells Hnext]
  inext
  rw [hsie, hproc]
  iapply wpNext_intro_pin
  iintro %cpu' %pin %t %hn HK HPC Hbuffers
  ihave Hnext := wpNext_at _ _ _ cpu' _ pin $$ Hnext
  iapply Hnext $$ %t %(steps cpu' t hn) [HT HK HPC Hcells Hbuffers]
  dsimp only [fullOwn, mixedOwn, regOwn, Stack.State.machine, payload]
  rw [op.next_cells row.rvc cpu' a s t hn]
  iframe HT HK HPC Hcells Hbuffers

/-- One uniform lift for every existing register/control action. Clients
provide only the actual row and its pure successor invariant. -/
def regFullPlan (row : Binary.Row) (action : RegAction) (s : State)
    (edge : State → State → Prop) (address : s.machine.pc = row.pc)
    (decoded : row.code = action.code)
    (steps : ∀ cpu, edge s (regRun action row.rvc cpu s)) : FullPlan State.machine (payload (GF := GF)) edge s :=
  .instruction ⟨row, .reg action, (fun _ t => s.withMachine t), address, decoded,
    True.intro, (fun _ _ _ => rfl),
    (fun _ _ _ => by unfold payload State.withMachine; iintro H; iexact H),
    (fun cpu t hn => by
      change t = ⟨(action.run row.rvc cpu s.machine.machine).ctx,
        (action.run row.rvc cpu s.machine.machine).pc, s.machine.cells⟩ at hn
      subst t
      exact steps cpu)⟩

structure BytePlan (edge : State → State → Prop) (s : State) where
  row : Binary.Row
  action : Op
  access : Access
  address : s.machine.pc = row.pc
  decoded : row.code = action.code
  enabled : action.Enabled access s
  steps : ∀ cpu t, action.Next row.rvc cpu access s t → edge s t

inductive Plan (edge : State → State → Prop) (s : State) where
  | full (plan : FullPlan State.machine (payload (GF := GF)) edge s)
  | byte (plan : BytePlan edge s)

/-- Constructor used by ordinary symbolic prefixes. -/
def regPlan (row : Binary.Row) (action : RegAction) (s : State)
    (edge : State → State → Prop) (address : s.machine.pc = row.pc)
    (decoded : row.code = action.code)
    (steps : ∀ cpu, edge s (regRun action row.rvc cpu s)) : Plan (GF := GF) edge s :=
  .full (regFullPlan row action s edge address decoded steps)

theorem Plan.transfer (edge : State → State → Prop) (s : State) (plan : Plan (GF := GF) edge s)
    (sie : Bool) (proc : BitVec 64)
    (hsie : s.machine.ctx.sie = sie) (hproc : s.machine.ctx.proc = proc) :
    Transfer (fullOwn State.machine (payload (GF := GF))) sie proc edge s := by
  cases plan with
  | full p => exact FullPlan.transfer State.machine payload edge s p sie proc hsie hproc
  | byte p => exact p.action.transfer p.row p.access s edge p.address p.decoded p.enabled p.steps sie proc hsie hproc

theorem wp_memory (sie : Bool) (proc : BitVec 64) (good cut : State → Prop) (edge : State → State → Prop)
    (closed : Closed good cut edge)
    (indices : ∀ s, good s → s.machine.ctx.sie = sie ∧ s.machine.ctx.proc = proc)
    (compile : ∀ s, good s → ¬ cut s → Plan (GF := GF) edge s)
    (cpu : CPU) (s : State) (entry : good s) :
    fullOwn State.machine (payload (GF := GF)) cpu s ∗ wpNext sie proc cpu (fun cpu' => iprop(
      ∀ t, ⌜good t⌝ -∗ ⌜cut t⌝ -∗ fullOwn State.machine (payload (GF := GF)) cpu' t -∗ wpLoop cpu')) ⊢ wpLoop cpu :=
  wp_control_flow (fullOwn State.machine (payload (GF := GF))) sie proc closed
    (fun a hg hc => (compile a hg hc).transfer edge a sie proc (indices a hg).1 (indices a hg).2) cpu s entry

end Xv6.WholeFunction.Memory
