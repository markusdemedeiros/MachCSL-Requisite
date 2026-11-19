import Experiments.WholeFunction.KernelStackGraph

/-! Registered callee summaries at a real machine-call boundary. Callee specs
have unguarded continuations; the actual JAL supplies the guarded progress
needed by whole-CFG composition. Thus a call action fuses JAL and its registered
callee contract, rather than assuming a callee can consume a later for free. -/
namespace Xv6.WholeFunction
open Iris Iris.BI Iris.ProgramLogic MachCSL LeanRV64D

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
variable [CurCtx] [KernelGeom] [KernelImage GF]
variable {S : Type}

def fullOwn (machine : S → Stack.State) (payload : S → IProp GF)
    (cpu : CPU) (s : S) : IProp GF :=
  iprop(mixedOwn cpu (machine s) ∗ payload s)

/-- The resources visible to a callee: its kernel context and semantic data.
The caller's saved stack cells and static kernel text are framed separately. -/
def callOwn (machine : S → Stack.State) (payload : S → IProp GF)
    (cpu : CPU) (s : S) : IProp GF :=
  iprop(kctx cpu (machine s).ctx ∗ pcIs cpu (machine s).pc ∗ payload s)

/-- Register one semantic contract for a callee. This is an ordinary callee
contract, not a spatial WP premise for each instruction of its callers. -/
def CalleeSpec (machine : S → Stack.State) (payload : S → IProp GF)
    (result : S → Prop) (entry : S) : Prop :=
  ∀ cpu, callOwn machine payload cpu entry ∗
    wpNext (machine entry).ctx.sie (machine entry).ctx.proc cpu (fun cpu' => iprop(
      ∀ t, ⌜result t⌝ -∗ callOwn machine payload cpu' t -∗ wpLoop cpu')) ⊢ wpLoop cpu

/-- The callee specification with the unchanged caller frame reattached. -/
def CallSummary (machine : S → Stack.State) (payload : S → IProp GF)
    (result : S → Prop) (entry : S) : Prop :=
  ∀ cpu, fullOwn machine payload cpu entry ∗
    wpNext (machine entry).ctx.sie (machine entry).ctx.proc cpu (fun cpu' => iprop(
      ∀ t, ⌜result t⌝ -∗ fullOwn machine payload cpu' t -∗ wpLoop cpu')) ⊢ wpLoop cpu

theorem summary_from_spec (machine : S → Stack.State) (payload : S → IProp GF)
    (result : S → Prop) (entry : S)
    (spec : CalleeSpec machine payload result entry)
    (frame : ∀ t, result t → (machine t).cells = (machine entry).cells) :
    CallSummary machine payload result entry := by
  intro cpu
  unfold fullOwn mixedOwn regOwn Stack.State.machine
  iintro ⟨⟨⟨⟨#HT, HK, HPC⟩, Hcells⟩, HP⟩, Hexit⟩
  iapply spec cpu $$ [HK HPC HP Hcells Hexit]
  isplitl [HK HPC HP]
  · unfold callOwn
    iframe HK HPC HP
  · iapply wpNext_intro_pin
    iintro %cpu' %hp %t %hr Hcall
    unfold callOwn
    icases Hcall with ⟨HK, HPC, HP⟩
    ihave Hexit := wpNext_at _ _ _ cpu' _ hp $$ Hexit
    ihave Hexit := Hexit $$ %t %hr
    rw [frame t hr]
    iapply Hexit $$ [HT HK HPC Hcells HP]
    iframe HT HK HPC Hcells HP

/-- Only validated linking JALs enter the call registry. Plain jumps remain
ordinary mixed actions; arbitrary indirect transfers are not invented. -/
structure LinkedJump where
  imm : BitVec 21
  link : BitVec 5
  valid : rdOk link

def LinkedJump.code (a : LinkedJump) : instruction := .JAL (a.imm, .Regidx a.link)

def LinkedJump.decode (i : instruction) : Option {a : LinkedJump // i = a.code} :=
  match i with
  | .JAL (imm, .Regidx rd) =>
    if h : rdOk rd then some ⟨⟨imm, rd, h⟩, rfl⟩ else none
  | _ => none

structure LocatedCall (pc : BitVec 64) where
  row : Binary.Row
  jump : LinkedJump
  address : pc = row.pc
  decoded : row.code = jump.code

def findCall (pc : BitVec 64) : List Binary.Row → Option (LocatedCall pc)
  | [] => none
  | row :: rest =>
    if hp : pc = row.pc then
      (LinkedJump.decode row.code).map (fun a => ⟨row, a.val, hp, a.property⟩)
    else findCall pc rest

def LocatedCall.target {pc : BitVec 64} (call : LocatedCall pc) : BitVec 64 :=
  call.row.pc + call.jump.imm.signExtend 64

/-- The linked jump's symbolic machine update. The rd restriction is the
production rule's: link writes may not overwrite sp or the migration tp. -/
def jalRun (row : Binary.Row) (imm : BitVec 21) (rd : BitVec 5)
    (s : Stack.State) : Stack.State :=
  ⟨s.ctx.setReg rd (row.pc + instrLen row.rvc), row.pc + imm.signExtend 64, s.cells⟩

/-- A checked JAL followed by a registered callee specification is one guarded
CFG transfer. The entry semantic state may change metadata via a resource
entailment, while the machine update is fixed by the decoded instruction. -/
theorem jal_transfer (machine : S → Stack.State) (payload : S → IProp GF)
    (edge : S → S → Prop) (s entry : S) (row : Binary.Row)
    (imm : BitVec 21) (rd : BitVec 5) (valid : rdOk rd)
    (address : (machine s).pc = row.pc)
    (decoded : row.code = instruction.JAL (imm, .Regidx rd))
    (entered : machine entry = jalRun row imm rd (machine s))
    (data : payload s ⊢ payload entry)
    (summary : CallSummary machine payload (edge s) entry)
    (sie : Bool) (proc : BitVec 64)
    (hsie : (machine s).ctx.sie = sie) (hproc : (machine s).ctx.proc = proc) :
    Transfer (fullOwn machine payload) sie proc edge s := by
  intro cpu
  unfold fullOwn mixedOwn regOwn Stack.State.machine
  iintro ⟨⟨⟨⟨#HT, HK, HPC⟩, Hcells⟩, HP⟩, Hnext⟩
  ihave #HI := row.instr (GF := GF) $$ HT
  rw [decoded, address]
  iapply wp_s_jal cpu (machine s).ctx row.pc row.rvc imm rd valid
    $$ [$HI $HK $HPC Hcells HP Hnext]
  inext
  iapply wpNext_intro_pin
  iintro %cpu' %hp HK HPC
  ihave HP := data $$ HP
  iapply summary cpu' $$ [HT HK HPC Hcells HP Hnext]
  isplitl [HK HPC Hcells HP]
  · unfold fullOwn mixedOwn regOwn Stack.State.machine
    rw [entered]
    dsimp only [jalRun]
    iframe HT HK HPC Hcells HP
  · have heSie : (machine entry).ctx.sie = sie := by rw [entered]; exact hsie
    have heProc : (machine entry).ctx.proc = proc := by rw [entered]; exact hproc
    rw [heSie, heProc]
    dsimp only [fullOwn, mixedOwn, regOwn, Stack.State.machine]
    iapply wpNext_shift sie proc cpu cpu' _ (by simpa only [hsie, hproc] using hp) $$ Hnext

end Xv6.WholeFunction

namespace Xv6.WholeFunction
open MachCSL
noncomputable section
private def walkaddrCallRow : Binary.Row := Binary.rowAt 0x800016ea#64 (by binary_rfl) (by binary_rfl)
private def vmfaultCallRow : Binary.Row := Binary.rowAt 0x800016f8#64 (by binary_rfl) (by binary_rfl)
private def memmoveCallRow : Binary.Row := Binary.rowAt 0x800016d0#64 (by binary_rfl) (by binary_rfl)

-- Each call target is computed from the actual binary, including sign extension.
example : ((findCall 0x800016ea#64 [walkaddrCallRow]).map LocatedCall.target) =
    some KA.«walkaddr» := by binary_rfl
example : ((findCall 0x800016f8#64 [vmfaultCallRow]).map LocatedCall.target) =
    some KA.«vmfault» := by binary_rfl
example : ((findCall 0x800016d0#64 [memmoveCallRow]).map LocatedCall.target) =
    some KA.«memmove» := by binary_rfl

-- Unsafe link registers and non-linking jumps cannot enter the call registry.
example : (LinkedJump.decode (.JAL (4#21, .Regidx 2#5))).isNone = true := by decide
example : (LinkedJump.decode (.JAL (4#21, .Regidx 0#5))).isNone = true := by decide
end
end Xv6.WholeFunction
