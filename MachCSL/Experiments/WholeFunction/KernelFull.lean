import Experiments.WholeFunction.KernelCalls

/-! Whole-function composition over an arbitrary semantic payload. Ordinary
rows use the shared register/stack semantics. Linked calls use a registered
callee contract, with their actual JAL providing guarded progress. The program
supplies pure state/invariant certificates and resource entailments, not a
separate instruction WP at every program counter. -/
namespace Xv6.WholeFunction
open Iris Iris.BI Iris.ProgramLogic MachCSL LeanRV64D

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
variable [CurCtx] [KernelGeom] [KernelImage GF]
variable {S : Type}

/-- Uniform lifting of any decoded register/stack action to semantic state. -/
theorem MixedAction.transfer_full (machine : S → Stack.State) (payload : S → IProp GF)
    (edge : S → S → Prop) (s : S) (row : Binary.Row) (a : MixedAction)
    (target : CPU → Stack.State → S)
    (address : (machine s).pc = row.pc) (decoded : row.code = a.code)
    (enabled : a.Enabled (machine s))
    (run : ∀ cpu t, a.Next row.rvc cpu (machine s) t → machine (target cpu t) = t)
    (frame : ∀ cpu t, a.Next row.rvc cpu (machine s) t → payload s ⊢ payload (target cpu t))
    (steps : ∀ cpu t, a.Next row.rvc cpu (machine s) t → edge s (target cpu t))
    (sie : Bool) (proc : BitVec 64)
    (hsie : (machine s).ctx.sie = sie) (hproc : (machine s).ctx.proc = proc) :
    Transfer (fullOwn machine payload) sie proc edge s := by
  intro cpu
  unfold fullOwn mixedOwn regOwn Stack.State.machine
  iintro ⟨⟨⟨⟨#HT, HK, HPC⟩, Hcells⟩, HP⟩, Hnext⟩
  ihave #HI := row.instr (GF := GF) $$ HT
  rw [← address, decoded]
  iapply a.sound row.rvc cpu (machine s) enabled $$ [$HI $HK $HPC $Hcells HP Hnext]
  inext
  rw [hsie, hproc]
  iapply wpNext_intro_pin
  iintro %cpu' %hp %t %hn HK HPC Hcells
  ihave HP := frame cpu' t hn $$ HP
  ihave Hnext := wpNext_at _ _ _ cpu' _ hp $$ Hnext
  ihave Hnext := Hnext $$ %(target cpu' t) %(steps cpu' t hn)
  rw [run cpu' t hn]
  dsimp only [fullOwn, mixedOwn, regOwn, Stack.State.machine]
  iapply Hnext $$ [HT HK HPC Hcells HP]
  iframe HT HK HPC Hcells HP

/-- A typed instruction certificate. The only spatial obligation transports
semantic resources; instruction execution is supplied by the generic backend. -/
structure InstructionPlan (machine : S → Stack.State) (payload : S → IProp GF)
    (edge : S → S → Prop) (s : S) where
  row : Binary.Row
  action : MixedAction
  target : CPU → Stack.State → S
  address : (machine s).pc = row.pc
  decoded : row.code = action.code
  enabled : action.Enabled (machine s)
  run : ∀ cpu t, action.Next row.rvc cpu (machine s) t → machine (target cpu t) = t
  frame : ∀ cpu t, action.Next row.rvc cpu (machine s) t → payload s ⊢ payload (target cpu t)
  steps : ∀ cpu t, action.Next row.rvc cpu (machine s) t → edge s (target cpu t)

/-- Generate every ordinary instruction plan by one table lookup. Clients
supply a uniform semantic-state update, not a spatial proof at each PC. -/
noncomputable def InstructionPlan.from_lookup
    (machine : S → Stack.State) (payload : S → IProp GF)
    (edge : S → S → Prop) (s : S) (slots : Nat) (rows : List Binary.Row)
    (ready : MixedReady slots rows (machine s))
    (found : ¬ MixedCut slots rows (machine s))
    (target : Stack.State → S)
    (run : ∀ t, machine (target t) = t)
    (frame : ∀ t, MixedEdge slots rows (machine s) t → payload s ⊢ payload (target t))
    (steps : ∀ t, MixedEdge slots rows (machine s) t → edge s (target t)) :
    InstructionPlan machine payload edge s := by
  have hex : ∃ r, findMixed slots (machine s).pc rows = some r :=
    Option.ne_none_iff_exists'.mp found
  let r := Classical.choose hex
  have hr := Classical.choose_spec hex
  exact ⟨r.row, r.action, fun _ t => target t, r.address, r.decoded, ready r hr,
    fun _ t _ => run t,
    fun cpu t hn => frame t ⟨r, hr, cpu, hn⟩,
    fun cpu t hn => steps t ⟨r, hr, cpu, hn⟩⟩

/-- A typed registered call certificate: binary link/jump correspondence,
semantic entry adaptation, and the callee's actual public contract. -/
structure CallPlan (machine : S → Stack.State) (payload : S → IProp GF)
    (edge : S → S → Prop) (s : S) where
  row : Binary.Row
  imm : BitVec 21
  link : BitVec 5
  valid : rdOk link
  entry : S
  address : (machine s).pc = row.pc
  decoded : row.code = instruction.JAL (imm, .Regidx link)
  entered : machine entry = jalRun row imm link (machine s)
  data : payload s ⊢ payload entry
  summary : CallSummary machine payload (edge s) entry

/-- Call-plan construction uses the checked linker output. The remaining
obligations concern only the registered semantic contract and its arguments. -/
def CallPlan.from_lookup (machine : S → Stack.State) (payload : S → IProp GF)
    (edge : S → S → Prop) (s entry : S) (r : LocatedCall (machine s).pc)
    (entered : machine entry = jalRun r.row r.jump.imm r.jump.link (machine s))
    (data : payload s ⊢ payload entry)
    (summary : CallSummary machine payload (edge s) entry) :
    CallPlan machine payload edge s :=
  ⟨r.row, r.jump.imm, r.jump.link, r.jump.valid, entry, r.address, r.decoded,
    entered, data, summary⟩

inductive FullPlan (machine : S → Stack.State) (payload : S → IProp GF)
    (edge : S → S → Prop) (s : S) where
  | instruction (plan : InstructionPlan machine payload edge s)
  | call (plan : CallPlan machine payload edge s)

theorem FullPlan.transfer (machine : S → Stack.State) (payload : S → IProp GF)
    (edge : S → S → Prop) (s : S) (plan : FullPlan machine payload edge s)
    (sie : Bool) (proc : BitVec 64)
    (hsie : (machine s).ctx.sie = sie) (hproc : (machine s).ctx.proc = proc) :
    Transfer (fullOwn machine payload) sie proc edge s := by
  cases plan with
  | instruction p =>
    exact p.action.transfer_full machine payload edge s p.row p.target
      p.address p.decoded p.enabled p.run p.frame p.steps sie proc hsie hproc
  | call p =>
    exact jal_transfer machine payload edge s p.entry p.row p.imm p.link p.valid
      p.address p.decoded p.entered p.data p.summary sie proc hsie hproc

/-- Whole-function importer with ordinary decoded rows and registered calls.
The sole cyclic proof is shared; no termination, fixed-hart assumption, or
callee-body re-verification is introduced. -/
theorem wp_full (machine : S → Stack.State) (payload : S → IProp GF)
    (sie : Bool) (proc : BitVec 64) (good cut : S → Prop) (edge : S → S → Prop)
    (closed : Closed good cut edge)
    (indices : ∀ s, good s → (machine s).ctx.sie = sie ∧ (machine s).ctx.proc = proc)
    (compile : ∀ s, good s → ¬ cut s → FullPlan machine payload edge s)
    (cpu : CPU) (s : S) (entry : good s) :
    fullOwn machine payload cpu s ∗ wpNext sie proc cpu (fun cpu' => iprop(
      ∀ t, ⌜good t⌝ -∗ ⌜cut t⌝ -∗ fullOwn machine payload cpu' t -∗ wpLoop cpu'))
      ⊢ wpLoop cpu :=
  wp_control_flow (fullOwn machine payload) sie proc closed
    (fun a hg hc => FullPlan.transfer machine payload edge a (compile a hg hc)
      sie proc (indices a hg).1 (indices a hg).2) cpu s entry

end Xv6.WholeFunction

open Lean in
run_cmd do
  let baseline := (← collectAxioms ``Xv6.WholeFunction.MixedAction.sound) ++
    (← collectAxioms ``MachCSL.wp_s_jal)
  for decl in #[``Xv6.WholeFunction.summary_from_spec, ``Xv6.WholeFunction.jal_transfer,
      ``Xv6.WholeFunction.MixedAction.transfer_full, ``Xv6.WholeFunction.wp_full] do
    let axs ← collectAxioms decl
    let extra := axs.filter fun a => !baseline.contains a
    unless extra.isEmpty do throwError "{decl}: new axioms {extra}"
    if axs.contains ``sorryAx then throwError "{decl}: contains sorryAx"
  logInfo "Registered-call/full-CFG composition adds no axioms beyond the production instruction backend."
