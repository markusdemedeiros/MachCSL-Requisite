import Experiments.WholeFunction.RequisiteHart

/-! Positive spatial test: an actual register-write primitive, with full
ownership of the old PC cell at entry and the new PC cell at the continuation.
The pure region and resource simulation are separately proved. No instruction
WP or desired conclusion is assumed in the simulation certificate. -/
namespace MachCSL.WholeFunction
open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProgramLogic.Language
open Iris.ProgramLogic.Language.Notation
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]

def writeCode (new : BitVec 64) : Bool → SailM Unit
  | false => .impure (.ok (.regWrite .PC new)) (fun _ => pure ())
  | true => pure ()

def writeOwn (cpu : CPU) (old new : BitVec 64) (done : Bool) : IProp GF :=
  iprop(Register.PC ↦ᵣ[cpu] (if done then new else old))

def writeEdge (done done' : Bool) : Prop := done = false ∧ done' = true

theorem writeSimulation (cpu : CPU) (old new : BitVec 64) :
    HartFootprintSimulation cpu (writeOwn (GF := GF) cpu old new) (writeCode new)
      (fun done => done = false) writeEdge where
  update done ready σ := by
    subst done
    simp only [writeOwn, Bool.false_eq_true, ↓reduceIte]
    iintro ⟨Hσ, Hr⟩
    icases machInterp_acc σ cpu $$ Hσ with ⟨Hregs, Hclose⟩
    imod reg_update cpu (σ.regs cpu) .PC old new $$ [$Hregs $Hr] with ⟨Hregs, Hr⟩
    iapply fupd_mask_intro LawfulSet.empty_subset
    iintro Hmask
    isplit
    · ipureintro
      exact ⟨hartObs_regWrite_quiet cpu σ .PC new (Or.inl (by decide)),
        pure (), σ.setReg cpu .PC new, Or.inl ⟨(), rfl, rfl⟩⟩
    inext
    iintro %m' %σ' %Hstep _
    change (∃ (_v : PUnit), m' = pure () ∧ σ' = σ.setReg cpu .PC new) ∨
      (False ∧ m' = writeCode new false) at Hstep
    rcases Hstep with ⟨_, rfl, rfl⟩ | ⟨h, _⟩
    · imod Hmask
      imodintro
      iexists true
      isplit
      · ipureintro; exact ⟨rfl, rfl, rfl⟩
      isplitl [Hregs Hclose]
      · iapply Hclose $$ Hregs
      · simp only [↓reduceIte]
        iexact Hr
    · exact h.elim

def writeGood (cpu : CPU) (new : BitVec 64) (e : Expr) (done : Bool) : Prop :=
  e = Expr.hart (genId (hlc := hlc) (GF := GF)) cpu (writeCode new done)

/-- The operational certificate knows only two control states. Every actual
write reaches the exit; power-loss stuttering keeps the entry safe. -/
theorem writeRegion (cpu : CPU) (new : BitVec 64) :
    FootprintRegion
      (hartEnabled (GF := GF) cpu (writeCode new) (fun done => done = false))
      (hartEdge (GF := GF) cpu (writeCode new) writeEdge)
      (writeGood (GF := GF) cpu new) (fun _ done => done = true) where
  safe e done good notcut := ⟨good, by cases done <;> simp_all⟩
  closed _e _done _e' _done' _good _notcut step := step.1

/-- A spatial contract derived by continuation requisiteness for a REAL hart
event. The PC cell is updated from `old` to `new`; the caller's frame and linear
continuation are preserved. This is safety, not termination after power loss. -/
theorem wp_write_via_requisiteness (cpu : CPU) (old new : BitVec 64)
    (frame : IProp GF) :
    resourceInv -∗
    (hartOwn (writeOwn cpu old new) true ∗ frame -∗
      WP (Expr.hart (genId (hlc := hlc) (GF := GF)) cpu (pure ()))
        @ Stuckness.NotStuck; ⊤ {{ _v, True }}) -∗
    hartOwn (writeOwn cpu old new) false ∗ frame -∗
      WP (Expr.hart (genId (hlc := hlc) (GF := GF)) cpu (writeCode new false))
        @ Stuckness.NotStuck; ⊤ {{ _v, True }} := by
  iintro #Hworld Hexit Hown
  iapply wp_footprint_region_cps (writeSimulation cpu old new).toFootprint
    (writeRegion cpu new) frame _ false rfl $$ Hworld [Hexit] Hown
  iintro %e' %done %Hgood %Hcut Hown
  subst done
  subst e'
  simp only [writeCode]
  iapply Hexit $$ Hown

/-- The example at the ordinary production proof boundary. Its statement
contains only the old/new register cells and `wpHart`/`wpLoop`; the proof goes
through the new abstract resource simulation and requisite region importer. -/
theorem wp_write_cell (cpu : CPU) (old new : BitVec 64) :
    Register.PC ↦ᵣ[cpu] old ∗ (Register.PC ↦ᵣ[cpu] new -∗ wpLoop cpu)
      ⊢@{IProp GF} wpHart cpu (writeCode new false) := by
  unfold wpHart hartWP
  iintro ⟨Hcell, Hcont⟩ #Hcert
  ihave #Hworld := genCert_resourceInv $$ Hcert
  iapply wp_write_via_requisiteness cpu old new iprop(emp)
    $$ Hworld [Hcont] [Hcell]
  · unfold hartOwn writeOwn
    simp only [↓reduceIte]
    iintro ⟨⟨#Hcert', Hnew⟩, _⟩
    ihave Hloop := Hcont $$ Hnew
    unfold wpLoop wpHart hartWP
    iapply Hloop $$ Hcert'
  · unfold hartOwn writeOwn
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe Hcert Hcell

end MachCSL.WholeFunction

open Classical
/-- info: 'MachCSL.WholeFunction.wp_write_via_requisiteness' depends on axioms: [propext, choice, Quot.sound] -/
#guard_msgs in
#print axioms MachCSL.WholeFunction.wp_write_via_requisiteness

/-- info: 'MachCSL.WholeFunction.wp_write_cell' depends on axioms: [propext, choice, Quot.sound] -/
#guard_msgs in
#print axioms MachCSL.WholeFunction.wp_write_cell
