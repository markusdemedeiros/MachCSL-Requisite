import Experiments.WholeFunction.KernelStackGraph

/-! Fail-closed symbolic register prefixes over the existing decoded action
backend. Register transfer semantics are exclusively RegAction.run. Branches
remain symbolic; returning stops after the RET even if its target is inside
the input rows. No outside-return-address assumption is introduced.
-/
namespace Xv6.WholeFunction.Symbolic
open Iris Iris.BI Iris.ProgramLogic MachCSL LeanRV64D

def hartFree : RegAction → Bool
  | .addi _ _ rs _ | .addiw _ _ rs _ | .andi _ _ rs _ | .srli _ _ rs _ | .ret rs => rs != 4#5
  | .add _ rs rt _ | .sub _ rs rt _ | .subw _ rs rt _ | .addw _ rs rt _ |
      .and _ rs rt _ | .branch _ rs rt _ _ =>
      rs != 4#5 && rt != 4#5
  | .lui .. | .jump .. => true

def returns : RegAction → Bool
  | .ret _ => true
  | _ => false

def canonical : CPU := ⟨0, by decide⟩

theorem rget_independent (k : KCtx) (r : BitVec 5) (h : r ≠ 4#5) (cpu : CPU) :
    k.rget cpu r = k.rget canonical r := by
  by_cases hz : r = 0#5
  · subst r; simp
  · rw [KCtx.rget_ne _ _ _ hz h, KCtx.rget_ne _ _ _ hz h]

theorem run_independent (a : RegAction) (rvc : Bool) (s : RegState) (cpu : CPU)
    (free : hartFree a = true) : a.run rvc cpu s = a.run rvc canonical s := by
  cases a <;> simp only [hartFree, Bool.and_eq_true, bne_iff_ne] at free <;>
    simp only [RegAction.run]
  all_goals first
    | rfl
    | rw [rget_independent _ _ free cpu]
    | rw [rget_independent _ _ free.1 cpu, rget_independent _ _ free.2 cpu]

inductive Error where
  | fuel | unsupported (pc : BitVec 64) | hartDependent (pc : BitVec 64)
  deriving DecidableEq

inductive Exit where
  | cut | returned
  deriving DecidableEq

structure Result where
  state : RegState
  exit : Exit

/-- Fuel exhaustion, missing/unsupported rows, and hart-dependent reads are
errors. A successful symbolic execution therefore covers every instruction
up to a chosen cut or a real return. -/
def runUntil (rows : List Binary.Row) (cut : BitVec 64 → Bool) :
    Nat → RegState → Except Error Result
  | fuel, s =>
    if cut s.pc then .ok ⟨s, .cut⟩ else
    match fuel with
    | 0 => .error .fuel
    | n + 1 =>
      match findReg s.pc rows with
      | none => .error (.unsupported s.pc)
      | some r =>
        if hartFree r.action then
          let t := r.action.run r.row.rvc canonical s
          if returns r.action then .ok ⟨t, .returned⟩ else runUntil rows cut n t
        else .error (.hartDependent s.pc)

/-- Universal operational certificate: a single canonical symbolic result
applies to every actual hart because each selected action is checked free
of tp reads. The action and code are still supplied by actual row lookup. -/
inductive Certificate (rows : List Binary.Row) (cut : BitVec 64 → Bool) :
    RegState → Result → Prop
  | stop (s : RegState) (hit : cut s.pc = true) : Certificate rows cut s ⟨s, .cut⟩
  | ret (s : RegState) (r : LocatedReg s.pc)
      (found : findReg s.pc rows = some r) (free : hartFree r.action = true)
      (returned : returns r.action = true) :
      Certificate rows cut s ⟨r.action.run r.row.rvc canonical s, .returned⟩
  | step (s : RegState) (r : LocatedReg s.pc) (result : Result)
      (found : findReg s.pc rows = some r) (free : hartFree r.action = true)
      (tail : Certificate rows cut (r.action.run r.row.rvc canonical s) result) :
      Certificate rows cut s result

theorem runUntil_certificate (rows : List Binary.Row) (cut : BitVec 64 → Bool)
    (fuel : Nat) (s : RegState) (result : Result)
    (checked : runUntil rows cut fuel s = .ok result) : Certificate rows cut s result := by
  induction fuel generalizing s with
  | zero =>
    simp only [runUntil] at checked
    split at checked
    · cases checked; exact .stop _ (by assumption)
    · cases checked
  | succ fuel ih =>
    simp only [runUntil] at checked
    split at checked
    · cases checked; exact .stop _ (by assumption)
    · cases found : findReg s.pc rows with
      | none => simp [found] at checked
      | some r =>
        simp only [found] at checked
        split at checked
        · rename_i free
          split at checked
          · rename_i returned
            cases checked
            exact .ret s r found free returned
          · exact .step s r result found free (ih _ checked)
        · cases checked

theorem Certificate.indices {rows : List Binary.Row} {cut : BitVec 64 → Bool}
    {s : RegState} {result : Result} (h : Certificate rows cut s result) :
    result.state.ctx.sie = s.ctx.sie ∧ result.state.ctx.proc = s.ctx.proc := by
  induction h with
  | stop => exact ⟨rfl, rfl⟩
  | ret s r => exact ⟨r.action.run_sie .., r.action.run_proc ..⟩
  | step s r _ _ _ _ ih =>
    exact ⟨ih.1.trans (r.action.run_sie ..), ih.2.trans (r.action.run_proc ..)⟩

theorem Certificate.append {rows : List Binary.Row} {first last : BitVec 64 → Bool}
    {s : RegState} {middle result : Result}
    (head : Certificate rows first s middle) (ended : middle.exit = .cut)
    (tail : Certificate rows last middle.state result) : Certificate rows last s result := by
  induction head with
  | stop => exact tail
  | ret => cases ended
  | step s r _ found free _ ih => exact .step s r result found free (ih ended tail)

theorem Certificate.cut_cases {rows : List Binary.Row} {cut : BitVec 64 → Bool}
    {s : RegState} {result : Result} (h : Certificate rows cut s result)
    (ended : result.exit = .cut) :
    s = result.state ∨ ∃ r : LocatedReg s.pc,
      findReg s.pc rows = some r ∧ hartFree r.action = true ∧
      Certificate rows cut (r.action.run r.row.rvc canonical s) result := by
  cases h with
  | stop => exact Or.inl rfl
  | ret => cases ended
  | step s r result found free tail => exact Or.inr ⟨r, found, free, tail⟩

def mixed {pc : BitVec 64} (r : LocatedReg pc) : LocatedMixed pc :=
  ⟨r.row, .reg r.action, r.address, r.decoded⟩

theorem findMixed_of_findReg (slots : Nat) (pc : BitVec 64) (rows : List Binary.Row)
    (r : LocatedReg pc) (found : findReg pc rows = some r) :
    findMixed slots pc rows = some (mixed r) := by
  induction rows with
  | nil => simp [findReg] at found
  | cons row rows ih =>
    simp only [findReg] at found
    unfold findMixed
    split at found
    · rename_i hp
      rw [dif_pos hp]
      cases hd : RegAction.decode row.code with
      | none => simp [hd] at found
      | some a =>
        simp only [hd, Option.map_some, Option.some.injEq] at found
        cases found
        simp only [MixedAction.decode, hd, Option.map_some, mixed]
    · rename_i hp
      rw [dif_neg hp]
      exact ih found

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
variable [CurCtx] [KernelGeom] [KernelImage GF]

/-- A successful symbolic prefix produces actual machine ownership at its
exact result. The arbitrary linear frame F survives all branches/migrations.
No per-PC WP proofs or per-prefix resource adapters are supplied by clients. -/
theorem wp_certificate {rows : List Binary.Row} {cut : BitVec 64 → Bool}
    {s : RegState} {result : Result} (h : Certificate rows cut s result)
    (F : IProp GF) (cpu : CPU) :
    regOwn cpu s ∗ F ∗ wpNext s.ctx.sie s.ctx.proc cpu (fun cpu' => iprop(
      regOwn cpu' result.state -∗ F -∗ wpLoop cpu')) ⊢ wpLoop cpu := by
  induction h generalizing cpu with
  | stop s hit =>
    iintro ⟨Hstate, HF, Hexit⟩
    ihave Hexit := wpNext_self _ _ cpu _ $$ Hexit
    iapply Hexit $$ Hstate HF
  | ret s r found free returned =>
    unfold regOwn
    iintro ⟨⟨#HT, HK, HPC⟩, HF, Hexit⟩
    ihave #HI := r.row.instr (GF := GF) $$ HT
    rw [← r.address, r.decoded]
    iapply r.action.sound r.row.rvc cpu s $$ [$HI $HK $HPC HF Hexit]
    inext
    iapply wpNext_intro_pin
    iintro %cpu' %hpin HK HPC
    have he := run_independent r.action r.row.rvc s cpu' free
    rw [he]
    ihave Hexit := wpNext_at _ _ cpu cpu' _ hpin $$ Hexit
    iapply Hexit $$ [HT HK HPC] HF
    iframe HT HK HPC
  | step s r result found free tail ih =>
    unfold regOwn
    iintro ⟨⟨#HT, HK, HPC⟩, HF, Hexit⟩
    ihave #HI := r.row.instr (GF := GF) $$ HT
    rw [← r.address, r.decoded]
    iapply r.action.sound r.row.rvc cpu s $$ [$HI $HK $HPC HF Hexit]
    inext
    iapply wpNext_intro_pin
    iintro %cpu' %hpin HK HPC
    have he := run_independent r.action r.row.rvc s cpu' free
    rw [he]
    iapply ih cpu' $$ [HT HK HPC HF Hexit]
    isplitl [HK HPC]
    · unfold regOwn
      iframe HT HK HPC
    · iframe HF
      rw [r.action.run_sie, r.action.run_proc]
      unfold regOwn
      iapply wpNext_shift _ _ cpu cpu' _ hpin $$ Hexit

theorem wp_runUntil (rows : List Binary.Row) (cut : BitVec 64 → Bool)
    (fuel : Nat) (s : RegState) (result : Result)
    (checked : runUntil rows cut fuel s = .ok result) (F : IProp GF) (cpu : CPU) :
    regOwn cpu s ∗ F ∗ wpNext s.ctx.sie s.ctx.proc cpu (fun cpu' => iprop(
      regOwn cpu' result.state -∗ F -∗ wpLoop cpu')) ⊢ wpLoop cpu :=
  wp_certificate (runUntil_certificate rows cut fuel s result checked) F cpu

end Xv6.WholeFunction.Symbolic
