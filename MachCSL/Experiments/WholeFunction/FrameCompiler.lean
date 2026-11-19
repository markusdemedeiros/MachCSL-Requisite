import Experiments.WholeFunction.StackReturn

/-! Shared frame compiler for save/restore sequences. A small layout descriptor
generates the expected decoder certificate; one finite-row theorem executes
both kinds of frame. Padding slots retain their arbitrary original values. -/
namespace Xv6.WholeFunction.FrameCompiler
open Iris Iris.BI Iris.ProgramLogic MachCSL LeanRV64D

abbrev SavedReg := { r : BitVec 5 // rdOk r }

structure Layout where
  slots : Nat
  saved : List SavedReg
  popImm : BitVec 12
  pushImm : BitVec 12
  popOffset : popImm.signExtend 64 = 8#64 * BitVec.ofNat 64 slots
  pushOffset : pushImm.signExtend 64 = -(8#64 * BitVec.ofNat 64 slots)

def Layout.registers (l : Layout) : List (BitVec 5) := l.saved.map Subtype.val

def Layout.frameCells (l : Layout) (entry : KCtx) (padding : List (BitVec 64)) : List Stack.Cell :=
  (Stack.addresses entry.sp l.slots).zip ((l.registers.map entry.regs) ++ padding)

def Layout.restore (l : Layout) (entry current : KCtx) : KCtx :=
  l.registers.foldl (fun k r => k.setReg r (entry.regs r)) current

abbrev Plan := StackReturn.Plan
abbrev compileRows := StackReturn.compileRows

def Layout.savePlan (l : Layout) (start : BitVec 64) : Plan :=
  l.saved.mapIdx (fun index r => (start + BitVec.ofNat 64 (2 * index), true,
    .stack (.save (BitVec.ofNat 12 (8 * (l.slots - index - 1))) r.val index))) ++
  [(start + BitVec.ofNat 64 (2 * l.saved.length), true, .reg (.addi l.popImm 8#5 2#5 (by decide)))]

def Layout.returnPlan (l : Layout) (start : BitVec 64) : Plan :=
  l.saved.mapIdx (fun index r => (start + BitVec.ofNat 64 (2 * index), true,
    .stack (.load (BitVec.ofNat 12 (8 * (l.slots - index - 1))) r.val index r.property))) ++
  [(start + BitVec.ofNat 64 (2 * l.saved.length), true, .stack (.pop l.popImm l.slots l.popOffset)),
   (start + BitVec.ofNat 64 (2 * l.saved.length + 2), true, .reg (.ret 1#5))]

/-- Reuse the existing proven symbolic save and return evaluators. -/
def saving : MixedAction → Bool
  | .reg (.addi ..) | .stack (.save ..) => true
  | _ => false

def supported (a : MixedAction) : Prop :=
  if saving a then StackValues.supported a else StackReturn.supported a

def eval (a : MixedAction) (rvc : Bool) (s : Stack.State) : Stack.State :=
  if saving a then StackValues.eval a rvc s else StackReturn.eval a rvc s

theorem next_eq_eval (a : MixedAction) (rvc : Bool) (cpu : CPU) (s t : Stack.State)
    (hs : supported a) (hn : a.Next rvc cpu s t) : t = eval a rvc s := by
  cases h : saving a with
  | false =>
    simp only [supported, h, Bool.false_eq_true, ↓reduceIte] at hs
    simpa only [eval, h, Bool.false_eq_true, ↓reduceIte] using StackReturn.next_eq_eval a rvc cpu s t hs hn
  | true =>
    simp only [supported, h, ↓reduceIte] at hs
    simpa only [eval, h, ↓reduceIte] using StackValues.next_eq_eval a rvc cpu s t hs hn

def planSafe : Plan → Stack.State → Prop
  | [], _ => True
  | (pc, rvc, a) :: rest, s => s.pc = pc ∧ supported a ∧ a.Enabled s ∧
      planSafe rest (eval a rvc s)

def evalPlan (p : Plan) (s : Stack.State) : Stack.State :=
  p.foldl (fun s a => eval a.2.2 a.2.1 s) s

theorem plan_safe {slots : Nat} {rows : List Binary.Row} {p : Plan}
    (compiled : compileRows slots rows = p.map some) (s : Stack.State)
    (safe : planSafe p s) : Linear.Safe slots rows s := by
  induction rows generalizing p s with
  | nil => trivial
  | cons row rows ih =>
    cases p with
    | nil => simp [compileRows, StackReturn.compileRows] at compiled
    | cons head p =>
      cases hd : MixedAction.decode slots row.code with
      | none => simp [compileRows, StackReturn.compileRows, hd] at compiled
      | some a =>
        simp only [compileRows, StackReturn.compileRows, List.map_cons, hd, Option.map_some,
          List.cons.injEq, Option.some.injEq] at compiled
        obtain ⟨rfl, hc⟩ := compiled
        obtain ⟨hp, hs, he, ht⟩ := safe
        refine ⟨a, hd, hp, he, ?_⟩
        intro cpu t hn
        rw [next_eq_eval a.val row.rvc cpu s t hs hn]
        exact ih hc _ ht

theorem plan_values {slots : Nat} {rows : List Binary.Row} {p : Plan}
    (compiled : compileRows slots rows = p.map some) {s t : Stack.State}
    (safe : planSafe p s) (run : Linear.RowRun slots rows s t) : t = evalPlan p s := by
  induction run generalizing p with
  | nil =>
    cases p with
    | nil => rfl
    | cons => simp [compileRows, StackReturn.compileRows] at compiled
  | cons row a cpu hd hp hn tail ih =>
    cases p with
    | nil => simp [compileRows, StackReturn.compileRows] at compiled
    | cons head p =>
      simp only [compileRows, StackReturn.compileRows, List.map_cons, hd, Option.map_some,
        List.cons.injEq, Option.some.injEq] at compiled
      obtain ⟨rfl, hc⟩ := compiled
      obtain ⟨_, hs, _, ht⟩ := safe
      have he := next_eq_eval a.val row.rvc cpu _ _ hs hn
      subst he
      exact ih hc ht

/-- Every concrete shaped frame is represented by a vector of arbitrary
initial contents; this includes padding and does not initialize any cell. -/
theorem cells_values (base : BitVec 64) (n : Nat) (cells : List Stack.Cell)
    (shape : cells.map Prod.fst = Stack.addresses base n) :
    ∃ values : Fin n → BitVec 64, cells = (Stack.addresses base n).zip (List.ofFn values) := by
  have len : cells.length = n := by simpa [Stack.addresses] using congrArg List.length shape
  let values : Fin n → BitVec 64 := fun i => (cells[i.val]'(by omega)).2
  have vals : cells.map Prod.snd = List.ofFn values := by
    apply List.ext_getElem?
    intro j
    by_cases hj : j < n
    · simp [List.getElem?_eq_getElem (by omega : j < cells.length), values, hj]
    · simp [List.getElem?_eq_none (by omega : cells.length ≤ j), hj]
  refine ⟨values, ?_⟩
  rw [← shape, ← vals, List.zip_map']
  simp

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
variable [CurCtx] [KernelGeom] [KernelImage GF]

theorem wp_plan {slots : Nat} {rows : List Binary.Row} {p : Plan}
    (compiled : compileRows slots rows = p.map some) (cpu : CPU) (s : Stack.State)
    (safe : planSafe p s) :
    mixedOwn (GF := GF) cpu s ∗ wpNext s.ctx.sie s.ctx.proc cpu (fun cpu' => iprop(
      mixedOwn cpu' (evalPlan p s) -∗ wpLoop cpu')) ⊢ wpLoop cpu := by
  iintro ⟨Hstate, Hexit⟩
  iapply Linear.wp_rows slots rows cpu s (plan_safe compiled s safe) $$ [$Hstate Hexit]
  iapply wpNext_mono _ _ _ _ _ $$ Hexit
  iintro %cpu' Hexit %t %run Hstate
  rw [plan_values compiled safe run]
  iapply Hexit $$ Hstate

/-- The shared push-and-save importer. A layout's saved-body proof is pure;
all actual instruction WPs and the arbitrary fresh frame are handled here. -/
theorem wp_push_plan (l : Layout) (push : Binary.Row) (rows : List Binary.Row) (p : Plan)
    (pushCode : push.code = (.stack (.push l.pushImm l.slots l.pushOffset) : MixedAction).code)
    (compiled : compileRows l.slots rows = p.map some) (cpu : CPU) (k : KCtx)
    (available : l.slots ≤ k.avail)
    (safe : ∀ cells, cells.map Prod.fst = Stack.addresses k.sp l.slots →
      planSafe p ⟨k.push l.slots, push.next, cells⟩) :
    kernelText (GF := GF) ∗ kctx cpu k ∗ pcIs cpu push.pc ∗
      wpNext k.sie k.proc cpu (fun cpu' => iprop(
        ∀ cells, ⌜cells.map Prod.fst = Stack.addresses k.sp l.slots⌝ -∗
          mixedOwn cpu' (evalPlan p ⟨k.push l.slots, push.next, cells⟩) -∗ wpLoop cpu'))
      ⊢ wpLoop cpu := by
  iintro ⟨#HT, HK, HPC, Hexit⟩
  ihave #HI := push.instr (GF := GF) $$ HT
  rw [pushCode]
  simp only [MixedAction.code, Stack.Action.code]
  iapply wp_s_push cpu k push.pc push.rvc l.pushImm l.slots available l.pushOffset
    $$ [$HI $HK $HPC Hexit]
  inext
  iapply wpNext_intro_pin
  iintro %cpu' %hp HK HPC Hframe
  icases Stack.stack_values k.sp l.slots $$ Hframe with ⟨%cells, %shape, Hcells⟩
  iapply wp_plan compiled cpu' ⟨k.push l.slots, push.next, cells⟩ (safe cells shape)
    $$ [HT HK HPC Hcells Hexit]
  isplitl [HK HPC Hcells]
  · have hn : push.next = push.pc + instrLen push.rvc := by unfold Binary.Row.next; cases push.rvc <;> rfl
    unfold mixedOwn regOwn Stack.State.machine
    rw [hn]
    iframe HT HK HPC Hcells
  · simp only [KCtx.push_sie, KCtx.push_proc]
    iapply wpNext_intro_pin
    iintro %cpu'' %hp' Hstate
    ihave Hexit := wpNext_at _ _ cpu cpu'' _ (fun h => (hp' h).trans (hp h)) $$ Hexit
    iapply Hexit $$ %cells %shape Hstate

end Xv6.WholeFunction.FrameCompiler
