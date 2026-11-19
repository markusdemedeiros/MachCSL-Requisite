import Experiments.WholeFunction.StackChecks

/-! Value-sensitive symbolic execution of the actual copyin save body.
The pure evaluator below functionalizes the existing MixedAction.Next
relation for hart-independent saves/ADDI; it introduces no machine semantics.
This file does not yet connect a completed linear trace to the graph cut.
-/
namespace Xv6.WholeFunction.StackValues
open MachCSL LeanRV64D

def supported : MixedAction → Prop
  | .reg (.addi _ _ rs _) => rs ≠ 4#5
  | .stack (.save _ rs _) => rs ≠ 4#5
  | _ => False

def eval (a : MixedAction) (rvc : Bool) (s : Stack.State) : Stack.State :=
  match a with
  | .reg a => let r := a.run rvc ⟨0, by decide⟩ s.machine; ⟨r.ctx, r.pc, s.cells⟩
  | .stack (.save _ rs i) =>
      let c := s.cells[i]?.getD (0#64, 0#64)
      ⟨s.ctx, s.pc + instrLen rvc, s.cells.set i (c.1, s.ctx.rget ⟨0, by decide⟩ rs)⟩
  | _ => s

theorem rget_hart_independent (k : KCtx) (rs : BitVec 5) (h : rs ≠ 4#5) (c d : CPU) :
    k.rget c rs = k.rget d rs := by
  by_cases hz : rs = 0#5
  · subst rs; simp
  · rw [KCtx.rget_ne _ _ _ hz h, KCtx.rget_ne _ _ _ hz h]

theorem next_eq_eval (a : MixedAction) (rvc : Bool) (cpu : CPU) (s t : Stack.State)
    (hs : supported a) (hn : a.Next rvc cpu s t) : t = eval a rvc s := by
  cases a with
  | reg a =>
    cases a <;> try exact False.elim hs
    rename_i imm rd rs valid
    cases hn
    simp only [eval, RegAction.run, Stack.State.machine]
    rw [rget_hart_independent _ _ hs cpu ⟨0, by decide⟩]
  | stack a =>
    cases a <;> try exact False.elim hs
    rename_i imm rs i
    obtain ⟨c, lookup, rfl⟩ := hn
    simp only [eval, lookup, Option.getD_some]
    rw [rget_hart_independent _ _ hs cpu ⟨0, by decide⟩]

abbrev Program := List (Bool × MixedAction)

/-- Compiler input is the binary row table. A failed decoder rejects the
whole program; unsupported rows are never filtered out. -/
def decodeProgram (slots : Nat) (rows : List Binary.Row) : Option Program :=
  rows.mapM fun row => (MixedAction.decode slots row.code).map fun a => (row.rvc, a.val)

def evalProgram (p : Program) (s : Stack.State) : Stack.State :=
  p.foldl (fun s a => eval a.2 a.1 s) s

/-- Every step quantifies its own hart: no fixed-hart execution assumption. -/
inductive Run : Program → Stack.State → Stack.State → Prop
  | nil (s : Stack.State) : Run [] s s
  | cons {p : Program} {s t u : Stack.State} (rvc : Bool) (a : MixedAction) (cpu : CPU)
      (step : a.Next rvc cpu s t) (tail : Run p t u) : Run ((rvc, a) :: p) s u

theorem run_exact {p : Program} {s t : Stack.State}
    (h : Run p s t) (safe : ∀ a ∈ p, supported a.2) : t = evalProgram p s := by
  induction h with
  | nil => rfl
  | cons rvc a cpu hn tail ih =>
    have he := next_eq_eval a rvc cpu _ _ (safe _ List.mem_cons_self) hn
    subst he
    exact ih (fun b hb => safe b (List.mem_cons_of_mem _ hb))

/-- A complete sequential run of decoded binary rows, including PC checks.
This relation uses the very same MixedAction.Next as the spatial backend. -/
inductive RowRun (slots : Nat) : List Binary.Row → Stack.State → Stack.State → Prop
  | nil (s : Stack.State) : RowRun slots [] s s
  | cons {rows : List Binary.Row} {s t u : Stack.State}
      (row : Binary.Row) (a : {a : MixedAction // row.code = a.code}) (cpu : CPU)
      (decode : MixedAction.decode slots row.code = some a)
      (pc : s.pc = row.pc) (step : a.val.Next row.rvc cpu s t)
      (tail : RowRun slots rows t u) : RowRun slots (row :: rows) s u

theorem rowRun_compile {slots : Nat} {rows : List Binary.Row} {s t : Stack.State}
    (h : RowRun slots rows s t) (p : Program)
    (compiled : rows.map (fun row => (MixedAction.decode slots row.code).map
      (fun a => (row.rvc, a.val))) = p.map some) : Run p s t := by
  induction h generalizing p with
  | nil =>
    cases p with
    | nil => exact .nil _
    | cons => simp at compiled
  | cons row a cpu hd hp hn tail ih =>
    cases p with
    | nil => simp at compiled
    | cons pair p =>
      simp only [List.map_cons, hd, Option.map_some, List.cons.injEq, Option.some.injEq] at compiled
      obtain ⟨rfl, hc⟩ := compiled
      exact .cons row.rvc a.val cpu hn (ih p hc)

def saveRegisters : List (BitVec 5) := [1, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26]

/-- Expected-output oracle for the concrete decoder test below, not compiler
input. The actual generated program is `copyinDecoded`. -/
def copyinProgram : Program :=
  [ (true, .stack (.save 88#12 1#5 0)),
    (true, .stack (.save 80#12 8#5 1)),
    (true, .stack (.save 72#12 9#5 2)),
    (true, .stack (.save 64#12 18#5 3)),
    (true, .stack (.save 56#12 19#5 4)),
    (true, .stack (.save 48#12 20#5 5)),
    (true, .stack (.save 40#12 21#5 6)),
    (true, .stack (.save 32#12 22#5 7)),
    (true, .stack (.save 24#12 23#5 8)),
    (true, .stack (.save 16#12 24#5 9)),
    (true, .stack (.save 8#12 25#5 10)),
    (true, .stack (.save 0#12 26#5 11)),
    (true, .reg (.addi 96#12 8#5 2#5 (by decide))) ]

/- The entire 13-instruction sequence is checked against the actual binary,
not hand-selected examples. Only the function's frame-size annotation is used. -/
set_option maxHeartbeats 0 in
theorem copyinProgram_binary :
    copyinSaveRows.map (fun row => (MixedAction.decode 12 row.code).map
      (fun a => (row.rvc, a.val))) = copyinProgram.map some := by
  binary_rfl

set_option maxHeartbeats 0 in
theorem copyin_decode_success : decodeProgram 12 copyinSaveRows = some copyinProgram := by
  binary_rfl

noncomputable def copyinDecoded : Program := (decodeProgram 12 copyinSaveRows).getD []

theorem copyinDecoded_eq : copyinDecoded = copyinProgram := by
  rw [copyinDecoded, copyin_decode_success]
  rfl

theorem copyinProgram_safe : ∀ a ∈ copyinProgram, supported a.2 := by
  intro a ha
  simp only [copyinProgram, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [supported]

def savedCells (k : KCtx) (cells : List Stack.Cell) : List Stack.Cell :=
  List.zipWith (fun c r => (c.1, k.regs r)) cells saveRegisters

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem copyinProgram_values (k : KCtx) (cells : Fin 12 → Stack.Cell) :
    evalProgram copyinProgram ⟨k, 0x8000168c#64, List.ofFn cells⟩ =
      ⟨k.setReg 8#5 (k.sp + 96#64), 0x800016a6#64, savedCells k (List.ofFn cells)⟩ := by
  simp [evalProgram, copyinProgram, eval, RegAction.run, Stack.State.machine,
    List.ofFn_succ, savedCells, saveRegisters, instrLen,
    KCtx.rget_ne, KCtx.sp]

theorem copyin_values (k : KCtx) (cells : List Stack.Cell) (length : cells.length = 12)
    (t : Stack.State) (h : Run copyinProgram ⟨k, 0x8000168c#64, cells⟩ t) :
    t = ⟨k.setReg 8#5 (k.sp + 96#64), 0x800016a6#64, savedCells k cells⟩ := by
  have hr := run_exact h copyinProgram_safe
  have repr : cells = List.ofFn (fun i : Fin 12 => cells[i.val]'(by omega)) := by
    apply List.ext_getElem?
    intro i
    by_cases hi : i < cells.length
    · simp only [List.getElem?_eq_getElem hi, List.getElem?_ofFn, length, show i < 12 by omega,
        ↓reduceDIte]
    · simp only [List.getElem?_eq_none (by omega : cells.length ≤ i), List.getElem?_ofFn,
        show ¬ i < 12 by omega, ↓reduceDIte]
  rw [repr, copyinProgram_values] at hr
  simpa only [← repr] using hr

theorem copyin_binary_values (k : KCtx) (cells : List Stack.Cell) (length : cells.length = 12)
    (t : Stack.State) (h : RowRun 12 copyinSaveRows ⟨k, 0x8000168c#64, cells⟩ t) :
    t = ⟨k.setReg 8#5 (k.sp + 96#64), 0x800016a6#64, savedCells k cells⟩ :=
  copyin_values k cells length t (rowRun_compile h _ copyinProgram_binary)

/-- The executable certificate takes only the generated decoder output. -/
theorem copyin_decoded_values (k : KCtx) (cells : List Stack.Cell) (length : cells.length = 12)
    (t : Stack.State) (h : Run copyinDecoded ⟨k, 0x8000168c#64, cells⟩ t) :
    t = ⟨k.setReg 8#5 (k.sp + 96#64), 0x800016a6#64, savedCells k cells⟩ := by
  rw [copyinDecoded_eq] at h
  exact copyin_values k cells length t h

/-- The stack pointer is unchanged through the save body; after the preceding
push, s0 is restored to the entry SP. All twelve cells retain their addresses
and contain ra,s0,s1,s2,...,s10 from before any save or frame-pointer update. -/
theorem copyin_binary_frame (base : BitVec 64) (k : KCtx) (cells : List Stack.Cell)
    (shape : Stack.Shape base 12 ⟨k, 0x8000168c#64, cells⟩)
    (t : Stack.State) (h : RowRun 12 copyinSaveRows ⟨k, 0x8000168c#64, cells⟩ t) :
    t.pc = 0x800016a6#64 ∧ t.ctx.sp = base - 96#64 ∧ t.ctx.regs 8#5 = base ∧
      t.cells = savedCells k cells := by
  have len : cells.length = 12 := by
    simpa [Stack.addresses] using congrArg List.length shape.2
  rw [copyin_binary_values k cells len t h]
  have hsp : k.sp = base - 96#64 := by simpa using shape.1
  refine ⟨rfl, (KCtx.setReg_sp _ _ _ (by decide)).trans hsp, ?_, rfl⟩
  change k.sp + 96#64 = base
  rw [hsp]
  exact BitVec.sub_add_cancel _ _

#print axioms copyinProgram_binary
#print axioms copyin_values
#print axioms copyin_binary_frame

end Xv6.WholeFunction.StackValues
