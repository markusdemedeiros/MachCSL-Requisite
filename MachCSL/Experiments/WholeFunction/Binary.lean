import Xv6.CodeTactics

/-! The binary-facing input of a whole-function compiler. Every row carries
the actual Sail decoder's M/S certificates, so its instruction resource is
obtained from kernelText, not from a second instruction semantics.

`Flow` is a conservative syntactic index for the compiler. It is NOT itself
an operational semantics theorem: compilation must still discharge the Sail
execution obligation for each row (including faults and interference).
-/
namespace Xv6.WholeFunction.Binary
open LeanRV64D MachCSL Iris BI

noncomputable section

structure Row where
  pc : BitVec 64
  rvc : Bool
  code : instruction
  original : instruction
  machine : textDecodeWith drefM pc = some (rvc, code, original)
  supervisor : textDecodeWith drefS pc = some (rvc, code, original)

theorem Row.instr {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] (r : Row) :
    kernelText (GF := GF) ⊢ MachCSL.instr r.pc r.rvc r.code :=
  text_instr r.pc r.rvc r.code r.original r.machine r.supervisor

def decodedAt (pc : BitVec 64) : Bool × instruction × instruction :=
  (textDecodeWith drefM pc).getD
    (false, .ILLEGAL 0#32, .ILLEGAL 0#32)

def rowAt (pc : BitVec 64)
    (hM : textDecodeWith drefM pc = some (decodedAt pc))
    (hS : textDecodeWith drefS pc = some (decodedAt pc)) : Row :=
  ⟨pc, (decodedAt pc).1, (decodedAt pc).2.1,
    (decodedAt pc).2.2, hM, hS⟩

def Row.next (r : Row) : BitVec 64 := r.pc + if r.rvc then 2#64 else 4#64

/-- All indirect transfer operands are retained. In particular a return is
not assumed to land at a particular continuation. -/
inductive Flow where
  | next (pc : BitVec 64)
  | branch (taken other : BitVec 64)
  | jump (pc : BitVec 64)
  | call (target resume : BitVec 64) (link : regidx)
  | indirect (offset : BitVec 12) (base link : regidx)
  | unsupported
  deriving BEq, Repr

def Row.flow (r : Row) : Flow :=
  match r.code with
  | .BTYPE (imm, _, _, _) => .branch (r.pc + imm.signExtend 64) r.next
  | .JAL (imm, rd) =>
    if rd == .Regidx 0#5 then .jump (r.pc + imm.signExtend 64)
    else .call (r.pc + imm.signExtend 64) r.next rd
  | .JALR (imm, rs, rd) => .indirect imm rs rd
  | .UTYPE _ | .ITYPE _ | .SHIFTIOP _ | .RTYPE _ | .LOAD _ | .STORE _
  | .ADDIW _ | .RTYPEW _ | .SHIFTIWOP _ => .next r.next
  | _ => .unsupported

/-- Check the complete, contiguous instruction partition. No assumption is
made that padding is executable: unsupported encodings fail `closed`. -/
def contiguous (start finish : BitVec 64) : List Row → Bool
  | [] => start == finish
  | r :: rs => start == r.pc && contiguous r.next finish rs

def memberPc (rows : List Row) (pc : BitVec 64) : Bool :=
  rows.any (fun r => r.pc == pc)

def closed (rows : List Row) : Bool := rows.all fun r =>
  match r.flow with
  | .next p | .jump p => memberPc rows p
  | .branch p q => memberPc rows p && memberPc rows q
  | .call _ resume _ => memberPc rows resume
  | .indirect _ _ _ => true
  | .unsupported => false

structure Function where
  entry : BitVec 64
  finish : BitVec 64
  rows : List Row
  covers : contiguous entry finish rows = true
  localEdges : closed rows = true

def Function.fetch? (f : Function) (pc : BitVec 64) : Option Row :=
  f.rows.find? (fun r => r.pc == pc)

theorem Function.fetch_instr {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
    (f : Function) (pc : BitVec 64) (r : Row) (h : f.fetch? pc = some r) :
    kernelText (GF := GF) ⊢ MachCSL.instr pc r.rvc r.code := by
  have hp : r.pc = pc := by
    have := List.find?_some h
    simpa only [beq_iff_eq] using this
  simpa only [hp] using r.instr (GF := GF)

/-- Direct calls are explicitly boundaries. Their callee contracts must be
provided to the compiler; their bodies are not silently treated as local. -/
def Function.calls (f : Function) : List (BitVec 64 × BitVec 64 × BitVec 64) :=
  f.rows.filterMap fun r => match r.flow with
    | .call target resume _ => some (r.pc, target, resume)
    | _ => none

def Function.backedges (f : Function) : List (BitVec 64 × BitVec 64) :=
  f.rows.flatMap fun r =>
    let targets := match r.flow with
      | .branch p q => [p, q]
      | .jump p => [p]
      | _ => []
    targets.filterMap fun p => if p.toNat ≤ r.pc.toNat then some (r.pc, p) else none

def Function.indirects (f : Function) : List (BitVec 64 × Flow) :=
  f.rows.filterMap fun r => match r.flow with
    | .indirect a b c => some (r.pc, .indirect a b c)
    | _ => none

end

open Lean Meta Elab Tactic in
elab "binary_rfl" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let tgt ← instantiateMVars (← g.getType)
    let some (_, lhs, _) := tgt.eq? | throwError "expected equality"
    let pf ← mkEqRefl lhs
    let aux ← mkAuxTheorem tgt pf
    g.assign aux
    replaceMainGoal []

end Xv6.WholeFunction.Binary
