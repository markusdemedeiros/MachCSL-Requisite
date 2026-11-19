import Experiments.WholeFunction.KernelReg

/-! Checked compilation from actual decoder output to register/control actions.
Unsupported operations return `none`; they cannot silently become fallthrough.
-/
namespace Xv6.WholeFunction
open MachCSL LeanRV64D

/-- The dependent output includes the correspondence proof. The definition
uses neither a second instruction decoder nor a table of handwritten ASTs. -/
def RegAction.decode (i : instruction) : Option {a : RegAction // i = a.code} :=
  match i with
  | .ITYPE (imm, .Regidx rs, .Regidx rd, .ADDI) =>
    if h : rdOk rd then some ⟨.addi imm rd rs h, rfl⟩ else none
  | .ADDIW (imm, .Regidx rs, .Regidx rd) =>
    if h : rdOk rd then some ⟨.addiw imm rd rs h, rfl⟩ else none
  | .ITYPE (imm, .Regidx rs, .Regidx rd, .ANDI) =>
    if h : rdOk rd then some ⟨.andi imm rd rs h, rfl⟩ else none
  | .SHIFTIOP (shamt, .Regidx rs, .Regidx rd, .SRLI) =>
    if h : rdOk rd then some ⟨.srli shamt rd rs h, rfl⟩ else none
  | .RTYPE (.Regidx rt, .Regidx rs, .Regidx rd, .ADD) =>
    if h : rdOk rd then some ⟨.add rd rs rt h, rfl⟩ else none
  | .RTYPE (.Regidx rt, .Regidx rs, .Regidx rd, .SUB) =>
    if h : rdOk rd then some ⟨.sub rd rs rt h, rfl⟩ else none
  | .RTYPEW (.Regidx rt, .Regidx rs, .Regidx rd, .SUBW) =>
    if h : rdOk rd then some ⟨.subw rd rs rt h, rfl⟩ else none
  | .RTYPEW (.Regidx rt, .Regidx rs, .Regidx rd, .ADDW) =>
    if h : rdOk rd then some ⟨.addw rd rs rt h, rfl⟩ else none
  | .RTYPE (.Regidx rt, .Regidx rs, .Regidx rd, .AND) =>
    if h : rdOk rd then some ⟨.and rd rs rt h, rfl⟩ else none
  | .UTYPE (imm, .Regidx rd, .LUI) =>
    if h : rdOk rd then some ⟨.lui imm rd h, rfl⟩ else none
  | .BTYPE (imm, .Regidx rt, .Regidx rs, op) =>
    if h : rs ≠ 0#5 ∨ rt ≠ 0#5 then some ⟨.branch imm rs rt h op, rfl⟩ else none
  | .JAL (imm, .Regidx 0#5) => some ⟨.jump imm, rfl⟩
  | .JALR (0#12, .Regidx rs, .Regidx 0#5) => some ⟨.ret rs, rfl⟩
  | _ => none

/-- A successful compiler output ties symbolic transfer to the actual kernel
bytes through the row's M/S Sail decode certificates. -/
structure RegRow where
  binary : Binary.Row
  action : RegAction
  correct : binary.code = action.code

def compileRegRow (row : Binary.Row) : Option RegRow :=
  (RegAction.decode row.code).map fun a => ⟨row, a.val, a.property⟩

end Xv6.WholeFunction
