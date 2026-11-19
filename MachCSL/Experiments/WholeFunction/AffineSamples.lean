import Experiments.WholeFunction.MemoryPrefix
import Experiments.WholeFunction.MemoryActions
import Experiments.WholeFunction.StrlenBinary

/-! Discovery data, not a correctness argument. The actual decoded register
prefixes and byte-load semantics determine every observed register value.
No existing STRLEN invariant or register-role assignment is imported. -/
namespace Xv6.WholeFunction.Affine
open MachCSL LeanRV64D
set_option linter.unusedSimpArgs false

def scanCut (pc : BitVec 64) : Bool := pc == 0x80000eb8#64 || pc == 0x80000ec2#64

def sampleRegs (base seed : Nat) : RegMap := fun r =>
  if r = 10#5 then BitVec.ofNat 64 base
  else BitVec.ofNat 64 (seed * (r.toNat + 17) + r.toNat * r.toNat)

structure ByteRow where
  row : Binary.Row
  action : Memory.Op
  decoded : row.code = action.code
  pc : BitVec 64
  rvc : Bool
  address : pc = row.pc
  width : rvc = row.rvc

open Lean Meta Elab Term in
elab "derive_affine_byte " row:term : term => do
  let row ← elabTerm row (some (mkConst ``Binary.Row))
  let code ← mkAppM ``Binary.Row.code #[row]
  let decoded ← withTransparency .all <| whnf (← mkAppM ``Memory.Op.decode #[code])
  unless decoded.isAppOfArity ``Option.some 2 do throwError "unsupported byte row"
  let action ← withTransparency .all <| reduce (← mkAppM ``Subtype.val #[decoded.getAppArgs[1]!])
  let args ← action.getAppArgs.mapM fun arg => do
    if ← isProof arg then mkAuxTheorem (← inferType arg) arg
    else
      let ty ← inferType arg
      if ty.isAppOfArity ``BitVec 1 then
        let value ← withTransparency .all <| reduce (← mkAppM ``BitVec.toNat #[arg])
        let width ← withTransparency .all <| reduce ty.getAppArgs[0]!
        pure (mkApp2 (mkConst ``BitVec.ofNat) width value)
      else pure arg
  let action := mkAppN action.getAppFn args
  let actual ← mkAppM ``Memory.Op.code #[action]
  unless ← withTransparency .all <| isDefEq code actual do throwError "byte decode did not replay"
  let proof ← mkAuxTheorem (← mkEq code actual) (← mkEqRefl code)
  let rawPc ← mkAppM ``Binary.Row.pc #[row]
  let pcNat ← withTransparency .all <| reduce (← mkAppM ``BitVec.toNat #[rawPc])
  let pc := mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 64) pcNat
  let rawRvc ← mkAppM ``Binary.Row.rvc #[row]
  let rvc ← withTransparency .all <| reduce rawRvc
  let address ← mkAuxTheorem (← mkEq pc rawPc) (← mkEqRefl pc)
  let width ← mkAuxTheorem (← mkEq rvc rawRvc) (← mkEqRefl rvc)
  mkAppM ``ByteRow.mk #[row,action,proof,pc,rvc,address,width]

noncomputable def firstByte : ByteRow := derive_affine_byte Binary.strlen_008
noncomputable def scanByte : ByteRow := derive_affine_byte Binary.strlen_016

def readResult (input : ByteRow) (k : KCtx) (byte : BitVec 8) : RegState :=
  (input.action.run input.rvc Memory.canonical ⟨0,0⟩ ⟨⟨k,input.pc,[]⟩,[]⟩
    ⟨0#64, .own 1, []⟩ byte).machine.machine

noncomputable def firstRead (k : KCtx) : RegState :=
  readResult firstByte k 1#8
noncomputable def nextRead (k : KCtx) : RegState :=
  readResult scanByte k 1#8

def Observation (_base _seed _iteration : Nat) (_state : RegState) : Prop := True

open Lean Meta Elab Tactic in
elab "affine_observe" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let goal ← instantiateMVars (← g.getType)
    unless goal.isAppOfArity ``Observation 4 do throwError "expected Observation"
    let args := goal.getAppArgs
    let pc ← withTransparency .all <| whnf
      (← mkAppM ``BitVec.toNat #[← mkAppM ``RegState.pc #[args[3]!]])
    unless (← getNatValue? pc) == some 0x80000eb8 do
      throwError "observation was not at the declared scan boundary"
    let mut theorems ← getSimpTheorems
    theorems := theorems.addDeclToUnfoldCore ``sampleRegs
    for name in #[``KCtx.setReg_regs, ``KCtx.withRegs_regs, ``RegMap.set_apply, ``KCtx.rget_eq] do
      theorems ← theorems.addConst name
    let context ← Simp.mkContext (simpTheorems := #[theorems])
    let procedures ← Simp.getSimprocs
    let mut records : Array Json := #[]
    for base in #[0, 37, 2147483647, 18446744073709551613] do
      for seed in #[3, 29] do
        let state := args[3]!.replace fun e =>
          if e == args[0]! then some (mkNatLit base)
          else if e == args[1]! then some (mkNatLit seed) else none
        let regs ← mkAppM ``KCtx.regs #[← mkAppM ``RegState.ctx #[state]]
        let mut values : Array Json := #[]
        for reg in List.range 32 do
          let r := mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 5) (mkNatLit reg)
          let (value, _) ← Meta.simp (← mkAppM ``BitVec.toNat #[mkApp regs r]) context
            (simprocs := #[procedures])
          let value := value.expr
          let some value ← getNatValue? value | throwError "non-numeric observation: {value}"
          values := values.push (toJson value)
        let iteration ← withTransparency .all <| reduce args[2]!
        let some iteration ← getNatValue? iteration | throwError "non-numeric iteration"
        records := records.push (Json.mkObj [("base",toJson base), ("seed",toJson seed),
          ("iteration",toJson iteration), ("registers",Json.arr values)])
    logInfo m!"AFFINE_SAMPLES {Json.compress (Json.arr records)}"
    g.assign (mkConst ``True.intro)
    replaceMainGoal []

set_option maxHeartbeats 800000 in
theorem observed_prefixes (k : KCtx) (base seed : Nat) :
    Symbolic.Prefix Binary.strlen.rows scanCut (firstRead (k.withRegs (sampleRegs base seed)))
      (fun r₁ => Observation base seed 1 r₁ ∧
        Symbolic.Prefix Binary.strlen.rows scanCut (nextRead r₁.ctx)
          (fun r₂ => Observation base seed 2 r₂ ∧
            Symbolic.Prefix Binary.strlen.rows scanCut (nextRead r₂.ctx)
              (Observation base seed 3))) := by
  dsimp only [firstRead, nextRead, readResult, firstByte, scanByte, Memory.Op.run, Stack.State.machine]
  prefix_step
  simp only [KCtx.setReg_regs, RegMap.set_apply, bcond,
    show (1#8).setWidth 64 = 1#64 from rfl,
    BitVec.reduceEq, Bool.false_eq_true, ↓reduceIte]
  symbolic_prefix 8
  all_goals simp_all only [bcond, KCtx.setReg_regs, RegMap.set_apply,
    BitVec.reduceEq, Bool.false_eq_true, ↓reduceIte]
  constructor
  · affine_observe
  · prefix_step
    simp only [KCtx.setReg_regs, RegMap.set_apply, bcond,
      show (1#8).setWidth 64 = 1#64 from rfl,
      BitVec.reduceEq, Bool.false_eq_true, ↓reduceIte]
    symbolic_prefix 8
    all_goals simp_all only [bcond, KCtx.setReg_regs, RegMap.set_apply,
      BitVec.reduceEq, Bool.false_eq_true, ↓reduceIte]
    constructor
    · affine_observe
    · prefix_step
      simp only [KCtx.setReg_regs, RegMap.set_apply, bcond,
        show (1#8).setWidth 64 = 1#64 from rfl,
        BitVec.reduceEq, Bool.false_eq_true, ↓reduceIte]
      symbolic_prefix 8
      all_goals simp_all only [bcond, KCtx.setReg_regs, RegMap.set_apply,
        BitVec.reduceEq, Bool.false_eq_true, ↓reduceIte]
      affine_observe

end Xv6.WholeFunction.Affine
