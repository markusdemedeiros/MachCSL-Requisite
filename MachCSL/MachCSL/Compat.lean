/-
MachCSL: Lean v4.34 compatibility shims.  Every root module imports this file.

* `bv_decide` without enum preprocessing.  Since v4.34 `bv_decide` turns equalities on enum
  inductives into `BitVec` equalities through auxiliary declarations (`T.enumToBitVec`, ...) that
  it realizes on demand.  Outside the module system a realized declaration is an ordinary one, so
  two modules that both meet the same enum (`PUnit`, `Iris.HasLC`, ...) clash as soon as a third
  imports both.  No proof here needs the enum support, so plain `bv_decide` runs with `-enums`.

* `if`s (and `decide`s) with a stale `Decidable` instance.  `simp` rewrites an `if`'s condition but leaves its
  instance at the old one; since v4.34 `rw` (e.g. `rw [if_neg _]`) and later `simp` calls check
  terms at reducible transparency and miss or reject such an `if`.  `resyncIteInst`
  re-synthesizes the instance for the new condition -- definitionally the same instance at equal
  arguments.  It is a default simproc, and `simp only [...]` gets it appended (`simp only`
  starts from no simprocs).
-/
import Std.Tactic.BVDecide
import Lean.Meta.Tactic.Simp

macro_rules | `(tactic| bv_decide) => `(tactic| bv_decide -enums)

namespace MachCSL.Compat

open Lean Meta Simp

/-- `@ite α c inst t e` / `@dite α c inst t e` with `inst : Decidable c'`, `c' ≢ c`: re-synthesize. -/
def resyncIteInstCore (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5 do return .continue
  let args := e.getAppArgs
  let c := args[1]!
  if c.hasLooseBVars then return .continue
  let ty ← instantiateMVars (← inferType args[2]!)
  if ty.isAppOfArity ``Decidable 1 && ty.appArg! == c then return .continue
  let inst? ← (try synthInstance? (mkApp (mkConst ``Decidable) c) catch _ => pure none)
  -- (a classical instance stays classical)
  let inst? := inst?.orElse fun _ =>
    if args[2]!.isAppOfArity ``Classical.propDecidable 1 then some (mkApp (mkConst ``Classical.propDecidable) c)
    else none
  let some inst := inst? | return .continue
  let mut args := args.set! 2 inst
  if e.isAppOfArity ``dite 5 then
    if let .lam n _ b bi := args[3]! then args := args.set! 3 (.lam n c b bi)
    if let .lam n _ b bi := args[4]! then args := args.set! 4 (.lam n (mkNot c) b bi)
  return .done (mkAppN e.getAppFn args)

dsimproc resyncIteInst (@ite _ _ _ _ _) := resyncIteInstCore
dsimproc resyncDIteInst (@dite _ _ _ _ _) := resyncIteInstCore

/-- The same for `@decide c inst`. -/
def resyncDecideInstCore (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity ``Decidable.decide 2 do return .continue
  let c := e.appFn!.appArg!
  let inst := e.appArg!
  if c.hasLooseBVars then return .continue
  let ty ← instantiateMVars (← inferType inst)
  if ty.isAppOfArity ``Decidable 1 && ty.appArg! == c then return .continue
  let inst? ← (try synthInstance? (mkApp (mkConst ``Decidable) c) catch _ => pure none)
  let inst? := inst?.orElse fun _ =>
    if inst.isAppOfArity ``Classical.propDecidable 1 then some (mkApp (mkConst ``Classical.propDecidable) c)
    else none
  let some inst' := inst? | return .continue
  return .done (mkApp2 e.appFn!.appFn! c inst')

dsimproc resyncDecideInst (@Decidable.decide _ _) := resyncDecideInstCore

end MachCSL.Compat

open Lean in
macro_rules
  | `(tactic| simp $cfg:optConfig $[$disch:discharger]? only [$args,*] $[$loc:location]?) => do
    -- (once: the expansion is itself a `simp only`)
    if args.getElems.any (fun a => (a.raw.find? fun t =>
        t.isIdent && t.getId.eraseMacroScopes == `MachCSL.Compat.resyncIteInst).isSome) then
      Macro.throwUnsupported
    -- (rebuilt from the elements: a list spliced from an empty array keeps a trailing `,`)
    let e₁ ← `(Lean.Parser.Tactic.simpLemma| MachCSL.Compat.resyncIteInst)
    let e₂ ← `(Lean.Parser.Tactic.simpLemma| MachCSL.Compat.resyncDIteInst)
    let e₃ ← `(Lean.Parser.Tactic.simpLemma| MachCSL.Compat.resyncDecideInst)
    let all : Array (TSyntax [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase,
        `Lean.Parser.Tactic.simpLemma]) := args.getElems ++ #[⟨e₁.raw⟩, ⟨e₂.raw⟩, ⟨e₃.raw⟩]
    `(tactic| simp $cfg:optConfig $[$disch:discharger]? only [$all,*] $[$loc:location]?)
