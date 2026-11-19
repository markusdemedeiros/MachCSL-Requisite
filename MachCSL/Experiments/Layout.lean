import Lean

/-! Route a field lookup using lengths, then apply its observation law.
Unlike search over list equations, these are two deterministic rewrite passes.
Only the supplied definitions/laws are unfolded. -/
namespace MachCSL.Layout

-- A failed arithmetic side condition must reject the rewrite, not recover by
-- inserting an error placeholder. The resulting proof is still kernel checked.
elab "layout_strict " t:Lean.Parser.Tactic.tacticSeq : tactic =>
  Lean.Elab.Term.withoutErrToSorry <| Lean.Elab.Tactic.withoutRecover <|
    Lean.Elab.Tactic.evalTactic t

macro "layout_lookup" " [" rules:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (simp (disch := layout_strict ((try simp only [List.length_append, $rules,*]) <;> omega)) only
      [List.length_append, Nat.reduceAdd, Nat.add_sub_cancel_left, Nat.add_zero, Nat.zero_add,
       List.getElem?_append_left, List.getElem?_append_right, $rules,*]
    <;> simp (disch := layout_strict omega) only [$rules,*] <;> done))

end MachCSL.Layout
