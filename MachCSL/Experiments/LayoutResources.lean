import MachCSL.ByteWord2
import MachCSL.ByteWord4

namespace MachCSL.Layout
open Iris Iris.BI

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [CurCtx]

/-- Existing separation equivalences can be used by the layout normalizer. -/
theorem append_eq (a : BitVec 64) (dq : DFrac) (xs ys : List (BitVec 8)) :
    byteBuf (GF := GF) a dq (xs ++ ys) =
      iprop(byteBuf a dq xs ∗ byteBuf (a + BitVec.ofNat 64 xs.length) dq ys) :=
  BiEntails.to_eq (byteBuf_append a dq xs ys)

macro "layout_resources" " [" rules:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (simp (disch := assumption) only [List.append_assoc, append_eq, halfBytes_length,
      wordToBytes4_length, wordToBytes_length, BitVec.add_assoc,
      ← ofNat64_add, Nat.reduceAdd, $rules,*]; try exact .rfl))

end MachCSL.Layout
