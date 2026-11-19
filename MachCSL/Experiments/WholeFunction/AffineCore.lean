import MachCSL.KCtx

namespace Xv6.WholeFunction.Affine
open MachCSL

/-- A bounded-search candidate, interpreted modulo the machine word width. -/
structure Rule where
  register : BitVec 5
  anchor : Int
  counter : Int
  offset : Int
  deriving Repr, DecidableEq

def Rule.value (r : Rule) (base : BitVec 64) (iteration : Nat) : BitVec 64 :=
  BitVec.ofInt 64 r.anchor * base +
    BitVec.ofInt 64 r.counter * BitVec.ofNat 64 iteration + BitVec.ofInt 64 r.offset

def Holds (rules : List Rule) (base : BitVec 64) (iteration : Nat) (k : KCtx) : Prop :=
  ∀ rule ∈ rules, k.regs rule.register = rule.value base iteration

end Xv6.WholeFunction.Affine
