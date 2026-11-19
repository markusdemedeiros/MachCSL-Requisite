import Experiments.WholeFunction.KernelFull

/-! Owned byte buffers for the extensible function compiler. Buffer fractions
and boundaries are explicit; ordinary separation logic supplies alias safety.
The existing byteBuf access/update lemmas remain the single byte-level lens. -/
namespace Xv6.WholeFunction.Memory
open Iris Iris.BI Iris.ProgramLogic MachCSL LeanRV64D

structure Buffer where
  base : BitVec 64
  fraction : DFrac
  bytes : List (BitVec 8)

structure State where
  machine : Stack.State
  buffers : List Buffer

def State.withMachine (s : State) (machine : Stack.State) : State := ⟨machine, s.buffers⟩

structure Access where
  buffer : Nat
  index : Nat

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [CurCtx]

def Buffer.owns (buffer : Buffer) : IProp GF := byteBuf buffer.base buffer.fraction buffer.bytes

def owns (buffers : List Buffer) : IProp GF := iprop%
  [∗list] buffer ∈ buffers, buffer.owns

def payload (s : State) : IProp GF := owns s.buffers

theorem buffer_read (buffers : List Buffer) (j : Nat) (buffer : Buffer)
    (found : buffers[j]? = some buffer) :
    owns (GF := GF) buffers ⊢ buffer.owns ∗ (buffer.owns -∗ owns buffers) := by
  unfold owns
  iintro H
  icases BigSepL.bigSepL_insert_acc (Φ := fun (_ : Nat) (b : Buffer) => b.owns (GF := GF)) found $$ H
    with ⟨Hbuffer, Hclose⟩
  iframe Hbuffer
  iintro Hbuffer
  have hlt : j < buffers.length := (List.getElem?_eq_some_iff.mp found).1
  have hb : buffers[j] = buffer := (List.getElem?_eq_some_iff.mp found).2
  have same : buffers.set j buffer = buffers := by rw [← hb]; exact List.set_getElem_self hlt
  have restore : owns (GF := GF) (buffers.set j buffer) ⊢ owns buffers := by rw [same]
  unfold owns at restore
  iapply restore
  iapply Hclose $$ %buffer Hbuffer

theorem buffer_update (buffers : List Buffer) (j : Nat) (buffer : Buffer)
    (found : buffers[j]? = some buffer) :
    owns (GF := GF) buffers ⊢ buffer.owns ∗
      (∀ buffer' : Buffer, buffer'.owns -∗ owns (buffers.set j buffer')) := by
  unfold owns
  exact BigSepL.bigSepL_insert_acc (Φ := fun (_ : Nat) (b : Buffer) => b.owns (GF := GF)) found

end Xv6.WholeFunction.Memory
