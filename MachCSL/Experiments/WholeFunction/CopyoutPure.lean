import Experiments.WholeFunction.CopyinPure
import Experiments.WholeFunction.CopyoutModel

namespace Xv6.WholeFunction.Copyout
open MachCSL LeanRV64D
open Experiments.WholeFunction.Copy

-- The page cursor arithmetic is shared with COPYIN, not re-proved per loop.
export Copyin (chunkSize chunk_facts next_cursor wrapped_toNat rounded_source chunk_register_updates)

theorem not_writable_of_unreadable {P : UPtd} {a : Nat} (h : ¬ uvaRmapped P a) :
    ¬ uvaWmapped P a := by
  rintro ⟨vpn, w, j, leaf, readable, _, bound, address⟩
  exact h ⟨vpn, w, j, leaf, readable, bound, address⟩

theorem not_writable_max {P : UPtd} {a : Nat} (wf : uptWf P) (high : 2 ^ 38 ≤ a) :
    ¬ uvaWmapped P a := by
  rintro ⟨vpn, w, j, leaf, _, _, bound, address⟩
  have hb := (wf.1 vpn w leaf).1
  rw [tfVpn_toNat] at hb
  omega

theorem not_writable_of_leaf {P : UPtd} {a : Nat} {w : BitVec 64}
    (leaf : Iris.Std.PartialMap.get? P.um (a / 4096) = some w)
    (readonly : w &&& PTE_W = 0#64) : ¬ uvaWmapped P a := by
  rintro ⟨vpn, w', j, lookup, _, writable, bound, address⟩
  have hvpn : a / 4096 = vpn := by omega
  rw [hvpn, lookup] at leaf
  cases Option.some.inj leaf
  exact writable readonly

theorem page_writable_chunk (P : UPtd) (a : BitVec 64) (d n : Nat) (w : BitVec 64)
    (leaf : Iris.Std.PartialMap.get? P.um ((a.toNat + d) / 4096) = some w)
    (readable : pteVU w) (writable : w &&& PTE_W ≠ 0#64)
    (fit : (a.toNat + d) % 4096 + n ≤ 4096)
    (pageBound : (a.toNat + d) / 4096 * 4096 < 2 ^ 38) :
    ∀ j, j < n → uvaWmapped P (a + BitVec.ofNat 64 (d + j)).toNat := by
  intro j hj
  rw [wrapped_toNat a (d + j) (by omega)]
  exact ⟨(a.toNat + d) / 4096, w, (a.toNat + d) % 4096 + j,
    leaf, readable, writable, by omega, by omega⟩

theorem write_chunk_step (sz a : BitVec 64) (s : Experiments.WholeFunction.Copy.State)
    (bs : List (BitVec 8)) (w : BitVec 64) (positive : 0 < bs.length)
    (leaf : Iris.Std.PartialMap.get? s.table.um ((a.toNat + s.copied.length) / 4096) = some w)
    (readable : pteVU w) (writable : w &&& PTE_W ≠ 0#64)
    (fit : (a.toNat + s.copied.length) % 4096 + bs.length ≤ 4096)
    (pageBound : (a.toNat + s.copied.length) / 4096 * 4096 < 2 ^ 38) :
    Step .write sz a s (transfer .write a s bs) := by
  apply Step.chunk
  · exact positive
  · exact fit
  · exact UMemL.umMapped_page fit (by rw [leaf]; rfl)
  · exact page_writable_chunk s.table a s.copied.length bs.length w leaf readable writable fit pageBound
  · intro impossible
    cases impossible

end Xv6.WholeFunction.Copyout

open Lean in
run_cmd do
  for decl in #[``Xv6.WholeFunction.Copyout.not_writable_max,
      ``Xv6.WholeFunction.Copyout.not_writable_of_leaf,
      ``Xv6.WholeFunction.Copyout.write_chunk_step] do
    let axs ← collectAxioms decl
    unless axs.all (fun a => #[``propext, ``Classical.choice, ``Quot.sound].contains a) do
      throwError "{decl}: unexpected axioms {axs}"
