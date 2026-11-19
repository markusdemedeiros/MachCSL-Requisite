import Experiments.WholeFunction.KernelSymbolic

/-! Pure residual-prefix invariants shared by compiled functions. A state is
an annotated semantic endpoint preceded by a checked symbolic register prefix.
The resource projection is unchanged along that prefix. -/
namespace Xv6.WholeFunction.Residual
open MachCSL

structure View (S D : Type) where
  machine : S → RegState
  resources : S → D
  ext : ∀ s t, resources s = resources t → machine s = machine t → s = t

def Good {S D : Type} (v : View S D) (rows : List Binary.Row)
    (endpoint : S → Prop) (s : S) : Prop :=
  ∃ t cut, v.resources s = v.resources t ∧
    Symbolic.Certificate rows cut (v.machine s) ⟨v.machine t, .cut⟩ ∧ endpoint t

theorem at_endpoint {S D : Type} (v : View S D) (rows : List Binary.Row)
    (endpoint : S → Prop) (s : S) (h : endpoint s) : Good v rows endpoint s :=
  ⟨s, fun _ => true, rfl, .stop _ rfl, h⟩

theorem prepend {S D : Type} {v : View S D} {rows : List Binary.Row}
    {endpoint : S → Prop} {s t : S} {cut : BitVec 64 → Bool}
    (data : v.resources s = v.resources t)
    (pre : Symbolic.Certificate rows cut (v.machine s) ⟨v.machine t, .cut⟩)
    (h : Good v rows endpoint t) : Good v rows endpoint s := by
  obtain ⟨goal, finalCut, hd, cert, he⟩ := h
  exact ⟨goal, finalCut, data.trans hd, pre.append rfl cert, he⟩

theorem endpoint_of_no_decode {S D : Type} {v : View S D} {rows : List Binary.Row}
    {endpoint : S → Prop} {s : S} (h : Good v rows endpoint s)
    (absent : findReg (v.machine s).pc rows = none) : endpoint s := by
  obtain ⟨goal, cut, hd, cert, he⟩ := h
  rcases cert.cut_cases rfl with same | ⟨r, found, _, _⟩
  · exact (v.ext s goal hd same).symm ▸ he
  · rw [absent] at found
    cases found

theorem decode_or_endpoint {S D : Type} {v : View S D} {rows : List Binary.Row}
    {endpoint : S → Prop} {s : S} (h : Good v rows endpoint s) :
    endpoint s ∨ ∃ r, findReg (v.machine s).pc rows = some r := by
  obtain ⟨goal, cut, hd, cert, he⟩ := h
  rcases cert.cut_cases rfl with same | ⟨r, found, _, _⟩
  · exact Or.inl ((v.ext s goal hd same).symm ▸ he)
  · exact Or.inr ⟨r, found⟩

/-- A genuine decoded register step consumes one certified prefix action.
No function-specific PC enumeration or register update proof appears here. -/
theorem advance {S D : Type} {v : View S D} {rows : List Binary.Row}
    {endpoint : S → Prop} {s t : S} (h : Good v rows endpoint s)
    (terminal : ∀ s, endpoint s → findReg (v.machine s).pc rows = none)
    (r : LocatedReg (v.machine s).pc) (found : findReg (v.machine s).pc rows = some r)
    (cpu : CPU) (data : v.resources t = v.resources s)
    (machine : v.machine t = r.action.run r.row.rvc cpu (v.machine s)) : Good v rows endpoint t := by
  obtain ⟨goal, cut, hd, cert, he⟩ := h
  rcases cert.cut_cases rfl with same | ⟨r', found', free, tail⟩
  · have es : endpoint s := (v.ext s goal hd same).symm ▸ he
    rw [terminal s es] at found
    cases found
  · rw [found] at found'
    cases Option.some.inj found'
    refine ⟨goal, cut, data.trans hd, ?_, he⟩
    rw [machine, Symbolic.run_independent r.action r.row.rvc (v.machine s) cpu free]
    exact tail

theorem indices {S D : Type} {v : View S D} {rows : List Binary.Row}
    {endpoint : S → Prop} {s : S} {sie : Bool} {proc : BitVec 64}
    (h : Good v rows endpoint s)
    (ends : ∀ s, endpoint s → (v.machine s).ctx.sie = sie ∧ (v.machine s).ctx.proc = proc) :
    (v.machine s).ctx.sie = sie ∧ (v.machine s).ctx.proc = proc := by
  obtain ⟨t, cut, _, cert, he⟩ := h
  have hi := cert.indices
  have ht := ends t he
  exact ⟨hi.1.symm.trans ht.1, hi.2.symm.trans ht.2⟩

end Xv6.WholeFunction.Residual
