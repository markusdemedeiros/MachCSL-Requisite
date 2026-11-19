import Lean

/-! Bounded-index list normalization. Prove length once, then reason only about
valid element observations; this avoids manufacturing the out-of-bounds cases
that dominate option-valued extensional proofs. Client definitions are explicit.
The bounded closure uses only the listed collection laws; element extensionality and ambient theorem search are disabled.
The tactic uses existing list theorems and produces an ordinary Lean proof. -/
namespace MachCSL.Collections

macro "collections_eq" " [" rules:Lean.Parser.Tactic.grindParam,* "]" : tactic =>
  `(tactic| (
    apply List.ext_getElem
    · grind (ext := false) (splits := 32) only [List.length_append, List.length_take, List.length_drop,
        List.length_set, List.length_map, List.length_mapIdx, List.length_replicate,
        List.length_range, List.length_nil, List.length_cons, Nat.min_def,
        List.getElem?_eq_some_iff, $rules,*]
    · intro index leftBound rightBound
      grind (ext := false) (splits := 32) only [List.length_append, List.length_take, List.length_drop, List.length_set,
        List.length_map, List.length_mapIdx, List.length_replicate,
        List.length_range, List.length_nil, List.length_cons,
        List.getElem_set, List.getElem_append, List.getElem_take,
        List.getElem_drop, List.getElem_map, List.getElem_mapIdx,
        List.getElem_replicate, List.getElem_range,
        List.getElem?_eq_some_iff, List.getElem?_eq_getElem, List.getElem?_append,
        Option.getD_some, Nat.min_def, $rules,*]))

end MachCSL.Collections
