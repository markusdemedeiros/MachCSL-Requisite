import Experiments.SolverSurvey.MapOverlay
import Lean.Util.CollectAxioms

/-! The production log-write interface with unchanged ownership, masks, and
postcondition. Only deterministic map reconstruction is delegated. -/
namespace Experiments.MapOverlay.Checks
open Xv6 Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FsBlocksG GF]

set_option maxHeartbeats 1000000 in
theorem byteRange_log_update (E : CoPset) (gL gc gX : GName) (homeL : List Nat)
    (Xv : Nat → List (BitVec 8)) (C : BlockMap) (b off : Nat)
    (subOld subNew bsOld : List (BitVec 8))
    (hE : (↑logN : CoPset) ⊆ E) (hoff : off + subOld.length ≤ BSIZE)
    (hpos : 0 < subOld.length)
    (hshape : bsOld.length = BSIZE → subNew.length = subOld.length) :
    fsBytesInv (GF := GF) gL gc gX homeL Xv -∗ excSealed gX -∗ (gc ↪●MAP C) -∗
      byteRange gL b off subOld -∗ (gc ↪◯MAP[b]{DFrac.own (1 : Qp).half} bsOld) -∗
      |={E}=> (⌜PartialMap.get? C b = some bsOld ∧ bsOld.length = BSIZE ∧
                 subOld = (bsOld.drop off).take subOld.length⌝ ∗
        (gc ↪●MAP PartialMap.insert C b (blkSplice off subNew bsOld)) ∗
        byteRange gL b off subNew ∗
        (gc ↪◯MAP[b]{DFrac.own (1 : Qp).half} (blkSplice off subNew bsOld))) := by
  unfold fsBytesInv
  iintro #Hinv #Hseal Hca Hr Hm
  ihave Hacc := inv_acc (E := E) (N := fsbN) (P := fsBytesBody gL gc gX homeL Xv)
    (fsbN_sub E hE) $$ Hinv
  imod Hacc with ⟨Hbody, Hclose⟩
  unfold fsBytesBody
  icases Hbody with ⟨%L, %C0, %X0, >Ha, >HC, >Hxa, >%hok⟩
  ihave %hxeq := excSealedEmpty gX X0 $$ Hxa Hseal
  subst hxeq
  ihave %hsub := byteRange_lookup gL L b off subOld $$ Ha Hr
  have hb : b ∈ homeL :=
    bytesDom_home L homeL b off subOld hok.bdom (by omega) hpos hsub
  obtain ⟨bsi, hbi⟩ := (hok.dom b).2 hb
  icases BigSepM.bigSepM_insert_acc (Φ := fun b bs =>
    iprop(gc ↪◯MAP[b]{DFrac.own (1 : Qp).half} bs)) hbi $$ HC with ⟨Hi, Hback⟩
  ihave %hbso := ghost_map_elem_agree gc b (DFrac.own (1 : Qp).half)
    (DFrac.own (1 : Qp).half) bsOld bsi $$ [Hm Hi]
  case' _ => iframe Hm Hi
  subst hbso
  have hlbo : bsOld.length = BSIZE := hok.lens b bsOld hbi
  have hshape' : subNew.length = subOld.length := hshape hlbo
  have htie : bytesTie L C0 := (bytesTieExc_empty L C0).1 hok.tie
  have hslice : subOld = (bsOld.drop off).take subOld.length :=
    mapSeq_slice bsOld subOld (b * BSZ) off L (by rw [hlbo]; omega) (htie b bsOld hbi) hsub
  icases cacheJoin gc b bsOld bsOld $$ [Hm Hi] with ⟨He, -⟩
  · iframe Hm Hi
  ihave %hclk := ghost_map_lookup $$ Hca He
  imod (ghost_map_update (γ := gc) (m := C) (k := b) (v := bsOld)
    (blkSplice off subNew bsOld)) $$ Hca He with ⟨Hca, He⟩
  icases cacheSplit gc b (blkSplice off subNew bsOld) $$ He with ⟨Hm, Hi⟩
  imod byteRange_update gL L b off subOld subNew hshape' $$ Ha Hr with ⟨Ha, Hr⟩
  ihave HC := Hback $$ %(blkSplice off subNew bsOld) Hi
  ihave Hcl := Hclose $$ [Ha HC Hxa]
  case' _ =>
    inext
    iexists (PartialMap.union (mapSeq (b * BSZ + off) subNew) L),
      (PartialMap.insert C0 b (blkSplice off subNew bsOld)), ([] : List Nat)
    iframe Ha HC Hxa
    ipureintro
    exact cache_splice _ L C0 homeL Xv b off subNew bsOld hok hbi
      (by omega) (isOverlay_union _ _)
  imod Hcl
  imodintro
  iframe Hca Hr Hm
  ipureintro
  exact ⟨hclk, hlbo, hslice⟩


/-- Moving the patch one byte changes the actual finite map. -/
theorem reject_wrong_address :
    ¬ isOverlay (mapSeq 0 [1#8]) (mapSeq 1 [1#8]) (mapSeq 0 []) := by
  intro h
  have mismatch := h 0
  simp [mapSeq_get?] at mismatch

/-- Reversing overlay priority destroys written values. -/
theorem reject_wrong_priority :
    ¬ isOverlay (mapSeq 0 [0#8]) (mapSeq 0 [1#8]) (mapSeq 0 [0#8]) := by
  intro h
  have mismatch := h 0
  simp [mapSeq_get?] at mismatch

example : True := by
  fail_if_success
    have overrun : isOverlay (mapSeq 0 (blkSplice 1 [1#8] []))
        (mapSeq 1 [1#8]) (mapSeq 0 []) := by
      apply splice_overlay
      decide
  trivial

open Lean Elab Command in
/-- info: Map overlay: unchanged statements, independent proofs, no additional axioms -/
#guard_msgs in
run_cmd do
  let pairs := #[( ``Experiments.MapOverlay.splice_sub, ``Xv6.mapSeq_splice_sub),
    (``Experiments.MapOverlay.other_sub, ``Xv6.mapSeq_other_sub),
    (``byteRange_log_update, ``Xv6.byteRange_log_update)]
  let forbidden := pairs.map Prod.snd
  let env ← getEnv
  for (candidate, original) in pairs do
    let ci ← getConstInfo candidate
    let oi ← getConstInfo original
    unless ← liftTermElabM <| Meta.isDefEq ci.type oi.type do
      throwError "Changed statement: {candidate}"
    let allowed ← liftCoreM <| collectAxioms original
    for ax in (← liftCoreM <| collectAxioms candidate) do
      unless allowed.contains ax do throwError "New assumption: {candidate}: {ax}"
    let mut pending := #[candidate]
    let mut seen : NameSet := {}
    while !pending.isEmpty do
      let current := pending.back!
      pending := pending.pop
      unless seen.contains current do
        seen := seen.insert current
        if forbidden.contains current then throwError "Original proof reused: {candidate}: {current}"
        if let some info := env.find? current then
          pending := pending ++ info.type.getUsedConstants
          if let some value := info.value? then pending := pending ++ value.getUsedConstants
  let standard := #[``propext, ``Classical.choice, ``Quot.sound]
  for declaration in #[``splice_overlay, ``cache_splice, ``reject_wrong_address, ``reject_wrong_priority] do
    for ax in (← liftCoreM <| collectAxioms declaration) do
      unless standard.contains ax do throwError "Unexpected assumption: {declaration}: {ax}"
  logInfo "Map overlay: unchanged statements, independent proofs, no additional axioms"

end Experiments.MapOverlay.Checks
