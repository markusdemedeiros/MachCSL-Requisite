import Experiments.WholeFunction.CopyContracts

namespace Experiments.WholeFunction.Copy

open Xv6

/-- The write loop chooses each chunk from the current source cursor.
Its full source-prefix equation is derived by induction, not supplied on exit. -/
inductive WriteRun (sz a : BitVec 64) (src : List (BitVec 8))
    (P : UPtd) (M : Image) (ke : Nat) : State → Prop
  | start : WriteRun sz a src P M ke (initial P M ke)
  | fault {s : State} (h : WriteRun sz a src P M ke s) (Q : UPtd) (ke' : Nat)
      (he : s.table.extSz sz Q) (hk : s.lend ≤ ke') :
      WriteRun sz a src P M ke (extend s Q ke')
  | chunk {s : State} (h : WriteRun sz a src P M ke s) (bs : List (BitVec 8))
      (step : Step .write sz a s (transfer .write a s bs))
      (bound : s.copied.length + bs.length ≤ src.length)
      (source : bs = (src.drop s.copied.length).take bs.length) :
      WriteRun sz a src P M ke (transfer .write a s bs)

theorem prefix_append (src : List (BitVec 8)) (d n : Nat) :
    src.take d ++ (src.drop d).take n = src.take (d + n) := by
  rw [List.take_drop]
  have h := List.take_append_drop d (src.take (d + n))
  simpa only [List.take_take, Nat.min_eq_left (Nat.le_add_right d n)] using h

theorem write_run_certificate {sz a : BitVec 64} {src : List (BitVec 8)}
    {P : UPtd} {M : Image} {ke : Nat} {s : State}
    (h : WriteRun sz a src P M ke s) :
    Trace .write sz a (initial P M ke) s ∧ s.copied.length ≤ src.length ∧
      s.copied = src.take s.copied.length := by
  induction h with
  | start => exact ⟨.refl _, Nat.zero_le _, rfl⟩
  | fault h Q ke' he hk ih =>
    exact ⟨.snoc ih.1 (.fault _ Q ke' he hk), ih.2⟩
  | chunk h bs hs hb hsrc ih =>
    rename_i s
    refine ⟨.snoc ih.1 hs, ?_, ?_⟩
    · simpa only [transfer, List.length_append] using hb
    · change s.copied ++ bs = src.take (s.copied ++ bs).length
      rw [List.length_append]
      calc s.copied ++ bs = src.take s.copied.length ++ (src.drop s.copied.length).take bs.length :=
             (congrArg (· ++ bs) ih.2.2).trans (congrArg (src.take s.copied.length ++ ·) hsrc)
           _ = _ := prefix_append _ _ _

/-- A return/failure test plus the operational write run discharges the
exact production pure contract, including a partial failure after any number
of faults. No global memory equation or source-prefix premise is needed. -/
theorem write_run_contract {sz a r : BitVec 64} {src : List (BitVec 8)}
    {P : UPtd} {M : Image} {ke : Nat} {s : State}
    (h : WriteRun sz a src P M ke s)
    (exit : (r = 0#64 ∧ s.copied.length = src.length) ∨
      (r = -1#64 ∧ s.copied.length < src.length ∧
        ¬ uvaWmapped s.table (a + BitVec.ofNat 64 s.copied.length).toNat)) :
    P.extSz sz s.table ∧
      ((r = 0#64 ∧ s.image = umemWrite (viewFaulted P s.table M) a.toNat src ∧
          umMapped s.table a.toNat src.length ∧ uvaWprefix s.table a src.length) ∨
       (r = -1#64 ∧ ∃ d, d < src.length ∧
          s.image = umemWrite (viewFaulted P s.table M) a.toNat (src.take d) ∧
          umMapped s.table a.toNat d ∧ uvaWprefix s.table a d ∧
          ¬ uvaWmapped P (a + BitVec.ofNat 64 d).toNat)) := by
  obtain ⟨ht, hb, hp⟩ := write_run_certificate h
  apply copyout_contract src ht
  rcases exit with ⟨hz, hd⟩ | ⟨hf, hd, hn⟩
  · exact Or.inl ⟨hz, by simpa only [hd, List.take_length] using hp⟩
  · exact Or.inr ⟨hf, hd, hp, hn⟩

/-- The string scanner may fault between chunks; every nonterminal chunk
contains no NUL. A terminating NUL is handled by `scan_nul_contract`. -/
inductive ScanRun (sz a : BitVec 64) (max : Nat)
    (P : UPtd) (M : Image) (ke : Nat) : State → Prop
  | start : ScanRun sz a max P M ke (initial P M ke)
  | fault {s : State} (h : ScanRun sz a max P M ke s) (Q : UPtd) (ke' : Nat)
      (he : s.table.extSz sz Q) (hk : s.lend ≤ ke') :
      ScanRun sz a max P M ke (extend s Q ke')
  | chunk {s : State} (h : ScanRun sz a max P M ke s) (bs : List (BitVec 8))
      (step : Step .read sz a s (transfer .read a s bs))
      (bound : s.copied.length + bs.length ≤ max)
      (nonzero : ∀ b, b ∈ bs → b ≠ 0#8) :
      ScanRun sz a max P M ke (transfer .read a s bs)

theorem scan_run_certificate {sz a : BitVec 64} {max : Nat}
    {P : UPtd} {M : Image} {ke : Nat} {s : State}
    (h : ScanRun sz a max P M ke s) :
    Trace .read sz a (initial P M ke) s ∧ s.copied.length ≤ max ∧
      ∀ b, b ∈ s.copied → b ≠ 0#8 := by
  induction h with
  | start => exact ⟨.refl _, Nat.zero_le _, by simp [initial]⟩
  | fault h Q ke' he hk ih => exact ⟨.snoc ih.1 (.fault _ Q ke' he hk), ih.2⟩
  | chunk h bs hs hb hn ih =>
    refine ⟨.snoc ih.1 hs, ?_, ?_⟩
    · simpa only [transfer, List.length_append] using hb
    · intro b hm
      rcases List.mem_append.mp hm with hm | hm
      · exact ih.2.2 b hm
      · exact hn b hm

/-- The terminating one-byte load/store is sufficient to derive the
first-NUL claim for the entire run, even across lazy-page faults. -/
theorem scan_nul_contract {sz a : BitVec 64} {P : UPtd} {M : Image} {ke : Nat}
    {s : State} (old : List (BitVec 8))
    (h : ScanRun sz a old.length P M ke s)
    (room : s.copied.length < old.length)
    (nul : Step .read sz a s (transfer .read a s [0#8])) :
    P.extSz sz s.table ∧
      ∃ str, umemStr (viewFaulted P s.table M) a.toNat old.length = some str ∧
        buffer (transfer .read a s [0#8]) old = str ++ old.drop str.length ∧
        umMapped s.table a.toNat str.length := by
  obtain ⟨ht, hb, hn⟩ := scan_run_certificate h
  have ht' := Trace.snoc ht nul
  have hi := trace_certificate ht
  have hi' := trace_certificate ht'
  have hr := hi.read rfl
  have hr' := hi'.read rfl
  have hfirst : ∀ j, j < s.copied.length → umemByte s.image (a.toNat + j) ≠ 0#8 := by
    intro j hj
    apply hn _
    apply List.mem_of_getElem? (i := j)
    rw [hr, UMemL.umemRead_getElem?, ite_eq_left hj]
  have hzero : umemByte s.image (a.toNat + s.copied.length) = 0#8 := by
    have he := congrArg (fun bs => bs[s.copied.length]?) hr'
    simp only [transfer, imageAfter, List.length_append, List.length_cons,
      List.length_nil] at he
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at he
    rw [UMemL.umemRead_getElem?, ite_eq_left (by omega)] at he
    exact Option.some.inj he.symm
  have hbound : (transfer .read a s [0#8]).copied.length ≤ old.length := by
    simp only [transfer, List.length_append, List.length_cons, List.length_nil]
    omega
  have hc := copyinstr_contract (r := 0#64) old ht' hbound
    (Or.inl ⟨rfl, s.copied.length, by simp [transfer], hfirst, hzero⟩)
  exact ⟨hc.1, (hc.2.resolve_right (by intro hh; have := hh.1; contradiction)).2⟩

end Experiments.WholeFunction.Copy
