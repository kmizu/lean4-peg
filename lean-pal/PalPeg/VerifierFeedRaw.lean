import PalPeg.VerifierFeedPrimitive

/-! Feed invariants at arbitrary verifier instruction boundaries.
Unlike `VFeedInv'`, these indices do not use the macro-level ghost state:
the scanner's internal moves can precede its next ghost-state update. -/
set_option autoImplicit false

namespace PalPeg.VerifierFeedRaw
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.TextFeed PalPeg.VerifierFeed

variable {k : ℕ}

/-- Regard channel 1 as channel 2, solely to reuse the channel-local laws. -/
def channel1 (M : VMachine' k) : VMachine' k :=
  { M with
    m2 := M.m1
    Q2 := M.Q1
    R2 := M.R1
    vt := (M.vt.1, { M.vt.2 with Txt2 := M.vt.1 GSTapes.tT }) }

abbrev Txt1Inv (blank mark : Fin k) (Text : List (Fin k)) (n : ℕ)
    (M : VMachine' k) (i : ℕ) := Txt2Inv blank mark Text n (channel1 M) i

structure RawInv (blank mark : Fin k) (Text : List (Fin k)) (n : ℕ)
    (M : VMachine' k) (i₁ i₂ : ℕ) : Prop where
  one : Txt1Inv blank mark Text n M i₁
  two : Txt2Inv blank mark Text n M i₂

theorem of_feedInv {blank startSym endSym mark : Fin k} {u v Text : List (Fin k)}
    {d p r n : ℕ} {M : VMachine' k}
    (h : VFeedInv' blank startSym endSym mark u v Text d p r n M) :
    RawInv blank mark Text n M (M.z.1.pos + M.z.1.q)
      (M.z.1.pos - u.length + M.z.2) :=
  ⟨⟨h.scan.txt, h.buf1, h.qinv1, h.qlist1, h.m1le, h.hd1⟩, h.txt2Inv⟩

theorem read1_blank_iff {blank mark : Fin k} {Text : List (Fin k)} {n i : ℕ}
    {M : VMachine' k} (hb : blank ∉ Text) (hn : n ≤ Text.length)
    (h : Txt1Inv blank mark Text n M i) :
    Tape.read (M.vt.1 GSTapes.tT) = blank ↔ i = M.m1 :=
  read_Txt2_blank_iff hb hn h

/-- A tape-only guard, valid even while the macro ghost state is stale. -/
def fill1 (blank mark : Fin k) (M : VMachine' k) : VMachine' k :=
  if Tape.read (M.vt.1 GSTapes.tT) = blank ∧ peek blank M.R1 ≠ mark then
    vfill1' blank mark M
  else { M with R1 := headT blank M.R1 }

theorem fill1_inv {blank mark : Fin k} {Text : List (Fin k)} {n i : ℕ}
    {M : VMachine' k} (hmb : mark ≠ blank) (hb : blank ∉ Text) (hm : mark ∉ Text)
    (hn : n ≤ Text.length) (h : Txt1Inv blank mark Text n M i) :
    Txt1Inv blank mark Text n (fill1 blank mark M) i ∧
      (i < (fill1 blank mark M).m1 ∨ (fill1 blank mark M).m1 = n) := by
  obtain ⟨hi, hok⟩ := vfillHead2_inv hmb hb hm hn h
  unfold fill1
  split_ifs with hc
  · have hc' : Tape.read (channel1 M).vt.2.Txt2 = blank ∧
        peek blank (channel1 M).R2 ≠ mark := hc
    simp only [vfillHead2, if_pos hc'] at hi hok
    refine ⟨⟨?_, hi.buf, hi.qinv, hi.qlist, hi.m2le, hi.hle⟩, hok⟩
    simpa only [channel1, vfill1', GSTapes.upd_self] using hi.view
  · have hc' : ¬(Tape.read (channel1 M).vt.2.Txt2 = blank ∧
        peek blank (channel1 M).R2 ≠ mark) := hc
    simp only [vfillHead2, if_neg hc'] at hi hok
    exact ⟨⟨hi.view, hi.buf, hi.qinv, hi.qlist, hi.m2le, hi.hle⟩, hok⟩

theorem fill1_other (blank mark : Fin k) (M : VMachine' k) :
    (fill1 blank mark M).vt.2 = M.vt.2 ∧ (fill1 blank mark M).m2 = M.m2 ∧
      (fill1 blank mark M).Q2 = M.Q2 ∧ (fill1 blank mark M).R2 = M.R2 ∧
      ∀ j, j ≠ GSTapes.tT → (fill1 blank mark M).vt.1 j = M.vt.1 j := by
  unfold fill1
  split_ifs
  · refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    intro j hj
    exact GSTapes.upd_ne M.vt.1 _ hj
  · exact ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem raw_fill1 {blank mark : Fin k} {Text : List (Fin k)} {n i₁ i₂ : ℕ}
    {M : VMachine' k} (hmb : mark ≠ blank) (hb : blank ∉ Text) (hm : mark ∉ Text)
    (hn : n ≤ Text.length) (h : RawInv blank mark Text n M i₁ i₂) :
    RawInv blank mark Text n (fill1 blank mark M) i₁ i₂ ∧
      (i₁ < (fill1 blank mark M).m1 ∨ (fill1 blank mark M).m1 = n) := by
  obtain ⟨h₁, hok⟩ := fill1_inv hmb hb hm hn h.one
  obtain ⟨hv, hn', hq, hr, _⟩ := fill1_other blank mark M
  refine ⟨⟨h₁, ?_⟩, hok⟩
  constructor
  · simpa only [hv, hn'] using h.two.view
  · simpa only [hr, hq] using h.two.buf
  · simpa only [hq] using h.two.qinv
  · simpa only [hq, hn'] using h.two.qlist
  · simpa only [hn'] using h.two.m2le
  · simpa only [hn'] using h.two.hle

theorem raw_fill2 {blank mark : Fin k} {Text : List (Fin k)} {n i₁ i₂ : ℕ}
    {M : VMachine' k} (hmb : mark ≠ blank) (hb : blank ∉ Text) (hm : mark ∉ Text)
    (hn : n ≤ Text.length) (h : RawInv blank mark Text n M i₁ i₂) :
    RawInv blank mark Text n (vfillHead2 blank mark M) i₁ i₂ ∧
      Ok2 n (vfillHead2 blank mark M) i₂ := by
  obtain ⟨h₂, hok⟩ := vfillHead2_inv hmb hb hm hn h.two
  refine ⟨⟨?_, h₂⟩, hok⟩
  constructor
  · simpa only [channel1, vfillHead2_vt1, vfillHead2_m1] using h.one.view
  · simpa only [channel1, vfillHead2_Q1, vfillHead2_R1] using h.one.buf
  · simpa only [channel1, vfillHead2_Q1] using h.one.qinv
  · simpa only [channel1, vfillHead2_Q1, vfillHead2_m1] using h.one.qlist
  · simpa only [channel1, vfillHead2_m1] using h.one.m2le
  · simpa only [channel1, vfillHead2_m1] using h.one.hle

private theorem qlist_arrive {Text : List (Fin k)} {n m : ℕ} {Q : Queue (Fin k)}
    {a : Fin k} (hqinv : Inv Q) (hn : n < Text.length) (ha : Text[n]? = some a)
    (hm : m ≤ n) (hq : toList Q = (Text.take n).drop m) :
    toList (snoc Q a) = (Text.take (n + 1)).drop m := by
  have hlen : (Text.take n).length = n := by simp only [List.length_take]; omega
  have htake : Text.take (n + 1) = Text.take n ++ [a] := by
    rw [List.take_add_one, ha]; rfl
  rw [toList_snoc hqinv, hq, htake,
    List.drop_append_of_le_length (by rw [hlen]; exact hm)]

/-- Arrival is valid between any two internal verifier instructions;
it does not require a macro-level scan invariant or a control reset. -/
theorem raw_arrive {blank mark : Fin k} {Text : List (Fin k)} {n i₁ i₂ : ℕ}
    {a : Fin k} {M : VMachine' k} (hmb : mark ≠ blank) (hn : n < Text.length)
    (ha : Text[n]? = some a) (h : RawInv blank mark Text n M i₁ i₂) :
    RawInv blank mark Text (n + 1) (varrive' blank mark a M) i₁ i₂ := by
  constructor
  · exact ⟨h.one.view, snocT_encodes hmb h.one.buf h.one.qinv,
      inv_snoc h.one.qinv a, qlist_arrive h.one.qinv hn ha h.one.m2le h.one.qlist,
      Nat.le_succ_of_le h.one.m2le, h.one.hle⟩
  · exact ⟨h.two.view, snocT_encodes hmb h.two.buf h.two.qinv,
      inv_snoc h.two.qinv a, qlist_arrive h.two.qinv hn ha h.two.m2le h.two.qlist,
      Nat.le_succ_of_le h.two.m2le, h.two.hle⟩

theorem read1_real {blank mark : Fin k} {Text : List (Fin k)} {n i : ℕ}
    {M : VMachine' k} (hn : n ≤ Text.length) (h : Txt1Inv blank mark Text n M i)
    (hi : i < M.m1) : Text[i]? = some (Tape.read (M.vt.1 GSTapes.tT)) := by
  have hv := h.view.read_eq
  rw [padW_getElem?_of_lt (le_trans h.m2le hn) hi] at hv
  exact hv

theorem read2_real {blank mark : Fin k} {Text : List (Fin k)} {n i : ℕ}
    {M : VMachine' k} (hn : n ≤ Text.length) (h : Txt2Inv blank mark Text n M i)
    (hi : i < M.m2) : Text[i]? = some (Tape.read M.vt.2.Txt2) := by
  have hv := h.view.read_eq
  rw [padW_getElem?_of_lt (le_trans h.m2le hn) hi] at hv
  exact hv

/-- After a Q1 supply attempt, its blank wait guard means precisely
that the actual head is at the arrival frontier. -/
theorem fill1_wait_iff {blank mark : Fin k} {Text : List (Fin k)} {n i : ℕ}
    {M : VMachine' k} (hmb : mark ≠ blank) (hb : blank ∉ Text) (hm : mark ∉ Text)
    (hn : n ≤ Text.length) (h : Txt1Inv blank mark Text n M i) :
    Tape.read ((fill1 blank mark M).vt.1 GSTapes.tT) = blank ↔ i = n := by
  obtain ⟨hi, hok⟩ := fill1_inv hmb hb hm hn h
  rw [read1_blank_iff hb hn hi]
  have hle : i ≤ (fill1 blank mark M).m1 := hi.hle
  have hmle : (fill1 blank mark M).m1 ≤ n := hi.m2le
  omega

theorem fill2_wait_iff {blank mark : Fin k} {Text : List (Fin k)} {n i : ℕ}
    {M : VMachine' k} (hmb : mark ≠ blank) (hb : blank ∉ Text) (hm : mark ∉ Text)
    (hn : n ≤ Text.length) (h : Txt2Inv blank mark Text n M i) :
    Tape.read (vfillHead2 blank mark M).vt.2.Txt2 = blank ↔ i = n := by
  obtain ⟨hi, hok⟩ := vfillHead2_inv hmb hb hm hn h
  rw [read_Txt2_blank_iff hb hn hi]
  have hle := hi.hle
  have hmle := hi.m2le
  unfold Ok2 at hok
  omega

/-- info: 'PalPeg.VerifierFeedRaw.raw_arrive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_arrive

/-- info: 'PalPeg.VerifierFeedRaw.fill1_wait_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fill1_wait_iff

/-- info: 'PalPeg.VerifierFeedRaw.fill2_wait_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fill2_wait_iff

/-- info: 'PalPeg.VerifierFeedRaw.raw_fill1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_fill1

/-- info: 'PalPeg.VerifierFeedRaw.raw_fill2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_fill2

end PalPeg.VerifierFeedRaw
