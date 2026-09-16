import PalPeg.VerifierFeedRawPrimitive

/-! Refinement to an ideal verifier whose two text tapes contain the
whole word. Filling and arrival stutter on that ideal machine; a safe
verifier instruction performs the same ideal instruction. -/
set_option autoImplicit false

namespace PalPeg.VerifierFeedRefinement
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang
open PalPeg.TextFeedControl PalPeg.TextFeed PalPeg.VerifierFeed
open PalPeg.VerifierFeedRaw PalPeg.VerifierFeedRawPrimitive PalPeg.VerifierFeedPrimitive

variable {k : ℕ}

def stepTapes (e : Env k) (a : GSVProg.Act10) (I : GSVTapes.VTapes' k) : GSVTapes.VTapes' k :=
  fromTapes (applyTrace e.blank (GSVProg.vTS I)
    [actVec (GSVProg.I10 (Terminal := Unit) e.blank e.endSym e.mark e.startSym) a (GSVProg.vTS I)])

structure Refines (e : Env k) (Text : List (Fin k)) (n : ℕ)
    (M : VMachine' k) (I : GSVTapes.VTapes' k) (i₁ i₂ : ℕ) : Prop where
  feed : RawInv e.blank e.mark Text n M i₁ i₂
  one : Tape.SeqView e.blank (I.1 GSTapes.tT) (padW e.blank Text Text.length) i₁
  two : Tape.SeqView e.blank I.2.Txt2 (padW e.blank Text Text.length) i₂
  other : ∀ j, j ≠ GSVProg.e8 GSTapes.tT → j ≠ GSVProg.tX → rawTape M.vt j = rawTape I j

theorem other_at {V W : GSVTapes.VTapes' k}
    (h : ∀ j, j ≠ GSTapes.tT → V.1 j = W.1 j) (hU : V.2.U = W.2.U)
    (j : Fin 10) (hj₁ : j ≠ GSVProg.e8 GSTapes.tT) (hj₂ : j ≠ GSVProg.tX) :
    rawTape V j = rawTape W j := by
  fin_cases j <;> first
    | exact hU
    | exact h _ (by decide)
    | exact False.elim (hj₁ rfl)
    | exact False.elim (hj₂ rfl)

/-- An ideal proof witness, not a tape populated by the physical machine. -/
def wordTape (blank : Fin k) (w : List (Fin k)) (i : ℕ) : TapeConfiguration k :=
  ⟨(w.take i).reverse, w[i]?.getD blank, w.drop (i + 1)⟩

theorem wordTape_view (blank : Fin k) (w : List (Fin k)) (i : ℕ) (hi : i < w.length) :
    Tape.SeqView blank (wordTape blank w i) w i := by
  refine ⟨rfl, ?_, ⟨[], by simp [wordTape], by simp [Tape.Blanks]⟩⟩
  simp only [wordTape, List.getElem?_eq_getElem hi, Option.getD_some]

def idealTapes (e : Env k) (Text : List (Fin k)) (M : VMachine' k) (i₁ i₂ : ℕ) :
    GSVTapes.VTapes' k :=
  (GSTapes.upd M.vt.1 GSTapes.tT (wordTape e.blank (padW e.blank Text Text.length) i₁),
    { M.vt.2 with Txt2 := wordTape e.blank (padW e.blank Text Text.length) i₂ })

/-- Every raw physical state has a full-text ideal witness. No premise
asserts that future text has already arrived on the physical tapes. -/
theorem initial {e : Env k} {Text : List (Fin k)} {n i₁ i₂ : ℕ} {M : VMachine' k}
    (hn : n ≤ Text.length) (h : RawInv e.blank e.mark Text n M i₁ i₂) :
    Refines e Text n M (idealTapes e Text M i₁ i₂) i₁ i₂ := by
  have hlen : (padW e.blank Text Text.length).length = Text.length + 1 := padW_length (Nat.le_refl _)
  have hi₁ : i₁ < (padW e.blank Text Text.length).length := by
    have hle : i₁ ≤ M.m1 := h.one.hle
    have hm : M.m1 ≤ n := h.one.m2le
    omega
  have hi₂ : i₂ < (padW e.blank Text Text.length).length := by
    have hle := h.two.hle
    have hm := h.two.m2le
    omega
  refine ⟨h, ?_, wordTape_view _ _ _ hi₂, ?_⟩
  · simpa only [idealTapes, GSTapes.upd_self] using wordTape_view e.blank _ i₁ hi₁
  · intro j hj₁ hj₂
    apply other_at (V := M.vt) (W := idealTapes e Text M i₁ i₂) _ rfl j hj₁ hj₂
    intro l hl
    exact (GSTapes.upd_ne M.vt.1 _ hl).symm

/-- At a macro boundary, the ideal witness has the full verifier encoding
required by the existing GS correctness theorem. -/
theorem Refines.encodes {e : Env k} {u v Text : List (Fin k)} {d p r n : ℕ}
    {M : VMachine' k} {I : GSVTapes.VTapes' k}
    (h : Refines e Text n M I (M.z.1.pos + M.z.1.q) (M.z.1.pos - u.length + M.z.2))
    (hf : VFeedInv' e.blank e.startSym e.endSym e.mark u v Text d p r n M) :
    GSVTapes.VEncodes' e.blank e.startSym e.endSym e.mark u v
      (padW e.blank Text Text.length) d p r I M.z := by
  have ht : ∀ j, j ≠ GSTapes.tT → M.vt.1 j = I.1 j := by
    intro j hj
    have he := h.other (GSVProg.e8 j) (fun hh => hj (Fin.ext (congrArg (fun x : Fin 10 => x.val) hh)))
      (GSVProg.e8_ne_tX j)
    simpa only [rawTape_e8] using he
  have hu : M.vt.2.U = I.2.U := h.other GSVProg.tU (by decide) (by decide)
  exact ⟨⟨(ht GSTapes.tP (by decide)) ▸ hf.scan.pat, h.one,
    (ht GSTapes.tC1 (by decide)) ▸ hf.scan.c1, (ht GSTapes.tC2 (by decide)) ▸ hf.scan.c2,
    ⟨(ht GSTapes.tAp (by decide)) ▸ hf.scan.quad.ap, (ht GSTapes.tAn (by decide)) ▸ hf.scan.quad.an,
      (ht GSTapes.tRp (by decide)) ▸ hf.scan.quad.rp, (ht GSTapes.tRn (by decide)) ▸ hf.scan.quad.rn⟩⟩,
    hu ▸ hf.pat, h.two⟩

theorem seq_index_eq {blank : Fin k} {tp : TapeConfiguration k} {v w : List (Fin k)}
    {i j : ℕ} (hi : Tape.SeqView blank tp v i) (hj : Tape.SeqView blank tp w j) : i = j := by
  have hli : tp.left.length = i := by
    rw [hi.left_eq, List.length_reverse, List.length_take, Nat.min_eq_left (Nat.le_of_lt hi.lt)]
  have hlj : tp.left.length = j := by
    rw [hj.left_eq, List.length_reverse, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj.lt)]
  exact hli.symm.trans hlj

/-- Recover the macro invariant from the ideal GS endpoint. The new `z`
is only a proof annotation; all physical fields and both FIFOs are unchanged.
Actual head indices are derived from tape views, not assumed or reset. -/
theorem Refines.feed_of_encodes {e : Env k} {u v Text : List (Fin k)} {d p r n i₁ i₂ : ℕ}
    {M : VMachine' k} {I : GSVTapes.VTapes' k} {z : VState}
    (h : Refines e Text n M I i₁ i₂)
    (he : GSVTapes.VEncodes' e.blank e.startSym e.endSym e.mark u v
      (padW e.blank Text Text.length) d p r I z)
    (hq : z.1.q ≤ v.length) (hc : z.2 ≤ u.length) (hp : u.length ≤ z.1.pos) :
    VFeedInv' e.blank e.startSym e.endSym e.mark u v Text d p r n { M with z := z } := by
  have hi₁ : i₁ = z.1.pos + z.1.q := seq_index_eq h.one he.scan.txt
  have hi₂ : i₂ = z.1.pos - u.length + z.2 := seq_index_eq h.two he.txt2
  have ht : ∀ j, j ≠ GSTapes.tT → M.vt.1 j = I.1 j := by
    intro j hj
    have hh := h.other (GSVProg.e8 j)
      (fun hh => hj (Fin.ext (congrArg (fun x : Fin 10 => x.val) hh))) (GSVProg.e8_ne_tX j)
    simpa only [rawTape_e8] using hh
  have hu : M.vt.2.U = I.2.U := h.other GSVProg.tU (by decide) (by decide)
  have htxt₁ : Tape.SeqView e.blank (M.vt.1 GSTapes.tT) (padW e.blank Text M.m1)
      (z.1.pos + z.1.q) := by rw [← hi₁]; exact h.feed.one.view
  have htxt₂ : Tape.SeqView e.blank M.vt.2.Txt2 (padW e.blank Text M.m2)
      (z.1.pos - u.length + z.2) := by rw [← hi₂]; exact h.feed.two.view
  have hhd₁ : z.1.pos + z.1.q ≤ M.m1 := by rw [← hi₁]; exact h.feed.one.hle
  have hhd₂ : z.1.pos - u.length + z.2 ≤ M.m2 := by rw [← hi₂]; exact h.feed.two.hle
  exact {
    scan := ⟨(ht GSTapes.tP (by decide)).symm ▸ he.scan.pat, htxt₁,
      (ht GSTapes.tC1 (by decide)).symm ▸ he.scan.c1, (ht GSTapes.tC2 (by decide)).symm ▸ he.scan.c2,
      ⟨(ht GSTapes.tAp (by decide)).symm ▸ he.scan.quad.ap,
        (ht GSTapes.tAn (by decide)).symm ▸ he.scan.quad.an,
        (ht GSTapes.tRp (by decide)).symm ▸ he.scan.quad.rp,
        (ht GSTapes.tRn (by decide)).symm ▸ he.scan.quad.rn⟩⟩
    pat := hu.symm ▸ he.pat
    txt2 := htxt₂
    buf1 := h.feed.one.buf
    qinv1 := h.feed.one.qinv
    qlist1 := h.feed.one.qlist
    m1le := h.feed.one.m2le
    buf2 := h.feed.two.buf
    qinv2 := h.feed.two.qinv
    qlist2 := h.feed.two.qlist
    m2le := h.feed.two.m2le
    hd1 := hhd₁
    hd2 := hhd₂
    qle := hq
    cle := hc
    posle := hp }

theorem Refines.fill1 {e : Env k} {Text : List (Fin k)} {n i₁ i₂ : ℕ}
    {M : VMachine' k} {I : GSVTapes.VTapes' k}
    (h : Refines e Text n M I i₁ i₂) (hmb : e.mark ≠ e.blank)
    (hb : e.blank ∉ Text) (hm : e.mark ∉ Text) (hn : n ≤ Text.length) :
    Refines e Text n (VerifierFeedRaw.fill1 e.blank e.mark M) I i₁ i₂ := by
  obtain ⟨hv, _, _, _, ht⟩ := fill1_other e.blank e.mark M
  refine ⟨(raw_fill1 hmb hb hm hn h.feed).1, h.one, h.two, ?_⟩
  intro j hj₁ hj₂
  exact (other_at ht (congrArg GSVTapes.VExt.U hv) j hj₁ hj₂).trans (h.other j hj₁ hj₂)

theorem Refines.fill2 {e : Env k} {Text : List (Fin k)} {n i₁ i₂ : ℕ}
    {M : VMachine' k} {I : GSVTapes.VTapes' k}
    (h : Refines e Text n M I i₁ i₂) (hmb : e.mark ≠ e.blank)
    (hb : e.blank ∉ Text) (hm : e.mark ∉ Text) (hn : n ≤ Text.length) :
    Refines e Text n (vfillHead2 e.blank e.mark M) I i₁ i₂ := by
  refine ⟨(raw_fill2 hmb hb hm hn h.feed).1, h.one, h.two, ?_⟩
  intro j hj₁ hj₂
  exact (other_at (fun j _ => congrFun (vfillHead2_vt1 e.blank e.mark M) j)
    (vfillHead2_U e.blank e.mark M) j hj₁ hj₂).trans (h.other j hj₁ hj₂)

theorem Refines.arrive {e : Env k} {Text : List (Fin k)} {n i₁ i₂ : ℕ}
    {M : VMachine' k} {I : GSVTapes.VTapes' k} {a : Fin k}
    (h : Refines e Text n M I i₁ i₂) (hmb : e.mark ≠ e.blank)
    (hn : n < Text.length) (ha : Text[n]? = some a) :
    Refines e Text (n + 1) (varrive' e.blank e.mark a M) I i₁ i₂ :=
  ⟨raw_arrive hmb hn ha h.feed, h.one, h.two, h.other⟩

theorem Refines.primitive {e : Env k} {Text : List (Fin k)} {n i₁ i₂ : ℕ}
    {M : VMachine' k} {I : GSVTapes.VTapes' k} {a : GSVProg.Act10}
    (h : Refines e Text n M I i₁ i₂) (hn : n ≤ Text.length) (hs : Safe a M i₁ i₂) :
    Refines e Text n (VerifierFeedPrimitive.primitive e a M) (stepTapes e a I)
      (nextIndex a (GSVProg.e8 GSTapes.tT) i₁) (nextIndex a GSVProg.tX i₂) := by
  have hm₁ : M.m1 ≤ Text.length := le_trans h.feed.one.m2le hn
  have hm₂ : M.m2 ≤ Text.length := le_trans h.feed.two.m2le hn
  have hs₁ : SafeAt a (GSVProg.e8 GSTapes.tT) i₁ Text.length := by
    intro hj
    exact ⟨(hs.1 hj).1, fun hr => lt_of_lt_of_le ((hs.1 hj).2 hr) hm₁⟩
  have hs₂ : SafeAt a GSVProg.tX i₂ Text.length := by
    intro hj
    exact ⟨(hs.2 hj).1, fun hr => lt_of_lt_of_le ((hs.2 hj).2 hr) hm₂⟩
  have hv₁ : Tape.SeqView e.blank (rawTape ({ M with vt := I } : VMachine' k).vt
      (GSVProg.e8 GSTapes.tT)) (padW e.blank Text Text.length) i₁ := by
    simpa only [rawTape_e8] using h.one
  have hv₂ : Tape.SeqView e.blank (rawTape ({ M with vt := I } : VMachine' k).vt
      GSVProg.tX) (padW e.blank Text Text.length) i₂ := h.two
  obtain ⟨hv₁', _⟩ := primitive_view (Nat.le_refl Text.length)
    (le_trans h.feed.one.hle hm₁) hv₁ hs₁
  obtain ⟨hv₂', _⟩ := primitive_view (Nat.le_refl Text.length)
    (le_trans h.feed.two.hle hm₂) hv₂ hs₂
  refine ⟨raw_primitive hn h.feed hs, ?_, hv₂', ?_⟩
  · simpa only [rawTape_e8, VerifierFeedPrimitive.primitive, stepTapes] using hv₁'
  · intro j hj₁ hj₂
    change rawTape (VerifierFeedPrimitive.primitive e a M).vt j =
      rawTape (VerifierFeedPrimitive.primitive e a { M with vt := I }).vt j
    rw [primitive_at, primitive_at]
    change (if a.1 = j then Tape.step e.blank (rawTape M.vt j)
      (if a.2.1 then (rawTape M.vt j).focus else e.blank) a.2.2 else rawTape M.vt j) =
      (if a.1 = j then Tape.step e.blank (rawTape I j)
      (if a.2.1 then (rawTape I j).focus else e.blank) a.2.2 else rawTape I j)
    rw [h.other j hj₁ hj₂]

theorem stepTapes_stay (e : Env k) (j : Fin 10) (I : GSVTapes.VTapes' k) :
    stepTapes e (j, true, .stay) I = I := by
  unfold stepTapes
  have ht : applyTrace e.blank (GSVProg.vTS I)
      [actVec (GSVProg.I10 (Terminal := Unit) e.blank e.endSym e.mark e.startSym)
        (j, true, .stay) (GSVProg.vTS I)] = GSVProg.vTS I := by
    funext l
    simp only [applyTrace_cons, applyTrace_nil, actVec, GSVProg.I10, GSVProg.actOf10,
      touchVec, ↓reduceIte]
    by_cases hl : l = j
    · subst l
      simp only [ite_self, applyAction_focus_stay]
    · simp only [if_neg hl, applyAction_focus_stay]
  rw [ht, fromTapes_vTS]

/-- The actual instruction, including automatic Q2 filling, refines one
ordinary ideal GS instruction, not a ghost-level atomic scan step. -/
theorem Refines.effect {e : Env k} {Text : List (Fin k)} {n i₁ i₂ : ℕ}
    {M : VMachine' k} {I : GSVTapes.VTapes' k} {a : GSVProg.Act10}
    (h : Refines e Text n M I i₁ i₂) (hmb : e.mark ≠ e.blank)
    (hb : e.blank ∉ Text) (hm : e.mark ∉ Text) (hn : n ≤ Text.length)
    (hs : Safe a M i₁ i₂) :
    Refines e Text n (VerifierFeedPrimitive.effect e a M) (stepTapes e a I)
      (nextIndex a (GSVProg.e8 GSTapes.tT) i₁) (nextIndex a GSVProg.tX i₂) := by
  have hp := h.primitive hn hs
  unfold VerifierFeedPrimitive.effect
  split_ifs with hxr hxs
  · change a = (GSVProg.tX, true, .right) at hxr
    subst a
    rw [primitive_XR] at hp
    exact hp.fill2 hmb hb hm hn
  · change a = (GSVProg.tX, true, .stay) at hxs
    subst a
    simp only [nextIndex, moveIndex, ite_self, stepTapes_stay]
    exact h.fill2 hmb hb hm hn
  · exact hp

theorem Refines.read1 {e : Env k} {Text : List (Fin k)} {n i₁ i₂ : ℕ}
    {M : VMachine' k} {I : GSVTapes.VTapes' k}
    (h : Refines e Text n M I i₁ i₂) (hn : n ≤ Text.length) (hi : i₁ < M.m1) :
    Tape.read (M.vt.1 GSTapes.tT) = Tape.read (I.1 GSTapes.tT) := by
  have hp := read1_real hn h.feed.one hi
  have hiT : i₁ < Text.length := lt_of_lt_of_le hi (le_trans h.feed.one.m2le hn)
  have he := h.one.read_eq
  rw [padW_getElem?_of_lt (Nat.le_refl Text.length) hiT] at he
  exact Option.some.inj (hp.symm.trans he)

theorem Refines.read2 {e : Env k} {Text : List (Fin k)} {n i₁ i₂ : ℕ}
    {M : VMachine' k} {I : GSVTapes.VTapes' k}
    (h : Refines e Text n M I i₁ i₂) (hn : n ≤ Text.length) (hi : i₂ < M.m2) :
    Tape.read M.vt.2.Txt2 = Tape.read I.2.Txt2 := by
  have hp := read2_real hn h.feed.two hi
  have hiT : i₂ < Text.length := lt_of_lt_of_le hi (le_trans h.feed.two.m2le hn)
  have he := h.two.read_eq
  rw [padW_getElem?_of_lt (Nat.le_refl Text.length) hiT] at he
  exact Option.some.inj (hp.symm.trans he)

theorem Refines.focus {e : Env k} {Text : List (Fin k)} {n i₁ i₂ : ℕ}
    {M : VMachine' k} {I : GSVTapes.VTapes' k}
    (h : Refines e Text n M I i₁ i₂) (hn : n ≤ Text.length) (j : Fin 10)
    (h₁ : j = GSVProg.e8 GSTapes.tT → i₁ < M.m1)
    (h₂ : j = GSVProg.tX → i₂ < M.m2) :
    (GSVProg.vTS M.vt j).focus = (GSVProg.vTS I j).focus := by
  by_cases hj₁ : j = GSVProg.e8 GSTapes.tT
  · subst j
    exact h.read1 hn (h₁ rfl)
  · by_cases hj₂ : j = GSVProg.tX
    · subst j
      exact h.read2 hn (h₂ rfl)
    · exact congrArg Tape.read (h.other j hj₁ hj₂)

/-- Only cells a condition actually inspects need to be filled.
In particular, end-of-pattern guards do not demand a future text symbol. -/
def CondReady (e : Env k) (c : GSVProg.Cond10) (M : VMachine' k) (i₁ i₂ : ℕ) : Prop :=
  match c with
  | .notMark j => (j = GSVProg.e8 GSTapes.tT → i₁ < M.m1) ∧ (j = GSVProg.tX → i₂ < M.m2)
  | .matchOk => Tape.read (M.vt.1 GSTapes.tP) ≠ e.endSym → i₁ < M.m1
  | .compOk => Tape.read M.vt.2.U ≠ e.endSym → i₂ < M.m2
  | _ => True

theorem Refines.condition {e : Env k} {Text : List (Fin k)} {n i₁ i₂ : ℕ}
    {M : VMachine' k} {I : GSVTapes.VTapes' k}
    (h : Refines e Text n M I i₁ i₂) (hn : n ≤ Text.length)
    (c : GSVProg.Cond10) (hr : CondReady e c M i₁ i₂) :
    GSVProg.condOf10 e.endSym e.mark e.startSym c (fun j => (GSVProg.vTS M.vt j).focus) =
      GSVProg.condOf10 e.endSym e.mark e.startSym c (fun j => (GSVProg.vTS I j).focus) := by
  have hp : Tape.read (M.vt.1 GSTapes.tP) = Tape.read (I.1 GSTapes.tP) :=
    congrArg Tape.read (h.other (GSVProg.e8 GSTapes.tP) (by decide) (by decide))
  have hu : Tape.read M.vt.2.U = Tape.read I.2.U :=
    congrArg Tape.read (h.other GSVProg.tU (by decide) (by decide))
  cases c with
  | notMark j =>
    change decide ((GSVProg.vTS M.vt j).focus ≠ e.mark) = decide ((GSVProg.vTS I j).focus ≠ e.mark)
    rw [h.focus hn j hr.1 hr.2]
  | notStart =>
    change decide (Tape.read (M.vt.1 GSTapes.tP) ≠ e.startSym) =
      decide (Tape.read (I.1 GSTapes.tP) ≠ e.startSym)
    rw [hp]
  | notStartU =>
    change decide (Tape.read M.vt.2.U ≠ e.startSym) = decide (Tape.read I.2.U ≠ e.startSym)
    rw [hu]
  | matchOk =>
    change decide (Tape.read (M.vt.1 GSTapes.tP) ≠ e.endSym ∧
      Tape.read (M.vt.1 GSTapes.tP) = Tape.read (M.vt.1 GSTapes.tT)) =
      decide (Tape.read (I.1 GSTapes.tP) ≠ e.endSym ∧
      Tape.read (I.1 GSTapes.tP) = Tape.read (I.1 GSTapes.tT))
    by_cases he : Tape.read (M.vt.1 GSTapes.tP) = e.endSym
    · rw [← hp, he]
      simp
    · rw [h.read1 hn (hr he), hp]
  | compOk =>
    change decide (Tape.read M.vt.2.U ≠ e.endSym ∧ Tape.read M.vt.2.U = Tape.read M.vt.2.Txt2) =
      decide (Tape.read I.2.U ≠ e.endSym ∧ Tape.read I.2.U = Tape.read I.2.Txt2)
    by_cases he : Tape.read M.vt.2.U = e.endSym
    · rw [← hu, he]
      simp
    · rw [h.read2 hn (hr he), hu]

theorem match_ready_of_nowait {e : Env k} {Text : List (Fin k)} {n i₁ i₂ : ℕ}
    {M : VMachine' k} (hb : e.blank ∉ Text) (hn : n ≤ Text.length)
    (h : RawInv e.blank e.mark Text n M i₁ i₂)
    (hw : ¬(Tape.read (M.vt.1 GSTapes.tP) ≠ e.endSym ∧ Tape.read (M.vt.1 GSTapes.tT) = e.blank)) :
    CondReady e .matchOk M i₁ i₂ := by
  intro hp
  have hne : i₁ ≠ M.m1 := fun he => hw ⟨hp, (read1_blank_iff hb hn h.one).mpr he⟩
  have hle : i₁ ≤ M.m1 := h.one.hle
  omega

theorem comp_ready_of_nowait {e : Env k} {Text : List (Fin k)} {n i₁ i₂ : ℕ}
    {M : VMachine' k} (hb : e.blank ∉ Text) (hn : n ≤ Text.length)
    (h : RawInv e.blank e.mark Text n M i₁ i₂)
    (hw : ¬(Tape.read M.vt.2.U ≠ e.endSym ∧ Tape.read M.vt.2.Txt2 = e.blank)) :
    CondReady e .compOk M i₁ i₂ := by
  intro hu
  have hne : i₂ ≠ M.m2 := fun he => hw ⟨hu, (read_Txt2_blank_iff hb hn h.two).mpr he⟩
  have hle := h.two.hle
  omega

/-- info: 'PalPeg.VerifierFeedRefinement.Refines.condition' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Refines.condition

/-- info: 'PalPeg.VerifierFeedRefinement.initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms initial

/-- info: 'PalPeg.VerifierFeedRefinement.Refines.encodes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Refines.encodes

/-- info: 'PalPeg.VerifierFeedRefinement.Refines.feed_of_encodes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Refines.feed_of_encodes

/-- info: 'PalPeg.VerifierFeedRefinement.Refines.effect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Refines.effect

/-- info: 'PalPeg.VerifierFeedRefinement.Refines.fill1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Refines.fill1

end PalPeg.VerifierFeedRefinement
