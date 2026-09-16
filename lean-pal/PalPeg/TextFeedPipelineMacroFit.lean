import PalPeg.TextFeedPipelineIdealEngine
import PalPeg.ProgLangBlankEq

/-! Derive a completed macro's finite-word bound from its actual final
head. Right blank padding is used only as an equivalent proof witness. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelineMacroFit
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.TextFeedControl
open PalPeg.TextFeedPipelineIdealEngine PalPeg.TextFeedPipelineCoupled
open PalPeg.GSVTapes PalPeg.GSVTapesZ PalPeg.GSVerifierZ PalPeg.VerifierFeedRefinement
variable {k : ℕ}

theorem blanks_getD {blank : Fin k} {xs : List (Fin k)} (h : Tape.Blanks blank xs) (n : ℕ) :
    xs[n]?.getD blank = blank := by
  cases he : xs[n]? with
  | none => rfl
  | some a => exact h a (List.mem_of_getElem? he)

theorem rightBlankEq_append_left {blank : Fin k} {xs ys : List (Fin k)}
    (h : RightBlankEq blank xs ys) (pre : List (Fin k)) :
    RightBlankEq blank (pre ++ xs) (pre ++ ys) := by
  induction pre with
  | nil => exact h
  | cons a pre ih => exact ih.cons

theorem seq_pad_blankEq {blank : Fin k} {tp : TapeConfiguration k} {Word : List (Fin k)}
    {i : ℕ} (h : Tape.SeqView blank tp Word i) (N : ℕ) :
    STape.BlankEq blank (GSProg.toS tp)
      (GSProg.toS (wordTape blank (Word ++ List.replicate N blank) i)) := by
  have hi := h.lt
  refine ⟨?_, ?_, ?_⟩
  · change tp.left = ((Word ++ List.replicate N blank).take i).reverse
    rw [List.take_append_of_le_length (Nat.le_of_lt hi)]
    exact h.left_eq
  · change tp.focus = (Word ++ List.replicate N blank)[i]?.getD blank
    rw [List.getElem?_append_left hi, h.focus_eq]
    rfl
  · change RightBlankEq blank tp.right ((Word ++ List.replicate N blank).drop (i + 1))
    obtain ⟨t, ht, hb⟩ := h.right_eq
    rw [ht, List.drop_append_of_le_length (by omega : i + 1 ≤ Word.length)]
    apply rightBlankEq_append_left
    intro j
    rw [blanks_getD hb, blanks_getD (Tape.blanks_replicate blank N)]

theorem seq_left_length {blank : Fin k} {tp : TapeConfiguration k} {Word : List (Fin k)}
    {i : ℕ} (h : Tape.SeqView blank tp Word i) : tp.left.length = i := by
  rw [h.left_eq, List.length_reverse, List.length_take, Nat.min_eq_left (Nat.le_of_lt h.lt)]

def padIdeal (e : Env k) (Word : List (Fin k)) (N i j : ℕ) (I : VTapes' k) : VTapes' k :=
  (GSTapes.upd I.1 GSTapes.tT (wordTape e.blank (Word ++ List.replicate N e.blank) i),
    { I.2 with Txt2 := wordTape e.blank (Word ++ List.replicate N e.blank) j })

theorem pad_encoding {e : Env k} {Word leftPat rightPat : List (Fin k)}
    {rate p r : ℕ} {I : VTapes' k} {z : VStateZ}
    (h : VEncodesZ' e.blank e.startSym e.endSym e.mark leftPat rightPat Word rate p r I z) (N : ℕ) :
    VEncodesZ' e.blank e.startSym e.endSym e.mark leftPat rightPat
      (Word ++ List.replicate N e.blank) rate p r
      (padIdeal e Word N (z.1.pos + z.1.q) (z.1.pos - leftPat.length + z.2.head) I) z := by
  have h1 := wordTape_view e.blank (Word ++ List.replicate N e.blank) (z.1.pos + z.1.q)
    (by have hh := h.scan.txt.lt; simp only [List.length_append, List.length_replicate]; omega)
  have h2 := wordTape_view e.blank (Word ++ List.replicate N e.blank) (z.1.pos - leftPat.length + z.2.head)
    (by have hh := h.txt2.lt; simp only [List.length_append, List.length_replicate]; omega)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, h.pat, h2⟩
  · exact h.scan.pat
  · exact h1
  · exact h.scan.c1
  · exact h.scan.c2
  · exact ⟨h.scan.quad.ap, h.scan.quad.an, h.scan.quad.rp, h.scan.quad.rn⟩

theorem pad_bundle {e : Env k} {Word leftPat rightPat : List (Fin k)}
    {rate p r : ℕ} {I : VTapes' k} {z : VStateZ}
    (h : VEncodesZ' e.blank e.startSym e.endSym e.mark leftPat rightPat Word rate p r I z)
    (N : ℕ) (dir : STape (Fin k)) :
    ∀ j, STape.BlankEq e.blank (bundle I dir j)
      (bundle (padIdeal e Word N (z.1.pos + z.1.q) (z.1.pos - leftPat.length + z.2.head) I) dir j) := by
  intro j
  have h1 := seq_pad_blankEq h.scan.txt N
  have h2 := seq_pad_blankEq h.txt2 N
  fin_cases j <;> first
    | exact STape.BlankEq.refl _ _
    | exact h1
    | exact h2

theorem step_append {Word rightPat : List (Fin k)} {rate p r : ℕ} {st : ScanState}
    (hi : st.pos + st.q < Word.length) (tail : List (Fin k)) :
    scanStep rightPat rate p r (Word ++ tail) st = scanStep rightPat rate p r Word st := by
  simp only [scanStep, List.getElem?_append_left hi]

theorem ends_blankEq {e : Env k} {p : GSVProgZLoop.DProg}
    {T U V W : Fin 11 → STape (Fin k)} {m cost : ℕ}
    (h : Ends e (List.replicate m none) [p] T [] V)
    (hb : ∀ j, STape.BlankEq e.blank (T j) (U j))
    (hr : GSVProgZLoop.RunsTo (engine e) e.blank p U W cost) :
    ∀ j, STape.BlankEq e.blank (V j) (W j) := by
  obtain ⟨acts, he, hW, hc⟩ := hr
  have ht : GSVProgZLoop.RunsTo (engine e) e.blank p T (applyTrace e.blank T acts) cost :=
    ⟨acts, exec_blankEq hb he, rfl, hc⟩
  rw [h.result_of_runsTo ht, ← hW]
  exact applyTrace_blankEq hb acts

/-- The real final text head lies in the arrived prefix. Transfer the GS
execution to a sufficiently long, observationally equivalent blank tail;
its exact head position then proves the original finite-word bound. -/
theorem completed_fit {e : Env k} {Text leftPat rightPat : List (Fin k)}
    {rate p r n m : ℕ} {u v : Snapshot k} {z : VStateZ}
    (hrate : 0 < rate) (hp : 0 < p) (hmb : e.mark ≠ e.blank)
    (hstart : e.startSym ∉ rightPat) (hend : e.endSym ∉ rightPat)
    (hendu : e.endSym ∉ leftPat) (hstartu : e.startSym ∉ leftPat) (hse : e.startSym ≠ e.endSym)
    (hE : VEncodesZ' e.blank e.startSym e.endSym e.mark leftPat rightPat
      (TextFeed.padW e.blank Text Text.length) rate p r u.ideal z)
    (hwf : ZWf leftPat.length z.2) (hq : z.1.q ≤ rightPat.length) (hpos : leftPat.length ≤ z.1.pos)
    (hf : Refines e Text n v.model v.ideal v.i1 v.i2) (hn : n ≤ Text.length)
    (hdir : u.dir = GSVProgZLoop.dirTape e.blank e.mark z.2.up 0)
    (hr : Ends e (List.replicate m none) [GSVProgZLoop.stepProg rate]
      (bundle u.ideal u.dir) [] (bundle v.ideal v.dir)) :
    (scanStep rightPat rate p r (TextFeed.padW e.blank Text Text.length) z.1).pos +
      (scanStep rightPat rate p r (TextFeed.padW e.blank Text Text.length) z.1).q <
        (TextFeed.padW e.blank Text Text.length).length := by
  let Word := TextFeed.padW e.blank Text Text.length
  let st := scanStep rightPat rate p r Word z.1
  let N := st.pos + st.q + 1
  let Word' := Word ++ List.replicate N e.blank
  let J := padIdeal e Word N (z.1.pos + z.1.q) (z.1.pos - leftPat.length + z.2.head) u.ideal
  let J' := vApplyActs' e.blank (vprogramZ' e.blank e.startSym e.endSym e.mark rate z.2.up J) J
  have hJ := pad_encoding hE N
  have hs : scanStep rightPat rate p r Word' z.1 = st := step_append hE.scan.txt.lt _
  have hfit : (scanStep rightPat rate p r Word' z.1).pos +
      (scanStep rightPat rate p r Word' z.1).q < Word'.length := by
    rw [hs]
    simp only [Word', List.length_append, List.length_replicate, N]
    omega
  have henc := (vencodes_stepZ hrate hp hmb hend hendu hstartu hse hJ hwf hq hpos hfit).1
  have hrun := GSVProgZLoop.stepProg_runsTo (Terminal := Unit) hrate hmb hstart hJ.scan hq z.2.up
  rw [hdir] at hr
  have hblank := ends_blankEq hr (pad_bundle hE N (GSVProgZLoop.dirTape e.blank e.mark z.2.up 0)) hrun
  have ht := hblank (Fin.castAdd 1 (GSVProg.e8 GSTapes.tT))
  change STape.BlankEq e.blank (GSProg.toS (v.ideal.1 GSTapes.tT)) (GSProg.toS (J'.1 GSTapes.tT)) at ht
  have hleft : (v.ideal.1 GSTapes.tT).left.length = (J'.1 GSTapes.tT).left.length :=
    congrArg List.length ht.left
  have hnew : (J'.1 GSTapes.tT).left.length = st.pos + st.q := by
    have hh := seq_left_length henc.scan.txt
    change (J'.1 GSTapes.tT).left.length =
      (vStepZ leftPat rightPat rate p r Word' z).1.pos +
        (vStepZ leftPat rightPat rate p r Word' z).1.q at hh
    simpa only [vStepZ_fst, hs] using hh
  have hold : (v.ideal.1 GSTapes.tT).left.length = v.i1 := seq_left_length hf.one
  have hbound : v.i1 ≤ n := hf.feed.one.hle.trans hf.feed.one.m2le
  change st.pos + st.q < Word.length
  have hlen : Word.length = Text.length + 1 := TextFeed.padW_length (Nat.le_refl _)
  omega

/-- info: 'PalPeg.TextFeedPipelineMacroFit.completed_fit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms completed_fit

end PalPeg.TextFeedPipelineMacroFit
