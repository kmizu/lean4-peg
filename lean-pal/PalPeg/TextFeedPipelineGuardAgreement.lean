import PalPeg.TextFeedPipelineFrames

/-! Ready-guard agreement for every verifier condition on the actual bundle.
Text not-mark tests do not require a arrived character: an unfilled blank is
also not a mark. Thus no unsupported oracle premise remains in next_erase. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelineGuardAgreement
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.TextFeedControl
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl
open PalPeg.TextFeed PalPeg.TextFeedPipelineControl PalPeg.TextFeedPipelineVerifier
open PalPeg.VerifierFeed PalPeg.VerifierFeedRaw PalPeg.VerifierFeedRefinement
open PalPeg.TextFeedPipelineFrames
variable {k : ℕ}

theorem view_not_mark {blank mark : Fin k} {Text : List (Fin k)} {m i : ℕ}
    {tp : TapeConfiguration k} (hmb : mark ≠ blank) (hm : mark ∉ Text)
    (h : Tape.SeqView blank tp (padW blank Text m) i) : Tape.read tp ≠ mark := by
  have hn : mark ∉ padW blank Text m := by
    intro he
    rcases List.mem_append.mp he with he | he
    · exact hm (List.mem_of_mem_take he)
    · exact hmb (List.eq_of_mem_replicate he)
  intro he
  exact hn (he ▸ List.mem_of_getElem? h.read_eq)

theorem notMark_agrees {e : Env k} {Text : List (Fin k)} {n i₁ i₂ : ℕ}
    {M : VMachine' k} {I : GSVTapes.VTapes' k}
    (h : Refines e Text n M I i₁ i₂) (hmb : e.mark ≠ e.blank) (hm : e.mark ∉ Text)
    (hn : n ≤ Text.length) (j : Fin 10) :
    GSVProg.condOf10 e.endSym e.mark e.startSym (.notMark j) (fun j => (GSVProg.vTS M.vt j).focus) =
      GSVProg.condOf10 e.endSym e.mark e.startSym (.notMark j) (fun j => (GSVProg.vTS I j).focus) := by
  change decide ((GSVProg.vTS M.vt j).focus ≠ e.mark) = decide ((GSVProg.vTS I j).focus ≠ e.mark)
  by_cases ht : j = GSVProg.e8 GSTapes.tT
  · subst j
    change decide (Tape.read (M.vt.1 GSTapes.tT) ≠ e.mark) = decide (Tape.read (I.1 GSTapes.tT) ≠ e.mark)
    have hr := view_not_mark hmb hm h.feed.one.view
    have hi := view_not_mark hmb hm h.one
    exact (decide_eq_true hr).trans (decide_eq_true hi).symm
  · by_cases hx : j = GSVProg.tX
    · subst j
      change decide (Tape.read M.vt.2.Txt2 ≠ e.mark) = decide (Tape.read I.2.Txt2 ≠ e.mark)
      have hr := view_not_mark hmb hm h.feed.two.view
      have hi := view_not_mark hmb hm h.two
      exact (decide_eq_true hr).trans (decide_eq_true hi).symm
    · rw [h.focus hn j (fun he => False.elim (ht he)) (fun he => False.elim (hx he))]

noncomputable def idealEval (e : Env k) (I : GSVTapes.VTapes' k) (dir : STape (Fin k)) : C → Bool
  | .inl c => GSVProg.condOf10 e.endSym e.mark e.startSym c (fun j => (GSVProg.vTS I j).focus)
  | .inr .up => decide (dir.focus = e.mark)
  | .inr .always => true

theorem guard_agreement {e : Env k} {Text : List (Fin k)} {n i₁ i₂ : ℕ}
    {M : VMachine' k} {I : GSVTapes.VTapes' k}
    (qt₁ : QT k) (m₁ : Mode) (qt₂ : QT k) (m₂ : Mode)
    (aux : Fin 5 → STape (Fin k)) (old : Fin k) (dir : STape (Fin k))
    (h : Refines e Text n M I i₁ i₂) (hmb : e.mark ≠ e.blank)
    (hb : e.blank ∉ Text) (hm : e.mark ∉ Text) (hn : n ≤ Text.length)
    (c : C)
    (hw : TextFeedPipelineBranch.Waiting
      (taskEval e (fun j => (tapes e qt₁ m₁ qt₂ m₂ M aux old dir j).focus)) c = false) :
    taskEval e (fun j => (tapes e qt₁ m₁ qt₂ m₂ M aux old dir j).focus) (verifyCond c) =
      idealEval e I dir c := by
  cases c with
  | inr c => cases c <;> rfl
  | inl c =>
    cases c with
    | matchOk => exact TextFeedPipelineRefinement.match_guard qt₁ m₁ qt₂ m₂ aux old dir h hb hn hw
    | compOk => exact TextFeedPipelineRefinement.comp_guard qt₁ m₁ qt₂ m₂ aux old dir h hb hn hw
    | notMark j =>
      rw [verifyCond, TextFeedPipelineRefinement.eval_verifier]
      exact notMark_agrees h hmb hm hn j
    | notStart =>
      rw [verifyCond, TextFeedPipelineRefinement.eval_verifier]
      exact h.condition hn .notStart trivial
    | notStartU =>
      rw [verifyCond, TextFeedPipelineRefinement.eval_verifier]
      exact h.condition hn .notStartU trivial

/-- All residual compiler frames refine ideal control under the physical
streaming invariant. Condition agreement is derived from the actual tapes. -/
theorem next_erase_physical {e : Env k} {Text : List (Fin k)} {n i₁ i₂ : ℕ}
    {M : VMachine' k} {I : GSVTapes.VTapes' k}
    (qt₁ : QT k) (m₁ : Mode) (qt₂ : QT k) (m₂ : Mode)
    (aux : Fin 5 → STape (Fin k)) (old : Fin k) (dir : STape (Fin k))
    (h : Refines e Text n M I i₁ i₂) (hmb : e.mark ≠ e.blank)
    (hb : e.blank ∉ Text) (hm : e.mark ∉ Text) (hn : n ≤ Text.length) (fs : List Frame) :
    let ev := taskEval e (fun j => (tapes e qt₁ m₁ qt₂ m₂ M aux old dir j).focus)
    ProgLangControlSteps.Star (idealEval e I dir) (erase fs)
      (destination (next ev fs).2 (next ev fs).1) :=
  next_erase _ _ (guard_agreement qt₁ m₁ qt₂ m₂ aux old dir h hmb hb hm hn) fs

/-- info: 'PalPeg.TextFeedPipelineGuardAgreement.next_erase_physical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms next_erase_physical

end PalPeg.TextFeedPipelineGuardAgreement
