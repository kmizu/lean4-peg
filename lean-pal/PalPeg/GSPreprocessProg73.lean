import PalPeg.GSPreprocessProg72

/-! # Finite normalization of the preprocessing result -/
set_option autoImplicit false
namespace PalPeg.PrepInstance
open PegSeparation.RealTimeTM PalPeg.PatternTapes PalPeg.PatternProg PalPeg.ProgLang
variable {sc : ℕ} {Terminal : Type} {blank mark : Fin sc}

def normalizeProg (endSym : Fin sc) : Prog (ActG 15 sc) (CondG 15 sc) :=
  counterCaseProg (blank := blank) sC1 mark
    (.seq (countSuffixProg (blank := blank) sP sC1 endSym)
      (decLoopProg blank sRp [] mark)) .skip

theorem normalize_spec {start endSym : Fin sc} {w : List (Fin sc)}
    {s p r : ℕ} (S : Tapes sc) (hmark : mark ≠ blank)
    (hne : start ≠ endSym) (hend : endSym ∉ w) (hs : s ≤ w.length)
    (hv : Tape.SeqView blank (S sP) (start :: w ++ [endSym]) (s + 1))
    (hc : Tape.CounterView' blank mark (S sC1) p)
    (hr : Tape.CounterView' blank mark (S sRp) r) :
    ∃ trace, ExecG Terminal blank (normalizeProg (blank := blank) (mark := mark) endSym) S trace ∧
      Tape.CounterView' blank mark (runG blank trace S sC1)
        (if p = 0 then w.length - s + 1 else p) ∧
      Tape.CounterView' blank mark (runG blank trace S sRp) (if p = 0 then 0 else r) ∧
      Tape.SeqView blank (runG blank trace S sP) (start :: w ++ [endSym])
        (if p = 0 then w.length + 1 else s + 1) ∧
      (∀ j, j ≠ sP → j ≠ sC1 → j ≠ sRp → runG blank trace S j = S j) ∧
      trace.length = if p = 0 then 2 * (w.length - s) + 2 * r + 5 else 2 := by
  have hrestore := counterProbe_restore hc
  by_cases hp : p = 0
  · subst p
    obtain ⟨a, ea, va, ca, fa, la⟩ := countSuffix_spec (Terminal := Terminal) S
      (i := sP) (c := sC1) (by decide) hne hend hs hv hc
    have hra : Tape.CounterView' blank mark (runG blank a S sRp) r := by
      rw [fa sRp (by decide) (by decide)]
      exact hr
    obtain ⟨b, eb, cb, fb, lb⟩ := clearCounter_spec (Terminal := Terminal) sRp r
      (runG blank a S) hmark hra
    have ee := counterCase_exec hmark hc (zero :=
      .seq (countSuffixProg (blank := blank) sP sC1 endSym) (decLoopProg blank sRp [] mark))
      (nonzero := .skip) (by simpa using execG_seq ea eb)
    refine ⟨[TAct.put sC1 blank .left, TAct.keep sC1 .right] ++ (a ++ b), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [normalizeProg] using ee
    · rw [runG_append, hrestore, runG_append, fb sC1 (by decide)]
      simpa using ca
    · rw [runG_append, hrestore, runG_append]
      simpa using cb
    · rw [runG_append, hrestore, runG_append, fb sP (by decide)]
      simpa using va
    · intro j hjp hjc hjr
      rw [runG_append, hrestore, runG_append, fb j hjr, fa j hjp hjc]
    · simp only [List.length_append, List.length_cons, List.length_nil, la, lb, ↓reduceIte]
      omega
  · have ee := counterCase_exec hmark hc (zero :=
      .seq (countSuffixProg (blank := blank) sP sC1 endSym) (decLoopProg blank sRp [] mark))
      (nonzero := .skip) (by simpa [hp] using (execG_skip (Terminal := Terminal) (blank := blank) (S := S)))
    refine ⟨[TAct.put sC1 blank .left, TAct.keep sC1 .right] ++ [], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [normalizeProg] using ee
    · simpa only [List.append_nil, hrestore, if_neg hp] using hc
    · simpa only [List.append_nil, hrestore, if_neg hp] using hr
    · simpa only [List.append_nil, hrestore, if_neg hp] using hv
    · intro j _ _ _
      simpa only [List.append_nil] using congrFun hrestore j
    · simp [hp]

def finiteEpilogue (start endSym : Fin sc) : Prog (ActG 15 sc) (CondG 15 sc) :=
  .seq (normalizeProg (blank := blank) (mark := mark) endSym)
    (.seq (clearSentinelProg (blank := blank) sP start endSym)
      (clearSentinelProg (blank := blank) sU start endSym))

/-- Finite epilogue for the core's clean final counter state.  Unmentioned
tapes, including all already-zero scratch counters, are preserved exactly. -/
theorem finiteEpilogue_spec {start endSym : Fin sc} {w : List (Fin sc)}
    {s p r : ℕ} (S : Tapes sc) (hmark : mark ≠ blank)
    (hne : start ≠ endSym) (hstart : start ∉ w) (hend : endSym ∉ w) (hs : s ≤ w.length)
    (hv : Tape.SeqView blank (S sP) (start :: w ++ [endSym]) (s + 1))
    (hu : Tape.SeqView blank (S sU) (start :: w ++ [endSym]) (s + 1))
    (hc : Tape.CounterView' blank mark (S sC1) p)
    (hr : Tape.CounterView' blank mark (S sRp) r) :
    ∃ trace, ExecG Terminal blank (finiteEpilogue (blank := blank) (mark := mark) start endSym) S trace ∧
      Tape.CounterView' blank mark (runG blank trace S sC1)
        (if p = 0 then w.length - s + 1 else p) ∧
      Tape.CounterView' blank mark (runG blank trace S sRp) (if p = 0 then 0 else r) ∧
      Tape.StackView blank (runG blank trace S sP) [] ∧
      Tape.StackView blank (runG blank trace S sU) [] ∧
      (∀ j, j ≠ sP → j ≠ sU → j ≠ sC1 → j ≠ sRp → runG blank trace S j = S j) ∧
      trace.length ≤ 6 * w.length + 2 * r + 11 := by
  obtain ⟨a, ea, ca, ra, va, fa, la⟩ := normalize_spec (Terminal := Terminal) S
    hmark hne hend hs hv hc hr
  obtain ⟨b, eb, vb, fb, lb⟩ := clearSentinel_spec_frame (Terminal := Terminal)
    sP start endSym w _ (runG blank a S) hne hstart hend va
  have hu' : Tape.SeqView blank (runG blank b (runG blank a S) sU)
      (start :: w ++ [endSym]) (s + 1) := by
    rw [fb sU (by decide), fa sU (by decide) (by decide) (by decide)]
    exact hu
  obtain ⟨c, ec, vc, fc, lc⟩ := clearSentinel_spec_frame (Terminal := Terminal)
    sU start endSym w (s + 1) (runG blank b (runG blank a S)) hne hstart hend hu'
  refine ⟨a ++ (b ++ c), execG_seq ea (execG_seq eb ec), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [runG_append]
    rw [fc sC1 (by decide), fb sC1 (by decide)]
    exact ca
  · simp only [runG_append]
    rw [fc sRp (by decide), fb sRp (by decide)]
    exact ra
  · simp only [runG_append]
    rw [fc sP (by decide)]
    exact vb
  · simpa only [runG_append] using vc
  · intro j hjp hju hjc hjr
    simp only [runG_append]
    rw [fc j hju, fb j hjp, fa j hjp hjc hjr]
  · simp only [List.length_append, la, lb, lc]
    split_ifs <;> omega

/-- info: 'PalPeg.PrepInstance.normalize_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms normalize_spec
/-- info: 'PalPeg.PrepInstance.finiteEpilogue_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finiteEpilogue_spec

end PalPeg.PrepInstance
