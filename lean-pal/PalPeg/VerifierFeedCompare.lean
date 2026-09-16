import PalPeg.VerifierFeedPrimitive

/-! Finite verifier comparisons with interposed input supply. In the
two-comparison quota the second condition sees the first fill's output. -/
set_option autoImplicit false

namespace PalPeg.VerifierFeedCompare
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.TextFeedControl PalPeg.VerifierFeed PalPeg.VerifierFeedShared

variable {k : ℕ} {Terminal : Type}

noncomputable def comp (e : Env k) : Prog (VerifierFeedShared.Act k) (Cond k) :=
  .ite (.inr .compOk)
    (.seq (.act (.inr (GSVProg.tU, true, .right))) (liftFeed (VerifierFeedClosed.stepXR e.blank e.mark)))
    .skip

noncomputable def comp2 (e : Env k) : Prog (VerifierFeedShared.Act k) (Cond k) := .seq (comp e) (comp e)

theorem comp_encoded {e : Env k} {M : VMachine' k} (hmb : e.mark ≠ e.blank)
    (hi : Inv M.Q2) (hb : Encodes e.blank e.mark M.R2.qt M.Q2) :
    Encodes e.blank e.mark (vcompFed e.blank e.endSym e.mark M).R2.qt
      (vcompFed e.blank e.endSym e.mark M).Q2 := by
  unfold vcompFed
  split_ifs
  · exact VerifierFeedPrimitive.vstepXR_encoded hmb hi hb
  · exact hb

theorem comp_matches {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    {qt : QT k} {m : Mode} {M : VMachine' k}
    (h : Ready e.blank e.mark qt m M.Q2) (hb : Encodes e.blank e.mark M.R2.qt M.Q2) :
    ∃ tr qt' m', Exec (shared (Terminal := Terminal) e) e.blank (comp e) (bundle e qt m M) tr ∧
      tr.length ≤ 49 ∧ applyTrace e.blank (bundle e qt m M) tr =
        bundle e qt' m' (vcompFed e.blank e.endSym e.mark M) ∧
      Ready e.blank e.mark qt' m' (vcompFed e.blank e.endSym e.mark M).Q2 := by
  have hcond : (shared (Terminal := Terminal) e).condOf (.inr .compOk)
      (fun j => (bundle e qt m M j).focus) =
        decide (Tape.read M.vt.2.U ≠ e.endSym ∧ Tape.read M.vt.2.U = Tape.read M.vt.2.Txt2) := rfl
  by_cases hp : Tape.read M.vt.2.U ≠ e.endSym ∧ Tape.read M.vt.2.U = Tape.read M.vt.2.Txt2
  · obtain ⟨a, hea, hna, hta⟩ := VerifierFeedPrimitive.primitive_exec (Terminal := Terminal)
      e (GSVProg.tU, true, .right) qt m M
    rw [VerifierFeedPrimitive.primitive_UR] at hta
    obtain ⟨b, qt', m', heb, hnb, htb, hr⟩ := VerifierFeedShared.step_matches
      (Terminal := Terminal) (M := vmoveUR e.blank M) hc hmb h hb
    refine ⟨a ++ b, qt', m', ?_, by simp only [List.length_append, hna]; omega, ?_, ?_⟩
    · apply exec_ite_pos (by rw [hcond]; exact decide_eq_true hp)
      exact exec_seq hea (hta ▸ heb)
    · rw [applyTrace_append, hta, htb]
      simp only [vcompFed, if_pos hp]
    · simpa only [vcompFed, if_pos hp] using hr
  · refine ⟨[], qt, m, exec_ite_neg (by rw [hcond]; exact decide_eq_false hp) (exec_skip _),
      by simp, ?_, ?_⟩
    · simp only [applyTrace_nil, vcompFed, if_neg hp]
    · simpa only [vcompFed, if_neg hp] using h

theorem comp2_matches {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    {qt : QT k} {m : Mode} {M : VMachine' k}
    (h : Ready e.blank e.mark qt m M.Q2) (hb : Encodes e.blank e.mark M.R2.qt M.Q2) :
    ∃ tr qt' m', Exec (shared (Terminal := Terminal) e) e.blank (comp2 e) (bundle e qt m M) tr ∧
      tr.length ≤ 98 ∧ applyTrace e.blank (bundle e qt m M) tr =
        bundle e qt' m' (vcomp2Fed e.blank e.endSym e.mark M) ∧
      Ready e.blank e.mark qt' m' (vcomp2Fed e.blank e.endSym e.mark M).Q2 := by
  obtain ⟨a, qt₁, m₁, hea, hna, hta, hr⟩ := comp_matches (Terminal := Terminal) hc hmb h hb
  obtain ⟨b, qt₂, m₂, heb, hnb, htb, hr'⟩ := comp_matches (Terminal := Terminal) hc hmb hr
    (comp_encoded hmb h.inv hb)
  refine ⟨a ++ b, qt₂, m₂, exec_seq hea (hta ▸ heb), by simp only [List.length_append]; omega, ?_, hr'⟩
  rw [applyTrace_append, hta, htb]
  rfl

/-- info: 'PalPeg.VerifierFeedCompare.comp2_matches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms comp2_matches

end PalPeg.VerifierFeedCompare
