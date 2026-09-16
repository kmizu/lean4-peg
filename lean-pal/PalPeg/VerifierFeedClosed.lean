import PalPeg.TextFeedAtomic
import PalPeg.VerifierFeed

/-! The verifier's fine-grained Txt2 fill is implemented by the closed
finite-mode FIFO. The eight-tape stage here is a view: its tT is Txt2,
not the scanner's first text tape. No arrival count is read by the program. -/
set_option autoImplicit false

namespace PalPeg.VerifierFeedClosed
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.TextFeedControl PalPeg.TextFeedTiming PalPeg.VerifierFeed

variable {k : ℕ} {Terminal : Type}

def fillEffect (e : Env k) (q : Queue (Fin k)) (S : Stage k) : Queue (Fin k) × Stage k :=
  if (S GSTapes.tT).focus = e.blank then TextFeedAtomic.supplyEffect e q S else (q, S)

theorem fill_bounded {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    {qt : QT k} {m : Mode} {q : Queue (Fin k)} (h : Ready e.blank e.mark qt m q) (S : Stage k) :
    ∃ ticks qt' m', ticks ≤ 47 ∧
      TExec (Terminal := Terminal) e (fillIf e.blank e.mark) qt m S ticks qt' m' (fillEffect e q S).2 ∧
      Ready e.blank e.mark qt' m' (fillEffect e q S).1 := by
  have ht := blankText_cond (Terminal := Terminal) e qt m S
  by_cases hb : (S GSTapes.tT).focus = e.blank
  · obtain ⟨ticks, qt', m', hn, he, hr⟩ := TextFeedAtomic.supply_bounded (Terminal := Terminal) hc hmb h S
    obtain ⟨tr, he, hlen, hout⟩ := texec_lift he
    refine ⟨ticks, qt', m', hn, ?_, ?_⟩
    · refine ⟨tr, exec_ite_pos (by rw [ht]; exact decide_eq_true hb) he, hlen, ?_⟩
      simpa only [fillEffect, if_pos hb] using hout
    · simpa only [fillEffect, if_pos hb] using hr
  · refine ⟨0, qt, m, by omega, ?_, ?_⟩
    · refine ⟨[], exec_ite_neg (by rw [ht]; exact decide_eq_false hb) (exec_skip _), rfl, ?_⟩
      simp only [fillEffect, if_neg hb, applyTrace_nil]
    · simpa only [fillEffect, if_neg hb] using h

def stage (M : VMachine' k) : Stage k :=
  Function.update (GSProg.TS M.vt.1) GSTapes.tT (RTQueueProg.toS M.vt.2.Txt2)

@[simp] theorem stage_text (M : VMachine' k) : stage M GSTapes.tT = RTQueueProg.toS M.vt.2.Txt2 :=
  Function.update_self _ _ _

theorem legacy_peek {e : Env k} {M : VMachine' k}
    (hi : Inv M.Q2) (hb : Encodes e.blank e.mark M.R2.qt M.Q2) :
    TextFeed.peek e.blank M.R2 = (toList M.Q2).head?.getD e.mark := by
  have hh := headT_read hb
  rw [head?_eq hi] at hh
  exact hh

theorem fill_effect {e : Env k} {M : VMachine' k}
    (hi : Inv M.Q2) (hb : Encodes e.blank e.mark M.R2.qt M.Q2) :
    fillEffect e M.Q2 (stage M) =
      ((vfillHead2 e.blank e.mark M).Q2, stage (vfillHead2 e.blank e.mark M)) := by
  have hp := legacy_peek hi hb
  have hfocus : (stage M GSTapes.tT).focus = Tape.read M.vt.2.Txt2 := rfl
  unfold fillEffect TextFeedAtomic.supplyEffect
  rw [hfocus]
  by_cases hx : Tape.read M.vt.2.Txt2 = e.blank
  · rw [if_pos hx]
    by_cases hq : (toList M.Q2).head?.getD e.mark = e.mark
    · simp only [vfillHead2, hp, hx, hq, ne_eq, not_true_eq_false,
        and_false, ↓reduceIte, stage]
    · rw [if_neg hq]
      simp only [vfillHead2, hp, hx, hq, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
      congr 1
      funext j
      by_cases hj : j = GSTapes.tT
      · subst j
        simp only [changeStage, stage, Function.update_self, RTQueueProg.toS_step]
      · simp only [changeStage, stage, Function.update_of_ne hj]
  · simp only [vfillHead2, hx, false_and, ↓reduceIte, stage]

/-- The legacy verifier model and the real queue may have different
physical role permutations; only their represented FIFO must agree. -/
theorem fill_matches {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    {qt : QT k} {m : Mode} {M : VMachine' k}
    (h : Ready e.blank e.mark qt m M.Q2) (hb : Encodes e.blank e.mark M.R2.qt M.Q2) :
    ∃ ticks qt' m', ticks ≤ 47 ∧
      TExec (Terminal := Terminal) e (fillIf e.blank e.mark) qt m (stage M) ticks qt' m'
        (stage (vfillHead2 e.blank e.mark M)) ∧
      Ready e.blank e.mark qt' m' (vfillHead2 e.blank e.mark M).Q2 := by
  have hh := fill_bounded (Terminal := Terminal) hc hmb h (stage M)
  rw [fill_effect h.inv hb] at hh
  exact hh

def moveXR : TP k := lift (liftScan (.act (GSTapes.tT, true, .right)))

noncomputable def stepXR (blank mark : Fin k) : TP k := .seq moveXR (fillIf blank mark)

theorem move_matches (e : Env k) (qt : QT k) (m : Mode) (M : VMachine' k) :
    TExec (Terminal := Terminal) e moveXR qt m (stage M) 1 qt m (stage (vmoveXR e.blank M)) := by
  have he := exec_act (I := GSProg.I8 (Terminal := Terminal) e.blank e.endSym e.mark e.startSym)
    (blank := e.blank) (GSProg.inputFree_I8 e.blank e.endSym e.mark e.startSym)
    (GSTapes.tT, true, .right) (stage M)
  have hh := texec_lift (executes_scan qt m he)
  have ht : applyTrace e.blank (stage M)
      [actVec (GSProg.I8 (Terminal := Terminal) e.blank e.endSym e.mark e.startSym)
        (GSTapes.tT, true, .right) (stage M)] = stage (vmoveXR e.blank M) := by
    funext j
    by_cases hj : j = GSTapes.tT
    · subst j
      simp only [applyTrace_cons, applyTrace_nil, actVec, GSProg.I8, GSProg.actOf8,
        touchVec, ↓reduceIte, stage, Function.update_self, vmoveXR, RTQueueProg.toS_step]
      rfl
    · simp only [applyTrace_cons, applyTrace_nil, actVec, GSProg.I8, GSProg.actOf8,
        touchVec, if_neg hj, stage, Function.update_of_ne hj, vmoveXR]
      rfl
  simpa only [moveXR, List.length_singleton, ht] using hh

theorem step_matches {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    {qt : QT k} {m : Mode} {M : VMachine' k}
    (h : Ready e.blank e.mark qt m M.Q2) (hb : Encodes e.blank e.mark M.R2.qt M.Q2) :
    ∃ ticks qt' m', ticks ≤ 48 ∧
      TExec (Terminal := Terminal) e (stepXR e.blank e.mark) qt m (stage M) ticks qt' m'
        (stage (vstepXR e.blank e.mark M)) ∧
      Ready e.blank e.mark qt' m' (vstepXR e.blank e.mark M).Q2 := by
  obtain ⟨ticks, qt', m', hn, he, hr⟩ := fill_matches (Terminal := Terminal) hc hmb
    (M := vmoveXR e.blank M) h hb
  exact ⟨1 + ticks, qt', m', by omega, texec_seq (move_matches e qt m M) he, hr⟩

/-- info: 'PalPeg.VerifierFeedClosed.step_matches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms step_matches

end PalPeg.VerifierFeedClosed
