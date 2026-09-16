import PalPeg.TextFeedTiming

/-! Prefix alignment consumes already-arrived input. An empty FIFO stalls
without moving the text head. The finite program never reads the ghost
arrival count or the ghost scanner position. -/
set_option autoImplicit false

namespace PalPeg.TextFeedAlign
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.TextFeedControl PalPeg.TextFeedTiming PalPeg.TextFeed

variable {k : ℕ} {Terminal : Type}

def moveRight : TP k := lift (liftScan (.act (GSTapes.tT, true, .right)))

noncomputable def program (blank mark : Fin k) : TP k :=
  .seq (lift (supplyNonempty blank mark)) (.ite (.inr .blankText) .skip moveRight)

/-- A proof model, not a controller parameter. -/
def advance (blank mark : Fin k) (n : ℕ) (M : Machine' k) : Machine' k :=
  if M.m < n then stepRight' blank (fill' blank mark M) else M

def AtFront (M : Machine' k) : Prop := M.st.pos = M.m ∧ M.st.q = 0

theorem advance_inv {blank startSym endSym mark : Fin k} {v Text : List (Fin k)}
    {d p r n : ℕ} {M : Machine' k} (hmb : mark ≠ blank) (hn : n ≤ Text.length)
    (hf : AtFront M) (h : FeedInv' blank startSym endSym mark v Text d p r n M) :
    FeedInv' blank startSym endSym mark v Text d p r n (advance blank mark n M) ∧
      AtFront (advance blank mark n M) ∧
      (advance blank mark n M).m = min (M.m + 1) n := by
  unfold advance
  split_ifs with ha
  · have hh := fill'_feedInv hmb hn ha (by rw [hf.1, hf.2]; omega) h
    refine ⟨stepRight'_feedInv ?_ ?_ hh, ?_, ?_⟩
    · change M.st.pos + M.st.q + 1 ≤ M.m + 1
      rw [hf.1, hf.2]
    · change M.m + 1 ≤ Text.length
      omega
    · change M.st.pos + 1 = M.m + 1 ∧ M.st.q = 0
      exact ⟨congrArg (· + 1) hf.1, hf.2⟩
    · change M.m + 1 = min (M.m + 1) n
      omega
  · exact ⟨h, hf, by have := h.mle; omega⟩

theorem advance_iterate {blank startSym endSym mark : Fin k} {v Text : List (Fin k)}
    {d p r n : ℕ} {M : Machine' k} (hmb : mark ≠ blank) (hn : n ≤ Text.length)
    (hf : AtFront M) (h : FeedInv' blank startSym endSym mark v Text d p r n M) (N : ℕ) :
    let M' := (advance blank mark n)^[N] M
    FeedInv' blank startSym endSym mark v Text d p r n M' ∧ AtFront M' ∧
      M'.m = min (M.m + N) n := by
  induction N generalizing M with
  | zero => exact ⟨h, hf, by simp only [Nat.add_zero]; exact (Nat.min_eq_left h.mle).symm⟩
  | succ N ih =>
    obtain ⟨hi, hf', hm⟩ := advance_inv hmb hn hf h
    obtain ⟨hi', hf'', hm'⟩ := ih hf' hi
    rw [Function.iterate_succ_apply]
    refine ⟨hi', hf'', ?_⟩
    rw [hm', hm]
    omega

theorem move_matches (e : Env k) (qt : QT k) (m : Mode) (M : Machine' k) :
    TExec (Terminal := Terminal) e moveRight qt m (GSProg.TS M.ts) 1 qt m
      (GSProg.TS (stepRight' e.blank M).ts) := by
  have he := exec_act (I := GSProg.I8 (Terminal := Terminal) e.blank e.endSym e.mark e.startSym)
    (blank := e.blank) (GSProg.inputFree_I8 e.blank e.endSym e.mark e.startSym)
    (GSTapes.tT, true, .right) (GSProg.TS M.ts)
  have hh := texec_lift (executes_scan qt m he)
  have ht : applyTrace e.blank (GSProg.TS M.ts)
      [actVec (GSProg.I8 (Terminal := Terminal) e.blank e.endSym e.mark e.startSym)
        (GSTapes.tT, true, .right) (GSProg.TS M.ts)] = GSProg.TS (stepRight' e.blank M).ts := by
    funext j
    by_cases hj : j = GSTapes.tT
    · subst j
      simp only [applyTrace_cons, applyTrace_nil, actVec, GSProg.I8, GSProg.actOf8,
        touchVec, ↓reduceIte, stepRight', GSProg.TS, GSTapes.upd_self, GSProg.toS_step]
      rfl
    · simp only [applyTrace_cons, applyTrace_nil, actVec, GSProg.I8, GSProg.actOf8,
        touchVec, if_neg hj, stepRight', GSProg.TS, GSTapes.upd]
      rfl
  simpa only [moveRight, List.length_singleton, ht] using hh

/-- At most 48 tape actions, even with a backlog of arbitrary size.
No arrival action occurs in this program. -/
theorem program_matches {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    {qt : QT k} {m : Mode} {M : Machine' k} {v Text : List (Fin k)} {d p r n : ℕ}
    (hblank : e.blank ∉ Text) (hmark : e.mark ∉ Text) (hn : n ≤ Text.length)
    (hq : Ready e.blank e.mark qt m M.Q) (hf : AtFront M)
    (h : FeedInv' e.blank e.startSym e.endSym e.mark v Text d p r n M) :
    ∃ ticks qt' m', ticks ≤ 48 ∧
      TExec (Terminal := Terminal) e (program e.blank e.mark) qt m (GSProg.TS M.ts)
        ticks qt' m' (GSProg.TS (advance e.blank e.mark n M).ts) ∧
      Ready e.blank e.mark qt' m' (advance e.blank e.mark n M).Q := by
  have hh : (toList M.Q).head?.getD e.mark ≠ e.mark ↔ M.m < n := by
    rw [← head?_eq hq.inv]
    exact TextFeedProg2.head_ne_mark_iff hmark hn h
  by_cases ha : M.m < n
  · obtain ⟨ticks, qt', m', hlen, hex, hr⟩ := supply_nonempty_runs (Terminal := Terminal)
      hc hmb M hq h.buf (hh.mpr ha)
    have hi := fill'_feedInv hmb hn ha (by rw [hf.1, hf.2]; omega) h
    have hne : (GSProg.TS (fill' e.blank e.mark M).ts GSTapes.tT).focus ≠ e.blank := by
      intro he
      have hbad := (TextFeedProg2.read_tT_blank_iff hblank hn hi).mp he
      change M.st.pos + M.st.q = M.m + 1 at hbad
      rw [hf.1, hf.2] at hbad
      omega
    obtain ⟨tr, he, hlen', hout⟩ := move_matches (Terminal := Terminal) e qt' m' (fill' e.blank e.mark M)
    have hcond : (IT (Terminal := Terminal) e).condOf (.inr .blankText)
        (fun j => (TextFeedControl.tapes e qt' m' (GSProg.TS (fill' e.blank e.mark M).ts) j).focus) = false := by
      rw [blankText_cond]
      exact decide_eq_false hne
    have hex' := texec_seq (texec_lift hex)
      (show TExec (Terminal := Terminal) e (.ite (.inr .blankText) .skip moveRight)
        qt' m' (GSProg.TS (fill' e.blank e.mark M).ts) 1 qt' m'
        (GSProg.TS (stepRight' e.blank (fill' e.blank e.mark M)).ts) from
        ⟨tr, exec_ite_neg hcond he, hlen', hout⟩)
    refine ⟨ticks + 1, qt', m', by omega, ?_, ?_⟩
    · simpa only [advance, if_pos ha, program] using hex'
    · simpa only [advance, if_pos ha, stepRight'] using hr
  · have hempty : (toList M.Q).head?.getD e.mark = e.mark := by
      by_contra hne
      exact ha (hh.mp hne)
    have hcT : (IT (Terminal := Terminal) e).condOf (.inr .blankText)
        (fun j => (TextFeedControl.tapes e qt m (GSProg.TS M.ts) j).focus) = true := by
      rw [blankText_cond]
      apply decide_eq_true
      exact (TextFeedProg2.read_tT_blank_iff hblank hn h).mpr (by rw [hf.1, hf.2]; omega)
    have hs := texec_seq (texec_lift (supply_empty_runs (Terminal := Terminal) hc hq (GSProg.TS M.ts) hempty))
      (show TExec (Terminal := Terminal) e (.ite (.inr .blankText) .skip moveRight)
        qt m (GSProg.TS M.ts) 0 qt m (GSProg.TS M.ts) from
        ⟨[], exec_ite_pos hcT (exec_skip _), rfl, rfl⟩)
    exact ⟨2, qt, m, by omega, by simpa only [advance, if_neg ha, program] using hs,
      by simpa only [advance, if_neg ha] using hq⟩

/-- info: 'PalPeg.TextFeedAlign.program_matches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms program_matches

/-- info: 'PalPeg.TextFeedAlign.advance_iterate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms advance_iterate

end PalPeg.TextFeedAlign
