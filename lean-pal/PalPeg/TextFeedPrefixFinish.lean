import PalPeg.TextFeedPrefixCycle

/-! Completion of the actual atomic source continuation, not only of its
expanded low program. The bound counts calls, hence applies to the finite
call scheduler rather than treating the whole prefix as one atomic action. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPrefixFinish
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.TextFeedControl PalPeg.TextFeed
open PalPeg.TextFeedPrefixAtomic PalPeg.TextFeedPrefixCycle

variable {k : ℕ}

def data (M : Machine' k) (U : TapeConfiguration k) : Model k := ⟨M.Q, GSProg.TS M.ts, U⟩

theorem supply_data {e : Env k} (M : Machine' k) (U : TapeConfiguration k)
    (hi : Inv M.Q) (hb : Encodes e.blank e.mark M.R.qt M.Q)
    (hne : (toList M.Q).head?.getD e.mark ≠ e.mark) :
    effect e .supply (data M U) = data (fill' e.blank e.mark M) U := by
  change (let z := TextFeedAtomic.supplyEffect e M.Q (GSProg.TS M.ts); Model.mk z.1 z.2 U) = _
  rw [TextFeedAtomic.supplyEffect, if_neg hne]
  change Model.mk (RTQueue.tail M.Q)
    (changeStage e.blank (GSProg.TS M.ts) GSTapes.tT ((toList M.Q).head?.getD e.mark) .stay) U = _
  rw [legacy_supply_stage M hi hb]
  rfl

theorem move_data (e : Env k) (M : Machine' k) (U : TapeConfiguration k) (mv : Move) :
    effect e (.uMove mv) (data M U) = data M (Tape.step e.blank U U.focus mv) := rfl

theorem right_data (e : Env k) (M : Machine' k) (U : TapeConfiguration k) :
    effect e .textRight (data M U) = data (stepRight' e.blank M) U := by
  change Model.mk M.Q (applyTrace e.blank (GSProg.TS M.ts)
    [actVec (GSProg.I8 (Terminal := Unit) e.blank e.endSym e.mark e.startSym)
      (GSTapes.tT, true, .right) (GSProg.TS M.ts)]) U =
    Model.mk M.Q (GSProg.TS (stepRight' e.blank M).ts) U
  congr 1
  funext j
  by_cases hj : j = GSTapes.tT
  · subst j
    simp only [applyTrace_cons, applyTrace_nil, actVec, GSProg.I8, GSProg.actOf8,
      touchVec, ↓reduceIte, stepRight', GSProg.TS, GSTapes.upd_self, GSProg.toS_step]
    rfl
  · simp only [applyTrace_cons, applyTrace_nil, actVec, GSProg.I8, GSProg.actOf8,
      touchVec, if_neg hj, stepRight', GSProg.TS, GSTapes.upd]
    rfl

theorem four_progress {e : Env k} {v Text : List (Fin k)} {d p r n : ℕ}
    (hmb : e.mark ≠ e.blank) (hblank : e.blank ∉ Text) (hmark : e.mark ∉ Text)
    (hn : n ≤ Text.length) (M : Machine' k) (U : TapeConfiguration k)
    (hf : TextFeedAlign.AtFront M)
    (h : FeedInv' e.blank e.startSym e.endSym e.mark v Text d p r n M)
    (ha : M.m < n) (hu : U.focus ≠ e.endSym) :
    let M' := stepRight' e.blank (fill' e.blank e.mark M)
    (tick e)^[4] (loopS, data M U) = (loopS, data M' (Tape.step e.blank U U.focus .right)) ∧
      FeedInv' e.blank e.startSym e.endSym e.mark v Text d p r n M' ∧ TextFeedAlign.AtFront M' := by
  have hne : (toList M.Q).head?.getD e.mark ≠ e.mark := by
    rw [← head?_eq h.qinv]
    exact (TextFeedProg2.head_ne_mark_iff hmark hn h).mpr ha
  have hs := supply_data M U h.qinv h.buf hne
  have hi := fill'_feedInv hmb hn ha (by rw [hf.1, hf.2]; omega) h
  have ht : ((effect e .supply (data M U)).S GSTapes.tT).focus ≠ e.blank := by
    rw [hs]
    intro hb
    have hb' := (TextFeedProg2.read_tT_blank_iff hblank hn hi).mp hb
    change M.st.pos + M.st.q = M.m + 1 at hb'
    rw [hf.1, hf.2] at hb'
    omega
  have he := tick_four e (data M U) hu ht
  rw [hs, move_data, right_data] at he
  obtain ⟨hi', hf', _⟩ := TextFeedAlign.advance_inv hmb hn hf h
  rw [TextFeedAlign.advance, if_pos ha] at hi' hf'
  exact ⟨he, hi', hf'⟩

theorem align_ticks {e : Env k} {u v Text : List (Fin k)} {d p r n : ℕ}
    (hmb : e.mark ≠ e.blank) (hblank : e.blank ∉ Text) (hmark : e.mark ∉ Text)
    (hend : e.endSym ∉ u) (hn : n ≤ Text.length) :
    ∀ N i (M : Machine' k) (U : TapeConfiguration k),
      i + N = u.length → M.m + N ≤ n → TextFeedAlign.AtFront M →
      FeedInv' e.blank e.startSym e.endSym e.mark v Text d p r n M →
      Tape.SeqView e.blank U (GSPre.pword e.startSym e.endSym u) (i + 1) →
      ∃ M' U', (tick e)^[4 * N] (loopS, data M U) = (loopS, data M' U') ∧
        FeedInv' e.blank e.startSym e.endSym e.mark v Text d p r n M' ∧
        TextFeedAlign.AtFront M' ∧ M'.m = M.m + N ∧
        Tape.SeqView e.blank U' (GSPre.pword e.startSym e.endSym u) (u.length + 1) := by
  intro N
  induction N with
  | zero =>
    intro i M U hi _ hf h hu
    have hi' : i = u.length := by omega
    exact ⟨M, U, rfl, h, hf, by omega, hi' ▸ hu⟩
  | succ N ih =>
    intro i M U hi hroom hf h hu
    have hne : U.focus ≠ e.endSym := by
      intro he
      have := (GSPre.read_pat_end_iff hend hu).mp he
      omega
    obtain ⟨hstep, hi', hf'⟩ := four_progress hmb hblank hmark hn M U hf h (by omega) hne
    have hu' : Tape.SeqView e.blank (Tape.step e.blank U U.focus .right)
        (GSPre.pword e.startSym e.endSym u) ((i + 1) + 1) :=
      Tape.seq_move_right hu (by rw [GSPre.pword_length]; omega)
    obtain ⟨M', U', he, hinv, hfront, hm, hU⟩ :=
      ih (i + 1) (stepRight' e.blank (fill' e.blank e.mark M)) (Tape.step e.blank U U.focus .right)
        (by omega) (by change M.m + 1 + N ≤ n; omega) hf' hi' hu'
    refine ⟨M', U', ?_, hinv, hfront, ?_, hU⟩
    · rw [show 4 * (N + 1) = 4 * N + 4 by omega, Function.iterate_add_apply, hstep, he]
    · change M'.m = M.m + 1 + N at hm
      omega

theorem rewind_ticks {e : Env k} {u : List (Fin k)}
    (hsu : e.startSym ∉ u) (hse : e.startSym ≠ e.endSym) (M : Machine' k) :
    ∀ i (U : TapeConfiguration k),
      Tape.SeqView e.blank U (GSPre.pword e.startSym e.endSym u) i →
      ∃ U', (tick e)^[i + 1] (rewindS, data M U) = ([], data M U') ∧
        Tape.SeqView e.blank U' (GSPre.pword e.startSym e.endSym u) 1 := by
  intro i
  induction i with
  | zero =>
    intro U hu
    have hr := hu.read_eq
    have hs : U.focus = e.startSym := (Option.some.inj hr).symm
    refine ⟨Tape.step e.blank U U.focus .right, ?_, Tape.seq_move_right hu ?_⟩
    · exact tick_of_step (rewind_end_step e (data M U) hs)
    · rw [GSPre.pword_length]; omega
  | succ i ih =>
    intro U hu
    have hr := hu.read_eq
    change (u ++ [e.endSym])[i]? = some U.focus at hr
    have hmem := List.mem_of_getElem? hr
    have hne : U.focus ≠ e.startSym := by
      intro he
      rcases List.mem_append.mp hmem with hm | hm
      · exact hsu (he ▸ hm)
      · exact hse (he.symm.trans (List.mem_singleton.mp hm))
    obtain ⟨U', he, hv⟩ := ih (Tape.step e.blank U U.focus .left) (Tape.seq_move_left hu)
    refine ⟨U', ?_, hv⟩
    rw [Function.iterate_succ_apply, tick_of_step (rewind_more_step e (data M U) hne), move_data]
    exact he

theorem finish_ticks {e : Env k} {u : List (Fin k)}
    (hsu : e.startSym ∉ u) (hse : e.startSym ≠ e.endSym) (M : Machine' k) (U : TapeConfiguration k)
    (hu : Tape.SeqView e.blank U (GSPre.pword e.startSym e.endSym u) (u.length + 1)) :
    ∃ U', (tick e)^[u.length + 2] (loopS, data M U) = ([], data M U') ∧
      Tape.SeqView e.blank U' (GSPre.pword e.startSym e.endSym u) 1 := by
  have hr := GSPre.read_pat_end hu rfl
  obtain ⟨U', he, hv⟩ := rewind_ticks hsu hse M u.length
    (Tape.step e.blank U U.focus .left) (Tape.seq_move_left hu)
  refine ⟨U', ?_, hv⟩
  rw [Function.iterate_succ_apply, tick_of_step (end_step e (data M U) hr hse), move_data]
  exact he

/-- Exactly 5|u|+2 worker calls suffice from position zero when the
prefix has already arrived. The source continuation is genuinely empty. -/
theorem source_completed {e : Env k} {u v Text : List (Fin k)} {d p r n : ℕ}
    (hmb : e.mark ≠ e.blank) (hblank : e.blank ∉ Text) (hmark : e.mark ∉ Text)
    (hend : e.endSym ∉ u) (hsu : e.startSym ∉ u) (hse : e.startSym ≠ e.endSym)
    (hn : n ≤ Text.length) (hroom : u.length ≤ n) (M : Machine' k) (U : TapeConfiguration k)
    (hf : TextFeedAlign.AtFront M) (hm : M.m = 0)
    (h : FeedInv' e.blank e.startSym e.endSym e.mark v Text d p r n M)
    (hu : Tape.SeqView e.blank U (GSPre.pword e.startSym e.endSym u) 1) :
    ∃ M' U', (tick e)^[5 * u.length + 2] ([source], data M U) = ([], data M' U') ∧
      FeedInv' e.blank e.startSym e.endSym e.mark v Text d p r n M' ∧
      M'.st.pos = u.length ∧ M'.st.q = 0 ∧ M'.m = u.length ∧
      Tape.SeqView e.blank U' (GSPre.pword e.startSym e.endSym u) 1 := by
  obtain ⟨M', U', he, hi, hf', hm', hu'⟩ := align_ticks hmb hblank hmark hend hn
    u.length 0 M U (by omega) (by omega) hf h hu
  obtain ⟨U'', he', hu''⟩ := finish_ticks hsu hse M' U' hu'
  refine ⟨M', U'', ?_, hi, ?_, hf'.2, ?_, hu''⟩
  · rw [tick_start_iterate e _ _ (by omega),
      show 5 * u.length + 2 = (u.length + 2) + 4 * u.length by omega,
      Function.iterate_add_apply, he, he']
  · have := hf'.1; omega
  · omega

/-- info: 'PalPeg.TextFeedPrefixFinish.source_completed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_completed

end PalPeg.TextFeedPrefixFinish
