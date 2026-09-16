import PalPeg.TextFeedAlign
import PalPeg.GSVerifierProgZLoop
import PalPeg.GSPreprocessTapes

/-! A marked prefix tape controls alignment. Successful supply advances
both its cursor and the scanner text head. Failed supply advances neither. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPrefixControl
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.TextFeedControl PalPeg.TextFeedTiming PalPeg.TextFeed
open PalPeg.GSVProgZLoop (RunsTo)

variable {k : ℕ} {Terminal : Type}

def uInterp (e : Env k) : Interp Terminal Move Bool (Fin k) 1 where
  actOf mv _ σ _ := (σ 0, mv)
  condOf isEnd σ := decide (σ 0 ≠ if isEnd then e.endSym else e.startSym)

abbrev Act (k : ℕ) := AP k ⊕ Move
abbrev Cond (k : ℕ) := ((CQ k ⊕ GSProg.Cond8) ⊕ Test) ⊕ Bool
abbrev PProg (k : ℕ) := Prog (Act k) (Cond k)

noncomputable def interp (e : Env k) := Interp.sum (IT (Terminal := Terminal) e) (uInterp e)

def tapes (T : Fin 19 → STape (Fin k)) (U : TapeConfiguration k) : Fin 20 → STape (Fin k) :=
  Fin.append T (fun _ : Fin 1 => GSProg.toS U)

def lift (p : TP k) : PProg k := p.map Sum.inl Sum.inl

noncomputable def step (e : Env k) : PProg k :=
  .seq (lift (TextFeedTiming.lift (supplyNonempty e.blank e.mark)))
    (.ite (.inl (.inr .blankText)) .skip
      (.seq (.act (.inr .right)) (lift TextFeedAlign.moveRight)))

/-- One fixed loop for all prefix lengths; the length is not a parameter. -/
noncomputable def align (e : Env k) : PProg k := .loop (.inr true) (.inr .stay) (step e)

def rewind : PProg k := .seq (.loop (.inr false) (.inr .left) .skip) (.act (.inr .right))

noncomputable def program (e : Env k) : PProg k := .seq (align e) rewind

theorem inputFree (e : Env k) : InputFree (interp (Terminal := Terminal) e) :=
  InputFree.sum (inputFree_IF e) (fun _ _ _ => rfl)

theorem lift_runs {e : Env k} {p : TP k} {T T' : Fin 19 → STape (Fin k)} {ticks : ℕ}
    (h : RunsTo (IT (Terminal := Terminal) e) e.blank p T T' ticks) (U : TapeConfiguration k) :
    RunsTo (interp (Terminal := Terminal) e) e.blank (lift p) (tapes T U) (tapes T' U) ticks := by
  obtain ⟨tr, he, ht, hn⟩ := h
  have hh := exec_sum_inl (I2 := uInterp (Terminal := Terminal) e) he (tapes T U)
  rw [tapes, extend_castAdd_append] at hh
  refine ⟨_, hh, ?_, by simpa only [List.length_map] using hn⟩
  have hx := applyTrace_extend (Fin.castAddEmb 1) e.blank (tapes T U) tr T
  simpa only [tapes, extend_castAdd_append, ht] using hx

theorem moveU_runs (e : Env k) (T : Fin 19 → STape (Fin k)) (U : TapeConfiguration k) (mv : Move) :
    RunsTo (interp (Terminal := Terminal) e) e.blank (.act (.inr mv)) (tapes T U)
      (tapes T (Tape.step e.blank U U.focus mv)) 1 := by
  have he := exec_act (I := uInterp (Terminal := Terminal) e) (blank := e.blank)
    (fun _ _ _ => rfl) mv (fun _ => GSProg.toS U)
  have hh := exec_sum_inr (I1 := IT (Terminal := Terminal) e) he (tapes T U)
  rw [tapes, extend_natAdd_append] at hh
  refine ⟨_, hh, ?_, rfl⟩
  have ht : applyTrace e.blank (fun _ : Fin 1 => GSProg.toS U)
      [actVec (uInterp (Terminal := Terminal) e) mv (fun _ => GSProg.toS U)] =
      (fun _ : Fin 1 => GSProg.toS (Tape.step e.blank U U.focus mv)) := by
    funext j
    simp only [applyTrace_cons, applyTrace_nil, actVec, uInterp, GSProg.toS_step]
    rfl
  have hx := applyTrace_extend (Fin.natAddEmb 19) e.blank (tapes T U)
    [actVec (uInterp (Terminal := Terminal) e) mv (fun _ => GSProg.toS U)] (fun _ => GSProg.toS U)
  simpa only [tapes, extend_natAdd_append, ht] using hx

theorem blank_cond (e : Env k) (qt : QT k) (m : Mode) (S : Stage k) (U : TapeConfiguration k) :
    (interp (Terminal := Terminal) e).condOf (.inl (.inr .blankText))
      (fun j => (tapes (TextFeedControl.tapes e qt m S) U j).focus) =
      decide ((S GSTapes.tT).focus = e.blank) := by
  change (IT (Terminal := Terminal) e).condOf (.inr .blankText)
    (fun j => (tapes (TextFeedControl.tapes e qt m S) U (Fin.castAdd 1 j)).focus) = _
  simp only [tapes, Fin.append_left]
  exact blankText_cond e qt m S

theorem u_cond (e : Env k) (T : Fin 19 → STape (Fin k)) (U : TapeConfiguration k) (b : Bool) :
    (interp (Terminal := Terminal) e).condOf (.inr b) (fun j => (tapes T U j).focus) =
      decide (U.focus ≠ if b then e.endSym else e.startSym) := rfl

theorem moveU_action (e : Env k) (T : Fin 19 → STape (Fin k)) (U : TapeConfiguration k) (mv : Move) :
    (fun j => (tapes T U j).applyAction e.blank
      (actVec (interp (Terminal := Terminal) e) (.inr mv) (tapes T U) j)) =
      tapes T (Tape.step e.blank U U.focus mv) := by
  have hi : extend (Fin.natAddEmb 19) (fun _ : Fin 1 => GSProg.toS U) (tapes T U) = tapes T U := by
    exact extend_natAdd_append _ _ _
  have hv := actOf_transport (Fin.natAddEmb 19) (uInterp (Terminal := Terminal) e)
    mv none (fun _ => GSProg.toS U) (tapes T U)
  rw [hi] at hv
  change (fun j => (tapes T U j).applyAction e.blank
    (((uInterp (Terminal := Terminal) e).transport (Fin.natAddEmb 19)).actOf mv none
      (fun j => (tapes T U j).focus) j)) = _
  rw [hv]
  change (fun j => (tapes T U j).applyAction e.blank
    (extendVec (Fin.natAddEmb 19) (tapes T U)
      ((uInterp (Terminal := Terminal) e).actOf mv none (fun _ => U.focus)) j)) = _
  have hh := applyAction_extend (Fin.natAddEmb 19) e.blank (fun _ : Fin 1 => GSProg.toS U)
    (tapes T U) ((uInterp (Terminal := Terminal) e).actOf mv none (fun _ => U.focus))
  rw [hi] at hh
  rw [hh]
  have hu : (fun i : Fin 1 => (GSProg.toS U).applyAction e.blank
      ((uInterp (Terminal := Terminal) e).actOf mv none (fun _ => U.focus) i)) =
      (fun _ : Fin 1 => GSProg.toS (Tape.step e.blank U U.focus mv)) := by
    funext i
    simp only [uInterp, GSProg.toS_step]
  rw [hu]
  exact extend_natAdd_append _ _ _

/-- A successful alignment unit consumes a queued symbol, not a fresh arrival. -/
theorem step_success {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    {qt : QT k} {m : Mode} {M : Machine' k} {v Text : List (Fin k)} {d p r n : ℕ}
    (hblank : e.blank ∉ Text) (hmark : e.mark ∉ Text) (hn : n ≤ Text.length)
    (hq : Ready e.blank e.mark qt m M.Q) (hf : TextFeedAlign.AtFront M)
    (h : FeedInv' e.blank e.startSym e.endSym e.mark v Text d p r n M)
    (ha : M.m < n) (U : TapeConfiguration k) :
    let M' := stepRight' e.blank (fill' e.blank e.mark M)
    ∃ ticks qt' m', ticks ≤ 49 ∧
      RunsTo (interp (Terminal := Terminal) e) e.blank (step e)
        (tapes (TextFeedControl.tapes e qt m (GSProg.TS M.ts)) U)
        (tapes (TextFeedControl.tapes e qt' m' (GSProg.TS M'.ts)) (Tape.step e.blank U U.focus .right)) ticks ∧
      Ready e.blank e.mark qt' m' M'.Q := by
  have hh : (toList M.Q).head?.getD e.mark ≠ e.mark := by
    rw [← head?_eq hq.inv]
    exact (TextFeedProg2.head_ne_mark_iff hmark hn h).mpr ha
  obtain ⟨ticks, qt', m', hlen, hex, hr⟩ := supply_nonempty_runs (Terminal := Terminal) hc hmb M hq h.buf hh
  obtain ⟨tr, he, hlen', ht⟩ := texec_lift hex
  have hs := lift_runs ⟨tr, he, ht, hlen'⟩ U
  have hi := fill'_feedInv hmb hn ha (by rw [hf.1, hf.2]; omega) h
  have hne : (GSProg.TS (fill' e.blank e.mark M).ts GSTapes.tT).focus ≠ e.blank := by
    intro hb
    have hb' := (TextFeedProg2.read_tT_blank_iff hblank hn hi).mp hb
    change M.st.pos + M.st.q = M.m + 1 at hb'
    rw [hf.1, hf.2] at hb'
    omega
  obtain ⟨trR, heR, hnR, htR⟩ := TextFeedAlign.move_matches (Terminal := Terminal) e qt' m' (fill' e.blank e.mark M)
  have hR := lift_runs ⟨trR, heR, htR, hnR⟩ (Tape.step e.blank U U.focus .right)
  have hU := moveU_runs (Terminal := Terminal) e
    (TextFeedControl.tapes e qt' m' (GSProg.TS (fill' e.blank e.mark M).ts)) U .right
  have hb := (hU.seq hR).ite_neg (c := .inl (.inr .blankText)) (p := .skip)
    (by rw [blank_cond]; exact decide_eq_false hne)
  exact ⟨ticks + (1 + 1), qt', m', by omega, hs.seq hb, hr⟩

theorem step_empty {e : Env k} (hc : Function.Injective e.code)
    {qt : QT k} {m : Mode} {q : Queue (Fin k)} (hq : Ready e.blank e.mark qt m q)
    (S : Stage k) (U : TapeConfiguration k) (hS : (S GSTapes.tT).focus = e.blank)
    (hempty : (toList q).head?.getD e.mark = e.mark) :
    RunsTo (interp (Terminal := Terminal) e) e.blank (step e)
      (tapes (TextFeedControl.tapes e qt m S) U) (tapes (TextFeedControl.tapes e qt m S) U) 2 := by
  obtain ⟨tr, he, hn, ht⟩ := texec_lift (supply_empty_runs (Terminal := Terminal) hc hq S hempty)
  have hs := lift_runs ⟨tr, he, ht, hn⟩ U
  have hb : RunsTo (interp (Terminal := Terminal) e) e.blank .skip
      (tapes (TextFeedControl.tapes e qt m S) U) (tapes (TextFeedControl.tapes e qt m S) U) 0 :=
    ⟨[], exec_skip _, rfl, rfl⟩
  exact hs.seq (hb.ite_pos (c := .inl (.inr .blankText))
    (by rw [blank_cond]; exact decide_eq_true hS))

theorem align_cons {e : Env k} {T : Fin 19 → STape (Fin k)} {U : TapeConfiguration k}
    {V W : Fin 20 → STape (Fin k)} {a b : ℕ}
    (hc : U.focus ≠ e.endSym)
    (hb : RunsTo (interp (Terminal := Terminal) e) e.blank (step e) (tapes T U) V a)
    (hl : RunsTo (interp (Terminal := Terminal) e) e.blank (align e) V W b) :
    RunsTo (interp (Terminal := Terminal) e) e.blank (align e) (tapes T U) W (1 + (a + b)) := by
  obtain ⟨tr, he, ht, hn⟩ := hb
  obtain ⟨tr', he', ht', hn'⟩ := hl
  have hh : (fun j => (tapes T U j).applyAction e.blank
      (actVec (interp (Terminal := Terminal) e) (.inr .stay) (tapes T U) j)) = tapes T U := by
    rw [moveU_action]
    rfl
  refine ⟨_ :: (tr ++ tr'), exec_loop_cont (inputFree e) ?_ ?_ ?_, ?_, ?_⟩
  · rw [u_cond]
    exact decide_eq_true hc
  · rw [hh]; exact he
  · rw [hh, ht]; exact he'
  · rw [applyTrace_cons, hh, applyTrace_append, ht, ht']
  · simp only [List.length_cons, List.length_append, hn, hn']; omega

/-- If the queued backlog already covers the remaining prefix, the fixed
marker-controlled loop terminates in at most 50 actions per prefix symbol. -/
theorem align_runs {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    {u v Text : List (Fin k)} {d p r n : ℕ}
    (hblank : e.blank ∉ Text) (hmark : e.mark ∉ Text) (hend : e.endSym ∉ u)
    (hn : n ≤ Text.length) :
    ∀ (N i : ℕ) (M : Machine' k) (qt : QT k) (m : Mode) (U : TapeConfiguration k),
    i + N = u.length → M.m + N ≤ n →
    Ready e.blank e.mark qt m M.Q → TextFeedAlign.AtFront M →
    FeedInv' e.blank e.startSym e.endSym e.mark v Text d p r n M →
    Tape.SeqView e.blank U (GSPre.pword e.startSym e.endSym u) (i + 1) →
    ∃ ticks qt' m' M' U', ticks ≤ 50 * N ∧
      RunsTo (interp (Terminal := Terminal) e) e.blank (align e)
        (tapes (TextFeedControl.tapes e qt m (GSProg.TS M.ts)) U)
        (tapes (TextFeedControl.tapes e qt' m' (GSProg.TS M'.ts)) U') ticks ∧
      Ready e.blank e.mark qt' m' M'.Q ∧
      FeedInv' e.blank e.startSym e.endSym e.mark v Text d p r n M' ∧
      TextFeedAlign.AtFront M' ∧ M'.m = M.m + N ∧
      Tape.SeqView e.blank U' (GSPre.pword e.startSym e.endSym u) (u.length + 1) := by
  intro N
  induction N with
  | zero =>
    intro i M qt m U hi _ hq hf h hu
    have hi' : i = u.length := by omega
    refine ⟨0, qt, m, M, U, by omega, ?_, hq, h, hf, by omega, hi' ▸ hu⟩
    refine ⟨[], exec_loop_stop ?_, rfl, rfl⟩
    rw [u_cond]
    apply decide_eq_false
    simp only [↓reduceIte, not_not]
    exact GSPre.read_pat_end hu hi'
  | succ N ih =>
    intro i M qt m U hi hroom hq hf h hu
    have ha : M.m < n := by omega
    have hi' : i < u.length := by omega
    have hU : U.focus ≠ e.endSym := by
      intro he
      have he' := (GSPre.read_pat_end_iff hend hu).mp he
      omega
    obtain ⟨ticks, qt1, m1, hlen, hs, hr⟩ := step_success (Terminal := Terminal)
      hc hmb hblank hmark hn hq hf h ha U
    have hnext : TextFeedAlign.advance e.blank e.mark n M = stepRight' e.blank (fill' e.blank e.mark M) := by
      rw [TextFeedAlign.advance, if_pos ha]
    obtain ⟨hinv, hfront, _⟩ := TextFeedAlign.advance_inv hmb hn hf h
    rw [hnext] at hinv hfront
    have hu' : Tape.SeqView e.blank (Tape.step e.blank U U.focus .right)
        (GSPre.pword e.startSym e.endSym u) ((i + 1) + 1) :=
      Tape.seq_move_right hu (by rw [GSPre.pword_length]; omega)
    obtain ⟨ticks', qt', m', M', U', hlen', hl, hr', hinv', hfront', hm', hu''⟩ :=
      ih (i + 1) (stepRight' e.blank (fill' e.blank e.mark M)) qt1 m1
        (Tape.step e.blank U U.focus .right) (by omega) (by change M.m + 1 + N ≤ n; omega)
        hr hfront hinv hu'
    refine ⟨1 + (ticks + ticks'), qt', m', M', U', by omega,
      align_cons hU hs hl, hr', hinv', hfront', ?_, hu''⟩
    change M'.m = M.m + 1 + N at hm'
    omega

theorem rewind_loop_runs {e : Env k} {u : List (Fin k)}
    (hsu : e.startSym ∉ u) (hse : e.startSym ≠ e.endSym)
    (T : Fin 19 → STape (Fin k)) :
    ∀ (i : ℕ) (U : TapeConfiguration k),
      Tape.SeqView e.blank U (GSPre.pword e.startSym e.endSym u) i →
      ∃ U', RunsTo (interp (Terminal := Terminal) e) e.blank (.loop (.inr false) (.inr .left) .skip)
        (tapes T U) (tapes T U') i ∧
        Tape.SeqView e.blank U' (GSPre.pword e.startSym e.endSym u) 0 := by
  intro i
  induction i with
  | zero =>
    intro U hu
    have hr := hu.read_eq
    change some e.startSym = some U.focus at hr
    refine ⟨U, ⟨[], exec_loop_stop ?_, rfl, rfl⟩, hu⟩
    rw [u_cond]
    apply decide_eq_false
    change ¬ U.focus ≠ e.startSym
    exact not_not_intro (Option.some.inj hr).symm
  | succ i ih =>
    intro U hu
    have hr := hu.read_eq
    change (u ++ [e.endSym])[i]? = some U.focus at hr
    have hmem := List.mem_of_getElem? hr
    have hne : U.focus ≠ e.startSym := by
      intro he
      rcases List.mem_append.mp hmem with hm | hm
      · exact hsu (he ▸ hm)
      · have hh : U.focus = e.endSym := List.mem_singleton.mp hm
        exact hse (he.symm.trans hh)
    have hl := Tape.seq_move_left hu
    obtain ⟨U', ⟨tr, he, ht, hn⟩, hu'⟩ := ih (Tape.step e.blank U U.focus .left) hl
    refine ⟨U', ⟨_ :: ([] ++ tr), exec_loop_cont (inputFree e) ?_ ?_ ?_, ?_, ?_⟩, hu'⟩
    · rw [u_cond]
      exact decide_eq_true hne
    · exact exec_skip _
    · rw [applyTrace_nil, moveU_action]
      exact he
    · rw [List.nil_append, applyTrace_cons, moveU_action, ht]
    · simp only [List.nil_append, List.length_cons, hn]

theorem rewind_runs {e : Env k} {u : List (Fin k)}
    (hsu : e.startSym ∉ u) (hse : e.startSym ≠ e.endSym)
    (T : Fin 19 → STape (Fin k)) (i : ℕ) (U : TapeConfiguration k)
    (hu : Tape.SeqView e.blank U (GSPre.pword e.startSym e.endSym u) i) :
    ∃ U', RunsTo (interp (Terminal := Terminal) e) e.blank rewind (tapes T U) (tapes T U') (i + 1) ∧
      Tape.SeqView e.blank U' (GSPre.pword e.startSym e.endSym u) 1 := by
  obtain ⟨U', hr, hv⟩ := rewind_loop_runs (Terminal := Terminal) hsu hse T i U hu
  refine ⟨Tape.step e.blank U' U'.focus .right, hr.seq (moveU_runs e T U' .right), ?_⟩
  exact Tape.seq_move_right hv (by rw [GSPre.pword_length]; omega)

/-- Starting at scanner position zero, the fixed source program consumes
the prefix from the existing FIFO and restores U to its first symbol.
Neither input length nor prefix length occurs in the source program. -/
theorem program_runs {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    {u v Text : List (Fin k)} {d p r n : ℕ}
    (hblank : e.blank ∉ Text) (hmark : e.mark ∉ Text)
    (hend : e.endSym ∉ u) (hsu : e.startSym ∉ u) (hse : e.startSym ≠ e.endSym)
    (hn : n ≤ Text.length) (hroom : u.length ≤ n)
    (M : Machine' k) (qt : QT k) (m : Mode) (U : TapeConfiguration k)
    (hq : Ready e.blank e.mark qt m M.Q) (hf : TextFeedAlign.AtFront M) (hm : M.m = 0)
    (h : FeedInv' e.blank e.startSym e.endSym e.mark v Text d p r n M)
    (hu : Tape.SeqView e.blank U (GSPre.pword e.startSym e.endSym u) 1) :
    ∃ ticks qt' m' M' U', ticks ≤ 51 * u.length + 2 ∧
      RunsTo (interp (Terminal := Terminal) e) e.blank (program e)
        (tapes (TextFeedControl.tapes e qt m (GSProg.TS M.ts)) U)
        (tapes (TextFeedControl.tapes e qt' m' (GSProg.TS M'.ts)) U') ticks ∧
      Ready e.blank e.mark qt' m' M'.Q ∧
      FeedInv' e.blank e.startSym e.endSym e.mark v Text d p r n M' ∧
      M'.st.pos = u.length ∧ M'.st.q = 0 ∧ M'.m = u.length ∧
      Tape.SeqView e.blank U' (GSPre.pword e.startSym e.endSym u) 1 := by
  obtain ⟨ticks, qt', m', M', U', hlen, ha, hr, hi, hfront, hm', hu'⟩ :=
    align_runs (Terminal := Terminal) hc hmb hblank hmark hend hn u.length 0 M qt m U
      (by omega) (by omega) hq hf h hu
  obtain ⟨U'', hw, hu''⟩ := rewind_runs (Terminal := Terminal) hsu hse
    (TextFeedControl.tapes e qt' m' (GSProg.TS M'.ts)) (u.length + 1) U' hu'
  refine ⟨ticks + (u.length + 1 + 1), qt', m', M', U'', by omega,
    ha.seq hw, hr, hi, ?_, hfront.2, ?_, hu''⟩ <;> have := hfront.1 <;> omega

/-- info: 'PalPeg.TextFeedPrefixControl.program_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms program_runs

/-- info: 'PalPeg.TextFeedPrefixControl.align_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms align_runs

/-- info: 'PalPeg.TextFeedPrefixControl.step_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms step_success

/-- info: 'PalPeg.TextFeedPrefixControl.step_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms step_empty

end PalPeg.TextFeedPrefixControl
