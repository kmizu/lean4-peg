import PalPeg.TextFeedPrefixFinish

/-! Phase-indexed progress of the atomic worker. Arrival changes only the
FIFO and the arrival count, not the remaining-work rank. Once the prefix
has arrived, each worker call strictly lowers the rank until completion. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPrefixRank
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.TextFeedControl PalPeg.TextFeed
open PalPeg.TextFeedPrefixAtomic PalPeg.TextFeedPrefixCycle PalPeg.TextFeedPrefixFinish

variable {k : ℕ}

structure Rep (e : Env k) (u v Text : List (Fin k)) (d p r n : ℕ)
    (M : Machine' k) (U : TapeConfiguration k) (i j : ℕ) : Prop where
  feed : FeedInv' e.blank e.startSym e.endSym e.mark v Text d p r n M
  pos : M.st.pos = i
  q : M.st.q = 0
  pat : Tape.SeqView e.blank U (GSPre.pword e.startSym e.endSym u) j

inductive Good (e : Env k) (u v Text : List (Fin k)) (d p r n : ℕ) :
    ℕ → (Stack Act Cond × Model k) → Prop
  | loop {M U i} (h : Rep e u v Text d p r n M U i (i + 1)) (hm : M.m = i) (hi : i ≤ u.length) :
      Good e u v Text d p r n (4 * (u.length - i) + u.length + 2) (loopS, data M U)
  | fill {M U i} (h : Rep e u v Text d p r n M U i (i + 1)) (hm : M.m = i) (hi : i < u.length) :
      Good e u v Text d p r n (4 * (u.length - i) + u.length + 2 - 1) (fillS, data M U)
  | gateReady {M U i} (h : Rep e u v Text d p r n M U i (i + 1)) (hm : M.m = i + 1) (hi : i < u.length) :
      Good e u v Text d p r n (4 * (u.length - i) + u.length + 2 - 2) (gateS, data M U)
  | gateEmpty {M U i} (h : Rep e u v Text d p r n M U i (i + 1)) (hm : M.m = i) (hi : i < u.length) :
      Good e u v Text d p r n (4 * (u.length - i) + u.length + 2) (gateS, data M U)
  | right {M U i} (h : Rep e u v Text d p r n M U i (i + 2)) (hm : M.m = i + 1) (hi : i < u.length) :
      Good e u v Text d p r n (4 * (u.length - i) + u.length + 2 - 3) (rightS, data M U)
  | rewind {M U j} (h : Rep e u v Text d p r n M U u.length j) (hm : M.m = u.length) (hj : j ≤ u.length) :
      Good e u v Text d p r n (j + 1) (rewindS, data M U)
  | done {M U} (h : Rep e u v Text d p r n M U u.length 1) (hm : M.m = u.length) :
      Good e u v Text d p r n 0 ([], data M U)

theorem Good.bound {e : Env k} {u v Text : List (Fin k)} {d p r n fuel : ℕ}
    {z : Stack Act Cond × Model k} (h : Good e u v Text d p r n fuel z) :
    fuel ≤ 5 * u.length + 2 := by
  cases h <;> omega

theorem Rep.arrive {e : Env k} {u v Text : List (Fin k)} {d p r n i j : ℕ}
    {M : Machine' k} {U : TapeConfiguration k} {a : Fin k}
    (h : Rep e u v Text d p r n M U i j) (hmb : e.mark ≠ e.blank)
    (hn : n < Text.length) (ha : Text[n]? = some a) :
    Rep e u v Text d p r (n + 1) (arrive' e.blank e.mark a M) U i j :=
  ⟨arrive'_feedInv hmb hn ha h.feed, h.pos, h.q, h.pat⟩

def arrive (a : Fin k) (z : Stack Act Cond × Model k) : Stack Act Cond × Model k :=
  (z.1, { z.2 with q := snoc z.2.q a })

theorem arrive_data (e : Env k) (a : Fin k) (s : Stack Act Cond) (M : Machine' k) (U : TapeConfiguration k) :
    arrive a (s, data M U) = (s, data (arrive' e.blank e.mark a M) U) := rfl

/-- New input preserves both the phase and its rank. -/
theorem Good.arrive {e : Env k} {u v Text : List (Fin k)} {d p r n fuel : ℕ}
    {z : Stack Act Cond × Model k} {a : Fin k}
    (h : Good e u v Text d p r n fuel z) (hmb : e.mark ≠ e.blank)
    (hn : n < Text.length) (ha : Text[n]? = some a) :
    Good e u v Text d p r (n + 1) fuel (arrive a z) := by
  cases h with
  | loop h hm hi => rw [arrive_data e]; exact Good.loop (h.arrive hmb hn ha) hm hi
  | fill h hm hi => rw [arrive_data e]; exact Good.fill (h.arrive hmb hn ha) hm hi
  | gateReady h hm hi => rw [arrive_data e]; exact Good.gateReady (h.arrive hmb hn ha) hm hi
  | gateEmpty h hm hi => rw [arrive_data e]; exact Good.gateEmpty (h.arrive hmb hn ha) hm hi
  | right h hm hi => rw [arrive_data e]; exact Good.right (h.arrive hmb hn ha) hm hi
  | rewind h hm hi => rw [arrive_data e]; exact Good.rewind (h.arrive hmb hn ha) hm hi
  | done h hm => rw [arrive_data e]; exact Good.done (h.arrive hmb hn ha) hm

theorem Rep.notEnd {e : Env k} {u v Text : List (Fin k)} {d p r n i : ℕ}
    {M : Machine' k} {U : TapeConfiguration k}
    (h : Rep e u v Text d p r n M U i (i + 1)) (hend : e.endSym ∉ u) (hi : i < u.length) :
    U.focus ≠ e.endSym := by
  intro he
  have := (GSPre.read_pat_end_iff hend h.pat).mp he
  omega

theorem Rep.notStart {e : Env k} {u v Text : List (Fin k)} {d p r n i j : ℕ}
    {M : Machine' k} {U : TapeConfiguration k}
    (h : Rep e u v Text d p r n M U i (j + 1)) (hsu : e.startSym ∉ u) (hse : e.startSym ≠ e.endSym) :
    U.focus ≠ e.startSym := by
  have hr := h.pat.read_eq
  change (u ++ [e.endSym])[j]? = some U.focus at hr
  have hm := List.mem_of_getElem? hr
  intro he
  rcases List.mem_append.mp hm with hm | hm
  · exact hsu (he ▸ hm)
  · exact hse (he.symm.trans (List.mem_singleton.mp hm))

/-- Once all prefix symbols have arrived, a worker call cannot stutter.
Arrivals may still be interleaved between these calls. -/
theorem Good.progress_of_supply {e : Env k} {u v Text : List (Fin k)} {d p r n fuel : ℕ}
    {z : Stack Act Cond × Model k} (h : Good e u v Text d p r n fuel z)
    (hmb : e.mark ≠ e.blank) (hblank : e.blank ∉ Text) (hmark : e.mark ∉ Text)
    (hend : e.endSym ∉ u) (hsu : e.startSym ∉ u) (hse : e.startSym ≠ e.endSym)
    (hn : n ≤ Text.length)
    (hok : (toList z.2.q).head?.getD e.mark ≠ e.mark ∨ z.1 ≠ fillS) :
    Good e u v Text d p r n (fuel - 1) (tick e z) := by
  cases h with
  | @loop M U i h hm hi =>
    by_cases hlt : i < u.length
    · rw [tick_of_step (loop_step e (data M U) (h.notEnd hend hlt))]
      exact Good.fill h hm hlt
    · have hie : i = u.length := by omega
      have he : U.focus = e.endSym := GSPre.read_pat_end h.pat hie
      rw [tick_of_step (end_step e (data M U) he hse), move_data]
      have hpat := Tape.seq_move_left h.pat
      have hh : Rep e u v Text d p r n M (Tape.step e.blank U U.focus .left) u.length i :=
        ⟨h.feed, h.pos.trans hie, h.q, hpat⟩
      have hr := Good.rewind hh (hm.trans hie) hi
      convert hr using 1; omega
  | @fill M U i h hm hi =>
    have hne : (toList M.Q).head?.getD e.mark ≠ e.mark := by
      rcases hok with hh | hh
      · exact hh
      · exact (hh rfl).elim
    have hlt : M.m < n := by
      rw [← head?_eq h.feed.qinv] at hne
      exact (TextFeedProg2.head_ne_mark_iff hmark hn h.feed).mp hne
    rw [tick_of_step (fill_step e (data M U)), supply_data M U h.feed.qinv h.feed.buf hne]
    have hfront : M.st.pos + M.st.q = M.m := by rw [h.pos, h.q, hm]; omega
    have hh : Rep e u v Text d p r n (fill' e.blank e.mark M) U i (i + 1) :=
      ⟨fill'_feedInv hmb hn hlt hfront h.feed, h.pos, h.q, h.pat⟩
    have hr := Good.gateReady hh (by change M.m + 1 = i + 1; omega) hi
    convert hr using 1; omega
  | @gateReady M U i h hm hi =>
    have hne : ((data M U).S GSTapes.tT).focus ≠ e.blank := by
      intro he
      have hh := (TextFeedProg2.read_tT_blank_iff hblank hn h.feed).mp he
      rw [h.pos, h.q, hm] at hh
      omega
    rw [tick_of_step (gate_ready_step e (data M U) hne), move_data]
    have hh : Rep e u v Text d p r n M (Tape.step e.blank U U.focus .right) i (i + 2) :=
      ⟨h.feed, h.pos, h.q, Tape.seq_move_right h.pat (by rw [GSPre.pword_length]; omega)⟩
    have hr := Good.right hh hm hi
    convert hr using 1; omega
  | @gateEmpty M U i h hm hi =>
    have he : ((data M U).S GSTapes.tT).focus = e.blank :=
      (TextFeedProg2.read_tT_blank_iff hblank hn h.feed).mpr (by rw [h.pos, h.q, hm]; omega)
    rw [tick_of_step (gate_wait_step e (data M U) he (h.notEnd hend hi))]
    exact Good.fill h hm hi
  | @right M U i h hm hi =>
    rw [tick_of_step (right_step e (data M U)), right_data]
    have hh : Rep e u v Text d p r n (stepRight' e.blank M) U (i + 1) ((i + 1) + 1) := by
      refine ⟨stepRight'_feedInv ?_ (h.feed.mle.trans hn) h.feed, ?_, h.q, h.pat⟩
      · rw [h.pos, h.q, hm]
      · change M.st.pos + 1 = i + 1
        rw [h.pos]
    have hr := Good.loop hh hm (by omega)
    convert hr using 1; omega
  | @rewind M U j h hm hj =>
    cases j with
    | zero =>
      have hr := h.pat.read_eq
      have he : U.focus = e.startSym := (Option.some.inj hr).symm
      rw [tick_of_step (rewind_end_step e (data M U) he), move_data]
      exact Good.done ⟨h.feed, h.pos, h.q,
        Tape.seq_move_right h.pat (by rw [GSPre.pword_length]; omega)⟩ hm
    | succ j =>
      rw [tick_of_step (rewind_more_step e (data M U) (h.notStart hsu hse)), move_data]
      exact Good.rewind ⟨h.feed, h.pos, h.q, Tape.seq_move_left h.pat⟩ hm (by omega)
  | done h hm =>
    rw [tick_nil]
    exact Good.done h hm

theorem Good.supply_available {e : Env k} {u v Text : List (Fin k)} {d p r n fuel : ℕ}
    {z : Stack Act Cond × Model k} (h : Good e u v Text d p r n fuel z)
    (hmark : e.mark ∉ Text) (hn : n ≤ Text.length) (hroom : u.length ≤ n) :
    (toList z.2.q).head?.getD e.mark ≠ e.mark ∨ z.1 ≠ fillS := by
  cases h with
  | @fill M U i h hm hi =>
    left
    change (toList M.Q).head?.getD e.mark ≠ e.mark
    rw [← head?_eq h.feed.qinv]
    exact (TextFeedProg2.head_ne_mark_iff hmark hn h.feed).mpr (by omega)
  | loop _ _ _ => right; simp [loopS, fillS]
  | gateReady _ _ _ => right; simp [gateS, fillS, gate, body]
  | gateEmpty _ _ _ => right; simp [gateS, fillS, gate, body]
  | right _ _ _ => right; simp [rightS, fillS, body]
  | rewind _ _ _ => right; simp [rewindS, fillS, body]
  | done _ _ => right; simp [fillS]

theorem Good.progress {e : Env k} {u v Text : List (Fin k)} {d p r n fuel : ℕ}
    {z : Stack Act Cond × Model k} (h : Good e u v Text d p r n fuel z)
    (hmb : e.mark ≠ e.blank) (hblank : e.blank ∉ Text) (hmark : e.mark ∉ Text)
    (hend : e.endSym ∉ u) (hsu : e.startSym ∉ u) (hse : e.startSym ≠ e.endSym)
    (hn : n ≤ Text.length) (hroom : u.length ≤ n) :
    Good e u v Text d p r n (fuel - 1) (tick e z) :=
  h.progress_of_supply hmb hblank hmark hend hsu hse hn (h.supply_available hmark hn hroom)

theorem Good.preserve {e : Env k} {u v Text : List (Fin k)} {d p r n fuel : ℕ}
    {z : Stack Act Cond × Model k} (h : Good e u v Text d p r n fuel z)
    (hmb : e.mark ≠ e.blank) (hblank : e.blank ∉ Text) (hmark : e.mark ∉ Text)
    (hend : e.endSym ∉ u) (hsu : e.startSym ∉ u) (hse : e.startSym ≠ e.endSym)
    (hn : n ≤ Text.length) :
    ∃ fuel', Good e u v Text d p r n fuel' (tick e z) := by
  by_cases hok : (toList z.2.q).head?.getD e.mark ≠ e.mark ∨ z.1 ≠ fillS
  · exact ⟨_, h.progress_of_supply hmb hblank hmark hend hsu hse hn hok⟩
  · have hst : z.1 = fillS := by by_contra hs; exact hok (Or.inr hs)
    have heq : (toList z.2.q).head?.getD e.mark = e.mark := by by_contra hs; exact hok (Or.inl hs)
    cases h with
    | @fill M U i h hm hi =>
      change (toList M.Q).head?.getD e.mark = e.mark at heq
      rw [tick_of_step (fill_step e (data M U))]
      have he : effect e .supply (data M U) = data M U := by
        change (let qS := TextFeedAtomic.supplyEffect e M.Q (GSProg.TS M.ts); Model.mk qS.1 qS.2 U) = _
        rw [TextFeedAtomic.supplyEffect, if_pos heq]
        rfl
      rw [he]
      exact ⟨_, Good.gateEmpty h hm hi⟩
    | loop _ _ _ => simp [loopS, fillS] at hst
    | gateReady _ _ _ => simp [gateS, fillS, gate, body] at hst
    | gateEmpty _ _ _ => simp [gateS, fillS, gate, body] at hst
    | right _ _ _ => simp [rightS, fillS, body] at hst
    | rewind _ _ _ => simp [rewindS, fillS, body] at hst
    | done _ _ => simp [fillS] at hst

theorem Good.finished {e : Env k} {u v Text : List (Fin k)} {d p r n : ℕ}
    {z : Stack Act Cond × Model k} (h : Good e u v Text d p r n 0 z) :
    z.1 = [] ∧ ∃ M U, z.2 = data M U ∧ Rep e u v Text d p r n M U u.length 1 ∧ M.m = u.length := by
  generalize hzero : (0 : ℕ) = fuel at h
  cases h with
  | loop _ _ _ => omega
  | fill _ _ hi => omega
  | gateReady _ _ hi => omega
  | gateEmpty _ _ _ => omega
  | right _ _ hi => omega
  | rewind _ _ _ => omega
  | done h hm => exact ⟨rfl, _, _, rfl, h, hm⟩

theorem Good.complete {e : Env k} {u v Text : List (Fin k)} {d p r n fuel : ℕ}
    {z : Stack Act Cond × Model k} (h : Good e u v Text d p r n fuel z)
    (hmb : e.mark ≠ e.blank) (hblank : e.blank ∉ Text) (hmark : e.mark ∉ Text)
    (hend : e.endSym ∉ u) (hsu : e.startSym ∉ u) (hse : e.startSym ≠ e.endSym)
    (hn : n ≤ Text.length) (hroom : u.length ≤ n) :
    Good e u v Text d p r n 0 ((tick e)^[fuel] z) := by
  induction fuel generalizing z with
  | zero => exact h
  | succ fuel ih =>
    rw [Function.iterate_succ_apply]
    exact ih (h.progress hmb hblank hmark hend hsu hse hn hroom)

/-- info: 'PalPeg.TextFeedPrefixRank.Good.progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Good.progress

/-- info: 'PalPeg.TextFeedPrefixRank.Good.arrive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Good.arrive

end PalPeg.TextFeedPrefixRank
