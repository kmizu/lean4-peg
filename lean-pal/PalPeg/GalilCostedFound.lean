import PalPeg.GalilTraceCost
import PalPeg.GalilPlaceEvents
import PalPeg.GalilCycleNoShift
import PalPeg.GalilRoundConstruct

/-!
# `CostedRun` data for the found cycles

From the found comparison at `sF` to the restarted state, a sound run of `k`
ticks together with a `GalilTraceCost.CostedRun` of `k + p0` ticks, where
`p0` counting ticks were pending before the found comparison (charged to its
piece).  Pieces:

* one `cmpPiece` per matched comparison (found, preparation, watch, round and
  final segments) at the new right place, whose wait is the counting ticks
  since the previous comparison (`≤ delay − 1`, `watchSeg_costed`);
* one `shiftPiece` at each terminal mismatch (first shift and every round):
  wait, the comparison tick and a `ShiftEv` of `h+1` ticks advancing `h`
  (`shift_costed`, `rounds_costed`);
* the breaking match carries the restart tick in its wait (`break_costed`).

Wait ticks (`¬ canRight`) cannot occur before a state strictly left of the
last gap (`no_wait`), so every tick is charged.  Separation comes from the
right head moving one place per comparison.
-/

set_option autoImplicit false

namespace PalPeg.GalilCostedFound

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open PalPeg.GalilScaffoldChainInputSupply
open Manacher GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier
open PalPeg.GalilTraceCost PalPeg.GalilIntervalCost

/-! ## Pieces and costed-run plumbing -/

/-- A comparison piece without slot events. -/
def cmpPiece (place wait : ℕ) (hw : wait ≤ 2048) : Piece :=
  ⟨place, [], [], wait, true, hw, fun h => absurd h (by decide), by simp⟩

/-- A comparison piece carrying one shift event. -/
def shiftPiece (place wait : ℕ) (hw : wait ≤ 2048) (e : ShiftEv) : Piece :=
  ⟨place, [e], [], wait, true, hw, fun h => absurd h (by decide), by simp⟩

theorem cmpPiece_ticks (place wait : ℕ) (hw : wait ≤ 2048) :
    (cmpPiece place wait hw).ticks = wait + 1 := by
  simp [cmpPiece, Piece.ticks, Piece.ev, Piece.cmpN, PlaceEvent.slot, PlaceEvent.shiftTicks,
    PlaceEvent.fbTicks, PlaceEvent.replayTicks]

theorem cmpPiece_adv (place wait : ℕ) (hw : wait ≤ 2048) : (cmpPiece place wait hw).adv = 0 := by
  simp [cmpPiece, Piece.adv, Piece.ev, PlaceEvent.adv, PlaceEvent.shiftAdv, PlaceEvent.fbAdv]

theorem shiftPiece_ticks (place wait : ℕ) (hw : wait ≤ 2048) (e : ShiftEv) :
    (shiftPiece place wait hw e).ticks = e.ticks + wait + 1 := by
  simp [shiftPiece, Piece.ticks, Piece.ev, Piece.cmpN, PlaceEvent.slot, PlaceEvent.shiftTicks,
    PlaceEvent.fbTicks, PlaceEvent.replayTicks]

theorem shiftPiece_adv (place wait : ℕ) (hw : wait ≤ 2048) (e : ShiftEv) :
    (shiftPiece place wait hw e).adv = e.adv := by
  simp [shiftPiece, Piece.adv, Piece.ev, PlaceEvent.adv, PlaceEvent.shiftAdv, PlaceEvent.fbAdv]

/-- A costed run only sees the positions of the centre and the right head at its ends. -/
theorem costedRun_congr {a a' b b' : GalilVM} {k : ℕ} {L : List Piece}
    (ha : position a.right = position a'.right) (hac : position a.center = position a'.center)
    (hb : position b.right = position b'.right) (hbc : position b.center = position b'.center)
    (h : CostedRun a' b' k L) : CostedRun a b k L :=
  ⟨h.ticks, by rw [hbc, hac]; exact h.centre, by rw [ha, hb]; exact h.right_mono,
    fun p hp => by rw [ha, hb]; exact h.places p hp, h.sep⟩

/-- A one-piece costed run. -/
theorem costedRun_single {a b : GalilVM} (p : Piece)
    (hpl : position a.right < p.place) (hpr : p.place ≤ position b.right)
    (hc : position b.center = position a.center + p.adv) :
    CostedRun a b p.ticks [p] :=
  ⟨by simp, by simpa using hc, by omega,
    fun q hq => by rw [List.mem_singleton.1 hq]; exact ⟨hpl, hpr⟩, List.pairwise_singleton _ _⟩

/-- A run of zero pieces between states with the same positions. -/
theorem costedRun_same {a b : GalilVM} (hr : position a.right = position b.right)
    (hc : position a.center = position b.center) : CostedRun a b 0 [] :=
  costedRun_congr rfl rfl hr.symm hc.symm (costedRun_nil a)


/-! ## Segments -/

/-- A matched scan segment is a general segment. -/
theorem watchSeg_of_scanSeg (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) {n : ℕ}
    {c c' : Control} {s t : GalilVM} (h : ScanSeg P q first delay n c s c' t) :
    WatchSeg P q first delay c s c' t := by
  induction h with
  | stop c s => exact .stop _ _
  | wait c s s' hm hr hn hb _ ih => exact .wait c s s' hm hr hn hb ih
  | count c s s' hm hr ha hc hb _ ih => exact .count c s s' hm hr ha hc hb ih
  | «match» c s vs vq o hm hr ha hc hcont hcmp hmt hwatch hq ho _ ih =>
    have hmatch : read (left s.left) = read (right s.right) := by
      obtain ⟨⟨hl0, hr0, _⟩, _⟩ := hcmp
      rw [scanLens.get_set] at hl0 hr0
      have := matched_parts P q first hmt
      rw [hl0, hr0] at this; exact this
    obtain ⟨w', hw'⟩ := hwatch
    have hne : s.chain ≠ .idle :=
      chainTick_source_ne_idle (compare_parts P q first hcmp hmatch).2.2 (by rw [hw']; intro h0; cases h0)
    exact .match c s vs vq o hm hr ha hc hne hcmp hmt hq ho ih

/-- A head that can still move right sits strictly before the last gap. -/
theorem pos_lt_of_canRight {raw : List (Fin 2)} {cen r : ℕ} {l rr : PlaceHead}
    (hi : ScanInvariant raw cen r l rr) (hc : canRight rr) : position rr < 2 * raw.length := by
  have h2 : ¬ position rr = 2 * raw.length := fun h0 =>
    (GalilEndOfInput.not_canRight_iff rr raw hi.rightRep hi.rightPresent).2 h0 hc
  have h3 := (represented_position _ raw hi.rightRep hi.rightPresent).2
  have h4 : position rr ≤ 2 * raw.length := by
    unfold position; split <;> omega
  omega

/-- A wait tick cannot precede a state strictly before the last gap. -/
theorem no_wait {raw : List (Fin 2)} {cen r r' : ℕ} {l l' rr rr' : PlaceHead}
    (hi : ScanInvariant raw cen r l rr) (hi' : ScanInvariant raw cen r' l' rr') (hrr : r ≤ r')
    (hn : ¬ canRight rr) (hc : position rr' < 2 * raw.length) : False := by
  have h1 := (GalilEndOfInput.not_canRight_iff rr raw hi.rightRep hi.rightPresent).1 hn
  have e1 := hi.rightPos
  have e2 := hi'.rightPos
  omega

/-- **A costed general segment.**  Entering with `p` pending counting ticks
(`p + clock ≤ delay`) and ending at a state
(strictly before the last gap) is a sound run of `k` ticks whose matched comparisons form the pieces of a
costed run of `kc` ticks, leaving `p'` pending ticks with `k + p = kc + p'`. -/
theorem watchSeg_costed (raw : List (Fin 2)) (P : Shared) (hP : P.onLetter = onLetterVM raw)
    (hP' : P.leftFirst = leftFirstVM) (q : ℕ) (first : Fin 9) (delay : ℕ) (hd : delay ≤ 2048)
    {c c' : Control} {s t : GalilVM} (h : WatchSeg P q first delay c s c' t) (cen : ℕ) :
    ∀ (r p : ℕ), ScanInvariant raw cen r s.left s.right → OutputRel raw c s →
      p + c.clock ≤ delay → position t.right < 2 * raw.length →
      ∃ (k kc p' r' : ℕ) (L : List Piece),
        StepsAll (galilFrameS P q first) delay (SoundOut raw) k ⟨c, s⟩ ⟨c', t⟩ ∧
        k + p = kc + p' ∧ p' + c'.clock ≤ delay ∧ CostedRun s t kc L ∧
        r ≤ r' ∧ ScanInvariant raw cen r' t.left t.right ∧ t.center = s.center := by
  induction h with
  | stop c s =>
    intro r p hi ho hp _
    exact ⟨0, 0, p, r, [], .zero _ ho, by omega, hp, costedRun_nil s, le_rfl, hi, rfl⟩
  | wait c s s' hm hr hn hb _ ih =>
    intro r p hi ho hp hct
    obtain ⟨hl, hr', _, _⟩ := background_frame P q first hb
    obtain ⟨k, kc, p', r', L, _, _, _, _, hrr, hi', _⟩ :=
      ih r p (by rw [hl, hr']; exact hi) (outputRel_background raw P q first hb rfl ho) hp hct
    exact absurd (no_wait hi hi' hrr hn hct) id
  | count c s s' hm hr ha hc hb _ ih =>
    intro r p hi ho hp hct
    obtain ⟨hl, hr', hcen, _⟩ := background_frame P q first hb
    obtain ⟨k, kc, p', r', L, hs, hk, hp', hcr, hrr, hi', hce⟩ :=
      ih r (p+1) (by rw [hl, hr']; exact hi) (outputRel_background raw P q first hb rfl ho)
        (by show p + 1 + (c.clock - 1) ≤ delay; omega) hct
    refine ⟨k+1, kc, p', r', L, .succ ho (.scan_count c s s' hm (Or.inr ha) hc hb) hs, by omega, hp',
      costedRun_congr (by rw [hr']) (by rw [hcen]) rfl rfl hcr, hrr, hi', by rw [hce, hcen]⟩
  | «match» c s vs vq o hm hr ha hc hne hcmp hmt hq ho' _ ih =>
    intro r p hi ho hp hct
    have hi1 := matched_invariant raw P q first vq hcmp hmt ha hi
    obtain ⟨k, kc, p', r', L, hs, hk, hp', hcr, hrr, hi', hce⟩ :=
      ih (r+1) 0 hi1 (outputRel_of_refresh' raw P hP hP' q first _ c.output o hi1 ho' _ rfl)
        (by show 0 + delay ≤ delay; omega) hct
    have hpos : position (afterCompare s vs vq).right = position s.right + 1 := by
      have e1 := hi.rightPos; have e2 := hi1.rightPos; omega
    have hw : p ≤ 2048 := by omega
    have h1 := costedRun_single (a := s) (b := afterCompare s vs vq)
      (cmpPiece (position s.right + 1) p hw) (by simp [cmpPiece]) (by simp [cmpPiece, hpos])
      (by rw [cmpPiece_adv, afterCompare_center]; simp)
    rw [cmpPiece_ticks] at h1
    refine ⟨k+1, (p+1) + kc, p', r', _,
      .succ ho (scan_match_S P q first delay c s vs vq o hm hr ha hc hne hcmp hmt hq ho') hs,
      by omega, hp', costedRun_trans h1 hcr, by omega, hi', by rw [hce, afterCompare_center]⟩

/-! ## The terminal mismatch and its shift -/

/-- **The cost of a terminal mismatch with its shift.**  One piece at the new
right place `position s1.right + 1`: the `p` pending counting ticks as the
wait, the comparison tick, and the `h+1`-tick shift (`ShiftEv`) advancing the
centre by `h`. -/
theorem shift_costed {c1 : Control} {s1 : GalilVM} (raw : List (Fin 2)) (P : Shared) (q : ℕ)
    (first : Fin 9) (delay h : ℕ) (hd : delay ≤ 2048) (hh : 0 < h)
    (hc1 : c1.clock = 1) (w : GalilScaffoldChainWatch.State)
    (hav : canRight s1.right) (vs : ScanVM) (vq : SearchVM)
    (hcmp : (galilFrame P q first).compare s1 (scanLens.set s1 vs))
    (s2 : GalilVM) (hs2 : beginShiftVM h w (afterMismatch s1 vs vq) s2)
    {t' : ShiftState} {v : GalilScaffoldChainWatch.State} {cycle : Counter}
    {cen r : ℕ} (hi1 : ScanInvariant raw cen r s1.left s1.right)
    (p : ℕ) (hp : p + c1.clock ≤ delay)
    (hcen : position (shiftLens.set s2 ⟨t', .watch v, cycle⟩).center = position s1.center + h) :
    ∃ L : List Piece, CostedRun s1 (shiftLens.set s2 ⟨t', .watch v, cycle⟩) (p + (1 + (h+1))) L := by
  have hcmp0 := hcmp
  obtain ⟨⟨_, hr, _⟩, _⟩ := hcmp0
  rw [scanLens.get_set] at hr
  have hr' : vs.right = right s1.right := hr
  have hSright : s2.right = right s1.right := by
    rw [hs2.2]; simp [afterMismatch, searchLens, scanLens, hr']
  have hpos : position (shiftLens.set s2 ⟨t', .watch v, cycle⟩).right = position s1.right + 1 := by
    show position s2.right = _
    rw [hSright]
    exact right_position s1.right hav (represented_position _ raw hi1.rightRep hi1.rightPresent).1
  have hw : p ≤ 2048 := by omega
  let e : ShiftEv := ⟨h+1, h, hh, le_rfl⟩
  have h1 := costedRun_single (a := s1) (b := shiftLens.set s2 ⟨t', .watch v, cycle⟩)
    (shiftPiece (position s1.right + 1) p hw e) (by simp [shiftPiece]) (by simp [shiftPiece, hpos])
    (by rw [shiftPiece_adv, hcen])
  rw [shiftPiece_ticks] at h1
  rw [show p + (1 + (h+1)) = e.ticks + p + 1 by show _ = h + 1 + p + 1; omega]
  exact ⟨_, h1⟩

/-! ## The re-shift rounds -/

/-- **Costed rounds.**  The re-shift rounds as a sound run whose ticks are
exactly the ticks of a costed run: per round, the matched comparisons of the
segment and one shift piece at the terminal mismatch. -/
theorem rounds_costed (raw : List (Fin 2)) (P : Shared) (hP : P.onLetter = onLetterVM raw)
    (hP' : P.leftFirst = leftFirstVM) (q : ℕ) (first : Fin 9) (delay h : ℕ) (hd : delay ≤ 2048)
    {m : ℕ} {c c' : Control} {s s' : GalilVM} (hr : Rounds P q first delay h m c s c' s') :
    ∀ w0 : GalilScaffoldChainWatch.State, s.periodOnly = true → s.chain = .watch w0 →
      zero w0.lag = true → ∀ org : ReadOrigin raw, org.interior.length+1 = h →
      Entry raw org (toOnly s w0) → OutputRel raw c s → c.clock ≤ delay →
      ∃ (k : ℕ) (L : List Piece),
        StepsAll (galilFrameS P q first) delay (SoundScan raw) k ⟨c, s⟩ ⟨c', s'⟩ ∧
        CostedRun s s' k L ∧ c'.clock ≤ delay := by
  induction hr with
  | stop c s =>
    intro w0 _ _ _ org _ _ ho hcl
    exact ⟨0, [], .zero _ (fun _ => ho), costedRun_nil s, hcl⟩
  | @next m c s n c1 s1 hseg hm1 hr1 hc1 w hs1 hav vs vq hcmp hmis hq hend hpred hlen hg s2 hb hs2 hi2
      t' v cycle hchain o ho c' s' rest ih =>
    intro w0 hp hs hz org hint he hout hcl
    have hi : ScanInvariant raw _ _ s.left s.right := entry_scanInvariant he
    obtain ⟨es, hsc⟩ := scanSeg_heads P q first delay hseg
    have hi1' := scan_events_invariant (hsc raw _ _) hi
    obtain ⟨kS, kc, p', r', Lseg, hstS, hkS, hp', hcrS, _, hi1, hceS⟩ :=
      watchSeg_costed raw P hP hP' q first delay hd (watchSeg_of_scanSeg P q first delay hseg) _ _ 0 hi hout
        (by omega) (pos_lt_of_canRight hi1' hav)
    obtain ⟨_, hcr1⟩ := round_next P q first delay h hseg w0 hp hs hz hm1 hr1 hc1 w hs1 hav vs vq
      hcmp hmis hq hend hpred hlen hg s2 hb hs2 hi2 hchain o ho
    obtain ⟨org', he', _, hinterior, _, _, _, hcenter', _⟩ := rounds_origin hcr1 org hint he
    have hint' : org'.interior.length+1 = h := by rw [hinterior]; exact hint
    have hi2' := entry_scanInvariant he'
    obtain ⟨w1, hw1, hz1, _, _⟩ := scanSeg_only P q first delay hseg w0 hp hs hz
    have hww : w1 = w := by rw [hs1] at hw1; injection hw1 with e; exact e.symm
    subst hww
    have hout1 : OutputRel raw c1 s1 := stepsAll_last hstS
    have hst3 := first_shift_stepsAll raw P hP hP' q first delay h hm1 hr1 hc1 w1 hs1 hav vs vq hcmp hmis hq
      hg s2 hb hs2 hi2 hchain o ho hz1 hout1 hi2'
    have hh : 0 < h := by omega
    have hcen : position (shiftLens.set s2 ⟨t', .watch v, cycle⟩).center = position s1.center + h := by
      have e1 := he'.centerPos
      have e2 := he.centerPos
      rw [hint'] at e1; rw [hint] at e2
      have e3 : s1.center = s.center := hceS
      have e4 : position (toOnly (shiftLens.set s2 ⟨t', .watch v, cycle⟩) v).center =
          position (shiftLens.set s2 ⟨t', .watch v, cycle⟩).center := rfl
      have e5 : position (toOnly s w0).center = position s.center := rfl
      rw [e4] at e1; rw [e5] at e2
      rw [e3]; simp only [Nat.one_mul] at hcenter'; omega
    obtain ⟨Lsh, hcrSh⟩ := shift_costed raw P q first delay h hd hh hc1 w1 hav vs vq hcmp s2 hs2 hi1 p' hp' hcen
    obtain ⟨kR, LR, hstR, hcrR, hclR⟩ := ih _ (by show s2.periodOnly = true; rw [hs2.2]) rfl
      (by rw [chain_shift_lag hchain]; exact hz1) org' hint' he'
      (outputRel_of_refreshS' raw P hP hP' q first _ _ o hi2' ho _ rfl) (by show delay ≤ delay; exact le_rfl)
    have lift : ∀ st, SoundOut raw st → SoundScan raw st := fun st h0 _ => h0
    refine ⟨kS + (1 + (h+1)) + kR, Lseg ++ Lsh ++ LR, stepsAll_trans (stepsAll_trans (stepsAll_mono lift hstS) hst3) hstR,
      ?_, hclR⟩
    rw [show kS + (1 + (h+1)) + kR = kc + (p' + (1 + (h+1))) + kR by omega]
    exact costedRun_trans (costedRun_trans hcrS hcrSh) hcrR

/-! ## The found comparison, the preparation and the watch -/

/-- **The costed prefix of a found cycle.**  From the found comparison at
`sF` (with `p0` counting ticks pending before it, charged to its piece)
through the preparation segment and the watch segment, up to the terminal
comparison state `s1`, which can still move right. -/
theorem found_prefix_costed (raw : List (Fin 2)) (P : Shared) (hP : P.onLetter = onLetterVM raw)
    (hP' : P.leftFirst = leftFirstVM) (qq : ℕ) (first : Fin 9) (delay : ℕ) (hd : delay ≤ 2048)
    {cF : Control} {sF : GalilVM} (hmF : cF.mode = .scan) (hrF : cF.replaying = false)
    (hcF : cF.clock = 1) (havF : canRight sF.right) (hidle : sF.chain = .idle)
    {cen R : ℕ} (hscan : ScanInvariant raw cen R sF.left sF.right) (houtF : OutputRel raw cF sF)
    (vq : SearchVM) (hq : searchEffect P true sF vq) (hfound : vq.search.mode = .found)
    (hmt : read (left sF.left) = read (right sF.right))
    (ch : ChainVM)
    (hch : ChainMatched (chainStart (vq.dp.config.tapes 11) (P.centre sF) (P.place sF) sF.center sF.radius) ch)
    (hchne : ch ≠ .idle) (oF : Bool)
    (hoF : refresh (galilFrame P qq first)
      (afterBirth true (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq)) cF.output oF)
    {es : List Bool} {c2 : Control} {s2 : GalilVM}
    (hprepSeg : WatchSegE P qq first delay es {cF with clock := delay, output := oF, replaying := false}
      (afterBirth true (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq)) c2 s2)
    {c1 : Control} {s1 : GalilVM} (hseg : WatchSeg P qq first delay c2 s2 c1 s1)
    (hav1 : canRight s1.right) (p0 : ℕ) (hp0 : p0 + cF.clock ≤ delay) :
    ∃ (k kc p1 r1 : ℕ) (L : List Piece),
      StepsAll (galilFrameS P qq first) delay (SoundOut raw) k ⟨cF, sF⟩ ⟨c1, s1⟩ ∧
      k + p0 = kc + p1 ∧ p1 + c1.clock ≤ delay ∧ CostedRun sF s1 kc L ∧
      ScanInvariant raw cen r1 s1.left s1.right ∧ s1.center = sF.center := by
  have htickF := found_start_match P qq first delay cF sF hmF hrF hcF havF hidle vq hq hfound hmt ch hch oF hoF
  have hoF' : refresh (galilFrame P qq first)
      (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq) cF.output oF :=
    (refresh_afterBirth_iff hP hP' true _ _ _).1 hoF
  obtain ⟨hinv1, hout1⟩ := outputRel_matched_refresh' raw P hP hP' qq first vq rfl rfl hmt havF hscan
    cF.output oF hoF' {cF with clock := delay, output := oF, replaying := false} rfl
  have hneA : (afterBirth true (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq)).chain
      ≠ .idle := by
    rw [afterBirth_chain, afterCompare_chain]; exact hchne
  have hprep := watchSeg_of_E P qq first delay hprepSeg hneA
  have hinv2 := (watchSegE_output_inv raw P hP hP' qq first delay hprepSeg cen (R+1) hinv1 hout1).2
  have hne2 : s2.chain ≠ .idle := watchSegE_ne_idle P qq first delay hprepSeg hneA
  obtain ⟨es2, _, hsc2, _⟩ := watchSeg_events P qq first delay hseg hne2
  have hi3 := scan_events_invariant (hsc2 raw cen _) hinv2
  have hlt1 := pos_lt_of_canRight hi3 hav1
  have hlt2 : position s2.right < 2 * raw.length := by
    have := hinv2.rightPos; have := hi3.rightPos; omega
  obtain ⟨k1, kc1, p1', r1', L1, hst1, hk1, hp1, hcr1, _, hi2', hce1⟩ :=
    watchSeg_costed raw P hP hP' qq first delay hd hprep cen (R+1) 0 hinv1 hout1
      (by show 0 + delay ≤ delay; omega) hlt2
  have hout2 : OutputRel raw c2 s2 := stepsAll_last hst1
  obtain ⟨k2, kc2, p2, r2, L2, hst2, hk2, hp2, hcr2, _, hi3', hce2⟩ :=
    watchSeg_costed raw P hP hP' qq first delay hd hseg cen r1' p1' hi2' hout2 hp1 hlt1
  have hposA : position (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq).right =
      position sF.right + 1 := by
    have := hinv1.rightPos; have := hscan.rightPos; omega
  have hw : p0 ≤ 2048 := by omega
  have h0 := costedRun_single (a := sF)
    (b := afterBirth true (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq))
    (cmpPiece (position sF.right + 1) p0 hw) (by simp [cmpPiece, afterBirth_right])
    (by simp [cmpPiece, afterBirth_right, hposA])
    (by rw [cmpPiece_adv, afterBirth_center, afterCompare_center]; simp)
  rw [cmpPiece_ticks] at h0
  refine ⟨k1 + k2 + 1, (p0 + 1) + kc1 + kc2, p2, r2, _,
    .succ houtF htickF (stepsAll_trans hst1 hst2), by omega, hp2,
    costedRun_trans (costedRun_trans h0 hcr1) hcr2, hi3',
    by rw [hce2, hce1, afterBirth_center, afterCompare_center]⟩

/-- The breaking matched comparison and the restart tick: one piece at the
new right place whose wait holds the `p` pending counting ticks and the
restart tick. -/
theorem break_costed {raw : List (Fin 2)} {s3 sR : GalilVM} {vs3 : ScanVM} {vq3 : SearchVM}
    {cen r : ℕ} (hi : ScanInvariant raw cen r s3.left s3.right)
    (hi' : ScanInvariant raw cen (r+1) (afterCompare s3 vs3 vq3).left (afterCompare s3 vs3 vq3).right)
    (hR : sR.right = (afterCompare s3 vs3 vq3).right) (hRc : sR.center = s3.center)
    (p : ℕ) (hp : p + 1 ≤ 2048) :
    ∃ L : List Piece, CostedRun s3 sR (p + 2) L := by
  have hpos : position sR.right = position s3.right + 1 := by
    rw [hR]; have := hi.rightPos; have := hi'.rightPos; omega
  have h0 := costedRun_single (a := s3) (b := sR) (cmpPiece (position s3.right + 1) (p+1) hp)
    (by simp [cmpPiece]) (by simp [cmpPiece, hpos]) (by rw [cmpPiece_adv, hRc]; simp)
  rw [cmpPiece_ticks] at h0
  exact ⟨_, h0⟩

/-! ## (a) The found cycle without a shift -/

/-- **`costedRun_found_noshift`.**  The found cycle whose watch ends at a
breaking *match*: from the found comparison to the restarted state, a sound
run of `k` ticks and a costed run of `k + p0` ticks (`p0` = counting ticks
pending before the found comparison).  The centre does not move. -/
theorem costedRun_found_noshift (raw : List (Fin 2)) (P : Shared) (hP : P.onLetter = onLetterVM raw)
    (hP' : P.leftFirst = leftFirstVM) (qq : ℕ) (first : Fin 9) (delay : ℕ) (hd : delay ≤ 2048)
    {cF : Control} {sF : GalilVM} (hmF : cF.mode = .scan) (hrF : cF.replaying = false)
    (hcF : cF.clock = 1) (havF : canRight sF.right) (hidle : sF.chain = .idle)
    {cen R : ℕ} (hscan : ScanInvariant raw cen R sF.left sF.right) (houtF : OutputRel raw cF sF)
    (vq : SearchVM) (hq : searchEffect P true sF vq) (hfound : vq.search.mode = .found)
    (hmt : read (left sF.left) = read (right sF.right))
    (ch : ChainVM)
    (hch : ChainMatched (chainStart (vq.dp.config.tapes 11) (P.centre sF) (P.place sF) sF.center sF.radius) ch)
    (hchne : ch ≠ .idle) (oF : Bool)
    (hoF : refresh (galilFrame P qq first)
      (afterBirth true (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq)) cF.output oF)
    {es : List Bool} {c2 : Control} {s2 : GalilVM}
    (hprepSeg : WatchSegE P qq first delay es {cF with clock := delay, output := oF, replaying := false}
      (afterBirth true (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq)) c2 s2)
    {c3 : Control} {s3 : GalilVM} (hseg : WatchSeg P qq first delay c2 s2 c3 s3)
    (hm3 : c3.mode = .scan) (hr3 : c3.replaying = false) (hc3 : c3.clock = 1)
    (w3 : GalilScaffoldChainWatch.State) (hs3 : s3.chain = .watch w3)
    (hz3 : GalilScaffoldCounter.zero w3.lag = true) (hav3 : canRight s3.right)
    (vs3 : ScanVM) (vq3 : SearchVM)
    (hcmp3 : (galilFrame P qq first).compare s3 (scanLens.set s3 vs3))
    (hmt3 : (galilFrame P qq first).matched (scanLens.set s3 vs3))
    (hq3 : searchEffect P true s3 vq3)
    (o3 : Bool) (ho3 : refresh (galilFrame P qq first) (afterCompare s3 vs3 vq3) c3.output o3)
    (w3' : GalilScaffoldChainWatch.State) (hbroken : (afterCompare s3 vs3 vq3).chain = .broken w3')
    (hmargin : negative w3'.margin = false) (hlast : positive w3'.machine.control.last = true)
    (hlag : zero w3'.lag = true) (entry : ℕ) (hres : ∀ s t, restartVM entry s t → P.restart s t)
    (p0 : ℕ) (hp0 : p0 + cF.clock ≤ delay) :
    ∃ (k : ℕ) (L : List Piece),
      StepsAll (galilFrameS P qq first) delay (SoundScanNR raw) k ⟨cF, sF⟩
        ⟨{c3 with clock := delay, output := o3, replaying := false}, {(afterCompare s3 vs3 vq3) with chain := .idle, lower := w3'.machine.control.last, search := GalilScaffoldSearchFinish.begin w3'.machine.control.last (afterCompare s3 vs3 vq3).radius, dp := GalilScaffoldControl.reset entry (afterCompare s3 vs3 vq3).dp}⟩ ∧
      CostedRun sF {(afterCompare s3 vs3 vq3) with chain := .idle, lower := w3'.machine.control.last, search := GalilScaffoldSearchFinish.begin w3'.machine.control.last (afterCompare s3 vs3 vq3).radius, dp := GalilScaffoldControl.reset entry (afterCompare s3 vs3 vq3).dp} (k + p0) L ∧
      position (afterCompare s3 vs3 vq3).center = position sF.center := by
  obtain ⟨k1, kc1, p3, r3, L1, hst1, hk1, hp3, hcr1, hi3, hce1⟩ :=
    found_prefix_costed raw P hP hP' qq first delay hd hmF hrF hcF havF hidle hscan houtF vq hq hfound
      hmt ch hch hchne oF hoF hprepSeg hseg hav3 p0 hp0
  have hinv4 := matched_invariant raw P qq first vq3 hcmp3 hmt3 hav3 hi3
  have hne3 : s3.chain ≠ .idle := by rw [hs3]; intro h0; cases h0
  have htick3 := scan_match_S P qq first delay c3 s3 vs3 vq3 o3 hm3 hr3 hav3 hc3 hne3 hcmp3 hmt3 hq3 ho3
  have hout3 : OutputRel raw c3 s3 := stepsAll_last hst1
  have hQ4 : SoundOut raw ⟨{c3 with clock := delay, output := o3, replaying := false},
      afterCompare s3 vs3 vq3⟩ :=
    outputRel_of_refresh' raw P hP hP' qq first _ c3.output o3 hinv4 ho3 _ rfl
  have hmain : StepsAll (galilFrameS P qq first) delay (SoundOut raw) (k1 + (0 + 1)) ⟨cF, sF⟩
      ⟨{c3 with clock := delay, output := o3, replaying := false}, afterCompare s3 vs3 vq3⟩ :=
    stepsAll_trans hst1 (.succ hout3 htick3 (.zero _ hQ4))
  have htick : Tick (galilFrameS P qq first) delay
      ⟨{c3 with clock := delay, output := o3, replaying := false}, afterCompare s3 vs3 vq3⟩
      ⟨{c3 with clock := delay, output := o3, replaying := false}, {(afterCompare s3 vs3 vq3) with chain := .idle, lower := w3'.machine.control.last, search := GalilScaffoldSearchFinish.begin w3'.machine.control.last (afterCompare s3 vs3 vq3).radius, dp := GalilScaffoldControl.reset entry (afterCompare s3 vs3 vq3).dp}⟩ :=
    .restart _ _ _ hm3 (hres _ _ ⟨w3', hbroken, hmargin, hlast, hlag, rfl⟩)
  have lift1 : ∀ st, SoundOut raw st → SoundScanNR raw st := fun st h0 _ _ => h0
  have hfin := stepsAll_keep_tick raw P qq first delay (stepsAll_mono lift1 hmain) htick rfl
  obtain ⟨L2, hcr2⟩ := break_costed (sR := {(afterCompare s3 vs3 vq3) with chain := .idle, lower := w3'.machine.control.last, search := GalilScaffoldSearchFinish.begin w3'.machine.control.last (afterCompare s3 vs3 vq3).radius, dp := GalilScaffoldControl.reset entry (afterCompare s3 vs3 vq3).dp}) hi3 hinv4 rfl rfl p3 (by omega)
  refine ⟨_, L1 ++ L2, hfin, ?_, by rw [afterCompare_center, hce1]⟩
  rw [show k1 + (0 + 1) + 1 + p0 = kc1 + (p3 + 2) by omega]
  exact costedRun_trans hcr1 hcr2

/-! ## (b) The found cycle with the first shift and the rounds -/

/-- **`costedRun_found_shift`.**  The found cycle whose watch ends at a
terminal mismatch: the first shift, `m` re-shift rounds, the final scan
segment, the breaking match and the restart tick.  A sound run of `k` ticks
from the found comparison to the restarted state and a costed run of
`k + p0` ticks; the centre advances by `(m+1)·h`. -/
theorem costedRun_found_shift (raw : List (Fin 2)) (P : Shared) (hP : P.onLetter = onLetterVM raw)
    (hP' : P.leftFirst = leftFirstVM) (qq : ℕ) (first : Fin 9) (delay : ℕ) (hd : delay ≤ 2048)
    {cF : Control} {sF : GalilVM} (hmF : cF.mode = .scan) (hrF : cF.replaying = false)
    (hcF : cF.clock = 1) (havF : canRight sF.right) (hidle : sF.chain = .idle)
    {cen R : ℕ} (hscan : ScanInvariant raw cen R sF.left sF.right) (houtF : OutputRel raw cF sF)
    (vq : SearchVM) (hq : searchEffect P true sF vq) (hfound : vq.search.mode = .found)
    (hmt : read (left sF.left) = read (right sF.right))
    (ch : ChainVM)
    (hch : ChainMatched (chainStart (vq.dp.config.tapes 11) (P.centre sF) (P.place sF) sF.center sF.radius) ch)
    (hchne : ch ≠ .idle) (oF : Bool)
    (hoF : refresh (galilFrame P qq first)
      (afterBirth true (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq)) cF.output oF)
    {es : List Bool} {c2 : Control} {s2 : GalilVM}
    (hprepSeg : WatchSegE P qq first delay es {cF with clock := delay, output := oF, replaying := false}
      (afterBirth true (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq)) c2 s2)
    {c1 : Control} {s1 : GalilVM} (hseg : WatchSeg P qq first delay c2 s2 c1 s1)
    (h : ℕ) (hm1 : c1.mode = .scan) (hr1 : c1.replaying = false) (hc1 : c1.clock = 1)
    (w : GalilScaffoldChainWatch.State) (hs1 : s1.chain = .watch w) (hz : zero w.lag = true)
    (hav : canRight s1.right) (vs : ScanVM) (vq' : SearchVM)
    (hcmp : (galilFrame P qq first).compare s1 (scanLens.set s1 vs))
    (hmis : ¬ (galilFrame P qq first).matched (scanLens.set s1 vs))
    (hq' : searchEffect P false s1 vq')
    (hg : P.shiftGuard (afterMismatch s1 vs vq'))
    (s2' : GalilVM) (hb : P.beginShift (afterMismatch s1 vs vq') s2')
    (hs2' : beginShiftVM h w (afterMismatch s1 vs vq') s2') (hi2 : CopyIdle s2')
    {t' : ShiftState} {v : GalilScaffoldChainWatch.State} {cycle : Counter}
    (hchain : ChainShiftRun ⟨s1.center, left s1.left, ofNat h, inc s1.radius, inc (inc s1.length)⟩
      (GalilScaffoldChainWatch.immediate w) reset h t' v cycle)
    (o : Bool)
    (ho : refresh (galilFrameS P qq first) (shiftLens.set s2' ⟨t', .watch v, cycle⟩) c1.output o)
    (org : ReadOrigin raw) (hint : org.interior.length+1 = h)
    (he : Entry raw org (toOnly (shiftLens.set s2' ⟨t', .watch v, cycle⟩) v))
    (hoc : org.center = position sF.center)
    {m : ℕ} {c' : Control} {s' : GalilVM}
    (hrounds : Rounds P qq first delay h m {c1 with mode := .scan, clock := delay, output := o}
      (shiftLens.set s2' ⟨t', .watch v, cycle⟩) c' s')
    {n : ℕ} {c3 : Control} {s3 : GalilVM} (hseg3 : ScanSeg P qq first delay n c' s' c3 s3)
    (hm3 : c3.mode = .scan) (hr3 : c3.replaying = false) (hc3 : c3.clock = 1)
    (w3 : GalilScaffoldChainWatch.State) (hs3 : s3.chain = .watch w3)
    (hz3 : GalilScaffoldCounter.zero w3.lag = true) (hav3 : canRight s3.right)
    (vs3 : ScanVM) (vq3 : SearchVM)
    (hcmp3 : (galilFrame P qq first).compare s3 (scanLens.set s3 vs3))
    (hmt3 : (galilFrame P qq first).matched (scanLens.set s3 vs3))
    (hq3 : searchEffect P true s3 vq3)
    (o3 : Bool) (ho3 : refresh (galilFrame P qq first) (afterCompare s3 vs3 vq3) c3.output o3)
    (w3' : GalilScaffoldChainWatch.State) (hbroken : (afterCompare s3 vs3 vq3).chain = .broken w3')
    (hmargin : negative w3'.margin = false) (hlast : positive w3'.machine.control.last = true)
    (hlag : zero w3'.lag = true) (entry : ℕ) (hres : ∀ s t, restartVM entry s t → P.restart s t)
    (p0 : ℕ) (hp0 : p0 + cF.clock ≤ delay) :
    ∃ (k : ℕ) (L : List Piece),
      StepsAll (galilFrameS P qq first) delay (SoundScanNR raw) k ⟨cF, sF⟩
        ⟨{c3 with clock := delay, output := o3, replaying := false}, {(afterCompare s3 vs3 vq3) with chain := .idle, lower := w3'.machine.control.last, search := GalilScaffoldSearchFinish.begin w3'.machine.control.last (afterCompare s3 vs3 vq3).radius, dp := GalilScaffoldControl.reset entry (afterCompare s3 vs3 vq3).dp}⟩ ∧
      CostedRun sF {(afterCompare s3 vs3 vq3) with chain := .idle, lower := w3'.machine.control.last, search := GalilScaffoldSearchFinish.begin w3'.machine.control.last (afterCompare s3 vs3 vq3).radius, dp := GalilScaffoldControl.reset entry (afterCompare s3 vs3 vq3).dp} (k + p0) L ∧
      0 < h ∧ position (afterCompare s3 vs3 vq3).center = position sF.center + (m+1)*h := by
  -- the prefix
  obtain ⟨k1, kc1, p1, r1, L1, hst1, hk1, hp1, hcr1, hi1, hce1⟩ :=
    found_prefix_costed raw P hP hP' qq first delay hd hmF hrF hcF havF hidle hscan houtF vq hq hfound
      hmt ch hch hchne oF hoF hprepSeg hseg hav p0 hp0
  have hout1 : OutputRel raw c1 s1 := stepsAll_last hst1
  -- the first shift
  have hiEnd := entry_scanInvariant he
  have hst2 := first_shift_stepsAll raw P hP hP' qq first delay h hm1 hr1 hc1 w hs1 hav vs vq' hcmp hmis hq'
    hg s2' hb hs2' hi2 hchain o ho hz hout1 hiEnd
  have hh : 0 < h := by omega
  have hcen : position (shiftLens.set s2' ⟨t', .watch v, cycle⟩).center = position s1.center + h := by
    have e1 := he.centerPos
    rw [hint, hoc] at e1
    rw [hce1]; exact e1
  obtain ⟨Lsh, hcrSh⟩ := shift_costed raw P qq first delay h hd hh hc1 w hav vs vq' hcmp s2' hs2' hi1 p1 hp1 hcen
  -- the rounds
  have hp2 : (shiftLens.set s2' ⟨t', .watch v, cycle⟩).periodOnly = true := by
    show s2'.periodOnly = true; rw [hs2'.2]
  have hz2 : zero v.lag = true := by rw [chain_shift_lag hchain]; exact hz
  obtain ⟨kR, LR, hstR, hcrR, hclR⟩ := rounds_costed raw P hP hP' qq first delay h hd hrounds v hp2 rfl hz2
    org hint he (outputRel_of_refreshS' raw P hP hP' qq first _ _ o hiEnd ho _ rfl)
    (by show delay ≤ delay; exact le_rfl)
  -- the final segment
  obtain ⟨_, w', hw', hz', hp', hcr⟩ := rounds_lift P qq first delay h hrounds v hp2 rfl hz2
  obtain ⟨org', he', _, _, _, _, _, _, _⟩ := rounds_origin hcr org hint he
  have hinv' := entry_scanInvariant he'
  have hout' : OutputRel raw c' s' := stepsAll_last hstR (scanSeg_mode P qq first delay hseg3 hm3)
  obtain ⟨es3, hsc3⟩ := scanSeg_heads P qq first delay hseg3
  have hi3' := scan_events_invariant (hsc3 raw _ _) hinv'
  obtain ⟨k5, kc5, p5, r5, L5, hst5, hk5, hp5, hcr5, _, hi5, _⟩ :=
    watchSeg_costed raw P hP hP' qq first delay hd (watchSeg_of_scanSeg P qq first delay hseg3) _ _ 0
      hinv' hout' (by omega) (pos_lt_of_canRight hi3' hav3)
  -- the breaking comparison and the restart tick
  have hinv6 := matched_invariant raw P qq first vq3 hcmp3 hmt3 hav3 hi5
  have hne3 : s3.chain ≠ .idle := by rw [hs3]; intro h0; cases h0
  have htick3 := scan_match_S P qq first delay c3 s3 vs3 vq3 o3 hm3 hr3 hav3 hc3 hne3 hcmp3 hmt3 hq3 ho3
  have hQ3 : SoundScan raw ⟨c3, s3⟩ := fun _ => stepsAll_last hst5
  have hQ4 : SoundScan raw ⟨{c3 with clock := delay, output := o3, replaying := false}, afterCompare s3 vs3 vq3⟩ :=
    fun _ => outputRel_of_refresh' raw P hP hP' qq first _ c3.output o3 hinv6 ho3 _ rfl
  have lift : ∀ st, SoundOut raw st → SoundScan raw st := fun st h0 _ => h0
  have hmain : StepsAll (galilFrameS P qq first) delay (SoundScan raw)
      (k1 + ((1 + (h+1)) + (kR + (k5 + (0 + 1))))) ⟨cF, sF⟩
      ⟨{c3 with clock := delay, output := o3, replaying := false}, afterCompare s3 vs3 vq3⟩ :=
    stepsAll_trans (stepsAll_mono lift hst1) (stepsAll_trans hst2 (stepsAll_trans hstR
      (stepsAll_trans (stepsAll_mono lift hst5) (.succ hQ3 htick3 (.zero _ hQ4)))))
  have htick : Tick (galilFrameS P qq first) delay
      ⟨{c3 with clock := delay, output := o3, replaying := false}, afterCompare s3 vs3 vq3⟩
      ⟨{c3 with clock := delay, output := o3, replaying := false}, {(afterCompare s3 vs3 vq3) with chain := .idle, lower := w3'.machine.control.last, search := GalilScaffoldSearchFinish.begin w3'.machine.control.last (afterCompare s3 vs3 vq3).radius, dp := GalilScaffoldControl.reset entry (afterCompare s3 vs3 vq3).dp}⟩ :=
    .restart _ _ _ hm3 (hres _ _ ⟨w3', hbroken, hmargin, hlast, hlag, rfl⟩)
  have lift2 : ∀ st, SoundScan raw st → SoundScanNR raw st := fun st h0 hm _ => h0 hm
  have hfin := stepsAll_keep_tick raw P qq first delay (stepsAll_mono lift2 hmain) htick rfl
  obtain ⟨L6, hcr6⟩ := break_costed (sR := {(afterCompare s3 vs3 vq3) with chain := .idle, lower := w3'.machine.control.last, search := GalilScaffoldSearchFinish.begin w3'.machine.control.last (afterCompare s3 vs3 vq3).radius, dp := GalilScaffoldControl.reset entry (afterCompare s3 vs3 vq3).dp}) hi5 hinv6 rfl rfl p5 (by omega)
  -- the centre
  obtain ⟨_, _, hcentre⟩ := PalPeg.GalilChainReadyProgress.found_cycle_center_progress raw P qq first delay (sF := sF) h (c1 := c1) w hz vs vq'
    s2' hs2' hchain org hint he hoc hrounds hseg3 vs3 vq3
  refine ⟨_, L1 ++ Lsh ++ LR ++ L5 ++ L6, hfin, ?_, hh, hcentre⟩
  rw [show k1 + ((1 + (h+1)) + (kR + (k5 + (0 + 1)))) + 1 + p0 =
    kc1 + (p1 + (1 + (h+1))) + kR + kc5 + (p5 + 2) by omega]
  exact costedRun_trans (costedRun_trans (costedRun_trans (costedRun_trans hcr1 hcrSh) hcrR) hcr5) hcr6

#print axioms cmpPiece_ticks
#print axioms cmpPiece_adv
#print axioms shiftPiece_ticks
#print axioms shiftPiece_adv
#print axioms costedRun_congr
#print axioms costedRun_single
#print axioms costedRun_same
#print axioms watchSeg_of_scanSeg
#print axioms pos_lt_of_canRight
#print axioms no_wait
#print axioms watchSeg_costed
#print axioms shift_costed
#print axioms rounds_costed
#print axioms found_prefix_costed
#print axioms break_costed
#print axioms costedRun_found_noshift
#print axioms costedRun_found_shift

end PalPeg.GalilCostedFound
