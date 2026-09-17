import PalPeg.GalilSegmentConstruct2
import PalPeg.GalilSegmentConstruct3
import PalPeg.GalilChainReadyProgress
import PalPeg.GalilScaffoldTopCentre
import PalPeg.GalilFrontier

/-!
# L7c(i) — constructing the scan half of one re-shift round

`GalilSegmentConstruct3.rounds_construct_inv` iterates a *one-round oracle*
`hround`.  This module builds that oracle's scan half.

The round starts right after a centre shift: the chain is a zero-lag watch in
`periodOnly`, and the cycle counter holds the `h` places of the semiperiod.
The scan then

* counts down the clock (`ScanSeg.count`, from `backgroundS_exists`),
* performs a matched comparison at clock one while the cycle counter is not
  yet single (`ScanSeg.match`), and
* stops at the terminal, where the cycle counter *is* single.

The chain side is total here **without** the `hidx` span-containment gap of
`roundInv_good`: at lag zero `Internal` can only be `.idle`, so no `Good` is
needed for a background tick, and at a matched comparison
`chainMatched_watch_total` gives the *dichotomy* `Good`-or-`BreakStep`
outright from `WatchReady`.  What is genuinely input-dependent is which of the
two fires, and that is what the named hypotheses below isolate.
-/

set_option autoImplicit false
namespace PalPeg.GalilRoundConstruct

open PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilBranchInvariants PalPeg.GalilTickFun
open Manacher GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter
  GalilScaffoldInputHead GalilScaffoldChainVerifier

/-! ## Chain readiness at a zero-lag watch -/

/-- At lag zero a watching chain is `ChainReady` as soon as it is
`WatchReady`: the `Good`-at-positive-lag clause is vacuous and `Internal` has
only its `.idle` constructor. -/
theorem chainReady_watch_zero {w : GalilScaffoldChainWatch.State}
    (hz : zero w.lag = true) (hr : WatchReady w) : ChainReady (ChainVM.watch w) := by
  have hpf : positive w.lag = false := positive_of_zero hz
  refine ⟨?_, hr.2, ?_⟩
  · intro hp; rw [hpf] at hp; exact absurd hp (by simp)
  · intro m hm
    cases hm with
    | idle hz0 => exact hr.1
    | take hp hg => rw [hpf] at hp; exact absurd hp (by simp)

/-! ## The two kinds of scan step -/

/-- A background tick at a zero-lag watch, with the fields a scan segment
needs afterwards. -/
theorem scan_background (P : Shared) (q : ℕ) (first : Fin 9) {s : GalilVM}
    {w : GalilScaffoldChainWatch.State}
    (hs : s.chain = ChainVM.watch w) (hz : zero w.lag = true) (hrw : WatchReady w)
    (hsearch : ∀ (u : GalilVM) (a : Bool), ∃ v, searchEffect P a u v) :
    ∃ s', (galilFrameS P q first).background s s' ∧ s'.chain = ChainVM.watch w ∧
      s'.periodOnly = s.periodOnly ∧ s'.cycle = s.cycle ∧ s'.center = s.center ∧
      s'.right = s.right ∧ s'.left = s.left := by
  have hready : ChainReady s.chain := by rw [hs]; exact chainReady_watch_zero hz hrw
  obtain ⟨s', hb⟩ := backgroundS_exists P q first s (hsearch s false)
    (fun v => chainAt_exists false (decide (v.search.mode = .found)) (v.dp.config.tapes 11)
      (P.centre s) (P.place s) s.center s.radius s.chain hready)
  obtain ⟨hc, _, hpo⟩ := background_only P q first hb w hs hz
  obtain ⟨hl, hr, _, hcen, _, _, _, -, _⟩ := backgroundS_fields P q first hb
  have hcy := (backgroundS_periodOnly_of_ne_idle P q first hb (by rw [hs]; intro h0; cases h0)).2
  exact ⟨s', hb, hc, hpo, hcy, hcen, hr, hl⟩

/-- The output refresh of `galilFrame`, built explicitly. -/
theorem frame_refresh_exists (P : Shared) (q : ℕ) (first : Fin 9) (u : GalilVM) (old : Bool) :
    ∃ o, refresh (galilFrame P q first) u old o := by
  classical
  refine ⟨if P.onLetter u then decide (P.leftFirst u) else old, ?_, ?_⟩
  · intro hl
    have hl' : P.onLetter u := hl
    show (if P.onLetter u then decide (P.leftFirst u) else old) = true ↔ P.leftFirst u
    rw [if_pos hl']; exact decide_eq_true_iff
  · intro hl
    have hl' : ¬ P.onLetter u := hl
    show (if P.onLetter u then decide (P.leftFirst u) else old) = old
    rw [if_neg hl']

/-- The comparison data of a matched step at a zero-lag watch whose `Good`
holds: the chain stays watching, at `immediate w`. -/
theorem scan_compare_match (P : Shared) (q : ℕ) (first : Fin 9) {s : GalilVM}
    {w : GalilScaffoldChainWatch.State}
    (hs : s.chain = ChainVM.watch w) (hz : zero w.lag = true)
    (hmatch : read (left s.left) = read (right s.right))
    (hgood : GalilScaffoldChainWatch.Good w) :
    ∃ (vs : ScanVM) (vq : SearchVM),
      vs = ⟨left s.left, right s.right, ChainVM.watch (GalilScaffoldChainWatch.immediate w)⟩ ∧
      (galilFrame P q first).compare s (scanLens.set s vs) ∧
      (galilFrame P q first).matched (scanLens.set s vs) ∧
      searchEffect P true s vq ∧
      (afterCompare s vs vq).chain = ChainVM.watch (GalilScaffoldChainWatch.immediate w) := by
  have hpf : positive w.lag = false := positive_of_zero hz
  have hne : s.chain ≠ ChainVM.idle := by rw [hs]; intro h0; cases h0
  have htick : ChainTick true (ChainVM.watch w)
      (ChainVM.watch (GalilScaffoldChainWatch.immediate w)) :=
    chainTick_of_watch_true (.step (.idle w hpf) (.immediate w hz hgood))
  refine ⟨⟨left s.left, right s.right,
    ChainVM.watch (GalilScaffoldChainWatch.immediate w)⟩, searchLens.get s, rfl, ?_, ?_, ?_, ?_⟩
  · refine Lens.rel_set scanLens _ s _ ⟨rfl, rfl, ?_⟩
    show ChainTick (decide (read (left s.left) = read (right s.right))) s.chain
      (ChainVM.watch (GalilScaffoldChainWatch.immediate w))
    rw [decide_eq_true hmatch, hs]; exact htick
  · show read (scanLens.get (scanLens.set s _)).left
      = read (scanLens.get (scanLens.set s _)).right
    rw [scanLens.get_set]; exact hmatch
  · exact Or.inr ⟨hne, rfl⟩
  · rw [afterCompare_chain]

/-! ## The scan-half invariant -/

/-- The facts the scan half of a round carries: scan mode, no replay, a clock
inside `[1, delay]`, `periodOnly`, a *positive* cycle counter (the semiperiod
countdown) and a zero-lag watch satisfying the caller's watch predicate `W`. -/
structure SInv (delay : ℕ) (W : GalilScaffoldChainWatch.State → Prop)
    (c : Control) (s : GalilVM) : Prop where
  mode : c.mode = .scan
  repl : c.replaying = false
  clk1 : 1 ≤ c.clock
  clk2 : c.clock ≤ delay
  per : s.periodOnly = true
  pos : positive s.cycle = true
  wit : ∃ w, s.chain = ChainVM.watch w ∧ zero w.lag = true ∧ W w

/-- A positive counter that is not yet *single* stays positive after `dec`,
and its `pos` list gets shorter. -/
theorem dec_pos_of_not_single {x : Counter} (hp : positive x = true)
    (hs : singlePositive x = false) :
    positive (dec x) = true ∧ (dec x).pos.length + 1 = x.pos.length := by
  rcases x with ⟨ps, ns⟩
  cases ps with
  | nil => simp [positive] at hp
  | cons a t =>
    cases t with
    | nil => simp [singlePositive, positive] at hs
    | cons b u => simp [dec, positive]

/-! ## The report point inside a round

The last incoming letter is about to be consumed: the right head stands on a
gap with an empty saved stack (`PopsIncoming`, `GalilFrontier`) and the
incoming FIFO holds exactly one letter.  The controller has to report before
that comparison moves the head, so this is a fourth way a round's scan stops,
taken *before* the comparison. -/
def LastLetterEnd (c : Control) (s : GalilVM) : Prop :=
  c.clock = 1 ∧ canRight s.right ∧ PopsIncoming s.right ∧ ∃ a, s.right.head.incoming = [a]

/-! ## The loop -/

/-- **The scan half of a round.**  From a state satisfying `SInv` the
controller performs a scan segment and stops either because the input ran out
or because it reached the terminal comparison of the semiperiod (clock one,
`R` available, the cycle counter single).  The centre does not move.

The two input-dependent facts are the named hypothesis `hmid`: *before* the
terminal the outer symbols agree and the chain's watch is `Good`, so the
comparison is a match and the chain does not break.  This is exactly the
periodicity content — a matched comparison extends the palindrome and the
period extends with it — and it is isolated rather than assumed silently. -/
theorem scan_half (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (W : GalilScaffoldChainWatch.State → Prop)
    (hdelay : 1 ≤ delay)
    (hsearch : ∀ (u : GalilVM) (a : Bool), ∃ v, searchEffect P a u v)
    (hwr : ∀ w, W w → WatchReady w)
    (hwi : ∀ w, W w → W (GalilScaffoldChainWatch.immediate w))
    (hmid : ∀ (u : GalilVM) (w : GalilScaffoldChainWatch.State),
      u.chain = ChainVM.watch w → canRight u.right → singlePositive u.cycle = false →
      read (left u.left) = read (right u.right) ∧ GalilScaffoldChainWatch.Good w) :
    ∀ (fuel : ℕ) (c : Control) (s : GalilVM), SInv delay W c s →
      s.cycle.pos.length * (delay + 1) + c.clock ≤ fuel →
      ∃ (n : ℕ) (c1 : Control) (s1 : GalilVM), ScanSeg P q first delay n c s c1 s1 ∧
        SInv delay W c1 s1 ∧ s1.center = s.center ∧
        (¬ canRight s1.right ∨ LastLetterEnd c1 s1 ∨
          (c1.clock = 1 ∧ canRight s1.right ∧ singlePositive s1.cycle = true)) := by
  classical
  intro fuel
  induction fuel with
  | zero =>
    intro c s hI hf
    exact absurd hf (by have := hI.clk1; omega)
  | succ fuel ih =>
    intro c s hI hf
    obtain ⟨w, hsw, hzw, hWw⟩ := hI.wit
    by_cases hav : canRight s.right
    · rcases Nat.lt_or_ge 1 c.clock with hlt | hle
      · -- a counting tick
        obtain ⟨s', hb, hc', hpo', hcy', hcen', hr', hl'⟩ :=
          scan_background P q first hsw hzw (hwr w hWw) hsearch
        have hI' : SInv delay W {c with clock := c.clock - 1} s' := by
          refine ⟨hI.mode, hI.repl, ?_, ?_, ?_, ?_, ⟨w, hc', hzw, hWw⟩⟩
          · show 1 ≤ c.clock - 1; omega
          · show c.clock - 1 ≤ delay; have := hI.clk2; omega
          · rw [hpo']; exact hI.per
          · rw [hcy']; exact hI.pos
        obtain ⟨n, c1, s1, hseg, hI1, hcen1, hstop⟩ := ih _ s' hI' (by
          rw [hcy']; show s.cycle.pos.length * (delay + 1) + (c.clock - 1) ≤ fuel; omega)
        exact ⟨n, c1, s1, .count c s s' hI.mode hI.repl hav hlt hb hseg, hI1,
          by rw [hcen1, hcen'], hstop⟩
      · -- clock one
        have hc1 : c.clock = 1 := le_antisymm hle hI.clk1
        by_cases hlast : PopsIncoming s.right ∧ ∃ a, s.right.head.incoming = [a]
        · exact ⟨0, c, s, .stop _ _, hI, rfl, Or.inr (Or.inl ⟨hc1, hav, hlast.1, hlast.2⟩)⟩
        by_cases hend : singlePositive s.cycle = true
        · exact ⟨0, c, s, .stop _ _, hI, rfl, Or.inr (Or.inr ⟨hc1, hav, hend⟩)⟩
        · have hend' : singlePositive s.cycle = false := Bool.eq_false_iff.mpr hend
          obtain ⟨hmatch, hgood⟩ := hmid s w hsw hav hend'
          obtain ⟨vs, vq, hvs, hcmp, hmt, hq, hch⟩ :=
            scan_compare_match P q first hsw hzw hmatch hgood
          obtain ⟨o, ho⟩ := frame_refresh_exists P q first (afterCompare s vs vq) c.output
          obtain ⟨hdp, hdl⟩ := dec_pos_of_not_single hI.pos hend'
          have hcyc : (afterCompare s vs vq).cycle = dec s.cycle := by
            show cycleAfter s = dec s.cycle
            unfold cycleAfter; rw [hI.per]; simp
          have hI' : SInv delay W {c with clock := delay, output := o, replaying := false}
              (afterCompare s vs vq) := by
            refine ⟨hI.mode, rfl, hdelay, le_refl _, ?_, ?_,
              ⟨GalilScaffoldChainWatch.immediate w, hch, hzw, hwi w hWw⟩⟩
            · show (afterCompare s vs vq).periodOnly = true; exact hI.per
            · rw [hcyc]; exact hdp
          have hexp : s.cycle.pos.length * (delay + 1)
              = (dec s.cycle).pos.length * (delay + 1) + (delay + 1) := by
            rw [← hdl]; ring
          obtain ⟨n, c1, s1, hseg, hI1, hcen1, hstop⟩ := ih _ (afterCompare s vs vq) hI' (by
            rw [hcyc]
            show (dec s.cycle).pos.length * (delay + 1) + delay ≤ fuel
            omega)
          refine ⟨n + 1, c1, s1,
            .match c s vs vq o hI.mode hI.repl hav hc1 hend' hcmp hmt ⟨_, by rw [hvs]⟩ hq ho hseg,
            hI1, ?_, hstop⟩
          rw [hcen1]; rfl
    · exact ⟨0, c, s, .stop _ _, hI, rfl, Or.inl hav⟩

/-! ## The terminal, and the round -/

/-- The data the terminal of a round supplies when the shift guard holds.  It
is `Rounds.next`'s shift block: the prediction `hpred`, the canonical length,
the shift entry and the `h` unit head moves.  None of it is derivable from the
scan alone, so it travels as one named hypothesis. -/
def ShiftPack (P : Shared) (h : ℕ) (s1 : GalilVM) (w : GalilScaffoldChainWatch.State) : Prop :=
  read (right s1.right) = GalilScaffoldChainConsume.symbol w.machine.control.period.focus ∧
  Canonical s1.length ∧
  ∀ (vs : ScanVM) (vq : SearchVM), P.shiftGuard (afterMismatch s1 vs vq) →
    ∃ (s2 : GalilVM) (t' : ShiftState), P.beginShift (afterMismatch s1 vs vq) s2 ∧
      beginShiftVM h w (afterMismatch s1 vs vq) s2 ∧ CopyIdle s2 ∧
      ShiftRun ⟨s1.center, left s1.left, ofNat h, inc s1.radius, inc (inc s1.length)⟩ h t'

/-- `RoundEnd` of `GalilSegmentConstruct3` widened by the report point.  The
new alternative has the same shape as the other three: a scan segment followed
by the state predicate `LastLetterEnd`. -/
def RoundEnd' (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (c : Control) (s : GalilVM) : Prop :=
  RoundEnd P q first delay c s ∨
    ∃ (n : ℕ) (c1 : Control) (s1 : GalilVM),
      ScanSeg P q first delay n c s c1 s1 ∧ LastLetterEnd c1 s1

/-- **One round, or a terminal.**  This is `rounds_construct_inv`'s oracle
`hround` for the measure `μ c s = 2*|raw| − position s.center`.

The scan half is built by `scan_half`.  At the terminal the outer symbols
either differ — and then the shift guard decides between a genuine round
(`Rounds … 1`, assembled by `roundStep_of_shiftRun`) and `GuardFail` — or they
agree, and the chain must break, which is `BreakEnd`.

Named hypotheses, i.e. what is *not* derived here:

* `hsinv` — `RoundInv` implies the scan-half invariant `SInv` (in particular
  that the shift left the cycle counter positive and the watch in `W`);
* `hsearch`, `hwr`, `hwi` — the search/watch totality pack, as in
  `GalilSegmentConstruct`;
* `hmid` — before the terminal the comparison matches and the watch is `Good`
  (the periodicity content: each matched comparison extends the palindrome and
  `periodOn_span_of_next`/`palAt_shift_of_period` extend the period by one
  place, so the chain's prediction keeps agreeing);
* `hbreak` — a *matched* terminal breaks the chain;
* `hpack` — the shift block `ShiftPack` at a mismatching terminal;
* `hmeasure` — the centre still has `h` places of room, `position s.center + h
  ≤ 2*|raw|`, which is what makes `μ` decrease. -/
theorem round_scan_construct (P : Shared) (q : ℕ) (first : Fin 9) (delay h : ℕ)
    (raw : List (Fin 2)) (W : GalilScaffoldChainWatch.State → Prop)
    (hdelay : 1 ≤ delay)
    (hsinv : ∀ c s, RoundInv h raw c s → SInv delay W c s)
    (hsearch : ∀ (u : GalilVM) (a : Bool), ∃ v, searchEffect P a u v)
    (hwr : ∀ w, W w → WatchReady w)
    (hwi : ∀ w, W w → W (GalilScaffoldChainWatch.immediate w))
    (hmid : ∀ (u : GalilVM) (w : GalilScaffoldChainWatch.State),
      u.chain = ChainVM.watch w → canRight u.right → singlePositive u.cycle = false →
      read (left u.left) = read (right u.right) ∧ GalilScaffoldChainWatch.Good w)
    (hbreak : ∀ (u : GalilVM) (w : GalilScaffoldChainWatch.State),
      u.chain = ChainVM.watch w → canRight u.right → singlePositive u.cycle = true →
      read (left u.left) = read (right u.right) → ∃ w', BreakStep w w')
    (hpack : ∀ (u : GalilVM) (w : GalilScaffoldChainWatch.State),
      u.chain = ChainVM.watch w → canRight u.right → singlePositive u.cycle = true →
      read (left u.left) ≠ read (right u.right) → ShiftPack P h u w)
    (hmeasure : ∀ c s, RoundInv h raw c s → position s.center + h ≤ 2 * raw.length)
    (c : Control) (s : GalilVM) (hI : RoundInv h raw c s) :
    RoundEnd' P q first delay c s ∨
      ∃ (c' : Control) (s' : GalilVM), Rounds P q first delay h 1 c s c' s' ∧
        RoundInv h raw c' s' ∧
        2 * raw.length - position s'.center < 2 * raw.length - position s.center := by
  classical
  obtain ⟨org, w0, hint, hs0, hz0, hp0, he0, hper0, hmin0, hrepl0, hM0⟩ := hI
  have hI' : RoundInv h raw c s :=
    ⟨org, w0, hint, hs0, hz0, hp0, he0, hper0, hmin0, hrepl0, hM0⟩
  have hh : 0 < h := by omega
  obtain ⟨n, c1, s1, hseg, hI1, hcen1, hstop⟩ :=
    scan_half P q first delay W hdelay hsearch hwr hwi hmid
      (s.cycle.pos.length * (delay + 1) + c.clock) c s (hsinv c s hI') (le_refl _)
  obtain ⟨w, hsw, hzw, hWw⟩ := hI1.wit
  have hpf : positive w.lag = false := positive_of_zero hzw
  have hne1 : s1.chain ≠ ChainVM.idle := by rw [hsw]; intro h0; cases h0
  rcases hstop with hno | hlast | ⟨hc1, hav, hend⟩
  · exact Or.inl (Or.inl (Or.inr (Or.inl ⟨n, c1, s1, hseg, hno⟩)))
  · exact Or.inl (Or.inr ⟨n, c1, s1, hseg, hlast⟩)
  · by_cases hmatch : read (left s1.left) = read (right s1.right)
    · -- the terminal matches: the chain breaks
      obtain ⟨w', hbr⟩ := hbreak s1 w hsw hav hend hmatch
      have htick : ChainTick true (ChainVM.watch w) (ChainVM.broken w') := chainTick_of_break hbr
      refine Or.inl (Or.inl (Or.inl ⟨n, c1, s1, hseg, hI1.mode, hI1.repl, hc1, w, hsw, hav,
        ⟨left s1.left, right s1.right, ChainVM.broken w'⟩, searchLens.get s1, ?_, ?_, ?_, hend,
        w', rfl⟩))
      · refine Lens.rel_set scanLens _ s1 _ ⟨rfl, rfl, ?_⟩
        show ChainTick (decide (read (left s1.left) = read (right s1.right))) s1.chain
          (ChainVM.broken w')
        rw [decide_eq_true hmatch, hsw]; exact htick
      · show read (scanLens.get (scanLens.set s1 _)).left
          = read (scanLens.get (scanLens.set s1 _)).right
        rw [scanLens.get_set]; exact hmatch
      · exact Or.inr ⟨hne1, rfl⟩
    · -- the terminal mismatches
      have htick : ChainTick false (ChainVM.watch w) (ChainVM.watch w) :=
        chainTick_of_watch_false (.step (.idle w hpf) (.idle w))
      set vs : ScanVM := ⟨left s1.left, right s1.right, ChainVM.watch w⟩ with hvs
      set vq : SearchVM := searchLens.get s1 with hvq
      have hcmp : (galilFrame P q first).compare s1 (scanLens.set s1 vs) := by
        refine Lens.rel_set scanLens _ s1 vs ⟨rfl, rfl, ?_⟩
        show ChainTick (decide (read (left s1.left) = read (right s1.right))) s1.chain
          (ChainVM.watch w)
        rw [decide_eq_false hmatch, hsw]; exact htick
      have hmis : ¬ (galilFrame P q first).matched (scanLens.set s1 vs) := by
        show ¬ read (scanLens.get (scanLens.set s1 vs)).left
          = read (scanLens.get (scanLens.set s1 vs)).right
        rw [scanLens.get_set]; exact hmatch
      have hq : searchEffect P false s1 vq := Or.inr ⟨hne1, rfl⟩
      obtain ⟨hpred, hlen, hshift⟩ := hpack s1 w hsw hav hend hmatch
      by_cases hg : P.shiftGuard (afterMismatch s1 vs vq)
      · obtain ⟨s2, t', hb, hs2, hi2, hrun⟩ := hshift vs vq hg
        obtain ⟨v, cycle, o, hround⟩ :=
          roundStep_of_shiftRun P q first delay h hseg hI1.mode hI1.repl hc1 w hsw hav vs vq
            hcmp hmis hq hend hpred hlen hg s2 hb hs2 hi2 hrun
        refine Or.inr ⟨_, _, hround, ?_, ?_⟩
        · exact roundInv_preserved P q first delay h raw hround hI'
        · have hc := PalPeg.GalilChainReadyProgress.rounds_center raw P q first delay h hround w0 hp0 hs0 hz0 org hint he0
          have hbnd := hmeasure c s hI'
          omega
      · exact Or.inl (Or.inl (Or.inr (Or.inr ⟨n, c1, s1, hseg, hI1.mode, hI1.repl, hc1, hav,
          vs, vq, hcmp, hmis, hq, hg⟩)))

#print axioms chainReady_watch_zero
#print axioms scan_background
#print axioms frame_refresh_exists
#print axioms scan_compare_match
#print axioms dec_pos_of_not_single
#print axioms scan_half
#print axioms round_scan_construct

end PalPeg.GalilRoundConstruct
