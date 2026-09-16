import PalPeg.GalilRoundConstruct
import PalPeg.GalilFallbackLanding

/-!
# The mid-round fallback exit

`GalilRoundPeriod` shows that inside a re-shift round (chain a `.watch w`,
`singlePositive s.cycle = false`, i.e. *before* the terminal of the
semiperiod) the scan comparison may still mismatch — the period simply does
not extend.  `shiftGuardVM` is then false, because in `periodOnly` it demands
`singlePositive s.cycle = true`, so `Tick.scan_fallback` fires from a
*watching* chain state, not from the terminal that `GuardFail`
(`GalilSegmentConstruct3`) describes.

This module closes that exit:

1. `midround_guard_false` — reading `shiftGuardVM`: in `periodOnly` a
   non-single cycle counter makes the guard false, whatever the chain is.
2. `fallback_from_watch` — `fallback_landing` with a *watching* start state.
   The point is a negative one: `fallback_landing` never used `Restarted`, a
   `ChainMatched`/idle chain, or `SpanRep`; the only structural hypothesis it
   needs is `ShiftIdle s` (after a completed shift `remaining = 0`, so it
   holds), plus the input-tape facts that the found cycle got for free from
   `segment_mismatch_ready` and that a mid-round start has to supply by hand
   (`hrep`, `hfoc`, `hcan`, `heven`, `hout`).  Those are the named gaps.
3. `scan_half'` / `roundEnd_midFallback` — `GalilRoundConstruct.scan_half`
   and `round_scan_construct` with `hmid` weakened: before the terminal the
   comparison either matches with a `Good` watch (the periodicity content) or
   mismatches, and the mismatch is routed to the new state predicate
   `MidFallback`.
-/

set_option autoImplicit false
namespace PalPeg.GalilMidRoundFallback

open PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilRoundConstruct
open PalPeg.GalilBranchInvariants PalPeg.GalilTickFun
open Manacher GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter
  GalilScaffoldInputHead GalilScaffoldChainVerifier

/-! ## (1) The guard is false in mid-round -/

/-- `afterMismatch` touches only the scan projection, the search projection
and `radius`; `periodOnly` and `cycle` are carried through verbatim. -/
theorem afterMismatch_periodOnly (s : GalilVM) (vs : ScanVM) (vq : SearchVM) :
    (afterMismatch s vs vq).periodOnly = s.periodOnly := rfl

theorem afterMismatch_cycle (s : GalilVM) (vs : ScanVM) (vq : SearchVM) :
    (afterMismatch s vs vq).cycle = s.cycle := rfl

/-- **`midround_guard_false`.**  Inside a round the controller is in
`periodOnly`, where `shiftGuardVM` reads
`if s.periodOnly then singlePositive s.cycle = true else …`.  So a cycle
counter that is not yet *single* — the semiperiod countdown has not reached
its last place — makes the guard false at the state the comparison produces.
The watching chain `hsw` is *not* used: the guard fails on the counter
alone. -/
theorem midround_guard_false {s : GalilVM} {w : GalilScaffoldChainWatch.State}
    (_hsw : s.chain = ChainVM.watch w) (hper : s.periodOnly = true)
    (hcyc : singlePositive s.cycle = false) (vs : ScanVM) (vq : SearchVM) :
    ¬ shiftGuardVM (afterMismatch s vs vq) := by
  rintro ⟨w', _, _, _, _, hif, _⟩
  rw [afterMismatch_periodOnly, hper, if_pos rfl, afterMismatch_cycle, hcyc] at hif
  exact Bool.false_ne_true hif

/-- The form the round construction consumes: any state in `periodOnly` whose
cycle counter is not single fails the guard. -/
theorem midround_guard_false' (u : GalilVM) (hper : u.periodOnly = true)
    (hcyc : singlePositive u.cycle = false) : ¬ shiftGuardVM u := by
  rintro ⟨w', _, _, _, _, hif, _⟩
  rw [hper, if_pos rfl, hcyc] at hif
  exact Bool.false_ne_true hif

/-! ## (2) The fallback cycle from a watching chain -/

/-- **`fallback_from_watch`.**  `fallback_landing` with the chain a `.watch w`
instead of `.idle`, and with no `Restarted` at the start.

Which of `fallback_restarted_All` / `scan_fallback_cycle_All`'s hypotheses
genuinely need the found cycle's shape:

* `Restarted raw s Rad last` — **not needed**.  It appears in
  `cycle_fallback_stepsAll` only to run `segment_mismatch_ready` (producing
  `hrep`/`hfoc`/`hcan`) and `watchSegE_stepsAll` (producing `hout`); neither
  is a hypothesis of `fallback_landing` itself.
* `s.chain = .idle` — **not needed**.  `chainAt`'s first disjunct
  `(x ≠ .idle ∧ ChainTick a x z)` covers a watching chain, and
  `beginFallbackVM` sets `chain := .idle` regardless, which is why the landing
  still exports `t.chain = .idle`.
* `SpanRep s` — **not needed** here.  It is `leftmost_after_fallback_landing`'s
  hypothesis (it pays for the window coverage `2*(n−C)+1 ≤ W`), not
  `fallback_landing`'s.
* `ShiftIdle s` — **genuinely needed** (`hi`), and available mid-round: a round
  starts after a completed shift, where `remaining = 0`, and `shiftIdle_iff`
  is exactly `positive s.remaining = false`.

So the residual gaps of a mid-round start are only the input-tape facts
`hrep`, `hfoc`, `hcan`, `heven` and the output relation `hout`. -/
theorem fallback_from_watch (onLetter leftFirst : GalilVM → Prop) (rs : GalilVM → GalilVM → Prop)
    (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place) (entry : ℕ)
    (q : ℕ) (hq0 : 0 < q) (first : Fin 9) (h7 : first ≠ 7) (h8 : first ≠ 8) (delay : ℕ)
    (c : Control) (hm : c.mode = .scan) (hr : c.replaying = false) (hc : c.clock = 1)
    (s : GalilVM) (hi : ShiftIdle s) (hav : canRight s.right)
    (w : GalilScaffoldChainWatch.State) (hsw : s.chain = ChainVM.watch w)
    (vs : ScanVM) (vq : SearchVM) (hl : vs.left = left s.left) (hrr : vs.right = right s.right)
    (hct : ChainTick false (ChainVM.watch w) vs.chain)
    (hmis : read (left s.left) ≠ read (right s.right))
    (hq : searchEffect (galilShared onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' rs centre place entry)
      false s vq)
    (hg : ¬ shiftGuardVM (afterMismatch s vs vq))
    {raw : List (Fin 2)} (hrep : GalilScaffoldInputTrace.Represents (right s.right).head raw)
    (hfoc : (right s.right).head.focus ≠ none)
    (hcan : Canonical s.length) (ℓ : ℕ) (hv : value s.length = ℓ)
    (heven : ∀ (a : Fin 2) (xs rs' q' : List (Fin 2)),
      right s.right = represent ⟨a :: xs,(right s.right).gap⟩ (rs'.map some) q' →
      ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)).length % 2 = 0)
    (honL : onLetter = onLetterVM raw) (hlF : leftFirst = leftFirstVM) (hout : OutputRel raw c s) :
    ∃ (a : Fin 2) (xs rs' q' : List (Fin 2)),
      right s.right = represent ⟨a :: xs,(right s.right).gap⟩ (rs'.map some) q' ∧
      raw = (a :: xs).reverse ++ rs' ++ q' ∧
      ∃ (n : ℕ) (o : Bool) (t : GalilVM),
        StepsAll (galilFrameS (galilShared onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' rs centre place entry) q first) delay (SoundScanNR raw) (1 + (n+1)) ⟨c, s⟩
          ⟨{c with mode := .scan, clock := delay, output := o, replaying := decide (0 < chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1))), odd := oddAt false (((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)).length - (2*chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1))+1)), pair := pairAt (2*chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)))}, t⟩ ∧
        Restarted raw t 0 reset ∧
        position t.center = position (right s.right) - chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)) ∧
        Manacher.PalAt (encoded raw) (position (right s.right) - chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)))
          (chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1))) ∧
        (∀ r', 2*r'+1 ≤ ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)).length →
          Manacher.PalAt (encoded raw) (position (right s.right) - r') r' →
          r' ≤ chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1))) ∧
        t.replay = ofNat (chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1))) ∧
        ShiftIdle t ∧ t.chain = ChainVM.idle ∧
        t.right = GalilScaffoldInputHead.left^[chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1))] (right s.right) ∧
        t.center = t.right := by
  refine fallback_landing onLetter leftFirst rs centre place entry q hq0 first h7 h8 delay
    c hm hr hc s hi hav vs vq hl hrr hmis hq ?_ hg hrep hfoc hcan ℓ hv heven honL hlF hout
  refine Or.inl ⟨?_, ?_⟩
  · rw [hsw]; intro h0; cases h0
  · rw [hsw]; exact hct

/-! ## (3) The mid-round exit inside the round construction -/

/-- The state at which the scan half of a round stops with a *mid-round*
mismatch: clock one, the right symbol available, the semiperiod countdown not
yet single, and the outer symbols disagreeing. -/
def MidMismatch (c : Control) (s : GalilVM) : Prop :=
  c.clock = 1 ∧ canRight s.right ∧ singlePositive s.cycle = false ∧
    read (left s.left) ≠ read (right s.right)

/-- **`MidFallback`.**  The fourth way a round ends: a scan segment followed by
a mismatching comparison *before* the terminal, with the shift guard false, so
`Tick.scan_fallback` fires while the chain is still watching.  It has exactly
the shape of `GalilSegmentConstruct3.GuardFail` except that the cycle counter
is *not* single; `s1.periodOnly = true` and the watch are exported so that the
guard's failure and `fallback_from_watch` are both re-derivable. -/
def MidFallback (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (c : Control) (s : GalilVM) : Prop :=
  ∃ (n : ℕ) (c1 : Control) (s1 : GalilVM), ScanSeg P q first delay n c s c1 s1 ∧
    c1.mode = .scan ∧ c1.replaying = false ∧ c1.clock = 1 ∧ canRight s1.right ∧
    s1.periodOnly = true ∧ positive s1.cycle = true ∧ singlePositive s1.cycle = false ∧
    (∃ w, s1.chain = ChainVM.watch w) ∧
    ∃ (vs : ScanVM) (vq : SearchVM),
      (galilFrame P q first).compare s1 (scanLens.set s1 vs) ∧
      ¬ (galilFrame P q first).matched (scanLens.set s1 vs) ∧
      searchEffect P false s1 vq ∧ ¬ P.shiftGuard (afterMismatch s1 vs vq)

/-- **`scan_half'`.**  `GalilRoundConstruct.scan_half` with `hmid` weakened to
`hmid'`: before the terminal the comparison either matches with a `Good` watch
— and the loop step is unchanged — or it mismatches, and the segment stops
there with `MidMismatch`.  The proof is `scan_half`'s, with the mismatch case
added to the clock-one branch. -/
theorem scan_half' (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (W : GalilScaffoldChainWatch.State → Prop)
    (hdelay : 1 ≤ delay)
    (hsearch : ∀ (u : GalilVM) (a : Bool), ∃ v, searchEffect P a u v)
    (hwr : ∀ w, W w → WatchReady w)
    (hwi : ∀ w, W w → W (GalilScaffoldChainWatch.immediate w))
    (hmid' : ∀ (u : GalilVM) (w : GalilScaffoldChainWatch.State),
      u.chain = ChainVM.watch w → canRight u.right → singlePositive u.cycle = false →
      (read (left u.left) = read (right u.right) ∧ GalilScaffoldChainWatch.Good w) ∨
        read (left u.left) ≠ read (right u.right)) :
    ∀ (fuel : ℕ) (c : Control) (s : GalilVM), SInv delay W c s →
      s.cycle.pos.length * (delay + 1) + c.clock ≤ fuel →
      ∃ (n : ℕ) (c1 : Control) (s1 : GalilVM), ScanSeg P q first delay n c s c1 s1 ∧
        SInv delay W c1 s1 ∧ s1.center = s.center ∧
        (¬ canRight s1.right ∨ LastLetterEnd c1 s1 ∨
          (c1.clock = 1 ∧ canRight s1.right ∧ singlePositive s1.cycle = true) ∨
          MidMismatch c1 s1) := by
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
      · obtain ⟨s', hb, hc', hpo', hcy', hcen', hr', hl'⟩ :=
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
      · have hc1 : c.clock = 1 := le_antisymm hle hI.clk1
        by_cases hlast : PopsIncoming s.right ∧ ∃ a, s.right.head.incoming = [a]
        · exact ⟨0, c, s, .stop _ _, hI, rfl, Or.inr (Or.inl ⟨hc1, hav, hlast.1, hlast.2⟩)⟩
        by_cases hend : singlePositive s.cycle = true
        · exact ⟨0, c, s, .stop _ _, hI, rfl, Or.inr (Or.inr (Or.inl ⟨hc1, hav, hend⟩))⟩
        · have hend' : singlePositive s.cycle = false := Bool.eq_false_iff.mpr hend
          rcases hmid' s w hsw hav hend' with ⟨hmatch, hgood⟩ | hmis
          · obtain ⟨vs, vq, hvs, hcmp, hmt, hq, hch⟩ :=
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
          · exact ⟨0, c, s, .stop _ _, hI, rfl,
              Or.inr (Or.inr (Or.inr ⟨hc1, hav, hend', hmis⟩))⟩
    · exact ⟨0, c, s, .stop _ _, hI, rfl, Or.inl hav⟩

/-- **`roundEnd_midFallback`.**  `GalilRoundConstruct.round_scan_construct`
with `hmid` weakened to `hmid'` and the new exit `MidFallback` added to the
conclusion.

The guard's failure at the new exit is not assumed: it comes from `hPg`,
which `midround_guard_false'` discharges for the concrete shared record
(`P.shiftGuard = shiftGuardVM`, see `midFallback_guard_concrete`).  Everything
else is `round_scan_construct`'s proof verbatim. -/
theorem roundEnd_midFallback (P : Shared) (q : ℕ) (first : Fin 9) (delay h : ℕ)
    (raw : List (Fin 2)) (W : GalilScaffoldChainWatch.State → Prop)
    (hdelay : 1 ≤ delay)
    (hPg : ∀ u : GalilVM, u.periodOnly = true → singlePositive u.cycle = false →
      ¬ P.shiftGuard u)
    (hsinv : ∀ c s, RoundInv h raw c s → SInv delay W c s)
    (hsearch : ∀ (u : GalilVM) (a : Bool), ∃ v, searchEffect P a u v)
    (hwr : ∀ w, W w → WatchReady w)
    (hwi : ∀ w, W w → W (GalilScaffoldChainWatch.immediate w))
    (hmid' : ∀ (u : GalilVM) (w : GalilScaffoldChainWatch.State),
      u.chain = ChainVM.watch w → canRight u.right → singlePositive u.cycle = false →
      (read (left u.left) = read (right u.right) ∧ GalilScaffoldChainWatch.Good w) ∨
        read (left u.left) ≠ read (right u.right))
    (hbreak : ∀ (u : GalilVM) (w : GalilScaffoldChainWatch.State),
      u.chain = ChainVM.watch w → canRight u.right → singlePositive u.cycle = true →
      read (left u.left) = read (right u.right) → ∃ w', BreakStep w w')
    (hpack : ∀ (u : GalilVM) (w : GalilScaffoldChainWatch.State),
      u.chain = ChainVM.watch w → canRight u.right → singlePositive u.cycle = true →
      read (left u.left) ≠ read (right u.right) → ShiftPack P h u w)
    (hmeasure : ∀ c s, RoundInv h raw c s → position s.center + h ≤ 2 * raw.length)
    (c : Control) (s : GalilVM) (hI : RoundInv h raw c s) :
    RoundEnd' P q first delay c s ∨ MidFallback P q first delay c s ∨
      ∃ (c' : Control) (s' : GalilVM), Rounds P q first delay h 1 c s c' s' ∧
        RoundInv h raw c' s' ∧
        2 * raw.length - position s'.center < 2 * raw.length - position s.center := by
  classical
  obtain ⟨org, w0, hint, hs0, hz0, hp0, he0, hper0, hmin0, hrepl0, hM0⟩ := hI
  have hI' : RoundInv h raw c s :=
    ⟨org, w0, hint, hs0, hz0, hp0, he0, hper0, hmin0, hrepl0, hM0⟩
  have hh : 0 < h := by omega
  obtain ⟨n, c1, s1, hseg, hI1, hcen1, hstop⟩ :=
    scan_half' P q first delay W hdelay hsearch hwr hwi hmid'
      (s.cycle.pos.length * (delay + 1) + c.clock) c s (hsinv c s hI') (le_refl _)
  obtain ⟨w, hsw, hzw, hWw⟩ := hI1.wit
  have hpf : positive w.lag = false := positive_of_zero hzw
  have hne1 : s1.chain ≠ ChainVM.idle := by rw [hsw]; intro h0; cases h0
  rcases hstop with hno | hlast | ⟨hc1, hav, hend⟩ | ⟨hc1, hav, hend, hmm⟩
  · exact Or.inl (Or.inl (Or.inr (Or.inl ⟨n, c1, s1, hseg, hno⟩)))
  · exact Or.inl (Or.inr ⟨n, c1, s1, hseg, hlast⟩)
  · by_cases hmatch : read (left s1.left) = read (right s1.right)
    · obtain ⟨w', hbr⟩ := hbreak s1 w hsw hav hend hmatch
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
    · have htick : ChainTick false (ChainVM.watch w) (ChainVM.watch w) :=
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
        refine Or.inr (Or.inr ⟨_, _, hround, ?_, ?_⟩)
        · exact roundInv_preserved P q first delay h raw hround hI'
        · have hc := PalPeg.GalilChainReadyProgress.rounds_center raw P q first delay h hround w0 hp0 hs0 hz0 org hint he0
          have hbnd := hmeasure c s hI'
          omega
      · exact Or.inl (Or.inl (Or.inr (Or.inr ⟨n, c1, s1, hseg, hI1.mode, hI1.repl, hc1, hav,
          vs, vq, hcmp, hmis, hq, hg⟩)))
  · -- the new exit: a mid-round mismatch, where the guard is false in `periodOnly`
    have htick : ChainTick false (ChainVM.watch w) (ChainVM.watch w) :=
      chainTick_of_watch_false (.step (.idle w hpf) (.idle w))
    set vs : ScanVM := ⟨left s1.left, right s1.right, ChainVM.watch w⟩ with hvs
    set vq : SearchVM := searchLens.get s1 with hvq
    have hcmp : (galilFrame P q first).compare s1 (scanLens.set s1 vs) := by
      refine Lens.rel_set scanLens _ s1 vs ⟨rfl, rfl, ?_⟩
      show ChainTick (decide (read (left s1.left) = read (right s1.right))) s1.chain
        (ChainVM.watch w)
      rw [decide_eq_false hmm, hsw]; exact htick
    have hmis : ¬ (galilFrame P q first).matched (scanLens.set s1 vs) := by
      show ¬ read (scanLens.get (scanLens.set s1 vs)).left
        = read (scanLens.get (scanLens.set s1 vs)).right
      rw [scanLens.get_set]; exact hmm
    have hq : searchEffect P false s1 vq := Or.inr ⟨hne1, rfl⟩
    have hg : ¬ P.shiftGuard (afterMismatch s1 vs vq) := by
      refine hPg _ ?_ ?_
      · rw [afterMismatch_periodOnly]; exact hI1.per
      · rw [afterMismatch_cycle]; exact hend
    exact Or.inr (Or.inl ⟨n, c1, s1, hseg, hI1.mode, hI1.repl, hc1, hav, hI1.per, hI1.pos, hend,
      ⟨w, hsw⟩, vs, vq, hcmp, hmis, hq, hg⟩)

/-- For the concrete shared record `hPg` is discharged. -/
theorem midFallback_guard_concrete (onLetter leftFirst : GalilVM → Prop)
    (rs : GalilVM → GalilVM → Prop) (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry : ℕ) (u : GalilVM)
    (hper : u.periodOnly = true) (hcyc : singlePositive u.cycle = false) :
    ¬ (galilShared onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' rs centre place entry).shiftGuard u :=
  midround_guard_false' u hper hcyc

#print axioms midround_guard_false
#print axioms midround_guard_false'
#print axioms fallback_from_watch
#print axioms scan_half'
#print axioms roundEnd_midFallback
#print axioms midFallback_guard_concrete

end PalPeg.GalilMidRoundFallback
