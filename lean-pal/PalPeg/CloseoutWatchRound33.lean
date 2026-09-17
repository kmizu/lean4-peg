import PalPeg.CloseoutWatchRound32

/-!
# Closeout watch round 33 — pieces 1 and 2 of `shiftRoundAtC'_of_tick`, settled

**Piece 1 (`ShiftLagZeroC`) — verdict: FALSE as stated.**  `ShiftLagZeroC`
quantifies over every `s1` with a watching chain and a mismatching frame
compare.  The compare's chain tick is `ChainTick false`, i.e. one
`Internal` step; when the pre-compare lag is positive
and `Good w`, `Internal.take` is available and lands at `caught w` with the lag
decremented (`compare_of_take`).  With `w.lag = ofNat 1` the landing lag is
`0` (`caught_lag_zero_of_one`), so the guard's `zero` clause is met by the
POST-compare chain `caught w`, while `ShiftLagZeroC` demands
`positive w.lag = false` of the PRE-compare chain: `not_shiftLagZeroC` refutes
it from any such state.  Such states are not excluded by the model: the watch
enters at `backDone` carrying the lag accumulated by `ChainMatched.copy/back`
(one unit per matched compare during copy/back) and drains one unit per
background tick, so a `backDone` at clock `2` with lag `1` reaches the clock-`1`
compare with lag `1`.  (`GalilScaffoldChainLag.clock_catches` only gives lag
`0` after `2k+2` ticks — not before.)

Consequence: `ShiftRoundData` (Round 7) binds ONE `w` for
`s1.chain = .watch w`, `zero w.lag`, and `beginShiftVM h w (afterMismatch …)`;
in the `take` case it is unattainable.  The corrected data
`ShiftRoundDataL` binds the pre-compare `w` and the post-compare `w'` with
`Internal w w'` and `vs.chain = .watch w'`, and states the lag, guard, shift
entry and chain run on `w'`.  `ShiftRoundData` embeds into it (`w' := w`,
`Internal.idle` from `zero w.lag`; `shiftRoundDataL_of_data`).

**Piece 2 (`ShiftPeriodC h`) — verdict: `h` is CHOSEN.**  In the consumer
`CloseoutWatchPhase2.ShiftTailC` (used by `roundsRouteLP_of_tail`) `h` is
existentially bound per landing, whereas Round 30's `ShiftRoundAtC'` fixes one
`h` for all landings.  `beginShiftVM'` enters with `periodLength w'` of the
post-compare chain, so the landing-dependent `ShiftRoundAtCL'` concludes
`∃ h, ShiftRoundDataL … h …` with `h := periodLength w'`, and piece 2
disappears (`rfl` inside `shiftRoundAtCL_of_tick`).  The tie to the DP tape
(`pos 11 = h`) and to the origin (`org.interior.length + 1 = h`) stays where
it was: inside piece 5 (`ShiftOriginCL`).  If a caller insists on the
pre-compare period, `periodLength_post` transfers it across `Internal` under
`OnBlock` (the period tape is one block: `GalilChainCoupling.periodLength_consume`).

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

namespace PalPeg.CloseoutWatchRound33

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.CloseoutContracts
open PalPeg.GalilRunSkeleton PalPeg.GalilInvPlus PalPeg.GalilInvPlus2
open PalPeg.GalilFoundStage PalPeg.GalilTraceCost
open PalPeg.CloseoutWatchRun (LiveScanWatch)
open PalPeg.CloseoutWatchRound7 (ShiftRoundData)
open PalPeg.CloseoutWatchRound30 (ShiftCopyIdleC)
open PalPeg.CloseoutWatchRound32 (ShiftLagZeroC watch_after_compare)
open PalPeg.GalilBranchInvariants (OnBlock)
open PalPeg.GalilChainCoupling (periodLength_consume)

/-! ## 1. Piece 1: the pre-compare lag can be positive -/

/-- A lag of exactly one unit is caught by the compare's `take`: the landing
lag is zero. -/
theorem caught_lag_zero_of_one (w : GalilScaffoldChainWatch.State)
    (hl : w.lag = ofNat 1) : zero (GalilScaffoldChainWatch.caught w).lag = true := by
  simp only [GalilScaffoldChainWatch.caught]
  rw [hl]
  rfl

/-- One unit of lag is positive. -/
theorem positive_ofNat_one : positive (ofNat 1) = true := rfl

/-- **The counter-scenario at the tick.**  At a watching chain with positive
lag and `Good w`, an outer mismatch admits the frame compare whose chain tick
is `Internal.take`: the post-compare chain is `.watch (caught w)`. -/
theorem compare_of_take (P : Shared) (q : ℕ) (first : Fin 9) {s1 : GalilVM}
    {w : GalilScaffoldChainWatch.State} (hw : s1.chain = ChainVM.watch w)
    (hp : positive w.lag = true) (hg : GalilScaffoldChainWatch.Good w)
    (hne : read (left s1.left) ≠ read (right s1.right)) :
    ∃ vs : ScanVM,
      (galilFrame P q first).compare s1 (scanLens.set s1 vs) ∧
      ¬ (galilFrame P q first).matched (scanLens.set s1 vs) ∧
      vs.chain = ChainVM.watch (GalilScaffoldChainWatch.caught w) := by
  refine ⟨⟨left s1.left, right s1.right, ChainVM.watch (GalilScaffoldChainWatch.caught w)⟩, ?_, ?_, rfl⟩
  · refine ⟨⟨rfl, rfl, ?_⟩, rfl⟩
    show ChainTick (decide (read (left s1.left) = read (right s1.right))) s1.chain
      (ChainVM.watch (GalilScaffoldChainWatch.caught w))
    rw [decide_eq_false hne, hw]
    refine ⟨_, ChainStep.watchStep _ _ (GalilScaffoldChainWatch.Internal.take w hp hg), ?_⟩
    simp
  · intro hmt
    exact hne hmt

/-- **`ShiftLagZeroC` is false** whenever some watching state with positive lag,
`Good`, and an outer mismatch exists (the model admits them, see the header). -/
theorem not_shiftLagZeroC (P : Shared) (q : ℕ) (first : Fin 9)
    (hex : ∃ (s1 : GalilVM) (w : GalilScaffoldChainWatch.State),
      s1.chain = ChainVM.watch w ∧ GalilScaffoldChainWatch.Good w ∧ positive w.lag = true ∧
      read (left s1.left) ≠ read (right s1.right)) :
    ¬ ShiftLagZeroC P q first := by
  intro hlag
  obtain ⟨s1, w, hw, hg, hp, hne⟩ := hex
  obtain ⟨vs, hcmp, hmis, -⟩ := compare_of_take P q first hw hp hg hne
  have h0 := hlag s1 vs w hw hcmp hmis
  rw [hp] at h0
  exact Bool.noConfusion h0

/-- The post-compare chain, in both cases, is a watch `w'` with
`Internal w w'`; this is the shape the corrected data records. -/
theorem post_compare_internal {P : Shared} {q : ℕ} {first : Fin 9} {s1 : GalilVM}
    {vs : ScanVM} {w : GalilScaffoldChainWatch.State} (hw : s1.chain = ChainVM.watch w)
    (hcmp : (galilFrame P q first).compare s1 (scanLens.set s1 vs))
    (hmis : ¬ (galilFrame P q first).matched (scanLens.set s1 vs)) :
    ∃ w' : GalilScaffoldChainWatch.State, GalilScaffoldChainWatch.Internal w w' ∧ vs.chain = ChainVM.watch w' := by
  rcases watch_after_compare hw hcmp hmis with ⟨hz, hvs⟩ | ⟨hp, hg, hvs⟩
  · exact ⟨w, GalilScaffoldChainWatch.Internal.idle w hz, hvs⟩
  · exact ⟨GalilScaffoldChainWatch.caught w, GalilScaffoldChainWatch.Internal.take w hp hg, hvs⟩

/-! ## 2. The corrected data `ShiftRoundDataL` -/

/-- `CloseoutWatchRound7.ShiftRoundData` with the post-compare watch `w'`
(`Internal w w'`, `vs.chain = .watch w'`) carrying the lag, the shift entry and
the chain run.  Every other conjunct is verbatim. -/
def ShiftRoundDataL (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m h lower : ℕ) (sF : GalilVM) (vq : SearchVM)
    (c1 : Control) (s1 : GalilVM) : Prop :=
  ∃ (w w' : GalilScaffoldChainWatch.State)
      (vs : ScanVM) (vq' : SearchVM) (s2' : GalilVM) (t' : ShiftState)
      (v : GalilScaffoldChainWatch.State) (cycle : Counter) (o : Bool)
      (org : ReadOrigin raw) (mm : ℕ) (c' : Control) (s' : GalilVM)
      (n : ℕ) (c3 : Control) (s3 : GalilVM) (w3 : GalilScaffoldChainWatch.State)
      (vs3 : ScanVM) (vq3 : SearchVM) (o3 : Bool) (w3' : GalilScaffoldChainWatch.State),
      c1.mode = .scan ∧ c1.replaying = false ∧ c1.clock = 1 ∧
      s1.chain = ChainVM.watch w ∧ GalilScaffoldChainWatch.Internal w w' ∧ vs.chain = ChainVM.watch w' ∧
      zero w'.lag = true ∧ canRight s1.right ∧
      (galilFrame (PofC centre place entry raw) qq first).compare s1 (scanLens.set s1 vs) ∧
      ¬ (galilFrame (PofC centre place entry raw) qq first).matched (scanLens.set s1 vs) ∧
      searchEffect (PofC centre place entry raw) false s1 vq' ∧
      (PofC centre place entry raw).shiftGuard (afterMismatch s1 vs vq') ∧
      (PofC centre place entry raw).beginShift (afterMismatch s1 vs vq') s2' ∧
      beginShiftVM h w' (afterMismatch s1 vs vq') s2' ∧ CopyIdle s2' ∧
      ChainShiftRun ⟨s1.center, left s1.left, ofNat h, inc s1.radius, inc (inc s1.length)⟩
        (GalilScaffoldChainWatch.immediate w') reset h t' v cycle ∧
      refresh (galilFrameS (PofC centre place entry raw) qq first)
        (shiftLens.set s2' ⟨t', .watch v, cycle⟩) c1.output o ∧
      org.interior.length + 1 = h ∧
      Entry raw org (toOnly (shiftLens.set s2' ⟨t', .watch v, cycle⟩) v) ∧
      org.center = position sF.center ∧
      PalPeg.GalilRadiusConsumed.Aligned org ∧
      (GalilScaffoldProgram.denote vq.dp.config).pos 11 = h ∧
      (∀ δ, 0 < δ → δ ≤ lower → ¬ HasPeriod (Span raw org.center org.radius) (2*δ)) ∧
      Rounds (PofC centre place entry raw) qq first 2048 h mm
        {c1 with mode := .scan, clock := 2048, output := o}
        (shiftLens.set s2' ⟨t', .watch v, cycle⟩) c' s' ∧
      ScanSeg (PofC centre place entry raw) qq first 2048 n c' s' c3 s3 ∧
      c3.mode = .scan ∧ c3.replaying = false ∧ c3.clock = 1 ∧
      s3.chain = ChainVM.watch w3 ∧ canRight s3.right ∧
      (galilFrame (PofC centre place entry raw) qq first).compare s3 (scanLens.set s3 vs3) ∧
      (galilFrame (PofC centre place entry raw) qq first).matched (scanLens.set s3 vs3) ∧
      searchEffect (PofC centre place entry raw) true s3 vq3 ∧
      refresh (galilFrame (PofC centre place entry raw) qq first)
        (afterCompare s3 vs3 vq3) c3.output o3 ∧
      (afterCompare s3 vs3 vq3).chain = ChainVM.broken w3' ∧
      negative w3'.margin = false ∧ positive w3'.machine.control.last = true ∧
      zero w3'.lag = true ∧
      position (afterCompare s3 vs3 vq3).right ≤ 2 * m - 1

/-- The original data embeds (`w' := w`, the tick is `idle`). -/
theorem shiftRoundDataL_of_data (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m h lower : ℕ) (sF : GalilVM) (vq : SearchVM)
    (c1 : Control) (s1 : GalilVM)
    (hd : ShiftRoundData centre place entry qq first raw m h lower sF vq c1 s1) :
    ShiftRoundDataL centre place entry qq first raw m h lower sF vq c1 s1 := by
  obtain ⟨w, vs, vq', s2', t', v, cycle, o, org, mm, c', s', n, c3, s3, w3, vs3, vq3, o3, w3',
    hm1, hr1, hc1, hw, hz, hav, hcmp, hmis, hq', hg, hb, hs2', hi2, hchain, ho, hint, he, hoc,
    ha, hpos11, hlow, hrounds, hseg3, hm3, hr3, hc3, hs3, hav3, hcmp3, hmt3, hq3, ho3, hbroken,
    hmargin, hlast, hlag3, hbound⟩ := hd
  exact ⟨w, w, vs, vq', s2', t', v, cycle, o, org, mm, c', s', n, c3, s3, w3, vs3, vq3, o3, w3',
    hm1, hr1, hc1, hw, GalilScaffoldChainWatch.Internal.idle w (positive_of_zero hz), hs2'.1, hz, hav, hcmp, hmis, hq',
    hg, hb, hs2', hi2, hchain, ho, hint, he, hoc, ha, hpos11, hlow, hrounds, hseg3, hm3, hr3,
    hc3, hs3, hav3, hcmp3, hmt3, hq3, ho3, hbroken, hmargin, hlast, hlag3, hbound⟩

/-! ## 3. Piece 2: the period is read from the post-compare chain -/

/-- The period length is preserved across the compare's `Internal` step when
the period tape is one block (`OnBlock`), i.e. the pre-compare `periodLength w`
may be used for the entry. -/
theorem periodLength_post {w w' : GalilScaffoldChainWatch.State} (hi : GalilScaffoldChainWatch.Internal w w')
    (hb : OnBlock w.machine.control.period) : periodLength w' = periodLength w := by
  cases hi with
  | idle => rfl
  | take hp hg =>
    exact periodLength_consume w.machine w.lag w.margin (dec w.lag) w.margin hb

/-! ## 4. The landing-dependent producer: `h := periodLength w'` -/

/-- **`ShiftRoundAtC'` with the shift amount chosen at the landing.**  Same
premises as Round 30's `ShiftRoundAtC'`; the conclusion existentially binds
`h`, as the consumer `ShiftTailC` does. -/
def ShiftRoundAtCL' (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m lower : ℕ) : Prop :=
  ∀ (sF : GalilVM) (vq : SearchVM) (c1 : Control) (s1 : GalilVM) (vs : ScanVM),
    LiveScanWatch c1 s1 → c1.clock = 1 → canRight s1.right →
    (galilFrame (PofC centre place entry raw) qq first).compare s1 (scanLens.set s1 vs) →
    ¬ (galilFrame (PofC centre place entry raw) qq first).matched (scanLens.set s1 vs) →
    (∀ vq' : SearchVM, shiftGuardVM (afterMismatch s1 vs vq')) →
      ∃ h : ℕ, ShiftRoundDataL centre place entry qq first raw m h lower sF vq c1 s1

/-- **NAMED (open) — piece 4, landing form.**  The shift run of
`periodLength w'` units at the post-compare watch `w'`. -/
def ShiftRunCL : Prop :=
  ∀ (c1 : Control) (s1 : GalilVM) (w w' : GalilScaffoldChainWatch.State),
    LiveScanWatch c1 s1 → c1.clock = 1 → s1.chain = ChainVM.watch w → GalilScaffoldChainWatch.Internal w w' →
    canRight s1.right →
    ∃ t' : ShiftState,
      ShiftRun ⟨s1.center, left s1.left, ofNat (periodLength w'), inc s1.radius,
        inc (inc s1.length)⟩ (periodLength w') t'

/-- **NAMED (open) — piece 5, landing form.**  The origin ledger at the shift
landing, with `h := periodLength w'` (this is where `pos 11` and the origin
are tied to the period tape). -/
def ShiftOriginCL (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (lower : ℕ) : Prop :=
  ∀ (sF : GalilVM) (vq : SearchVM) (c1 : Control) (s1 : GalilVM) (vs : ScanVM)
    (vq' : SearchVM) (w w' : GalilScaffoldChainWatch.State) (s2' : GalilVM)
    (t' : ShiftState) (v : GalilScaffoldChainWatch.State) (cycle : Counter),
    LiveScanWatch c1 s1 → c1.clock = 1 → s1.chain = ChainVM.watch w → GalilScaffoldChainWatch.Internal w w' →
    beginShiftVM (periodLength w') w' (afterMismatch s1 vs vq') s2' →
    ChainShiftRun ⟨s1.center, left s1.left, ofNat (periodLength w'), inc s1.radius,
        inc (inc s1.length)⟩
      (GalilScaffoldChainWatch.immediate w') reset (periodLength w') t' v cycle →
    ∃ org : ReadOrigin raw,
      org.interior.length + 1 = periodLength w' ∧
      Entry raw org (toOnly (shiftLens.set s2' ⟨t', .watch v, cycle⟩) v) ∧
      org.center = position sF.center ∧
      PalPeg.GalilRadiusConsumed.Aligned org ∧
      (GalilScaffoldProgram.denote vq.dp.config).pos 11 = periodLength w' ∧
      (∀ δ, 0 < δ → δ ≤ lower → ¬ HasPeriod (Span raw org.center org.radius) (2*δ))

/-- **NAMED (open) — piece 6, landing form.** -/
def ShiftBreakRunCL (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m : ℕ) : Prop :=
  ∀ (c1 : Control) (s1 : GalilVM) (vs : ScanVM) (vq' : SearchVM)
    (w w' : GalilScaffoldChainWatch.State) (s2' : GalilVM) (t' : ShiftState)
    (v : GalilScaffoldChainWatch.State) (cycle : Counter) (o : Bool),
    LiveScanWatch c1 s1 → c1.clock = 1 → s1.chain = ChainVM.watch w → GalilScaffoldChainWatch.Internal w w' →
    beginShiftVM (periodLength w') w' (afterMismatch s1 vs vq') s2' →
    ChainShiftRun ⟨s1.center, left s1.left, ofNat (periodLength w'), inc s1.radius,
        inc (inc s1.length)⟩
      (GalilScaffoldChainWatch.immediate w') reset (periodLength w') t' v cycle →
    refresh (galilFrameS (PofC centre place entry raw) qq first)
      (shiftLens.set s2' ⟨t', .watch v, cycle⟩) c1.output o →
    ∃ (mm : ℕ) (c' : Control) (s' : GalilVM) (n : ℕ) (c3 : Control) (s3 : GalilVM)
      (w3 : GalilScaffoldChainWatch.State) (vs3 : ScanVM) (vq3 : SearchVM) (o3 : Bool)
      (w3' : GalilScaffoldChainWatch.State),
      Rounds (PofC centre place entry raw) qq first 2048 (periodLength w') mm
        {c1 with mode := .scan, clock := 2048, output := o}
        (shiftLens.set s2' ⟨t', .watch v, cycle⟩) c' s' ∧
      ScanSeg (PofC centre place entry raw) qq first 2048 n c' s' c3 s3 ∧
      c3.mode = .scan ∧ c3.replaying = false ∧ c3.clock = 1 ∧
      s3.chain = ChainVM.watch w3 ∧ canRight s3.right ∧
      (galilFrame (PofC centre place entry raw) qq first).compare s3 (scanLens.set s3 vs3) ∧
      (galilFrame (PofC centre place entry raw) qq first).matched (scanLens.set s3 vs3) ∧
      searchEffect (PofC centre place entry raw) true s3 vq3 ∧
      refresh (galilFrame (PofC centre place entry raw) qq first)
        (afterCompare s3 vs3 vq3) c3.output o3 ∧
      (afterCompare s3 vs3 vq3).chain = ChainVM.broken w3' ∧
      negative w3'.margin = false ∧ positive w3'.machine.control.last = true ∧
      zero w3'.lag = true ∧
      position (afterCompare s3 vs3 vq3).right ≤ 2 * m - 1

/-- **Derived — `ShiftRoundAtCL'` from the tick and pieces 3–6.**  Pieces 1
and 2 are gone: the post-compare watch comes from the tick
(`post_compare_internal`), the guard reads its lag, and the entry's period is
the chosen `h`. -/
theorem shiftRoundAtCL_of_tick (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m lower : ℕ)
    (h3 : ShiftCopyIdleC) (h4 : ShiftRunCL)
    (h5 : ShiftOriginCL centre place entry qq first raw lower)
    (h6 : ShiftBreakRunCL centre place entry qq first raw m) :
    ShiftRoundAtCL' centre place entry qq first raw m lower := by
  intro sF vq c1 s1 vs hL hclk hav hcmp hmis hg
  obtain ⟨hm1, hr1, hc1, w, hw⟩ := hL
  have hL' : LiveScanWatch c1 s1 := ⟨hm1, hr1, hc1, w, hw⟩
  obtain ⟨w', hint', hvs⟩ := post_compare_internal hw hcmp hmis
  -- the search quantum: the chain is not idle, so the search projection is kept
  have hq' : searchEffect (PofC centre place entry raw) false s1 (searchLens.get s1) :=
    Or.inr ⟨(by rw [hw]; intro h; cases h), rfl⟩
  -- the guard at that quantum, and its watch state is `w'`
  have hgc : shiftGuardVM (afterMismatch s1 vs (searchLens.get s1)) := hg (searchLens.get s1)
  obtain ⟨w₂, hw₂, hlag₂, -, -, -, -⟩ := hgc
  have hw₂' : w₂ = w' := by
    have h' : vs.chain = ChainVM.watch w₂ := hw₂
    rw [hvs] at h'
    exact (ChainVM.watch.inj h').symm
  have hlag : zero w'.lag = true := hw₂' ▸ hlag₂
  -- the shift entry, with the period read from the post-compare chain
  let s2' : GalilVM :=
    {afterMismatch s1 vs (searchLens.get s1) with
      remaining := ofNat (periodLength w'),
      length := inc (inc (afterMismatch s1 vs (searchLens.get s1)).length),
      chain := .watch (GalilScaffoldChainWatch.immediate w'),
      cycle := reset, periodOnly := true}
  have hs2' : beginShiftVM (periodLength w') w' (afterMismatch s1 vs (searchLens.get s1)) s2' :=
    ⟨hvs, rfl⟩
  have hb : (PofC centre place entry raw).beginShift (afterMismatch s1 vs (searchLens.get s1)) s2' := by
    show beginShiftVM' _ _
    exact ⟨w', hs2'⟩
  have hgP : (PofC centre place entry raw).shiftGuard (afterMismatch s1 vs (searchLens.get s1)) :=
    hg (searchLens.get s1)
  -- copy idle transported
  have hi2 : CopyIdle s2' := (copyIdle_iff s2').2 ((copyIdle_iff s1).1 (h3 c1 s1 hL' hclk))
  -- the shift run and its chain run
  obtain ⟨t', hrun⟩ := h4 c1 s1 w w' hL' hclk hw hint' hav
  obtain ⟨v, cycle, hchain⟩ :=
    shift_run_chain hrun (GalilScaffoldChainWatch.immediate w') reset
  -- the output refresh
  obtain ⟨o, ho⟩ := PalPeg.GalilTickFun3.refresh_exists (PofC centre place entry raw) qq first
    (shiftLens.set s2' ⟨t', .watch v, cycle⟩) c1.output
  -- the origin ledger and the break run
  obtain ⟨org, hint, he, hoc, ha, hpos11, hlow⟩ :=
    h5 sF vq c1 s1 vs (searchLens.get s1) w w' s2' t' v cycle hL' hclk hw hint' hs2' hchain
  obtain ⟨mm, c', s', n, c3, s3, w3, vs3, vq3, o3, w3', hrounds, hseg3, hm3, hr3, hc3, hs3,
    hav3, hcmp3, hmt3, hq3, ho3, hbroken, hmargin, hlast, hlag3, hbound⟩ :=
    h6 c1 s1 vs (searchLens.get s1) w w' s2' t' v cycle o hL' hclk hw hint' hs2' hchain ho
  exact ⟨periodLength w', w, w', vs, searchLens.get s1, s2', t', v, cycle, o, org, mm, c', s', n,
    c3, s3, w3, vs3, vq3, o3, w3', hm1, hr1, hclk, hw, hint', hvs, hlag, hav, hcmp, hmis, hq',
    hgP, hb, hs2', hi2, hchain, ho, hint, he, hoc, ha, hpos11, hlow, hrounds, hseg3, hm3, hr3,
    hc3, hs3, hav3, hcmp3, hmt3, hq3, ho3, hbroken, hmargin, hlast, hlag3, hbound⟩

end PalPeg.CloseoutWatchRound33

#print axioms PalPeg.CloseoutWatchRound33.caught_lag_zero_of_one
#print axioms PalPeg.CloseoutWatchRound33.compare_of_take
#print axioms PalPeg.CloseoutWatchRound33.not_shiftLagZeroC
#print axioms PalPeg.CloseoutWatchRound33.post_compare_internal
#print axioms PalPeg.CloseoutWatchRound33.shiftRoundDataL_of_data
#print axioms PalPeg.CloseoutWatchRound33.periodLength_post
#print axioms PalPeg.CloseoutWatchRound33.shiftRoundAtCL_of_tick
