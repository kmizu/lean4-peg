import PalPeg.CloseoutWatchRound4

/-!
# Round 5: the two terminal tails of the watch round

`PalPeg.CloseoutWatchRound4.foundExit_compare_final4` still takes the two
monolithic tails `CloseoutWatchRound3.ShiftExitTailC` and
`CloseoutWatchRound3.BreakExitTailC`, each of which turns a terminal *exit*
(`TerminalRunShiftC` / `TerminalRunBreakC`) into a whole
`CloseoutWatchPhase2.ShiftTailC` / `CloseoutWatchPhase3.NoShiftTailC0` bundle.
This file cuts both tails into state-local pieces and re-derives them.

## What is proved here (unconditionally, no `sorry`)

1. `watchTick_of_chainTick` — the converse of
   `GalilScaffoldChainInputSupply.chainTick_of_watch_true/false`: a chain tick
   between two *watching* chains **is** a `GalilScaffoldChainWatch.Tick`.
2. `run_append`, `run_of_watchSeg` — hence the **watch run accumulated along a
   watch segment**: with `CloseoutWatchRound3.CompareKeepsWatchC` (discharged
   in Round 4 from `NoBreakAtMatchC`) every `WatchSeg` out of a watching chain
   produces a `GalilScaffoldChainWatch.Run` whose event list is the segment's
   comparison record.  This is the missing link between the machine-level watch
   phase and the chain-level ledger lemmas of `GalilNoShiftStage`, which all
   speak about `Run (freshWatch …) es m`.
3. `breakStep_of_chainTick`, `breakStep_at_terminal` — a matched comparison
   landing on `ChainVM.broken w'` is exactly a `BreakStep w w'`.
4. `fresh_margin_false_of_places` / `fresh_places_pred_of_margin` — the
   **margin conjunct of the break tail is the fuel measure.**  Along a run out
   of `freshWatch`, `fresh_break_ledger` gives `distance = 4h + margin` and
   `break_control` gives `margin w' = margin m + 1`, so
   `negative w'.margin = false` is equivalent to `4h - 1 ≤ distance`, and
   `4*h ≤ distance` — i.e. `CloseoutWatchRun.roundFuel h = 0` — implies it.
   The remaining corner `distance = 4h - 1` is
   `GalilNoShiftStage.fresh_break_places`, not needed in this direction.
5. `margin_false_of_fuel` — the packaged form: at a terminal break reached from
   a `freshWatch` landing with the fuel spent, `negative w'.margin = false`.
6. `shiftTick_of_roundData` — the shift round really is a machine step:
   `GalilScaffoldTop.Tick.scan_shift` fires on the data the shift tail records.
7. `shiftExitTailC_of_parts` / `breakExitTailC_of_parts` — the two tails,
   re-derived from the state-local pieces.  The composition of the exit's own
   `WatchSeg` with the round's is `CloseoutWatchRun.watchSeg_append`.

## Still open, NAMED with exact types

* `PrepLandingLiveC` — every landing of the preparation segment is a live scan
  watch landing (`CloseoutWatchRun.LiveScanWatch`); the exits ask for it, and
  `CloseoutPrepInputs3.prep_of_prepInputsG3` branch A supplies it per event
  list.
* `FoundDpShiftC` — the DP record of the found answer (`GalilDpCorrect.Result`
  at `(lower, span)` and `pc = 346`) read off the found comparison's `vq`.
* `ShiftRoundC` — the shift round at a fuel-spent-or-guarded exit landing.
* `BreakLandingC` — the `freshWatch` shape of the preparation landing and
  `es.count true = 0`.
* `BreakTerminalC` — the terminal break at a break-family exit landing, stated
  with the fuel conjunct `roundFuel h s3 = 0` in place of the margin conjunct
  that §3 now derives (both `¬ canRight` and `BreakEndC` exits are accepted, so
  no exit needs excluding).
* `FoundDpBreakC` — the found comparison's DP candidate at `h`, the centre
  equation `position r.center = position sF.center`, and `Canonical sF.radius`.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutWatchRound5

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.CloseoutContracts
open PalPeg.GalilRunSkeleton PalPeg.GalilTraceCost
open PalPeg.GalilInvPlus (SegReachedW)
open PalPeg.GalilTickFun (ChainReady)
open PalPeg.GalilNoShiftStage (freshWatch fresh_break_ledger break_control)
open PalPeg.CloseoutWatchRun (LiveScanWatch roundFuel watchSeg_append places_of_fuel_zero)
open PalPeg.CloseoutWatchPhase2 (ShiftTailC LandingRestartReach)
open PalPeg.CloseoutWatchPhase3 (NoShiftTailC0)
open PalPeg.CloseoutWatchRound (TerminalC BreakEndC)
open PalPeg.CloseoutWatchRound2 (TerminalRunC FoundCompareCtxC)
open PalPeg.CloseoutWatchRound3 (WatchLedgerC CompareKeepsWatchC ExitSplitC
  ShiftExitTailC BreakExitTailC TerminalRunShiftC TerminalRunBreakC DistanceNonnegC)

/-! ## 1. A watch tick from a chain tick -/

/-- **Derived — the converse of `chainTick_of_watch_true/false`.** -/
theorem watchTick_of_chainTick {b : Bool} {w w' : GalilScaffoldChainWatch.State}
    (h : ChainTick b (ChainVM.watch w) (ChainVM.watch w')) :
    GalilScaffoldChainWatch.Tick w b w' := by
  obtain ⟨y, hstep, hm⟩ := h
  obtain ⟨w1, hi, rfl⟩ := PalPeg.CloseoutWatchRound4.step_of_watch hstep
  cases b with
  | false =>
      simp only [Bool.false_eq_true, if_false] at hm
      cases hm
      exact .step hi (.idle _)
  | true =>
      simp only [if_true] at hm
      cases hm with
      | watch _ _ ho => exact .step hi ho

/-- **Derived.**  A matched comparison landing on a broken chain is a
`BreakStep` out of the state the comparison was taken at, **provided the lag
reads zero**: then `Internal.take` is blocked and the internal step is
`Internal.idle` (`CloseoutWatchRound4.internal_eq_of_zero`).  Without that the
break could sit after a catch-up step and the conclusion would be about the
intermediate state instead. -/
theorem breakStep_of_chainTick {w w' : GalilScaffoldChainWatch.State}
    (hz : zero w.lag = true)
    (h : ChainTick true (ChainVM.watch w) (ChainVM.broken w')) :
    GalilScaffoldChainInputSupply.BreakStep w w' := by
  obtain ⟨y, hstep, hm⟩ := h
  obtain ⟨w1, hi, rfl⟩ := PalPeg.CloseoutWatchRound4.step_of_watch hstep
  simp only [if_true] at hm
  cases hm with
  | breaks _ _ hb =>
      have he : w1 = w := PalPeg.CloseoutWatchRound4.internal_eq_of_zero hz hi
      rw [he] at hb
      exact hb

/-! ## 2. The watch run accumulated along a watch segment -/

/-- **Derived.**  `GalilScaffoldChainWatch.Run` is transitive. -/
theorem run_append {w m t : GalilScaffoldChainWatch.State} {es es' : List Bool}
    (h1 : GalilScaffoldChainWatch.Run w es m)
    (h2 : GalilScaffoldChainWatch.Run m es' t) :
    GalilScaffoldChainWatch.Run w (es ++ es') t := by
  induction h1 with
  | stop s => simpa using h2
  | next ht _ ih => exact .next ht (ih h2)

/-- **Derived — the missing link to the chain ledgers.**  Every `WatchSeg` out
of a watching chain keeps it watching and records a `Run`. -/
theorem run_of_watchSeg (P : Shared) (q : ℕ) (first : Fin 9)
    (hkeep : CompareKeepsWatchC P q first)
    {c c' : Control} {s t : GalilVM}
    (h : WatchSeg P q first 2048 c s c' t) :
    ∀ w : GalilScaffoldChainWatch.State, s.chain = ChainVM.watch w →
      ∃ (es : List Bool) (w' : GalilScaffoldChainWatch.State),
        t.chain = ChainVM.watch w' ∧ GalilScaffoldChainWatch.Run w es w' := by
  induction h with
  | stop c s => exact fun w hw => ⟨[], w, hw, .stop _⟩
  | wait c s s' hm hr hn hb rest ih =>
      intro w hw
      have hne : s.chain ≠ ChainVM.idle := by rw [hw]; intro h0; cases h0
      have htick : ChainTick false (ChainVM.watch w) s'.chain := by
        rw [← hw]; exact backgroundS_chainTick P q first hb hne
      obtain ⟨w1, hw1⟩ := PalPeg.CloseoutWatchRound2.watchClosed w s'.chain htick
      obtain ⟨es, w', hend, hrun⟩ := ih w1 hw1
      refine ⟨false :: es, w', hend, .next (watchTick_of_chainTick ?_) hrun⟩
      rw [← hw1]; exact htick
  | count c s s' hm hr ha hc hb rest ih =>
      intro w hw
      have hne : s.chain ≠ ChainVM.idle := by rw [hw]; intro h0; cases h0
      have htick : ChainTick false (ChainVM.watch w) s'.chain := by
        rw [← hw]; exact backgroundS_chainTick P q first hb hne
      obtain ⟨w1, hw1⟩ := PalPeg.CloseoutWatchRound2.watchClosed w s'.chain htick
      obtain ⟨es, w', hend, hrun⟩ := ih w1 hw1
      refine ⟨false :: es, w', hend, .next (watchTick_of_chainTick ?_) hrun⟩
      rw [← hw1]; exact htick
  | «match» c s vs vq o hm hr ha hc hne hcmp hmt hq ho rest ih =>
      intro w hw
      obtain ⟨w1, hw1⟩ := hkeep s vs vq w hw hcmp hmt
      have hmatch : read (left s.left) = read (right s.right) := by
        obtain ⟨⟨hl0, hr0, -⟩, -⟩ := hcmp
        rw [scanLens.get_set] at hl0 hr0
        have hp := matched_parts P q first hmt
        rw [hl0, hr0] at hp; exact hp
      obtain ⟨-, -, htick⟩ := compare_parts P q first hcmp hmatch
      have htick' : ChainTick true (ChainVM.watch w) (afterCompare s vs vq).chain := by
        rw [afterCompare_chain, ← hw]; exact htick
      obtain ⟨es, w', hend, hrun⟩ := ih w1 hw1
      refine ⟨true :: es, w', hend, .next (watchTick_of_chainTick ?_) hrun⟩
      rw [← hw1]; exact htick'

/-- **Derived.**  The terminal comparison of the break tail is a `BreakStep`
out of the watch state the segment reached. -/
theorem breakStep_at_terminal (P : Shared) (q : ℕ) (first : Fin 9)
    {s3 : GalilVM} {vs3 : ScanVM} {vq3 : SearchVM}
    {w3 w3' : GalilScaffoldChainWatch.State}
    (hs3 : s3.chain = ChainVM.watch w3)
    (hz3 : GalilScaffoldCounter.zero w3.lag = true) (hz : zero w3.lag = true)
    (hcmp : (galilFrame P q first).compare s3 (scanLens.set s3 vs3))
    (hmt : (galilFrame P q first).matched (scanLens.set s3 vs3))
    (hbroken : (afterCompare s3 vs3 vq3).chain = ChainVM.broken w3') :
    GalilScaffoldChainInputSupply.BreakStep w3 w3' := by
  have hmatch : read (left s3.left) = read (right s3.right) := by
    obtain ⟨⟨hl0, hr0, -⟩, -⟩ := hcmp
    rw [scanLens.get_set] at hl0 hr0
    have hp := matched_parts P q first hmt
    rw [hl0, hr0] at hp; exact hp
  obtain ⟨-, -, htick⟩ := compare_parts P q first hcmp hmatch
  rw [hs3] at htick
  rw [afterCompare_chain] at hbroken
  rw [hbroken] at htick
  exact breakStep_of_chainTick hz htick

/-! ## 3. The margin conjunct is the fuel measure -/

/-- **Derived.**  Along a run out of `freshWatch`, `4*h ≤ distance` gives the
nonnegative break margin. -/
theorem fresh_margin_false_of_places (ver : GalilScaffoldInputHead.PlaceHead) (cen : Fin 3)
    (ys : List (Fin 3)) (b : Fin 3) (radius : Counter) (hrc : Canonical radius)
    {es : List Bool} {m w' : GalilScaffoldChainWatch.State}
    (hrun : GalilScaffoldChainWatch.Run (freshWatch ver cen ys b radius) es m)
    (hbr : GalilScaffoldChainInputSupply.BreakStep m w')
    (hplaces : 4 * ((ys.length : ℤ) + 1) ≤ value m.machine.control.distance) :
    negative w'.margin = false := by
  obtain ⟨xs, -, -, -, -, -, hbal, hcm⟩ := fresh_break_ledger ver cen ys b radius hrc hrun hbr
  obtain ⟨-, -, hmar'⟩ := break_control hbr
  have hcw' : Canonical w'.margin := by
    obtain ⟨-, -, -, -, -, hw⟩ := hbr
    rw [hw]; exact inc_canonical _ hcm.2
  by_contra hneg
  have hb : negative w'.margin = true := by
    cases hh : negative w'.margin with
    | false => exact absurd hh hneg
    | true => rfl
  have hlt := (negative_iff _ hcw').mp hb
  omega

/-- **Derived — the converse, up to the corner.**  A nonnegative break margin
only gives `4*h - 1 ≤ distance`; the corner `distance = 4*h - 1` is excluded by
`GalilNoShiftStage.fresh_break_places`, which needs the input palindromes.  So
the fuel conjunct is *strictly* stronger, which is why §3 goes from fuel to
margin and not back. -/
theorem fresh_places_pred_of_margin (ver : GalilScaffoldInputHead.PlaceHead) (cen : Fin 3)
    (ys : List (Fin 3)) (b : Fin 3) (radius : Counter) (hrc : Canonical radius)
    {es : List Bool} {m w' : GalilScaffoldChainWatch.State}
    (hrun : GalilScaffoldChainWatch.Run (freshWatch ver cen ys b radius) es m)
    (hbr : GalilScaffoldChainInputSupply.BreakStep m w')
    (hmargin : negative w'.margin = false) :
    4 * ((ys.length : ℤ) + 1) - 1 ≤ value m.machine.control.distance := by
  obtain ⟨xs, -, -, -, -, -, hbal, hcm⟩ := fresh_break_ledger ver cen ys b radius hrc hrun hbr
  obtain ⟨-, -, hmar'⟩ := break_control hbr
  have hcw' : Canonical w'.margin := by
    obtain ⟨-, -, -, -, -, hw⟩ := hbr
    rw [hw]; exact inc_canonical _ hcm.2
  have hnn : 0 ≤ value w'.margin := by
    by_contra hlt
    have hb : negative w'.margin = true := (negative_iff _ hcw').mpr (by omega)
    rw [hmargin] at hb; exact absurd hb (by simp)
  omega

/-- **Derived — the packaged form.**  A terminal break reached by a `WatchSeg`
from a `freshWatch` landing, with the fuel spent at the pre-break state, has a
nonnegative margin. -/
theorem margin_false_of_fuel (P : Shared) (q : ℕ) (first : Fin 9)
    (hkeep : CompareKeepsWatchC P q first) (hnn : DistanceNonnegC)
    (ver : GalilScaffoldInputHead.PlaceHead) (cen : Fin 3) (ys : List (Fin 3)) (b : Fin 3)
    (radius : Counter) (hrc : Canonical radius)
    {c2 c3 : Control} {s2 s3 : GalilVM} {vs3 : ScanVM} {vq3 : SearchVM}
    {w3 w3' : GalilScaffoldChainWatch.State}
    (hlanding : s2.chain = ChainVM.watch (freshWatch ver cen ys b radius))
    (hseg : WatchSeg P q first 2048 c2 s2 c3 s3)
    (hs3 : s3.chain = ChainVM.watch w3)
    (hz3 : GalilScaffoldCounter.zero w3.lag = true)
    (hcmp : (galilFrame P q first).compare s3 (scanLens.set s3 vs3))
    (hmt : (galilFrame P q first).matched (scanLens.set s3 vs3))
    (hbroken : (afterCompare s3 vs3 vq3).chain = ChainVM.broken w3')
    (hz : zero w3.lag = true)
    (hfuel : roundFuel (ys.length + 1) s3 = 0) :
    negative w3'.margin = false := by
  obtain ⟨es, w1, hend, hrun⟩ := run_of_watchSeg P q first hkeep hseg _ hlanding
  have hw1 : w1 = w3 := by
    rw [hs3] at hend
    injection hend with hinj
    exact hinj.symm
  subst hw1
  have hbr := breakStep_at_terminal P q first hs3 hz hcmp hmt hbroken
  have hplaces : 4 * ((ys.length : ℤ) + 1) ≤ value w1.machine.control.distance := by
    have hp := places_of_fuel_zero (ys.length + 1) hs3 (hnn s3 w1 hs3) hfuel
    push_cast at hp ⊢; linarith
  exact fresh_margin_false_of_places ver cen ys b radius hrc hrun hbr hplaces

/-! ## 4. The shift round is a legal machine step -/

/-- **Derived.**  `Tick.scan_shift` on the data the shift tail records.  So the
NAMED `ShiftRoundC` below asks only *which* round mismatches, not whether the
machine may shift there. -/
theorem shiftTick_of_roundData (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    {c1 : Control} {s1 s1' s2' : GalilVM}
    (hm1 : c1.mode = .scan) (hr1 : c1.replaying = false) (hc1 : c1.clock = 1)
    (hav : canRight s1.right)
    (hcmp : (galilFrameS P q first).compare s1 s1')
    (hmis : ¬ (galilFrameS P q first).matched s1')
    (hg : (galilFrameS P q first).shiftGuard s1')
    (hb : (galilFrameS P q first).beginShift s1' s2') :
    GalilScaffoldTop.Tick (galilFrameS P q first) delay ⟨c1, s1⟩
      ⟨{c1 with clock := delay, mode := .shift}, s2'⟩ :=
  GalilScaffoldTop.Tick.scan_shift c1 s1 s1' s2' hm1 (Or.inr hav) hc1 hcmp hmis hr1 hg hb

/-! ## 5. The two tails, on state-local pieces -/

/-- **NAMED (open).**  Every landing of the preparation segment is a live scan
watch landing.  Both exits (`TerminalRunShiftC` / `TerminalRunBreakC`) ask for
it; `CloseoutPrepInputs3.prep_of_prepInputsG3` branch A supplies exactly this
per event list (`c2.mode = .scan`, `c2.replaying = false`, `1 ≤ c2.clock`, and
a `.watch` chain). -/
def PrepLandingLiveC (P : Shared) (q : ℕ) (first : Fin 9) (cP : Control) (sP : GalilVM) : Prop :=
  ∀ (es : List Bool) (c2 : Control) (s2 : GalilVM),
    WatchSegE P q first 2048 es cP sP c2 s2 → LiveScanWatch c2 s2

/-- **NAMED (open).**  The DP record of the found answer, read off the found
comparison's own search state.  `CloseoutPrepInputs3.PrepInputsG3` carries the
same `GalilDpCorrect.Result` for its machine `y`; the missing step is
`vq.dp.config = y.config`. -/
def FoundDpShiftC (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (lower span : ℕ) (c0 : Control) (r : GalilVM) : Prop :=
  ∀ (a : Fin 2) (ls rs qw : List (Fin 2)) (gap : Bool) (es0 : List Bool) (cF : Control)
    (sF : GalilVM) (vq : SearchVM),
    WatchSegE (PofC centre place entry raw) qq first 2048 es0 c0 r cF sF →
    sF.center = represent ⟨a :: ls, gap⟩ (rs.map some) qw →
    searchEffect (PofC centre place entry raw) true sF vq → vq.search.mode = .found →
      GalilDpCorrect.Result ((GalilScaffoldPlace.stream ⟨a :: ls, gap⟩).take (span+1)) lower 0
        (GalilScaffoldProgram.denote vq.dp.config) ∧
      (GalilScaffoldProgram.denote vq.dp.config).pc = 346

/-- **NAMED (open) — the shift round.**  At a live watch landing where the fuel
is spent or the shift guard already holds, the machine performs one more
`WatchSeg` to a clock-`1` landing whose comparison *mismatches*, the guard
passes, `beginShift` fires (`§4`: this is a legal `Tick.scan_shift`), the chain
shift runs, and the subsequent `Rounds` and terminal `ScanSeg` break as the
shift tail records.  Everything here is run data about the landing `(cT, sT)`;
the found comparison enters only through `sF` (the centre position) and `vq`
(the DP head position `pos 11 = h`). -/
def ShiftRoundC (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m h lower : ℕ) : Prop :=
  ∀ (sF : GalilVM) (vq : SearchVM) (cT : Control) (sT : GalilVM),
    LiveScanWatch cT sT → (roundFuel h sT = 0 ∨ shiftGuardVM sT) →
    ∃ (c1 : Control) (s1 : GalilVM) (w : GalilScaffoldChainWatch.State)
      (vs : ScanVM) (vq' : SearchVM) (s2' : GalilVM) (t' : ShiftState)
      (v : GalilScaffoldChainWatch.State) (cycle : Counter) (o : Bool)
      (org : ReadOrigin raw) (mm : ℕ) (c' : Control) (s' : GalilVM)
      (n : ℕ) (c3 : Control) (s3 : GalilVM) (w3 : GalilScaffoldChainWatch.State)
      (vs3 : ScanVM) (vq3 : SearchVM) (o3 : Bool) (w3' : GalilScaffoldChainWatch.State),
      WatchSeg (PofC centre place entry raw) qq first 2048 cT sT c1 s1 ∧
      c1.mode = .scan ∧ c1.replaying = false ∧ c1.clock = 1 ∧
      s1.chain = ChainVM.watch w ∧ zero w.lag = true ∧ canRight s1.right ∧
      (galilFrame (PofC centre place entry raw) qq first).compare s1 (scanLens.set s1 vs) ∧
      ¬ (galilFrame (PofC centre place entry raw) qq first).matched (scanLens.set s1 vs) ∧
      searchEffect (PofC centre place entry raw) false s1 vq' ∧
      (PofC centre place entry raw).shiftGuard (afterMismatch s1 vs vq') ∧
      (PofC centre place entry raw).beginShift (afterMismatch s1 vs vq') s2' ∧
      beginShiftVM h w (afterMismatch s1 vs vq') s2' ∧ CopyIdle s2' ∧
      ChainShiftRun ⟨s1.center, left s1.left, ofNat h, inc s1.radius, inc (inc s1.length)⟩
        (GalilScaffoldChainWatch.immediate w) reset h t' v cycle ∧
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
      s3.chain = ChainVM.watch w3 ∧ GalilScaffoldCounter.zero w3.lag = true ∧
      canRight s3.right ∧
      (galilFrame (PofC centre place entry raw) qq first).compare s3 (scanLens.set s3 vs3) ∧
      (galilFrame (PofC centre place entry raw) qq first).matched (scanLens.set s3 vs3) ∧
      searchEffect (PofC centre place entry raw) true s3 vq3 ∧
      refresh (galilFrame (PofC centre place entry raw) qq first)
        (afterCompare s3 vs3 vq3) c3.output o3 ∧
      (afterCompare s3 vs3 vq3).chain = ChainVM.broken w3' ∧
      negative w3'.margin = false ∧ positive w3'.machine.control.last = true ∧
      zero w3'.lag = true ∧
      position (afterCompare s3 vs3 vq3).right ≤ 2 * m - 1

/-- **Derived — `ShiftExitTailC` re-derived.**  The exit's own `WatchSeg` and
the round's compose by `CloseoutWatchRun.watchSeg_append`. -/
theorem shiftExitTailC_of_parts (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m h lower span : ℕ) {c0 cP : Control} {r sP : GalilVM}
    (hdp : FoundDpShiftC centre place entry qq first raw lower span c0 r)
    (hround : ShiftRoundC centre place entry qq first raw m h lower) :
    ShiftExitTailC centre place entry qq first raw m h c0 r cP sP := by
  intro hctx hrun
  obtain ⟨es0, cF, sF, vq, ch, oF, a, ls, rs, qw, gap, hraw, hseg0, hmF, hrF, hcF, havF,
    hidle, hCen, hq, hfound, hmt, hch, hchne, hoF, hcPeq, hsPeq⟩ := hctx
  obtain ⟨hres, hpc⟩ := hdp a ls rs qw gap es0 cF sF vq hseg0 hCen hq hfound
  refine ⟨a, ls, rs, qw, gap, es0, cF, sF, vq, ch, oF, lower, span, hraw, hseg0, hmF, hrF, hcF,
    havF, hidle, hCen, hq, hfound, hmt, hch, hchne, hoF, hcPeq, hsPeq, hres, hpc, ?_⟩
  intro es c2 s2 hseg hwLanding
  obtain ⟨hmL, hrL, hcL⟩ := watchSegE_live_control (delay := 2048) (by omega) hseg
    (by rw [hcPeq]; exact hmF) (by rw [hcPeq]) (by simp [hcPeq])
  obtain ⟨cT, sT, hsegT, hLT, hexit⟩ := hrun es c2 s2 hseg ⟨hmL, hrL, hcL, hwLanding⟩
  obtain ⟨c1, s1, w, vs, vq', s2', t', v, cycle, o, org, mm, c', s', n, c3, s3, w3, vs3, vq3,
    o3, w3', hsegR, hm1, hr1, hc1, hs1, hz, hav, hcmp, hmis, hq', hg, hb, hs2', hi2, hchain,
    ho, hint, he, hoc, ha, hpos11, hlow, hrounds, hseg3, hm3, hr3, hc3, hs3, hav3, hcmp3,
    hmt3, hq3, ho3, hbroken, hmargin, hlast, hlag, hbound⟩ := hround sF vq cT sT hLT hexit
  exact ⟨c1, s1, h, w, vs, vq', s2', t', v, cycle, o, org, mm, c', s', n, c3, s3, w3, vs3, vq3,
    o3, w3', watchSeg_append hsegT hsegR, hm1, hr1, hc1, hs1, hz, hav, hcmp, hmis, hq', hg, hb,
    hs2', hi2, hchain, ho, hint, he, hoc, ha, hpos11, hlow, hrounds, hseg3, hm3, hr3, hc3, hs3,
    hav3, hcmp3, hmt3, hq3, ho3, hbroken, hmargin, hlast, hlag, hbound⟩

/-- **NAMED (open) — the break landing.**  The preparation lands on the fresh
watch state and credits no comparison.  This is the `freshWatch` half of
`CloseoutPrepInputs3.prep_of_prepInputsG3` branch A, whose lag reads
`value sP.radius + es.count true`; the tail needs `es.count true = 0`, i.e. the
delay-fit `CloseoutPrepInputs2.NoCompareInPrepG` records. -/
def BreakLandingC (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (h : ℕ) (sF : GalilVM) (cP : Control) (sP : GalilVM) : Prop :=
  ∀ (es : List Bool) (c2 : Control) (s2 : GalilVM),
    WatchSegE (PofC centre place entry raw) qq first 2048 es cP sP c2 s2 →
    (∃ wLive : GalilScaffoldChainWatch.State, s2.chain = ChainVM.watch wLive) →
      ∃ (cen : Fin 3) (ys : List (Fin 3)) (b : Fin 3),
        ys.length + 1 = h ∧
        s2.chain = ChainVM.watch (freshWatch sF.center cen ys b sF.radius) ∧
        es.count true = 0

/-- **NAMED (open) — the terminal break.**  At a break-family exit landing the
machine reaches a clock-`1` matched comparison that breaks the chain.  Note the
**fuel** conjunct `roundFuel h s3 = 0` in place of the break tail's
`negative w3'.margin = false`: §3 derives the latter from the former along a
run out of `freshWatch`, so the arithmetic conjunct is gone. -/
def BreakTerminalC (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m h : ℕ) : Prop :=
  ∀ (cT : Control) (sT : GalilVM), LiveScanWatch cT sT →
    (¬ canRight sT.right ∨ BreakEndC (PofC centre place entry raw) qq first cT sT) →
      ∃ (c3 : Control) (s3 : GalilVM) (w3 : GalilScaffoldChainWatch.State) (vs3 : ScanVM)
        (vq3 : SearchVM) (o3 : Bool) (w3' : GalilScaffoldChainWatch.State),
        WatchSeg (PofC centre place entry raw) qq first 2048 cT sT c3 s3 ∧
        c3.mode = .scan ∧ c3.replaying = false ∧ c3.clock = 1 ∧
        s3.chain = ChainVM.watch w3 ∧ GalilScaffoldCounter.zero w3.lag = true ∧
        canRight s3.right ∧
        (galilFrame (PofC centre place entry raw) qq first).compare s3 (scanLens.set s3 vs3) ∧
        (galilFrame (PofC centre place entry raw) qq first).matched (scanLens.set s3 vs3) ∧
        searchEffect (PofC centre place entry raw) true s3 vq3 ∧
        refresh (galilFrame (PofC centre place entry raw) qq first)
          (afterCompare s3 vs3 vq3) c3.output o3 ∧
        (afterCompare s3 vs3 vq3).chain = ChainVM.broken w3' ∧
        zero w3.lag = true ∧ roundFuel h s3 = 0 ∧
        position (afterCompare s3 vs3 vq3).right ≤ 2 * m - 1

/-- **NAMED (open).**  The found comparison's DP candidate at the half-period
`h`, the centre equation the no-shift branch needs, and the canonicity of the
radius the fresh watch starts from. -/
def FoundDpBreakC (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (lower span h : ℕ) (c0 : Control) (r : GalilVM) : Prop :=
  ∀ (a : Fin 2) (ls rs qw : List (Fin 2)) (gap : Bool) (es0 : List Bool) (cF : Control)
    (sF : GalilVM) (vq : SearchVM),
    WatchSegE (PofC centre place entry raw) qq first 2048 es0 c0 r cF sF →
    sF.center = represent ⟨a :: ls, gap⟩ (rs.map some) qw →
    searchEffect (PofC centre place entry raw) true sF vq → vq.search.mode = .found →
      GalilDpCorrect.Candidate
        ((GalilScaffoldPlace.stream ⟨a :: ls, gap⟩).take (span+1)) lower h ∧
      position r.center = position sF.center ∧ Canonical sF.radius

/-- **Derived — `BreakExitTailC` re-derived.**  The margin conjunct of the tail
is supplied by `margin_false_of_fuel`, so the NAMED pieces owe only the landing
shape, the terminal break with its fuel, and the found data. -/
theorem breakExitTailC_of_parts (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m h lower span : ℕ) {c0 cP : Control} {r sP : GalilVM}
    (hkeep : CompareKeepsWatchC (PofC centre place entry raw) qq first)
    (hnn : DistanceNonnegC)
    (hdp : FoundDpBreakC centre place entry qq first raw lower span h c0 r)
    (hland : ∀ sF : GalilVM, BreakLandingC centre place entry qq first raw h sF cP sP)
    (hterm : BreakTerminalC centre place entry qq first raw m h) :
    BreakExitTailC centre place entry qq first raw m h c0 r cP sP := by
  intro hctx hrun
  obtain ⟨es0, cF, sF, vq, ch, oF, a, ls, rs, qw, gap, hraw, hseg0, hmF, hrF, hcF, havF,
    hidle, hCen, hq, hfound, hmt, hch, hchne, hoF, hcPeq, hsPeq⟩ := hctx
  obtain ⟨hcand, hpr, hrc⟩ := hdp a ls rs qw gap es0 cF sF vq hseg0 hCen hq hfound
  refine ⟨es0, cF, sF, vq, ch, oF, a, ls, rs, qw, gap, span, lower, h, hraw, hCen, hpr, hcand,
    hseg0, hmF, hrF, hcF, havF, hidle, hq, hfound, hmt, hch, hchne, hoF, hcPeq, hsPeq, ?_⟩
  intro es c2 s2 hseg hwLanding
  obtain ⟨cen, ys, b, hys, hwatch2, hes0⟩ := hland sF es c2 s2 hseg hwLanding
  obtain ⟨hmL, hrL, hcL⟩ := watchSegE_live_control (delay := 2048) (by omega) hseg
    (by rw [hcPeq]; exact hmF) (by rw [hcPeq]) (by simp [hcPeq])
  obtain ⟨cT, sT, hsegT, hLT, hexit⟩ :=
    hrun es c2 s2 hseg ⟨hmL, hrL, hcL, hwLanding⟩
  obtain ⟨c3, s3, w3, vs3, vq3, o3, w3', hsegR, hm3, hr3, hc3, hs3, hav3, hcmp3, hmt3, hq3,
    ho3, hbroken, hz3, hfuel, hbound⟩ := hterm cT sT hLT hexit
  have hmargin : negative w3'.margin = false :=
    margin_false_of_fuel (PofC centre place entry raw) qq first hkeep hnn sF.center cen ys b
      sF.radius hrc hwatch2 (watchSeg_append hsegT hsegR) hs3 hcmp3 hmt3 hbroken hz3
      (by rw [hys]; exact hfuel)
  exact ⟨cen, ys, b, c3, s3, w3, vs3, vq3, o3, w3', hys, hwatch2, hes0,
    watchSeg_append hsegT hsegR, hm3, hr3, hc3, hs3, hav3, hcmp3, hmt3, hq3, ho3, hbroken,
    hmargin, hbound⟩


end PalPeg.CloseoutWatchRound5

#print axioms PalPeg.CloseoutWatchRound5.watchTick_of_chainTick
#print axioms PalPeg.CloseoutWatchRound5.breakStep_of_chainTick
#print axioms PalPeg.CloseoutWatchRound5.run_append
#print axioms PalPeg.CloseoutWatchRound5.run_of_watchSeg
#print axioms PalPeg.CloseoutWatchRound5.breakStep_at_terminal
#print axioms PalPeg.CloseoutWatchRound5.fresh_margin_false_of_places
#print axioms PalPeg.CloseoutWatchRound5.fresh_places_pred_of_margin
#print axioms PalPeg.CloseoutWatchRound5.margin_false_of_fuel
#print axioms PalPeg.CloseoutWatchRound5.shiftTick_of_roundData
#print axioms PalPeg.CloseoutWatchRound5.shiftExitTailC_of_parts
#print axioms PalPeg.CloseoutWatchRound5.breakExitTailC_of_parts
