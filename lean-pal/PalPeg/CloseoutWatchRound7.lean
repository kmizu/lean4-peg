import PalPeg.CloseoutWatchRound5

/-!
# Round 7: the six NAMED residues of `CloseoutWatchRound5`

Each of the six is either discharged from smaller NAMED pieces or reduced.

## What is proved here (unconditionally, no `sorry`)

1. `watchSegE_live_control` — **the control half of `PrepLandingLiveC` is
   unconditional.**  A `WatchSegE` out of `mode = .scan`, `replaying = false`,
   `1 ≤ clock` lands on the same shape: `wait` keeps the control, `count` only
   decrements a clock it knows is `> 1`, the matching constructors reset the
   clock to `delay` and clear `replaying`, and `countR` / `matchIdleR` — the
   only constructors that can set `replaying := true` — require
   `c.replaying = true` and so are unreachable.
2. `prepLandingLiveC_of_watch` — hence `PrepLandingLiveC` reduces to
   `PrepLandingWatchC`, the **chain** conjunct alone.
3. `foundDp_core` — the whole DP content of the found comparison (the `Result`,
   `pc = 346`, `pos 11`, the `Candidate`) from the stage entry data, by
   `GalilFoundStageInv.found_radius_bg`; `searchStep_false_of` replays the
   matched comparison's `true` arrival as the `false` one that lemma wants,
   without changing `dp` or the mode, and `watchSegE_center` identifies the
   landing's place with the stage entry's.
4. `foundDpShiftC_of_parts` / `foundDpBreakC_of_parts` — **`FoundDpShiftC` and
   `FoundDpBreakC` discharged** from `FoundStageEntryC`, `FoundIndexAgreeC` and
   (for the break) `FoundRadiusCanonC`.  The centre equation
   `position r.center = position sF.center` of `FoundDpBreakC` turns out to be
   unconditional — `watchSegE_center` gives the centres equal outright.
5. `breakTerminalC_of_roundStep` — **`BreakTerminalC` discharged** from a
   per-landing `CloseoutWatchRun.RoundStepC` at `BreakTermData`: the `WatchSeg`
   prefix is built by `watchRun_of_distance`, whose fuel is the catch-up
   `distance` (`4*h + 1` rounds).  The exit hypothesis is not needed.
6. `shiftRoundC_of_parts` — **`ShiftRoundC` cut at the mismatching landing**
   into `ShiftReachC` (reach it) and `ShiftRoundAtC` (`ShiftRoundData` there).

## Still open, NAMED with exact types

* `PrepLandingWatchC P q first cP sP` — `∀ es c2 s2, WatchSegE P q first 2048 es
  cP sP c2 s2 → ∃ w, s2.chain = ChainVM.watch w`.  Branch A of
  `CloseoutPrepInputs3.prep_of_prepInputsG3` gives this for *one* landing per
  event list; the universal form needs the landing determinism of `WatchSegE`,
  which does not exist in the tree.
* `FoundStageEntryC raw c0 r` — `∃ Rad last, Restarted raw r Rad last ∧
  c0.clock = 2048 ∧ StageEntry Rad last`; the datum
  `CloseoutPrepInputs.prepInputs_of_found` gets from `StageEntryC` +
  `replayStage_trans`, which the exits do not carry.
* `FoundIndexAgreeC … lower span h c0 r` — at the found comparison,
  `sF.chain = ChainVM.idle`, `(denote vq.dp.config).pos 11 = h`, and every
  `Result` window the DP satisfies has `k = lower` and `span' = span`.
  `GalilSearchResult.idle_segment_found_quantum` fixes `k = value last`,
  `span = 8 * max k 1` on the first-stage branch; `CloseoutPrepInputs3.LaterQuantumC`
  on the later-stage branch.
* `FoundRadiusCanonC … c0 r` — `Canonical sF.radius` at every landing.
  `Restarted` has it at `r`; the preservation along `WatchSegE` is not exported.
* `ShiftReachC … h`, `ShiftRoundAtC … m h lower` — the two halves of §4.
* `CloseoutWatchRound5.BreakLandingC` — **not reduced here.**  Branch A of
  `prep_of_prepInputsG3` lands with chain
  `ChainVM.watch ⟨⟨sP.center, ready cen ys b⟩, lag, margin⟩` and only
  `value lag = value sP.radius + es.count true`, whereas
  `GalilNoShiftStage.freshWatch` fixes `lag = inc sF.radius` and
  `margin = decFour^[ys.length+1] (inc sF.radius)` **syntactically**.  Closing it
  needs (a) `es.count true = 0` — the `2*h+2 < 2048` delay fit of
  `CloseoutPrepInputs2.NoCompareInPrepG` — and (b) the counter identification
  `Canonical → value-equal → equal` together with the margin ledger, neither of
  which is available at the branch-A interface.  The general (`hcont`) shape is
  `GalilNoShiftDischarge.foundRouteMC_noshift_d`'s.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutWatchRound7

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.CloseoutContracts
open PalPeg.GalilRunSkeleton
open PalPeg.CloseoutWatchRun (LiveScanWatch roundFuel watchSeg_append RoundStepC
  watchRun_of_distance)
open PalPeg.CloseoutWatchRound (BreakEndC)
open PalPeg.CloseoutWatchRound5 (PrepLandingLiveC BreakTerminalC)

/-! ## 1. The control half of `PrepLandingLiveC` is unconditional -/

/-- **NAMED (open) — the chain half of `PrepLandingLiveC`.**  Every landing of
the preparation segment carries a watching chain.  This is all that is left of
`PrepLandingLiveC`: the three control conjuncts are `watchSegE_live_control`.
The universal quantifier over landings is the reason this is not simply branch A
of `CloseoutPrepInputs3.prep_of_prepInputsG3`, which supplies one landing per
event list; closing it needs the landing determinism of `WatchSegE`, which is
not available. -/
def PrepLandingWatchC (P : Shared) (q : ℕ) (first : Fin 9) (cP : Control) (sP : GalilVM) : Prop :=
  ∀ (es : List Bool) (c2 : Control) (s2 : GalilVM),
    WatchSegE P q first 2048 es cP sP c2 s2 → ∃ w : GalilScaffoldChainWatch.State,
      s2.chain = ChainVM.watch w

/-- **Derived — `PrepLandingLiveC` from the chain half alone.** -/
theorem prepLandingLiveC_of_watch (P : Shared) (q : ℕ) (first : Fin 9) {cP : Control}
    {sP : GalilVM} (hm : cP.mode = .scan) (hr : cP.replaying = false) (hc : 1 <= cP.clock)
    (hw : PrepLandingWatchC P q first cP sP) : PrepLandingLiveC P q first cP sP := by
  intro es c2 s2 hseg
  obtain ⟨h1, h2, h3⟩ := watchSegE_live_control (by omega) hseg hm hr hc
  exact ⟨h1, h2, h3, hw es c2 s2 hseg⟩

#print axioms watchSegE_live_control
#print axioms prepLandingLiveC_of_watch

/-! ## 2. The found DP record: `FoundDpShiftC` / `FoundDpBreakC` -/

open PalPeg.GalilScaffoldChainInputSupply (Decodes Restarted StageEntry)
open PalPeg.GalilFoundStageInv (found_radius_bg searchStep_false_of)

/-- **Derived — the whole DP content of the found comparison, from the stage
entry data.**  `GalilFoundStageInv.found_radius_bg` is stated for a *background*
found tick (`searchEffect … false`); `searchStep_false_of` replays the matched
comparison's arrival as a `false` one without changing `dp` or the mode, so the
comparison tick is covered too.  The centre of the landing is the centre of the
stage entry (`watchSegE_center`), so the DP stream is the same place. -/
theorem foundDp_core (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (hP : Decodes (PofC centre place entry raw))
    (a : Fin 2) (ls rs qw : List (Fin 2)) (gap : Bool)
    {c0 : Control} {r : GalilVM} {Rad : ℕ} {last : Counter}
    (hR : Restarted raw r Rad last) (hcl : c0.clock = 2048) (hSt : StageEntry Rad last)
    {es0 : List Bool} {cF : Control} {sF : GalilVM}
    (hseg : WatchSegE (PofC centre place entry raw) qq first 2048 es0 c0 r cF sF)
    (hidle : sF.chain = ChainVM.idle)
    (hcen : sF.center = represent ⟨a :: ls, gap⟩ (rs.map some) qw)
    (vq : SearchVM) (hq : searchEffect (PofC centre place entry raw) true sF vq)
    (hfound : vq.search.mode = .found) :
    ∃ k h span : ℕ,
      GalilDpCorrect.Result ((GalilScaffoldPlace.stream ⟨a :: ls, gap⟩).take (span+1)) k 0
        (GalilScaffoldProgram.denote vq.dp.config) ∧
      (GalilScaffoldProgram.denote vq.dp.config).pc = 346 ∧
      (GalilScaffoldProgram.denote vq.dp.config).pos 11 = h ∧
      GalilDpCorrect.Candidate ((GalilScaffoldPlace.stream ⟨a :: ls, gap⟩).take (span+1)) k h := by
  have hcenr : sF.center = r.center :=
    watchSegE_center (PofC centre place entry raw) qq first 2048 hseg
  have hcen0 : r.center = represent ⟨a :: ls, gap⟩ (rs.map some) qw := by
    rw [← hcenr]; exact hcen
  have hstep : searchStep ((PofC centre place entry raw).place sF) true
      (searchLens.get sF) vq := by
    rcases hq with ⟨-, hstep⟩ | ⟨hne, -⟩
    · exact hstep
    · exact absurd hidle hne
  obtain ⟨vq', hstep', hdp', hmode'⟩ :=
    searchStep_false_of ((PofC centre place entry raw).place sF) true hstep
  have hq' : searchEffect (PofC centre place entry raw) false sF vq' := Or.inl ⟨hidle, hstep'⟩
  have hf' : vq'.search.mode = .found := by rw [hmode']; exact hfound
  obtain ⟨k, h, span, hres, hpc, hpos, hcand, -, -⟩ :=
    found_radius_bg (PofC centre place entry raw) qq first hP a ls rs qw gap hR hcen0 hcl hSt
      hseg hidle vq' hq' hf'
  rw [hdp'] at hres hpc hpos
  exact ⟨k, h, span, hres, hpc, hpos, hcand⟩

#print axioms foundDp_core

/-- **NAMED (open) — the stage entry behind the found comparison.**  The found
comparison's segment starts at a restart landing of a stage with a full clock.
This is the datum `CloseoutPrepInputs.prepInputs_of_found` obtains from
`StageEntryC` + `replayStage_trans`; the exits carry `(c0, r)` but not the
witness. -/
def FoundStageEntryC (raw : List (Fin 2)) (c0 : Control) (r : GalilVM) : Prop :=
  ∃ (Rad : ℕ) (last : Counter), Restarted raw r Rad last ∧ c0.clock = 2048 ∧ StageEntry Rad last

/-- **NAMED (open) — the index agreement.**  The `lower`/`span`/`h` the exit
carries are the ones the DP itself reports at the found comparison.  `foundDp_core`
produces the DP record at the DP's *own* least-candidate indices; this says the
exit's indices are those.  (`GalilSearchResult.idle_segment_found_quantum` fixes
them as `k = value last` and `span = 8 * max k 1` on the first-stage branch;
on the later-stage branch `CloseoutPrepInputs3.LaterQuantumC` does.)  The
conjunct `sF.chain = ChainVM.idle` is the search-tick side condition the exit
context has (`hidle`) but neither `FoundDpShiftC` nor `FoundDpBreakC` states. -/
def FoundIndexAgreeC (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (lower span h : ℕ) (c0 : Control) (r : GalilVM) : Prop :=
  ∀ (a : Fin 2) (ls rs qw : List (Fin 2)) (gap : Bool) (es0 : List Bool) (cF : Control)
    (sF : GalilVM) (vq : SearchVM),
    WatchSegE (PofC centre place entry raw) qq first 2048 es0 c0 r cF sF →
    sF.center = represent ⟨a :: ls, gap⟩ (rs.map some) qw →
    searchEffect (PofC centre place entry raw) true sF vq → vq.search.mode = .found →
      sF.chain = ChainVM.idle ∧
      (GalilScaffoldProgram.denote vq.dp.config).pos 11 = h ∧
      ∀ (k span' : ℕ),
        GalilDpCorrect.Result ((GalilScaffoldPlace.stream ⟨a :: ls, gap⟩).take (span'+1)) k 0
          (GalilScaffoldProgram.denote vq.dp.config) → k = lower ∧ span' = span

/-- **NAMED (open).**  The radius at the found comparison is canonical.
`Restarted` gives it at the stage entry `r`; the segment's increments preserve
it, but that is not exported. -/
def FoundRadiusCanonC (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (c0 : Control) (r : GalilVM) : Prop :=
  ∀ (es0 : List Bool) (cF : Control) (sF : GalilVM),
    WatchSegE (PofC centre place entry raw) qq first 2048 es0 c0 r cF sF → Canonical sF.radius

/-- **Derived — `CloseoutWatchRound5.FoundDpShiftC`.** -/
theorem foundDpShiftC_of_parts (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (hP : Decodes (PofC centre place entry raw))
    (lower span h : ℕ) {c0 : Control} {r : GalilVM}
    (hstage : FoundStageEntryC raw c0 r)
    (hidx : FoundIndexAgreeC centre place entry qq first raw lower span h c0 r) :
    PalPeg.CloseoutWatchRound5.FoundDpShiftC centre place entry qq first raw lower span c0 r := by
  intro a ls rs qw gap es0 cF sF vq hseg hcen hq hfound
  obtain ⟨Rad, last, hR, hcl, hSt⟩ := hstage
  obtain ⟨hidle, hpos, hagree⟩ := hidx a ls rs qw gap es0 cF sF vq hseg hcen hq hfound
  obtain ⟨k, h', span', hres, hpc, hpos', hcand⟩ :=
    foundDp_core centre place entry qq first raw hP a ls rs qw gap hR hcl hSt hseg hidle hcen
      vq hq hfound
  obtain ⟨hk, hs⟩ := hagree k span' hres
  subst hk; subst hs
  exact ⟨hres, hpc⟩

/-- **Derived — `CloseoutWatchRound5.FoundDpBreakC`.**  The centre equation is
unconditional: `watchSegE_center` already says the landing's centre *is* the
stage entry's. -/
theorem foundDpBreakC_of_parts (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (hP : Decodes (PofC centre place entry raw))
    (lower span h : ℕ) {c0 : Control} {r : GalilVM}
    (hstage : FoundStageEntryC raw c0 r)
    (hidx : FoundIndexAgreeC centre place entry qq first raw lower span h c0 r)
    (hrc : FoundRadiusCanonC centre place entry qq first raw c0 r) :
    PalPeg.CloseoutWatchRound5.FoundDpBreakC centre place entry qq first raw lower span h c0 r := by
  intro a ls rs qw gap es0 cF sF vq hseg hcen hq hfound
  obtain ⟨Rad, last, hR, hcl, hSt⟩ := hstage
  obtain ⟨hidle, hpos, hagree⟩ := hidx a ls rs qw gap es0 cF sF vq hseg hcen hq hfound
  obtain ⟨k, h', span', hres, hpc, hpos', hcand⟩ :=
    foundDp_core centre place entry qq first raw hP a ls rs qw gap hR hcl hSt hseg hidle hcen
      vq hq hfound
  obtain ⟨hk, hs⟩ := hagree k span' hres
  subst hk; subst hs
  have hh : h' = h := by rw [← hpos', hpos]
  subst hh
  refine ⟨hcand, ?_, hrc es0 cF sF hseg⟩
  rw [watchSegE_center (PofC centre place entry raw) qq first 2048 hseg]

#print axioms foundDpShiftC_of_parts
#print axioms foundDpBreakC_of_parts

/-! ## 3. `BreakTerminalC` from a per-round contract -/

/-- The terminal datum of the break family, **at the landing** (no `WatchSeg`
prefix): the clock-`1` matched comparison that breaks the chain, with the fuel
spent and the right head inside the span. -/
def BreakTermData (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m h : ℕ) (c3 : Control) (s3 : GalilVM) : Prop :=
  ∃ (w3 : GalilScaffoldChainWatch.State) (vs3 : ScanVM) (vq3 : SearchVM) (o3 : Bool)
    (w3' : GalilScaffoldChainWatch.State),
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

/-- **Derived — `CloseoutWatchRound5.BreakTerminalC` from one round.**  The
`WatchSeg` prefix of the terminal break is built by
`CloseoutWatchRun.watchRun_of_distance`: the catch-up `distance` gives the
`4*h + 1` bound on the number of rounds, so the only obligation left is the
**per-landing** step — either the landing already carries `BreakTermData`, or
one `WatchSeg` reaches the next live landing with a strictly smaller fuel.
Note that the exit hypothesis (`¬ canRight sT.right ∨ BreakEndC …`) is simply
discarded: the run does not need it. -/
theorem breakTerminalC_of_roundStep (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m h : ℕ)
    (hstep : ∀ (c : Control) (s : GalilVM), LiveScanWatch c s →
      RoundStepC (PofC centre place entry raw) qq first (roundFuel h)
        (BreakTermData centre place entry qq first raw m h) c s) :
    BreakTerminalC centre place entry qq first raw m h := by
  intro cT sT hL _
  obtain ⟨c3, s3, hseg, -, w3, vs3, vq3, o3, w3', hm3, hr3, hc3, hs3, hav3, hcmp3, hmt3,
    hq3, ho3, hbroken, hz3, hfuel, hbound⟩ :=
    watchRun_of_distance (PofC centre place entry raw) qq first h
      (BreakTermData centre place entry qq first raw m h) hstep cT sT hL
  exact ⟨c3, s3, w3, vs3, vq3, o3, w3', hseg, hm3, hr3, hc3, hs3, hav3, hcmp3, hmt3, hq3,
    ho3, hbroken, hz3, hfuel, hbound⟩

#print axioms breakTerminalC_of_roundStep

/-! ## 4. `ShiftRoundC` cut at the clock-`1` landing -/

/-- The shift round **at the mismatching landing** `(c1, s1)`: everything
`CloseoutWatchRound5.ShiftRoundC` asserts except its leading `WatchSeg`.  By
`CloseoutWatchRound5.shiftTick_of_roundData` the mismatch/guard/`beginShift`
block is a legal `GalilScaffoldTop.Tick.scan_shift`, so this predicate only
records *which* round mismatches. -/
def ShiftRoundData (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m h lower : ℕ) (sF : GalilVM) (vq : SearchVM)
    (c1 : Control) (s1 : GalilVM) : Prop :=
  ∃ (w : GalilScaffoldChainWatch.State)
      (vs : ScanVM) (vq' : SearchVM) (s2' : GalilVM) (t' : ShiftState)
      (v : GalilScaffoldChainWatch.State) (cycle : Counter) (o : Bool)
      (org : ReadOrigin raw) (mm : ℕ) (c' : Control) (s' : GalilVM)
      (n : ℕ) (c3 : Control) (s3 : GalilVM) (w3 : GalilScaffoldChainWatch.State)
      (vs3 : ScanVM) (vq3 : SearchVM) (o3 : Bool) (w3' : GalilScaffoldChainWatch.State),
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

/-- **NAMED (open) — the mismatching round is reached.**  From a live scan
landing where the fuel is spent or the guard already holds, a `WatchSeg` reaches
the landing that actually mismatches. -/
def ShiftReachC (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (h : ℕ) : Prop :=
  ∀ (cT : Control) (sT : GalilVM), LiveScanWatch cT sT →
    (roundFuel h sT = 0 ∨ shiftGuardVM sT) →
      ∃ (c1 : Control) (s1 : GalilVM),
        WatchSeg (PofC centre place entry raw) qq first 2048 cT sT c1 s1 ∧
        LiveScanWatch c1 s1 ∧ (roundFuel h s1 = 0 ∨ shiftGuardVM s1)

/-- **NAMED (open) — the round itself.**  At such a landing the shift round runs
to the terminal break. -/
def ShiftRoundAtC (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m h lower : ℕ) : Prop :=
  ∀ (sF : GalilVM) (vq : SearchVM) (c1 : Control) (s1 : GalilVM),
    LiveScanWatch c1 s1 → (roundFuel h s1 = 0 ∨ shiftGuardVM s1) →
      ShiftRoundData centre place entry qq first raw m h lower sF vq c1 s1

/-- **Derived — `CloseoutWatchRound5.ShiftRoundC` from the two halves.** -/
theorem shiftRoundC_of_parts (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m h lower : ℕ)
    (hreach : ShiftReachC centre place entry qq first raw h)
    (hat : ShiftRoundAtC centre place entry qq first raw m h lower) :
    PalPeg.CloseoutWatchRound5.ShiftRoundC centre place entry qq first raw m h lower := by
  intro sF vq cT sT hL hexit
  obtain ⟨c1, s1, hseg, hL1, hexit1⟩ := hreach cT sT hL hexit
  obtain ⟨w, vs, vq', s2', t', v, cycle, o, org, mm, c', s', n, c3, s3, w3, vs3, vq3, o3, w3',
    hm1, hr1, hc1, hs1, hz, hav, hcmp, hmis, hq', hg, hb, hs2', hi2, hchain, ho, hint, he,
    hoc, ha, hpos11, hlow, hrounds, hseg3, hm3, hr3, hc3, hs3, hav3, hcmp3, hmt3, hq3, ho3,
    hbroken, hmargin, hlast, hlag, hbound⟩ := hat sF vq c1 s1 hL1 hexit1
  exact ⟨c1, s1, w, vs, vq', s2', t', v, cycle, o, org, mm, c', s', n, c3, s3, w3, vs3, vq3,
    o3, w3', hseg, hm1, hr1, hc1, hs1, hz, hav, hcmp, hmis, hq', hg, hb, hs2', hi2, hchain,
    ho, hint, he, hoc, ha, hpos11, hlow, hrounds, hseg3, hm3, hr3, hc3, hs3, hav3, hcmp3,
    hmt3, hq3, ho3, hbroken, hmargin, hlast, hlag, hbound⟩

#print axioms shiftRoundC_of_parts

end PalPeg.CloseoutWatchRound7
