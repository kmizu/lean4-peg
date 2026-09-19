import PalPeg.CloseoutWatchRound27

/-!
# Closeout watch round 30 — `ShiftRoundAtC'` with the post-compare guard, produced

Round 27 showed that `CloseoutWatchRound7.ShiftRoundAtC` (no producer anywhere)
cannot feed `CloseoutWatchRound25.MismatchShiftRouteC`, because its trigger
`shiftGuardVM s1` reads the landing while the recorded guard reads the
post-compare scan projection.  This file replaces the trigger by the
post-compare guard `∀ vq', shiftGuardVM (afterMismatch s1 vs vq')` at the
frame's compare `vs` (`ShiftRoundAtC'`), keeps the conclusion `ShiftRoundData`
verbatim, and **produces** it from the shift tick.

`ShiftRoundData` decomposes as follows at a live clock-`1` landing with the
frame's mismatching compare `vs` and the guard on `afterMismatch s1 vs vq'`:

| conjunct(s) | source |
|---|---|
| mode / replaying / clock / `s1.chain = .watch w` / `canRight` | the landing |
| compare / `¬ matched` | premises |
| `searchEffect … false s1 vq'` | `vq' := searchLens.get s1` (chain not idle) |
| `zero w.lag` / `P.shiftGuard` | the guard (its watch state is `vs.chain`'s, so **piece 1**) |
| `P.beginShift` / `beginShiftVM h w …` | `beginShiftVM'` with `periodLength w = h` (**piece 2**) |
| `CopyIdle s2'` | `CopyIdle s1` transported (**piece 3**) |
| `ChainShiftRun … h t' v cycle` | `shift_run_chain` of a `ShiftRun` of `h` units (**piece 4**) |
| `refresh (galilFrameS …) … o` | `GalilTickFun3.refresh_exists` |
| origin data (`org`, `Entry`, `Aligned`, dp `pos 11`, period lower bound) | **piece 5** |
| `Rounds … mm`, terminal `ScanSeg`, breaking match, three counters, head bound | **piece 6** |

The six pieces are NAMED below, one hypothesis each; nothing in the tree
produces them (Round 14 records the missing iteration for piece 6, Round 9's
`ShiftAtMismatchC` carries pieces 3–4 in another packaging).  Piece 1 is new
and deserves a remark: `ShiftRoundData` (like `Rounds.next`) binds **one** `w`
for `s1.chain = .watch w` and for `beginShiftVM h w (afterMismatch s1 vs vq')`,
whereas `ChainTick false (.watch w) (.watch w')` only gives some
`GalilScaffoldChainWatch.Internal w w'`; so the data itself asserts that the
disabled tick of the mismatching compare keeps the watch state.

Round 25's route is then re-derived from `ShiftRoundAtC'`, with one bridge:
`MismatchShiftRouteC` records `¬ MismatchGuardFails s1` (Round 23), while
`guard_of_mismatchShift` (Round 27) needs the tied `¬ MismatchGuardFailsC` and
a frame compare at `s1`; `MismatchClassifierTieC` names exactly that (Round 27
already explains why the untied classifier does not pin `vs.right`).

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

namespace PalPeg.CloseoutWatchRound30

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.CloseoutContracts
open PalPeg.GalilRunSkeleton PalPeg.GalilInvPlus PalPeg.GalilInvPlus2
open PalPeg.GalilFoundStage PalPeg.GalilTraceCost
open PalPeg.CloseoutWatchRun (LiveScanWatch roundFuel)
open PalPeg.CloseoutWatchPhase2 (LandingRestartReach)
open PalPeg.CloseoutWatchRound2 (FoundCompareCtxC)
open PalPeg.CloseoutWatchRound3 (DistanceNonnegC)
open PalPeg.CloseoutWatchRound7 (ShiftRoundAtC ShiftRoundData ShiftReachC PrepLandingWatchC)
open PalPeg.CloseoutWatchRound10 (FoundDpAtC)
open PalPeg.CloseoutWatchRound6 (RightCanC RightSaneC StartLeC LedgerOriginC PeriodMatchC)
open PalPeg.CloseoutWatchRound4 (ZeroLagAtMatchC)
open PalPeg.CloseoutPrepInputs2 (MismatchExitG)
open PalPeg.CloseoutPrepInputs3 (PrepInputsG3)
open PalPeg.CloseoutWatchRound17 (FallbackRouteW)
open PalPeg.CloseoutWatchRound23 (MismatchGuardFails)
open PalPeg.CloseoutWatchRound25 (MismatchShiftRouteC)
open PalPeg.CloseoutWatchRound27 (MismatchGuardFailsC guard_of_mismatchShift)

/-! ## 1. `ShiftRoundAtC'` -/

/-- `CloseoutWatchRound7.ShiftRoundAtC` with the trigger
`roundFuel h s1 = 0 ∨ shiftGuardVM s1` replaced by the post-compare guard at the
frame's mismatching compare `vs`.  (The fuel branch is dropped: it is the
`ShiftReachC` family's exit, never what the mismatch-shift route records, and no
tick fires from fuel alone.)  Conclusion: `ShiftRoundData`, verbatim. -/
def ShiftRoundAtC' (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m h lower : ℕ) : Prop :=
  ∀ (sF : GalilVM) (vq : SearchVM) (c1 : Control) (s1 : GalilVM) (vs : ScanVM),
    LiveScanWatch c1 s1 → c1.clock = 1 → canRight s1.right →
    (galilFrame (PofC centre place entry raw) qq first).compare s1 (scanLens.set s1 vs) →
    ¬ (galilFrame (PofC centre place entry raw) qq first).matched (scanLens.set s1 vs) →
    (∀ vq' : SearchVM, shiftGuardVM (afterMismatch s1 vs vq')) →
      ShiftRoundData centre place entry qq first raw m h lower sF vq c1 s1

/-! ## 2. The six pieces of `ShiftRoundData` that no tick supplies -/

/-- **NAMED (open) — piece 1.**  The disabled chain tick of the mismatching
compare keeps the watch state (`ShiftRoundData` binds one `w` on both sides). -/
def ShiftChainStableC (P : Shared) (q : ℕ) (first : Fin 9) : Prop :=
  ∀ (s1 : GalilVM) (vs : ScanVM) (w : GalilScaffoldChainWatch.State),
    s1.chain = ChainVM.watch w →
    (galilFrame P q first).compare s1 (scanLens.set s1 vs) →
    ¬ (galilFrame P q first).matched (scanLens.set s1 vs) →
    vs.chain = ChainVM.watch w

/-- **NAMED (open) — piece 2.**  The watching chain's period tape has
semiperiod `h` (`beginShiftVM'` enters with `periodLength w`). -/
def ShiftPeriodC (h : ℕ) : Prop :=
  ∀ (c1 : Control) (s1 : GalilVM) (w : GalilScaffoldChainWatch.State),
    LiveScanWatch c1 s1 → c1.clock = 1 → s1.chain = ChainVM.watch w → periodLength w = h

/-- **NAMED (open) — piece 3.**  The copy tape is idle at the landing. -/
def ShiftCopyIdleC : Prop :=
  ∀ (c1 : Control) (s1 : GalilVM), LiveScanWatch c1 s1 → c1.clock = 1 → CopyIdle s1

/-- **NAMED (open) — piece 4.**  The shift run of exactly `h` units from the
entry shift state exists (Round 9's `ShiftAtMismatchC` carries the same fact). -/
def ShiftRunC (h : ℕ) : Prop :=
  ∀ (c1 : Control) (s1 : GalilVM), LiveScanWatch c1 s1 → c1.clock = 1 →
    canRight s1.right →
    ∃ t' : ShiftState,
      ShiftRun ⟨s1.center, left s1.left, ofNat h, inc s1.radius, inc (inc s1.length)⟩ h t'

/-- **NAMED (open) — piece 5.**  The origin ledger at the shift landing. -/
def ShiftOriginC (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (h lower : ℕ) : Prop :=
  ∀ (sF : GalilVM) (vq : SearchVM) (c1 : Control) (s1 : GalilVM) (vs : ScanVM)
    (vq' : SearchVM) (w : GalilScaffoldChainWatch.State) (s2' : GalilVM)
    (t' : ShiftState) (v : GalilScaffoldChainWatch.State) (cycle : Counter),
    LiveScanWatch c1 s1 → c1.clock = 1 → s1.chain = ChainVM.watch w →
    beginShiftVM h w (afterMismatch s1 vs vq') s2' →
    ChainShiftRun ⟨s1.center, left s1.left, ofNat h, inc s1.radius, inc (inc s1.length)⟩
      (GalilScaffoldChainWatch.immediate w) reset h t' v cycle →
    ∃ org : ReadOrigin raw,
      org.interior.length + 1 = h ∧
      Entry raw org (toOnly (shiftLens.set s2' ⟨t', .watch v, cycle⟩) v) ∧
      org.center = position sF.center ∧
      PalPeg.GalilRadiusConsumed.Aligned org ∧
      (GalilScaffoldProgram.denote vq.dp.config).pos 11 = h ∧
      (∀ δ, 0 < δ → δ ≤ lower → ¬ HasPeriod (Span raw org.center org.radius) (2*δ))

/-- **NAMED (open) — piece 6.**  The post-shift rounds run to the terminal
breaking match with the three counters and the head bound (Round 14's missing
iteration of `rounds_construct_of_measure`). -/
def ShiftBreakRunC (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m h : ℕ) : Prop :=
  ∀ (c1 : Control) (s1 : GalilVM) (vs : ScanVM) (vq' : SearchVM)
    (w : GalilScaffoldChainWatch.State) (s2' : GalilVM) (t' : ShiftState)
    (v : GalilScaffoldChainWatch.State) (cycle : Counter) (o : Bool),
    LiveScanWatch c1 s1 → c1.clock = 1 → s1.chain = ChainVM.watch w →
    beginShiftVM h w (afterMismatch s1 vs vq') s2' →
    ChainShiftRun ⟨s1.center, left s1.left, ofNat h, inc s1.radius, inc (inc s1.length)⟩
      (GalilScaffoldChainWatch.immediate w) reset h t' v cycle →
    refresh (galilFrameS (PofC centre place entry raw) qq first)
      (shiftLens.set s2' ⟨t', .watch v, cycle⟩) c1.output o →
    ∃ (mm : ℕ) (c' : Control) (s' : GalilVM) (n : ℕ) (c3 : Control) (s3 : GalilVM)
      (w3 : GalilScaffoldChainWatch.State) (vs3 : ScanVM) (vq3 : SearchVM) (o3 : Bool)
      (w3' : GalilScaffoldChainWatch.State),
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

/-! ## 3. The producer -/

/-- **Derived — `ShiftRoundAtC'` from the shift tick and the six pieces.**
The tick block itself (search quantum, guard, `beginShiftVM'` entry with the
period read from the chain, `ChainShiftRun` from the `ShiftRun`, output refresh)
is constructed here. -/
theorem shiftRoundAtC'_of_tick (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m h lower : ℕ)
    (h1 : ShiftChainStableC (PofC centre place entry raw) qq first)
    (h2 : ShiftPeriodC h) (h3 : ShiftCopyIdleC) (h4 : ShiftRunC h)
    (h5 : ShiftOriginC centre place entry qq first raw h lower)
    (h6 : ShiftBreakRunC centre place entry qq first raw m h) :
    ShiftRoundAtC' centre place entry qq first raw m h lower := by
  intro sF vq c1 s1 vs hL hclk hav hcmp hmis hg
  obtain ⟨hm1, hr1, hc1, w, hw⟩ := hL
  have hL' : LiveScanWatch c1 s1 := ⟨hm1, hr1, hc1, w, hw⟩
  have hvs : vs.chain = ChainVM.watch w := h1 s1 vs w hw hcmp hmis
  -- the search quantum: the chain is not idle, so the search projection is kept
  have hq' : searchEffect (PofC centre place entry raw) false s1 (searchLens.get s1) :=
    Or.inr ⟨(by rw [hw]; intro h; cases h), rfl⟩
  -- the guard at that quantum, and its watch state is `w`
  have hgc : shiftGuardVM (afterMismatch s1 vs (searchLens.get s1)) := hg (searchLens.get s1)
  obtain ⟨w₂, hw₂, hlag₂, -, -, -, -⟩ := hgc
  have hw₂' : w₂ = w := by
    have h' : vs.chain = ChainVM.watch w₂ := hw₂
    rw [hvs] at h'
    exact (ChainVM.watch.inj h').symm
  have hlag : zero w.lag = true := hw₂' ▸ hlag₂
  -- the shift entry
  have hper : periodLength w = h := h2 c1 s1 w hL' hclk hw
  let s2' : GalilVM :=
    {afterMismatch s1 vs (searchLens.get s1) with
      remaining := ofNat h,
      length := inc (inc (afterMismatch s1 vs (searchLens.get s1)).length),
      chain := .watch (GalilScaffoldChainWatch.immediate w),
      cycle := reset, periodOnly := true}
  have hs2' : beginShiftVM h w (afterMismatch s1 vs (searchLens.get s1)) s2' := ⟨hvs, rfl⟩
  have hb : (PofC centre place entry raw).beginShift (afterMismatch s1 vs (searchLens.get s1)) s2' := by
    show beginShiftVM' _ _
    refine ⟨w, ?_⟩
    rw [hper]
    exact hs2'
  have hgP : (PofC centre place entry raw).shiftGuard (afterMismatch s1 vs (searchLens.get s1)) :=
    hg (searchLens.get s1)
  -- copy idle transported
  have hi2 : CopyIdle s2' := (copyIdle_iff s2').2 ((copyIdle_iff s1).1 (h3 c1 s1 hL' hclk))
  -- the shift run and its chain run
  obtain ⟨t', hrun⟩ := h4 c1 s1 hL' hclk hav
  obtain ⟨v, cycle, hchain⟩ := shift_run_chain hrun (GalilScaffoldChainWatch.immediate w) reset
  -- the output refresh
  obtain ⟨o, ho⟩ := PalPeg.GalilTickFun3.refresh_exists (PofC centre place entry raw) qq first
    (shiftLens.set s2' ⟨t', .watch v, cycle⟩) c1.output
  -- the origin ledger and the break run
  obtain ⟨org, hint, he, hoc, ha, hpos11, hlow⟩ :=
    h5 sF vq c1 s1 vs (searchLens.get s1) w s2' t' v cycle hL' hclk hw hs2' hchain
  obtain ⟨mm, c', s', n, c3, s3, w3, vs3, vq3, o3, w3', hrounds, hseg3, hm3, hr3, hc3, hs3,
    hav3, hcmp3, hmt3, hq3, ho3, hbroken, hmargin, hlast, hlag3, hbound⟩ :=
    h6 c1 s1 vs (searchLens.get s1) w s2' t' v cycle o hL' hclk hw hs2' hchain ho
  exact ⟨w, vs, searchLens.get s1, s2', t', v, cycle, o, org, mm, c', s', n, c3, s3, w3, vs3,
    vq3, o3, w3', hm1, hr1, hclk, hw, hlag, hav, hcmp, hmis, hq', hgP, hb, hs2', hi2, hchain,
    ho, hint, he, hoc, ha, hpos11, hlow, hrounds, hseg3, hm3, hr3, hc3, hs3, hav3, hcmp3, hmt3,
    hq3, ho3, hbroken, hmargin, hlast, hlag3, hbound⟩

/-! ## 4. Round 25's route from `ShiftRoundAtC'` -/

/-- **NAMED (open) — the classifier bridge.**  At the mismatch-shift landing
(`¬ MismatchGuardFails s1`, Round 23) the frame has a compare at `s1` and the
*tied* classifier fails (`¬ MismatchGuardFailsC`, Round 27).  Round 27 §4
explains why this is not derivable: the untied classifier leaves `vs.right`
free. -/
def MismatchClassifierTieC (P : Shared) (q : ℕ) (first : Fin 9) : Prop :=
  ∀ (c1 : Control) (s1 : GalilVM), LiveScanWatch c1 s1 → c1.clock = 1 → canRight s1.right →
    read (left s1.left) ≠ read (right s1.right) → ¬ MismatchGuardFails s1 →
      (∃ vs : ScanVM, (galilFrame P q first).compare s1 (scanLens.set s1 vs)) ∧
        ¬ MismatchGuardFailsC P q first s1

/-- An outer mismatch makes the frame's compare unmatched. -/
theorem not_matched_of_compare {P : Shared} {q : ℕ} {first : Fin 9} {s1 : GalilVM}
    {vs : ScanVM} (hcmp : (galilFrame P q first).compare s1 (scanLens.set s1 vs))
    (hne : read (left s1.left) ≠ read (right s1.right)) :
    ¬ (galilFrame P q first).matched (scanLens.set s1 vs) := by
  obtain ⟨⟨hl, hr, -⟩, -⟩ := hcmp
  rw [scanLens.get_set] at hl hr
  intro hmt
  apply hne
  have hmt' : read (scanLens.get (scanLens.set s1 vs)).left =
      read (scanLens.get (scanLens.set s1 vs)).right := hmt
  rw [scanLens.get_set] at hmt'
  rw [hl, hr] at hmt'
  exact hmt'

/-- **Derived — `MismatchShiftRouteC` from `ShiftRoundAtC'` and the bridge.** -/
theorem mismatchShiftRouteC'_of_shiftRoundAtC' (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m h lower : ℕ)
    (hat : ShiftRoundAtC' centre place entry qq first raw m h lower)
    (htie : MismatchClassifierTieC (PofC centre place entry raw) qq first) :
    MismatchShiftRouteC centre place entry qq first raw m h lower := by
  intro sF vq c1 s1 hlive hclk hav hne hnG
  obtain ⟨⟨vs, hcmp⟩, hnGC⟩ := htie c1 s1 hlive hclk hav hne hnG
  have hmis := not_matched_of_compare hcmp hne
  have hgt := guard_of_mismatchShift hnGC hcmp hne
  exact hat sF vq c1 s1 vs hlive hclk hav hcmp hmis (fun vq' => (hgt vq').1)

/-! ## 5. The consumer -/

/-- **Derived — `CloseoutWatchRound25.foundExit_compare_final12` with
`MismatchShiftRouteC` replaced by `ShiftRoundAtC'` + `MismatchClassifierTieC`.**
`ShiftRoundAtC` (families 1–3, via `shiftRoundC_of_parts`) stays: its
fuel-zero trigger is not covered by `ShiftRoundAtC'`. -/
theorem foundExit_compare_final13' (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (m h lower span : ℕ)
    (hP : Decodes (PofC centre place entry w))
    (hex : ∀ s, (PofC centre place entry w).replayExhausted s = zero s.replay)
    (hready : PalPeg.GalilReplayChainSeg.ChainTickable)
    (hcan : RightCanC) (hsane : RightSaneC) (hstart : StartLeC)
    (hor : LedgerOriginC centre place entry q first 2048 w)
    (hzl : ZeroLagAtMatchC) (hnn : DistanceNonnegC) (hpm : PeriodMatchC)
    {c c' cP : Control} {r t sP : GalilVM}
    (hE : StageEntryC (PofC centre place entry w) q first w c r)
    (hsW : SegReachedW centre place entry q first w c r c' t)
    (a : Fin 2) (ls rs qw : List (Fin 2)) (gap : Bool)
    (hprep : PrepInputsG3 (PofC centre place entry w) q first ⟨a :: ls, gap⟩ lower span cP sP)
    (hmis : MismatchExitG (PofC centre place entry w) q first w m c r cP sP)
    (hctx : FoundCompareCtxC centre place entry q first w c r cP sP)
    (hfb : FallbackRouteW (PofC centre place entry w) q first w m c r cP sP)
    (hLR : LandingRestartReach (PofC centre place entry w) q first w c r)
    (hstage : ReplayStage w (PofC centre place entry w) q first c r)
    (hmP : cP.mode = .scan) (hrP : cP.replaying = false) (hcP : 1 ≤ cP.clock)
    (hreachWatch : ∃ (es : List Bool) (c2 : Control) (s2 : GalilVM),
      WatchSegE (PofC centre place entry w) q first 2048 es cP sP c2 s2 ∧
        PalPeg.CloseoutWatchRun.LiveScanWatch c2 s2)
    (hat : FoundDpAtC centre place entry q first w lower span h c r)
    (hreach : ShiftReachC centre place entry q first w h)
    (hround : ShiftRoundAtC centre place entry q first w m h lower)
    (hround' : ShiftRoundAtC' centre place entry q first w m h lower)
    (htie : MismatchClassifierTieC (PofC centre place entry w) q first)
    (hland : ∀ sF : GalilVM,
      PalPeg.CloseoutWatchRound5.BreakLandingC centre place entry q first w h sF cP sP)
    (hstepBreak : ∀ (c0 : Control) (s0 : GalilVM), LiveScanWatch c0 s0 →
      PalPeg.CloseoutWatchRun.RoundStepC (PofC centre place entry w) q first (roundFuel h)
        (PalPeg.CloseoutWatchRound7.BreakTermData centre place entry q first w m h) c0 s0) :
    FoundExit (PofC centre place entry w) q first w m c r :=
  PalPeg.CloseoutWatchRound25.foundExit_compare_final12 centre place entry q first w m h lower
    span hP hex hready hcan hsane hstart hor hzl hnn hpm hE hsW a ls rs qw gap hprep hmis hctx
    hfb hLR hstage hmP hrP hcP hreachWatch hat hreach hround
    (mismatchShiftRouteC'_of_shiftRoundAtC' centre place entry q first w m h lower hround' htie)
    hland hstepBreak

end PalPeg.CloseoutWatchRound30

#print axioms PalPeg.CloseoutWatchRound30.shiftRoundAtC'_of_tick
#print axioms PalPeg.CloseoutWatchRound30.not_matched_of_compare
#print axioms PalPeg.CloseoutWatchRound30.mismatchShiftRouteC'_of_shiftRoundAtC'
#print axioms PalPeg.CloseoutWatchRound30.foundExit_compare_final13'
