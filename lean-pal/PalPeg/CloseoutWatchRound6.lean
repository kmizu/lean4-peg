import PalPeg.CloseoutWatchRound4

/-!
# Round 6: discharging the NAMED contracts of `CloseoutWatchRound4`

`PalPeg.CloseoutWatchRound4.foundExit_compare_final4` takes eight watch-side
NAMED inputs.  Four of them are removed here, and two are replaced by more
primitive ones.

1. `LagLeRadiusC` is **not** an independent obligation: the radius ledger
   `distance + lag = radius` (carried by `WatchLedgerC`) turns it into
   `0 ≤ distance`, i.e. into `CloseoutWatchRound3.DistanceNonnegC`, which
   `final3` already needs.  Both directions are proved
   (`lagLeRadiusC_of_distanceNonneg`, `distanceNonnegC_of_lagLeRadius'`), so the
   two contracts are interchangeable and only the run invariant survives.
2. `PeriodSymbolC` and `NoBreakC` share a single cause: at a matched comparison
   the period tape's focus carries the symbol the verifier reads
   (`GalilCandidatePeriod.candidate_palAt`, and
   `GalilReplaySpan.mispredicted_beyond_candidate` contrapositively: a
   mispredicted place lies beyond `C + 4h`).  That one fact is `PeriodMatchC`,
   and it discharges both (`periodSymbolC_of_match`, `noBreakC_of_match`) —
   `BreakStep` is *defined* with `read ≠ some a`, so a correct prediction
   excludes it outright.
3. `CompareCanRightC` and `LandingCanRightC` are the right-head guard
   `canRight s.right`, which is exactly `GalilTrailAssembly.LagStep.rightCan`.
   Since `LedgerReachC` gives the ledger bundle at every watching state and
   `LagStepC` turns the bundle into `LagStep`, both are derivable
   (`watchCanRight`, `landingCanRightC_of_reach`, and the
   `CompareCanRightC`-free `noBreakAtMatchC_of_reach` /
   `compareKeepsWatchC_of_reach`, where the watch hypothesis *is* available at
   the use site — so the unrestricted `CompareCanRightC` is never needed).
4. `LagStepC` is split into its three components (`RightCanC`, `RightSaneC`,
   `StartLeC`), and the third is shown vacuous on watching states
   (`startLe_of_watch`): only the scan-side `ScanInvariant.rightPos` and
   `GalilFrontMono.Sane` remain.
5. `LedgerReachC` is reduced to `LedgerOriginC`: a watching state is reached by
   a `Steps` run from a state carrying the bundle.  `ledgerInvS_steps` then
   transports the bundle, so reachability is the only datum left.

**Still NAMED after this file** (exact types below):
`RightCanC`, `RightSaneC`, `StartLeC` (the `LagStepC` split), `LedgerOriginC`,
`ZeroLagAtMatchC` (the `Trail` obligation, unchanged),
`CloseoutWatchRound3.DistanceNonnegC`, `PeriodMatchC`, plus the entry data and
the `ExitSplitC` / tail contracts inherited from rounds 3–4.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutWatchRound6

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.CloseoutContracts
open PalPeg.GalilRunSkeleton
open PalPeg.GalilInvPlus (SegReachedW)
open PalPeg.GalilTickFun (ChainReady)
open PalPeg.CloseoutWatchPhase2 (LandingRestartReach)
open PalPeg.CloseoutWatchRound2 (FoundCompareCtxC)
open PalPeg.CloseoutWatchRound3 (WatchLedgerC CaughtAtMatchC PredictC LandingCanRightC
  DistanceNonnegC NoBreakAtMatchC CompareKeepsWatchC ExitSplitC ShiftExitTailC BreakExitTailC)
open PalPeg.CloseoutWatchRound4 (LedgerInvS LagStepC LedgerReachC ZeroLagAtMatchC LagLeRadiusC
  PeriodSymbolC NoBreakC watchLedgerC_of_reach caughtAtMatchC_of_zeroLag predictC_of_noBreak
  distanceNonnegC_of_lagLeRadius watch_not_broken_of_good ledgerInvS_steps)
open PalPeg.GalilChainCoupling (SumRel)
open PalPeg.GalilTrailAssembly (LagStep StartLe)

/-! ## 1. `LagLeRadiusC` is `DistanceNonnegC` -/

/-- **Derived.**  `distance + lag = radius` with `0 ≤ distance` gives
`lag ≤ radius`. -/
theorem lagLeRadiusC_of_distanceNonneg (hled : WatchLedgerC) (hnn : DistanceNonnegC) :
    LagLeRadiusC := by
  intro s w hw
  obtain ⟨-, -, hsum, hbr⟩ := hled s w hw
  have hsum' : value w.machine.control.distance + value w.lag = value s.radius := by
    have h : SumRel (ChainVM.watch w) (value s.radius) := by rw [← hw]; exact hsum
    exact h hbr
  have := hnn s w hw
  omega

/-- **Derived — the converse**, so the two are interchangeable. -/
theorem distanceNonnegC_of_lagLeRadius' (hled : WatchLedgerC) (hlr : LagLeRadiusC) :
    DistanceNonnegC :=
  distanceNonnegC_of_lagLeRadius hled hlr

/-! ## 2. One prediction fact for `PeriodSymbolC` and `NoBreakC` -/

/-- **NAMED (open).**  At a matched comparison the period tape's focus carries
exactly the symbol the chain verifier reads.  This is the machine form of the
candidate-period prediction (`GalilCandidatePeriod.candidate_palAt`, with
`GalilReplaySpan.mispredicted_beyond_candidate` contrapositively: for
`j ≤ C + 4h` the prediction agrees). -/
def PeriodMatchC : Prop :=
  ∀ (s : GalilVM) (w : GalilScaffoldChainWatch.State),
    s.chain = ChainVM.watch w → canRight s.right →
    read (left s.left) = read (right s.right) →
      ∃ a, GalilScaffoldChainConsume.symbol w.machine.control.period.focus = some a ∧
        read (GalilScaffoldChainVerifier.right w.machine.verifier) = some a

/-- **`PeriodSymbolC` discharged.** -/
theorem periodSymbolC_of_match (hpm : PeriodMatchC) : PeriodSymbolC := by
  intro s w hw hav hmm
  obtain ⟨a, ha, -⟩ := hpm s w hw hav hmm
  exact ⟨a, ha⟩

/-- **`NoBreakC` discharged.**  `BreakStep` demands `read ≠ some a` for the
period symbol `a`; a correct prediction contradicts that. -/
theorem noBreakC_of_match (hpm : PeriodMatchC) : NoBreakC := by
  intro s w hw hav hmm w' hbk
  obtain ⟨a, ha, hr⟩ := hpm s w hw hav hmm
  obtain ⟨-, -, b, hb, hne, -⟩ := hbk
  have hab : a = b := by
    rw [ha] at hb; exact Option.some.inj hb
  rw [← hab] at hne
  exact hne hr

/-- **Derived.**  Hence `PredictC` needs only the ledgers, the `Trail`
obligation and this one prediction. -/
theorem predictC_of_match (hled : WatchLedgerC) (hzl : ZeroLagAtMatchC)
    (hpm : PeriodMatchC) : PredictC :=
  predictC_of_noBreak hled hzl (periodSymbolC_of_match hpm) (noBreakC_of_match hpm)

/-! ## 3. The right-head guards are `LagStep.rightCan` -/

/-- **Derived.**  Every watching state has an available right head. -/
theorem watchCanRight (hst : LagStepC) (hre : LedgerReachC) (s : GalilVM)
    (w : GalilScaffoldChainWatch.State) (hw : s.chain = ChainVM.watch w) :
    canRight s.right := by
  obtain ⟨c, hI, -, -⟩ := hre s w hw
  exact (hst c s hI).rightCan

/-- **`LandingCanRightC` discharged.** -/
theorem landingCanRightC_of_reach (hst : LagStepC) (hre : LedgerReachC) :
    LandingCanRightC := by
  intro c s hL
  obtain ⟨-, -, -, w, hw⟩ := hL
  exact watchCanRight hst hre s w hw

/-- **`NoBreakAtMatchC` discharged without `CompareCanRightC`.**  The Round 4
proof asked for the right guard as a separate contract; at the use site the
watch hypothesis is present, so `watchCanRight` supplies it. -/
theorem noBreakAtMatchC_of_reach (P : Shared) (q : ℕ) (first : Fin 9)
    (hst : LagStepC) (hre : LedgerReachC) (hled : WatchLedgerC) (hcaught : CaughtAtMatchC)
    (hpred : PredictC) : NoBreakAtMatchC P q first := by
  intro s vs w hw hcmp hmt w' hvs
  have hmatch : read (left s.left) = read (right s.right) := by
    obtain ⟨⟨hl0, hr0, -⟩, -⟩ := hcmp
    rw [scanLens.get_set] at hl0 hr0
    have hp := matched_parts P q first hmt
    rw [hl0, hr0] at hp; exact hp
  have hav : canRight s.right := watchCanRight hst hre s w hw
  obtain ⟨hz, hg⟩ :=
    PalPeg.CloseoutWatchRound3.matchTickC_of_parts hled hcaught hpred s w hw hav hmatch
  obtain ⟨-, -, ht⟩ := compare_parts P q first hcmp hmatch
  have ht' : ChainTick true (ChainVM.watch w) vs.chain := by rw [← hw]; exact ht
  exact watch_not_broken_of_good hz hg ht' w' hvs

/-- **Derived.** -/
theorem compareKeepsWatchC_of_reach (P : Shared) (q : ℕ) (first : Fin 9)
    (hst : LagStepC) (hre : LedgerReachC) (hled : WatchLedgerC) (hcaught : CaughtAtMatchC)
    (hpred : PredictC) : CompareKeepsWatchC P q first :=
  PalPeg.CloseoutWatchRound3.compareKeepsWatch_of_noBreak P q first
    (noBreakAtMatchC_of_reach P q first hst hre hled hcaught hpred)

/-! ## 4. `LagStepC`, split into its three components -/

/-- **NAMED (open).**  The scan invariant's right guard
(`ScanInvariant.rightPos`). -/
def RightCanC : Prop := ∀ (c : Control) (s : GalilVM), LedgerInvS c s → canRight s.right

/-- **NAMED (open).**  The front-monotonicity shape of the right head
(`GalilFrontMono.Sane`). -/
def RightSaneC : Prop := ∀ (c : Control) (s : GalilVM), LedgerInvS c s →
  PalPeg.GalilFrontMono.Sane s.right

/-- **NAMED (open).**  A fresh `chain.start()` copies a centre head trailing `R`
by the radius.  Only states with an *idle* chain are concerned. -/
def StartLeC : Prop := ∀ (c : Control) (s : GalilVM), LedgerInvS c s →
  s.chain = ChainVM.idle → StartLe s.center s.radius (position s.right)

/-- **`LagStepC` split.** -/
theorem lagStepC_of_parts (hcan : RightCanC) (hsane : RightSaneC) (hstart : StartLeC) :
    LagStepC := fun c s hI => ⟨hcan c s hI, hsane c s hI, hstart c s hI⟩

/-- **Derived.**  On a watching state the third component is vacuous. -/
theorem startLe_of_watch (s : GalilVM) (w : GalilScaffoldChainWatch.State)
    (hw : s.chain = ChainVM.watch w) :
    s.chain = ChainVM.idle → StartLe s.center s.radius (position s.right) := by
  intro h
  rw [hw] at h
  exact absurd h (by simp)

/-! ## 5. `LedgerReachC` from reachability alone -/

section Origin
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9) (delay : ℕ) (w : List (Fin 2))

/-- **NAMED (open) — reachability.**  Every watching state of the run is reached
by a `Steps` run from a state that carries the ledger bundle, and locally has a
tickable, unbroken chain. -/
def LedgerOriginC : Prop :=
  ∀ (s : GalilVM) (ww : GalilScaffoldChainWatch.State), s.chain = ChainVM.watch ww →
    ∃ (c : Control) (n : ℕ) (x : State GalilVM),
      LedgerInvS x.ctl x.vm ∧
      Steps (galilFrameS (PofC centre place entry w) q first) delay n x ⟨c, s⟩ ∧
      ChainReady s.chain ∧ ww.machine.control.broken = false

/-- **`LedgerReachC` discharged** down to reachability: `ledgerInvS_steps`
transports the bundle along the run. -/
theorem ledgerReachC_of_origin (hst : LagStepC)
    (hor : LedgerOriginC centre place entry q first delay w) : LedgerReachC := by
  intro s ww hw
  obtain ⟨c, n, x, hI, hsteps, hrd, hbr⟩ := hor s ww hw
  refine ⟨c, ?_, hrd, hbr⟩
  exact ledgerInvS_steps (onLetterVM w) leftFirstVM centre place entry q first delay hst
    hsteps hI

end Origin

/-! ## 6. The composition -/

open PalPeg.CloseoutPrepInputs2 (MismatchExitG)
open PalPeg.CloseoutPrepInputs3 (PrepInputsG3)

/-- **Derived — `CloseoutWatchRound4.foundExit_compare_final4` re-derived.**
`LagLeRadiusC`, `PeriodSymbolC`, `NoBreakC` and `LandingCanRightC` are gone;
`LedgerReachC` became `LedgerOriginC` and `LagStepC` became its three
components.  What is left on the watch side is: the scan-side `RightCanC` /
`RightSaneC` / `StartLeC`, reachability `LedgerOriginC`, the trace obligation
`ZeroLagAtMatchC`, the run invariant `DistanceNonnegC`, the prediction
`PeriodMatchC`, the classifier `ExitSplitC`, the two tails and the entry
data. -/
theorem foundExit_compare_final6 (centreC : GalilVM → Fin 3)
    (placeC : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (m h : ℕ)
    (hP : Decodes (PofC centreC placeC entry w))
    (hex : ∀ s, (PofC centreC placeC entry w).replayExhausted s = zero s.replay)
    (hready : PalPeg.GalilReplayChainSeg.ChainTickable)
    (hcan : RightCanC) (hsane : RightSaneC) (hstart : StartLeC)
    (hor : LedgerOriginC centreC placeC entry q first 2048 w)
    (hzl : ZeroLagAtMatchC) (hnn : DistanceNonnegC) (hpm : PeriodMatchC)
    {c c' cP : Control} {r t sP : GalilVM}
    (hE : StageEntryC (PofC centreC placeC entry w) q first w c r)
    (hsW : SegReachedW centreC placeC entry q first w c r c' t)
    (hLR : LandingRestartReach (PofC centreC placeC entry w) q first w c r)
    (a : Fin 2) (ls rs qw : List (Fin 2)) (gap : Bool) {lower span : ℕ}
    (hprep : PrepInputsG3 (PofC centreC placeC entry w) q first ⟨a :: ls, gap⟩ lower span
      cP sP)
    (hmis : MismatchExitG (PofC centreC placeC entry w) q first w m c r cP sP)
    (hctx : FoundCompareCtxC centreC placeC entry q first w c r cP sP)
    (hsplit : ExitSplitC centreC placeC entry q first w h cP sP)
    (hshift : ShiftExitTailC centreC placeC entry q first w m h c r cP sP)
    (hbreak : BreakExitTailC centreC placeC entry q first w m h c r cP sP) :
    FoundExit (PofC centreC placeC entry w) q first w m c r :=
  have hst : LagStepC := lagStepC_of_parts hcan hsane hstart
  have hre : LedgerReachC :=
    ledgerReachC_of_origin centreC placeC entry q first 2048 w hst hor
  have hled : WatchLedgerC := watchLedgerC_of_reach hst hre
  PalPeg.CloseoutWatchRound4.foundExit_compare_final4 centreC placeC entry q first w m h
    hP hex hready hst hre hzl
    (lagLeRadiusC_of_distanceNonneg hled hnn)
    (periodSymbolC_of_match hpm) (noBreakC_of_match hpm)
    (landingCanRightC_of_reach hst hre)
    hE hsW hLR a ls rs qw gap hprep hmis hctx hsplit hshift hbreak

end PalPeg.CloseoutWatchRound6

#print axioms PalPeg.CloseoutWatchRound6.lagLeRadiusC_of_distanceNonneg
#print axioms PalPeg.CloseoutWatchRound6.distanceNonnegC_of_lagLeRadius'
#print axioms PalPeg.CloseoutWatchRound6.periodSymbolC_of_match
#print axioms PalPeg.CloseoutWatchRound6.noBreakC_of_match
#print axioms PalPeg.CloseoutWatchRound6.predictC_of_match
#print axioms PalPeg.CloseoutWatchRound6.watchCanRight
#print axioms PalPeg.CloseoutWatchRound6.landingCanRightC_of_reach
#print axioms PalPeg.CloseoutWatchRound6.noBreakAtMatchC_of_reach
#print axioms PalPeg.CloseoutWatchRound6.compareKeepsWatchC_of_reach
#print axioms PalPeg.CloseoutWatchRound6.lagStepC_of_parts
#print axioms PalPeg.CloseoutWatchRound6.startLe_of_watch
#print axioms PalPeg.CloseoutWatchRound6.ledgerReachC_of_origin
#print axioms PalPeg.CloseoutWatchRound6.foundExit_compare_final6
