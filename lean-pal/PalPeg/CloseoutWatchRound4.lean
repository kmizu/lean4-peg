import PalPeg.CloseoutWatchRound3
import PalPeg.GalilTrailOrder
import PalPeg.GalilScaffoldTopChainUnique

/-!
# Round 4: discharging the watch round's NAMED contracts

`PalPeg.CloseoutWatchRound3.foundExit_compare_final3` takes eight NAMED inputs.
This file cuts five of them down to strictly smaller pieces and re-derives the
entry point (`foundExit_compare_final4`).

## What is proved here (unconditionally, no `sorry`)

1. `LedgerInvS` / `ledgerInvS_tick` / `ledgerInvS_steps` — the **ledger bundle
   as a run invariant**.  `GalilChainCoupling.Coupled` and
   `GalilTrailAssembly.LagLe` are jointly closed under `Tick` and hence under
   `Steps`, the only per-step input being `GalilTrailAssembly.LagStep` at the
   source (NAMED `LagStepC`).
2. `watchLedger_at` / `watchLedgerC_of_reach` — **`WatchLedgerC` discharged**
   down to reachability (`LedgerReachC`): at a state carrying the invariant the
   four conjuncts of `WatchLedgerC` are exactly `Coupled.sum`, `LagLe` lifted
   along `GalilTrailOrder.pos_le_right` (legal right steps never lose a place),
   the supplied `ChainReady`, and the supplied unbrokenness.
3. `caughtAtMatchC_of_zeroLag` — **`CaughtAtMatchC` discharged** into the bare
   `Trail` obligation `ZeroLagAtMatchC` (`lag` reads zero at a matched
   comparison).  With `distance + lag = radius` the two are *equivalent*
   (`zeroLagAtMatchC_of_caught` is the converse, via `WatchLedgerC`), so this
   replaces an arithmetic contract by the trace invariant it really is.
4. `distanceNonnegC_of_lagLeRadius` — **`DistanceNonnegC` discharged** into
   `LagLeRadiusC` (`lag ≤ radius`), again by `distance = radius - lag`.
5. `predictC_of_noBreak` — **`PredictC` discharged** into `PeriodSymbolC` (the
   period focus carries a symbol at all) and `NoBreakC` (no `BreakStep` fires),
   which is the machine-level form of the contrapositive of
   `GalilReplaySpan.mispredicted_beyond_candidate`: a mispredicted place lies
   beyond the candidate, so inside it the prediction holds.
6. `internal_eq_of_zero`, `step_of_watch`, `watch_not_broken_of_good` — at zero
   lag the only internal watch step is `Internal.idle`, so a matched tick of a
   `Good` watch cannot break (`GalilScaffoldTopChainUnique.break_not_good`).
7. `noBreakAtMatchC_of_parts` — **`NoBreakAtMatchC` discharged** (hence
   `CompareKeepsWatchC`, hence `readyPacedS_watchSegE_watch`) from
   `WatchLedgerC` + `CaughtAtMatchC` + `PredictC` + `CompareCanRightC`.
8. `exitSplitC_of_noBreakExit` / `exitSplitC_of_noShiftExit` — `ExitSplitC`
   from either family being uniformly available.
9. `foundExit_compare_final4` — the re-derivation of
   `foundExit_compare_final3` on the split contracts.

The two tails `ShiftExitTailC` / `BreakExitTailC` of
`PalPeg.CloseoutWatchRound3` are **not** touched here; they stay NAMED with the
types given there (`CloseoutWatchPhase2.ShiftTailC` /
`CloseoutWatchPhase3.NoShiftTailC0` bundles, whose `Tick.scan_shift` and
`GalilNoShiftStage.fresh_break_ledger` routes are the next wave).

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutWatchRound4

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.CloseoutContracts
open PalPeg.GalilRunSkeleton
open PalPeg.GalilInvPlus (SegReachedW)
open PalPeg.GalilTickFun (ChainReady)
open PalPeg.CloseoutWatchRun (LiveScanWatch roundFuel)
open PalPeg.CloseoutWatchPhase2 (ShiftTailC LandingRestartReach)
open PalPeg.CloseoutWatchPhase3 (NoShiftTailC0)
open PalPeg.CloseoutWatchRound (TerminalC BreakEndC)
open PalPeg.CloseoutWatchRound2 (MatchTickC LandingReadyC TerminalRunC FoundCompareCtxC)
open PalPeg.CloseoutWatchRound3 (WatchLedgerC CaughtAtMatchC PredictC LandingCanRightC
  DistanceNonnegC NoBreakAtMatchC CompareKeepsWatchC ExitSplitC ShiftExitTailC BreakExitTailC
  TerminalRunShiftC TerminalRunBreakC)
open PalPeg.GalilChainCoupling (Coupled SumRel value_zero_of_zero)
open PalPeg.GalilTrailAssembly (LagLe LagStep lagOf lagLe_get lagLe_mono)

/-! ## 1. The ledger bundle as a run invariant -/

/-- The two arithmetic ledgers, bundled at one state. -/
def LedgerInvS (c : Control) (s : GalilVM) : Prop :=
  Coupled c s ∧ LagLe s.chain (position s.right)

/-- **NAMED (open) — the one per-step input.**  At every state carrying the
ledger bundle the scan side is in `LagStep` shape: the right head can move and
is sane, and a fresh `chain.start()` copies a centre head trailing `R` by the
radius.  This is `GalilTrailAssembly.LagStep`, i.e. `ScanInvariant.rightPos`
plus `GalilFrontMono.Sane`. -/
def LagStepC : Prop := ∀ (c : Control) (s : GalilVM), LedgerInvS c s → LagStep s

section Run
variable (onLetter leftFirst : GalilVM → Prop) (centre : GalilVM → Fin 3)
  (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9) (delay : ℕ)

/-- **Derived.**  The bundle survives one tick of `galilFrameS`. -/
theorem ledgerInvS_tick (hst : LagStepC) {c c' : Control} {s t : GalilVM}
    (hI : LedgerInvS c s)
    (h : GalilScaffoldTop.Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first)
      delay ⟨c, s⟩ ⟨c', t⟩) : LedgerInvS c' t :=
  ⟨PalPeg.GalilChainCoupling.coupled_tick onLetter leftFirst centre place entry q first delay
      hI.1 h,
   PalPeg.GalilTrailAssembly.lagLe_tick onLetter leftFirst centre place entry q first delay
      hI.2 (hst c s hI) h⟩

/-- **Derived.**  Hence along a whole run — the `Steps` counterpart of
`GalilChainCoupling.coupled_steps`. -/
theorem ledgerInvS_steps (hst : LagStepC) {n : ℕ} {x y : State GalilVM}
    (h : Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay n x y)
    (hI : LedgerInvS x.ctl x.vm) : LedgerInvS y.ctl y.vm := by
  induction h with
  | zero => exact hI
  | succ ht _ ih =>
      exact ih (ledgerInvS_tick onLetter leftFirst centre place entry q first delay hst hI ht)

end Run

/-- **Derived — the pointwise form of `WatchLedgerC`.**  `LagLe` is stated at
`position s.right`; `WatchLedgerC` asks for it at `position (right s.right)`,
and a legal right step never loses a place (`GalilTrailOrder.pos_le_right`). -/
theorem watchLedger_at (hst : LagStepC) {c : Control} {s : GalilVM}
    {w : GalilScaffoldChainWatch.State} (hI : LedgerInvS c s)
    (hrd : ChainReady s.chain) (hw : s.chain = ChainVM.watch w)
    (hbr : w.machine.control.broken = false) :
    ChainReady s.chain ∧ LagLe s.chain (position (right s.right)) ∧
      SumRel s.chain (value s.radius) ∧ w.machine.control.broken = false := by
  refine ⟨hrd, lagLe_mono hI.2 ?_, hI.1.sum, hbr⟩
  exact PalPeg.GalilTrailOrder.pos_le_right (hst c s hI).rightCan

/-- **NAMED (open) — reachability.**  Every watching state of the run carries
the ledger bundle, a tickable chain and an unbroken control.  This is what the
run-level invariants (`GalilChainCoupling.coupled_steps`, `ledgerInvS_steps`,
`GalilTickFun.ChainReady` transport) deliver; `WatchLedgerC` quantifies over all
states, so exactly this reachability datum is what it needs. -/
def LedgerReachC : Prop :=
  ∀ (s : GalilVM) (w : GalilScaffoldChainWatch.State), s.chain = ChainVM.watch w →
    ∃ c : Control, LedgerInvS c s ∧ ChainReady s.chain ∧ w.machine.control.broken = false

/-- **`WatchLedgerC` discharged** down to reachability. -/
theorem watchLedgerC_of_reach (hst : LagStepC) (hre : LedgerReachC) : WatchLedgerC := by
  intro s w hw
  obtain ⟨c, hI, hrd, hbr⟩ := hre s w hw
  exact watchLedger_at hst hI hrd hw hbr

/-! ## 2. `CaughtAtMatchC` is the `Trail` obligation -/

/-- **NAMED (open) — the bare `Trail` obligation.**  At a matched comparison the
chain verifier has caught up: the lag counter reads zero.  On the trace this is
`pos v + lag = pos R` together with the scan invariant; `GalilTrailAssembly`
provides the `≤` half unconditionally. -/
def ZeroLagAtMatchC : Prop :=
  ∀ (s : GalilVM) (w : GalilScaffoldChainWatch.State),
    s.chain = ChainVM.watch w → canRight s.right →
    read (left s.left) = read (right s.right) → zero w.lag = true

/-- **`CaughtAtMatchC` discharged**: `distance + lag = radius` turns zero lag
into `radius ≤ distance`. -/
theorem caughtAtMatchC_of_zeroLag (hled : WatchLedgerC) (hz : ZeroLagAtMatchC) :
    CaughtAtMatchC := by
  intro s w hw hav hmm
  obtain ⟨-, -, hsum, hbr⟩ := hled s w hw
  have hsum' : value w.machine.control.distance + value w.lag = value s.radius := by
    have h : SumRel (ChainVM.watch w) (value s.radius) := by rw [← hw]; exact hsum
    exact h hbr
  have h0 : value w.lag = 0 := value_zero_of_zero (hz s w hw hav hmm)
  omega

/-- **The converse**, so the two contracts are interchangeable: the arithmetic
form `radius ≤ distance` already forces the lag to read zero. -/
theorem zeroLagAtMatchC_of_caught (hled : WatchLedgerC) (hc : CaughtAtMatchC) :
    ZeroLagAtMatchC := by
  intro s w hw hav hmm
  obtain ⟨-, hlag, hsum, hbr⟩ := hled s w hw
  exact PalPeg.CloseoutWatchRound3.lag_zero_of_ledgers hw hlag hsum hbr (hc s w hw hav hmm)

/-! ## 3. `DistanceNonnegC` is `lag ≤ radius` -/

/-- **NAMED (open).**  The lag never exceeds the radius it was started from.
This is the `≤` direction of `GalilChainCoupling.SumRel` read as a bound, and on
the machine it follows from `LagLe` plus the scan invariant. -/
def LagLeRadiusC : Prop :=
  ∀ (s : GalilVM) (w : GalilScaffoldChainWatch.State),
    s.chain = ChainVM.watch w → value w.lag ≤ value s.radius

/-- **`DistanceNonnegC` discharged.** -/
theorem distanceNonnegC_of_lagLeRadius (hled : WatchLedgerC) (hlr : LagLeRadiusC) :
    DistanceNonnegC := by
  intro s w hw
  obtain ⟨-, -, hsum, hbr⟩ := hled s w hw
  have hsum' : value w.machine.control.distance + value w.lag = value s.radius := by
    have h : SumRel (ChainVM.watch w) (value s.radius) := by rw [← hw]; exact hsum
    exact h hbr
  have := hlr s w hw
  omega

/-! ## 4. `PredictC` is the absence of a `BreakStep` -/

/-- **NAMED (open).**  The period focus carries a symbol at all (it is not the
mismatch/end cell). -/
def PeriodSymbolC : Prop :=
  ∀ (s : GalilVM) (w : GalilScaffoldChainWatch.State),
    s.chain = ChainVM.watch w → canRight s.right →
    read (left s.left) = read (right s.right) →
      ∃ a, GalilScaffoldChainConsume.symbol w.machine.control.period.focus = some a

/-- **NAMED (open) — the machine form of
`GalilReplaySpan.mispredicted_beyond_candidate`, contrapositively.**  Inside the
candidate's radius no `BreakStep` fires: a mispredicted place lies beyond
`C + 4h` (`GalilCandidatePeriod.candidate_palAt`,
`GalilPeriodCentre`), and the watch phase runs strictly inside it. -/
def NoBreakC : Prop :=
  ∀ (s : GalilVM) (w : GalilScaffoldChainWatch.State),
    s.chain = ChainVM.watch w → canRight s.right →
    read (left s.left) = read (right s.right) →
      ∀ w' : GalilScaffoldChainWatch.State, ¬ BreakStep w w'

/-- **`PredictC` discharged.**  `BreakStep` is exactly `zero lag ∧ canRight ∧
∃ a, symbol = some a ∧ read ≠ some a`; with the first three in hand, its absence
*is* the prediction. -/
theorem predictC_of_noBreak (hled : WatchLedgerC) (hzl : ZeroLagAtMatchC)
    (hsym : PeriodSymbolC) (hnb : NoBreakC) : PredictC := by
  intro s w hw hav hmm
  obtain ⟨hrd, -, -, -⟩ := hled s w hw
  have hrd' : ChainReady (ChainVM.watch w) := by rw [← hw]; exact hrd
  have hz : zero w.lag = true := hzl s w hw hav hmm
  have hcr : canRight w.machine.verifier :=
    PalPeg.CloseoutWatchRound3.canRight_of_chainReady_zero hrd' hz
  obtain ⟨a, ha⟩ := hsym s w hw hav hmm
  refine ⟨a, ha, ?_⟩
  by_cases hre : read (GalilScaffoldChainVerifier.right w.machine.verifier) = some a
  · exact hre
  · exact absurd ⟨hz, hcr, a, ha, hre, rfl⟩
      (hnb s w hw hav hmm ⟨consume w.machine, w.lag, inc w.margin⟩)

/-! ## 5. `NoBreakAtMatchC` is derivable -/

/-- **Derived.**  At zero lag `Internal.take` is blocked, so the only internal
watch step is `Internal.idle` and the state does not move. -/
theorem internal_eq_of_zero {w m : GalilScaffoldChainWatch.State} (hz : zero w.lag = true)
    (hi : GalilScaffoldChainWatch.Internal w m) : m = w := by
  cases hi with
  | idle hp => rfl
  | take hp hg => rw [positive_of_zero hz] at hp; cases hp

/-- **Derived.**  `watchStep` is the only `ChainStep` out of a `.watch`. -/
theorem step_of_watch {w : GalilScaffoldChainWatch.State} {y : ChainVM}
    (h : ChainStep (ChainVM.watch w) y) :
    ∃ w' : GalilScaffoldChainWatch.State,
      GalilScaffoldChainWatch.Internal w w' ∧ y = ChainVM.watch w' := by
  cases h with
  | watchStep w1 w2 hi => exact ⟨w2, hi, rfl⟩

/-- **Derived.**  A matched tick of a `Good` watch at zero lag cannot break. -/
theorem watch_not_broken_of_good {w : GalilScaffoldChainWatch.State} {z : ChainVM}
    (hz : zero w.lag = true) (hg : GalilScaffoldChainWatch.Good w)
    (h : ChainTick true (ChainVM.watch w) z) :
    ∀ w' : GalilScaffoldChainWatch.State, z ≠ ChainVM.broken w' := by
  intro w' hzb
  obtain ⟨y, hstep, hm⟩ := h
  obtain ⟨w1, hi, rfl⟩ := step_of_watch hstep
  have hm' : ChainMatched (ChainVM.watch w1) z := hm
  rw [internal_eq_of_zero hz hi, hzb] at hm'
  cases hm' with
  | breaks => rename_i hb; exact break_not_good hb hg

/-- **NAMED (open).**  A comparison happens at an available right head — the
comparison form of `CloseoutWatchRound3.LandingCanRightC`. -/
def CompareCanRightC (P : Shared) (q : ℕ) (first : Fin 9) : Prop :=
  ∀ (s : GalilVM) (vs : ScanVM),
    (galilFrame P q first).compare s (scanLens.set s vs) → canRight s.right

/-- **`NoBreakAtMatchC` discharged** on the match-tick contracts. -/
theorem noBreakAtMatchC_of_parts (P : Shared) (q : ℕ) (first : Fin 9)
    (hled : WatchLedgerC) (hcaught : CaughtAtMatchC) (hpred : PredictC)
    (hcan : CompareCanRightC P q first) : NoBreakAtMatchC P q first := by
  intro s vs w hw hcmp hmt w' hvs
  have hmatch : read (left s.left) = read (right s.right) := by
    obtain ⟨⟨hl0, hr0, -⟩, -⟩ := hcmp
    rw [scanLens.get_set] at hl0 hr0
    have hp := matched_parts P q first hmt
    rw [hl0, hr0] at hp; exact hp
  have hav : canRight s.right := hcan s vs hcmp
  obtain ⟨hz, hg⟩ :=
    PalPeg.CloseoutWatchRound3.matchTickC_of_parts hled hcaught hpred s w hw hav hmatch
  obtain ⟨-, -, ht⟩ := compare_parts P q first hcmp hmatch
  have ht' : ChainTick true (ChainVM.watch w) vs.chain := by rw [← hw]; exact ht
  exact watch_not_broken_of_good hz hg ht' w' hvs

/-- **Derived.**  Hence the watch segment keeps watching, and the paced search
readiness transports (`CloseoutWatchRound3.readyPacedS_watchSegE_watch`). -/
theorem compareKeepsWatchC_of_parts (P : Shared) (q : ℕ) (first : Fin 9)
    (hled : WatchLedgerC) (hcaught : CaughtAtMatchC) (hpred : PredictC)
    (hcan : CompareCanRightC P q first) : CompareKeepsWatchC P q first :=
  PalPeg.CloseoutWatchRound3.compareKeepsWatch_of_noBreak P q first
    (noBreakAtMatchC_of_parts P q first hled hcaught hpred hcan)

/-! ## 6. `ExitSplitC` from either family -/

/-- **Derived.**  If the shift family is available outright, the split is `inl`. -/
theorem exitSplitC_of_noBreakExit (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (h : ℕ) (cP : Control) (sP : GalilVM)
    (hs : TerminalRunShiftC (PofC centre place entry raw) qq first h cP sP) :
    ExitSplitC centre place entry qq first raw h cP sP := fun _ => Or.inl hs

/-- **Derived.**  Dually for the break family. -/
theorem exitSplitC_of_noShiftExit (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (h : ℕ) (cP : Control) (sP : GalilVM)
    (hb : TerminalRunBreakC (PofC centre place entry raw) qq first h cP sP) :
    ExitSplitC centre place entry qq first raw h cP sP := fun _ => Or.inr hb

/-! ## 7. The composition -/

open PalPeg.CloseoutPrepInputs2 (MismatchExitG)
open PalPeg.CloseoutPrepInputs3 (PrepInputsG3)

/-- **Derived — `CloseoutWatchRound3.foundExit_compare_final3` re-derived.**
`WatchLedgerC`, `CaughtAtMatchC`, `PredictC` and `DistanceNonnegC` are gone;
what is left is the reachability datum `LedgerReachC` with its per-step input
`LagStepC`, the trace obligation `ZeroLagAtMatchC`, the arithmetic bounds
`LagLeRadiusC` / `PeriodSymbolC`, the no-break contract `NoBreakC`, the landing
guard `LandingCanRightC`, the classifier `ExitSplitC`, the two tails, and the
entry data. -/
theorem foundExit_compare_final4 (centreC : GalilVM → Fin 3)
    (placeC : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (m h : ℕ)
    (hP : Decodes (PofC centreC placeC entry w))
    (hex : ∀ s, (PofC centreC placeC entry w).replayExhausted s = zero s.replay)
    (hready : PalPeg.GalilReplayChainSeg.ChainTickable)
    (hst : LagStepC)
    (hre : LedgerReachC) (hzl : ZeroLagAtMatchC) (hlr : LagLeRadiusC)
    (hsym : PeriodSymbolC) (hnb : NoBreakC)
    (havail : LandingCanRightC)
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
  have hled : WatchLedgerC :=
    watchLedgerC_of_reach hst hre
  have hcaught : CaughtAtMatchC := caughtAtMatchC_of_zeroLag hled hzl
  have hpred : PredictC := predictC_of_noBreak hled hzl hsym hnb
  PalPeg.CloseoutWatchRound3.foundExit_compare_final3 centreC placeC entry q first w m h
    hP hex hready hled hcaught hpred havail
    (distanceNonnegC_of_lagLeRadius hled hlr)
    hE hsW hLR a ls rs qw gap hprep hmis hctx hsplit hshift hbreak

end PalPeg.CloseoutWatchRound4

#print axioms PalPeg.CloseoutWatchRound4.ledgerInvS_tick
#print axioms PalPeg.CloseoutWatchRound4.ledgerInvS_steps
#print axioms PalPeg.CloseoutWatchRound4.watchLedger_at
#print axioms PalPeg.CloseoutWatchRound4.watchLedgerC_of_reach
#print axioms PalPeg.CloseoutWatchRound4.caughtAtMatchC_of_zeroLag
#print axioms PalPeg.CloseoutWatchRound4.zeroLagAtMatchC_of_caught
#print axioms PalPeg.CloseoutWatchRound4.distanceNonnegC_of_lagLeRadius
#print axioms PalPeg.CloseoutWatchRound4.predictC_of_noBreak
#print axioms PalPeg.CloseoutWatchRound4.internal_eq_of_zero
#print axioms PalPeg.CloseoutWatchRound4.step_of_watch
#print axioms PalPeg.CloseoutWatchRound4.watch_not_broken_of_good
#print axioms PalPeg.CloseoutWatchRound4.noBreakAtMatchC_of_parts
#print axioms PalPeg.CloseoutWatchRound4.compareKeepsWatchC_of_parts
#print axioms PalPeg.CloseoutWatchRound4.exitSplitC_of_noBreakExit
#print axioms PalPeg.CloseoutWatchRound4.exitSplitC_of_noShiftExit
#print axioms PalPeg.CloseoutWatchRound4.foundExit_compare_final4
