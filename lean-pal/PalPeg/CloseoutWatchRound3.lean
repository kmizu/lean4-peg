import PalPeg.CloseoutWatchRound2
import PalPeg.CloseoutReadyStage
import PalPeg.GalilTrailAssembly

/-!
# Splitting the watch round's three NAMED contracts

`PalPeg.CloseoutWatchRound2.foundExit_compare_final` takes exactly three NAMED
inputs beyond the entry data: `MatchTickC` (head alignment at a matched
comparison), `LandingReadyC` (the shape of a watch landing) and
`TerminalTailsC'` (the terminal record is one of the two tails).  This file
replaces each of them by strictly smaller pieces and re-derives the entry point.

## What is proved here (unconditionally, no `sorry`)

1. `zero_of_canonical_value` — a canonical counter of value `0` really reads
   `zero = true`.  This is the bridge from the arithmetic ledgers
   (`GalilChainCoupling.SumRel`, `GalilTrailAssembly.LagLe`) to the boolean
   guard the watch tick tests.
2. `canRight_of_chainReady_zero` — at zero lag, `GalilTickFun.ChainReady` of a
   `.watch` already gives the verifier's right guard, because `Internal.idle`
   is an internal step there.  So `GalilScaffoldChainWatch.Good` reduces to the
   *period-tape prediction* alone.
3. `good_of_ready_predict` — `Good w` from `ChainReady` + zero lag + the
   prediction.
4. `lag_zero_of_ledgers` — **the `zero lag` half of `MatchTickC`, discharged**
   from the two ledgers: `LagLe` gives `Canonical w.lag` and `0 ≤ value w.lag`,
   `SumRel` gives `distance + lag = radius`, so `radius ≤ distance` forces
   `value w.lag = 0` and hence `zero w.lag = true`.
5. `matchTickC_of_parts` — **`MatchTickC` discharged** down to three narrower
   NAMED facts: `WatchLedgerC` (the two ledgers plus `ChainReady`, per
   landing), `CaughtAtMatchC` (`radius ≤ distance` at a matched comparison —
   the `Trail` obligation) and `PredictC` (the period tape predicts the symbol
   the verifier reads — `GalilReplaySpan.mispredicted_beyond_candidate` inside
   the candidate radius).
6. `landingReadyC_of_parts` — **`LandingReadyC` discharged** down to
   `WatchLedgerC` (which carries `ChainReady`), `LandingCanRightC` and
   `DistanceNonnegC`.
7. `searchGet_watchSegE_const`, `readyPacedS_watchSegE_watch` — the
   `ReadyPacedS` transport for the *watch* phase, the counterpart of
   `CloseoutReadyStage.readyIface_watchSegE` (which needs an idle chain).  On
   a non-idle chain `searchEffect` is `vq = searchLens.get s`
   (`GalilScaffoldTopSearch`), so the search state — and with it every
   readiness predicate about it — is *constant* along the whole segment.  The
   only per-step input is `CompareKeepsWatchC`, the match step's chain shape;
   the background steps are closed by `CloseoutWatchRound2.watchClosed`.
8. `TerminalRunShiftC` / `TerminalRunBreakC`, `ExitSplitC`, `ShiftExitTailC`,
   `BreakExitTailC`, `terminalTailsC'_of_split` — **`TerminalTailsC'` split
   into three.**  `TerminalC`'s four exits fall into two families: fuel-spent
   or shift-guarded (shift tail) and head-exhausted or broken (break tail).
   The split itself is one NAMED (`ExitSplitC`), and each family then owes only
   its own tail.
9. `places_of_shift_exit` — on the shift family the fuel-zero exit really gives
   `4h ≤ distance` (`CloseoutWatchRun.places_of_fuel_zero` on the
   `DistanceNonnegC` floor), i.e. the place count `GalilWatchPhase` asks for.
10. `foundExit_compare_final3` — the re-derivation of
   `CloseoutWatchRound2.foundExit_compare_final` on the split contracts.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutWatchRound3

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.CloseoutContracts
open PalPeg.GalilRunSkeleton
open PalPeg.GalilInvPlus (SegReachedW)
open PalPeg.GalilTickFun (ChainReady)
open PalPeg.CloseoutWatchRun (LiveScanWatch roundFuel places_of_fuel_zero)
open PalPeg.CloseoutWatchPhase2 (ShiftTailC LandingRestartReach)
open PalPeg.CloseoutWatchPhase3 (NoShiftTailC0)
open PalPeg.CloseoutWatchRound (TerminalC BreakEndC)
open PalPeg.CloseoutWatchRound2 (MatchTickC LandingReadyC TrivPrep TerminalRunC
  FoundCompareCtxC TerminalC' TerminalTailsC' watchClosed)
open PalPeg.CloseoutReadyStage (ReadyPacedS)

/-! ## 1. Canonical counters and the `Good` predicate -/

/-- **Derived.**  A canonical counter of value `0` reads `zero = true`. -/
theorem zero_of_canonical_value {c : Counter} (hc : Canonical c) (hv : value c = 0) :
    zero c = true := by
  have hlen : (c.pos.length : ℤ) = (c.neg.length : ℤ) := by
    have : (c.pos.length : ℤ) - (c.neg.length : ℤ) = 0 := hv
    omega
  rcases hc with h | h
  · have hp : c.pos.length = 0 := by rw [h]; simp
    have hn : c.neg.length = 0 := by omega
    simp only [zero, Bool.and_eq_true, List.isEmpty_iff]
    exact ⟨List.eq_nil_of_length_eq_zero hp, List.eq_nil_of_length_eq_zero hn⟩
  · have hn : c.neg.length = 0 := by rw [h]; simp
    have hp : c.pos.length = 0 := by omega
    simp only [zero, Bool.and_eq_true, List.isEmpty_iff]
    exact ⟨List.eq_nil_of_length_eq_zero hp, List.eq_nil_of_length_eq_zero hn⟩

/-- **Derived.**  `ChainReady` of a `.watch` hands over the verifier's right
guard at zero lag: `Internal.idle` is an internal step of that state, and
`ChainReady` closes `canRight` over every internal step. -/
theorem canRight_of_chainReady_zero {w : GalilScaffoldChainWatch.State}
    (hrd : ChainReady (ChainVM.watch w)) (hz : zero w.lag = true) :
    GalilScaffoldChainVerifier.canRight w.machine.verifier := by
  obtain ⟨-, -, hcr⟩ := hrd
  exact hcr w (.idle w (positive_of_zero hz))

/-- **Derived.**  With the right guard for free, `Good` is the prediction. -/
theorem good_of_ready_predict {w : GalilScaffoldChainWatch.State}
    (hrd : ChainReady (ChainVM.watch w)) (hz : zero w.lag = true)
    (hpred : ∃ a, GalilScaffoldChainConsume.symbol w.machine.control.period.focus = some a ∧
      GalilScaffoldInputHead.read (GalilScaffoldChainVerifier.right w.machine.verifier)
        = some a) :
    GalilScaffoldChainWatch.Good w :=
  ⟨canRight_of_chainReady_zero hrd hz, hpred⟩

/-! ## 2. `MatchTickC`, split -/

/-- **NAMED (open).**  The per-landing ledger bundle: the chain is tickable in
the sense of `GalilTickFun.ChainReady`, its lag is canonical and nonnegative
and bounded by the right head (`GalilTrailAssembly.LagLe`), and the radius
ledger `distance + lag = radius` holds (`GalilChainCoupling.SumRel`). -/
def WatchLedgerC : Prop :=
  ∀ (s : GalilVM) (w : GalilScaffoldChainWatch.State),
    s.chain = ChainVM.watch w →
      ChainReady s.chain ∧
      PalPeg.GalilTrailAssembly.LagLe s.chain (position (right s.right)) ∧
      PalPeg.GalilChainCoupling.SumRel s.chain (value s.radius) ∧
      w.machine.control.broken = false

/-- **NAMED (open) — the `Trail` obligation at a matched comparison.**  When
the outer comparison agrees, the chain verifier has caught up with the radius:
`radius ≤ distance`.  Together with `0 ≤ lag` and `distance + lag = radius`
this pins `lag = 0`. -/
def CaughtAtMatchC : Prop :=
  ∀ (s : GalilVM) (w : GalilScaffoldChainWatch.State),
    s.chain = ChainVM.watch w → canRight s.right →
    read (left s.left) = read (right s.right) →
      value s.radius ≤ value w.machine.control.distance

/-- **NAMED (open) — the prediction.**  At a matched comparison the period tape
under the chain's focus predicts exactly the symbol the chain verifier is about
to read.  Inside the candidate's radius this is
`GalilReplaySpan.mispredicted_beyond_candidate` read contrapositively (a
mispredicted position lies *beyond* the candidate). -/
def PredictC : Prop :=
  ∀ (s : GalilVM) (w : GalilScaffoldChainWatch.State),
    s.chain = ChainVM.watch w → canRight s.right →
    read (left s.left) = read (right s.right) →
      ∃ a, GalilScaffoldChainConsume.symbol w.machine.control.period.focus = some a ∧
        GalilScaffoldInputHead.read (GalilScaffoldChainVerifier.right w.machine.verifier)
          = some a

/-- **Derived — the `zero lag` half.**  Pure arithmetic on the two ledgers. -/
theorem lag_zero_of_ledgers {s : GalilVM} {w : GalilScaffoldChainWatch.State}
    (hw : s.chain = ChainVM.watch w)
    (hlag : PalPeg.GalilTrailAssembly.LagLe s.chain (position (right s.right)))
    (hsum : PalPeg.GalilChainCoupling.SumRel s.chain (value s.radius))
    (hbr : w.machine.control.broken = false)
    (hcaught : value s.radius ≤ value w.machine.control.distance) :
    zero w.lag = true := by
  have hlo : PalPeg.GalilTrailAssembly.lagOf s.chain = some (w.machine.verifier, w.lag) := by
    rw [hw]; rfl
  obtain ⟨hcan, hnn, -⟩ := PalPeg.GalilTrailAssembly.lagLe_get hlag hlo
  have hsum' : value w.machine.control.distance + value w.lag = value s.radius := by
    have : PalPeg.GalilChainCoupling.SumRel (ChainVM.watch w) (value s.radius) := by
      rw [← hw]; exact hsum
    exact this hbr
  exact zero_of_canonical_value hcan (by omega)

/-- **`MatchTickC` discharged** on the three narrower contracts. -/
theorem matchTickC_of_parts (hled : WatchLedgerC) (hcaught : CaughtAtMatchC)
    (hpred : PredictC) : MatchTickC := by
  intro s1 w1 hw1 hav hmm
  obtain ⟨hrd, hlag, hsum, hbr⟩ := hled s1 w1 hw1
  have hz : zero w1.lag = true :=
    lag_zero_of_ledgers hw1 hlag hsum hbr (hcaught s1 w1 hw1 hav hmm)
  have hrd' : ChainReady (ChainVM.watch w1) := by rw [← hw1]; exact hrd
  exact ⟨hz, good_of_ready_predict hrd' hz (hpred s1 w1 hw1 hav hmm)⟩

/-! ## 3. `LandingReadyC`, split -/

/-- **NAMED (open).**  Every live watch landing still has a right symbol.  This
is the scan loop's own guard: the watch phase is entered from a comparison and
left by the `¬ canRight` exit of `TerminalC`. -/
def LandingCanRightC : Prop :=
  ∀ (c : Control) (s : GalilVM), LiveScanWatch c s → canRight s.right

/-- **NAMED (open).**  The catch-up `distance` never goes negative.  It starts
at `0` on `watchStart` and only ever rises (`GalilScaffoldChainWatch.caught`,
`immediate`), so this is a run invariant, not a tick fact. -/
def DistanceNonnegC : Prop :=
  ∀ (s : GalilVM) (w : GalilScaffoldChainWatch.State),
    s.chain = ChainVM.watch w → 0 ≤ value w.machine.control.distance

/-- **`LandingReadyC` discharged** on `WatchLedgerC` + two narrower facts. -/
theorem landingReadyC_of_parts (hled : WatchLedgerC) (hav : LandingCanRightC)
    (hnn : DistanceNonnegC) :
    ∀ (c : Control) (s : GalilVM), LiveScanWatch c s → LandingReadyC s := by
  intro c s hL
  obtain ⟨hm, hr, hclk, w, hw⟩ := hL
  obtain ⟨hrd, -, -, -⟩ := hled s w hw
  exact ⟨hav c s ⟨hm, hr, hclk, w, hw⟩, hrd, fun w' hw' => hnn s w' hw'⟩

/-! ## 4. `ReadyPacedS` along the watch phase -/

/-- **Derived.**  An enabled tick of a watching chain lands either on a watch
again or on a `broken` (the `ChainMatched.breaks` side); `watchStep` is still
the only `ChainStep` out of a `.watch`. -/
theorem watchTick_true_shape {w : GalilScaffoldChainWatch.State} {z : ChainVM}
    (h : ChainTick true (ChainVM.watch w) z) :
    (∃ w' : GalilScaffoldChainWatch.State, z = ChainVM.watch w') ∨
      (∃ w' : GalilScaffoldChainWatch.State, z = ChainVM.broken w') := by
  obtain ⟨y, hstep, hm⟩ := h
  have hm' : ChainMatched y z := hm
  cases hstep with
  | watchStep w w' hi =>
      cases hm' with
      | watch a b ho => exact Or.inl ⟨_, rfl⟩
      | breaks a b hb => exact Or.inr ⟨_, rfl⟩

/-- **NAMED (open) — the one per-step input of §4.**  A *matched* comparison of
a watching chain does not break it.  `ChainMatched.breaks` needs a `BreakStep`,
which the watch's own `Outer` rules out at the matched symbol; inside
`CloseoutWatchRound2.roundStepC_of_align` this is `watchTick_immediate`, and
here it has to hold for an arbitrary segment step. -/
def NoBreakAtMatchC (P : Shared) (q : ℕ) (first : Fin 9) : Prop :=
  ∀ (s : GalilVM) (vs : ScanVM) (w : GalilScaffoldChainWatch.State),
    s.chain = ChainVM.watch w →
    (galilFrame P q first).compare s (scanLens.set s vs) →
    (galilFrame P q first).matched (scanLens.set s vs) →
      ∀ w' : GalilScaffoldChainWatch.State, vs.chain ≠ ChainVM.broken w'

/-- The comparison step of a watch segment lands on a watching chain. -/
def CompareKeepsWatchC (P : Shared) (q : ℕ) (first : Fin 9) : Prop :=
  ∀ (s : GalilVM) (vs : ScanVM) (vq : SearchVM) (w : GalilScaffoldChainWatch.State),
    s.chain = ChainVM.watch w →
    (galilFrame P q first).compare s (scanLens.set s vs) →
    (galilFrame P q first).matched (scanLens.set s vs) →
      ∃ w' : GalilScaffoldChainWatch.State,
        (afterCompare s vs vq).chain = ChainVM.watch w'

/-- **Derived.**  `CompareKeepsWatchC` from the break exclusion alone: the
matched comparison's chain effect is a `ChainTick true`
(`GalilScaffoldTopMatchedSeq.compare_parts` on the read equality supplied by
`matched_parts`), and `afterCompare` installs exactly `vs.chain`. -/
theorem compareKeepsWatch_of_noBreak (P : Shared) (q : ℕ) (first : Fin 9)
    (hnb : NoBreakAtMatchC P q first) : CompareKeepsWatchC P q first := by
  intro s vs vq w hw hcmp hmt
  have hmatch : read (left s.left) = read (right s.right) := by
    obtain ⟨⟨hl0, hr0, -⟩, -⟩ := hcmp
    rw [scanLens.get_set] at hl0 hr0
    have hp := matched_parts P q first hmt
    rw [hl0, hr0] at hp; exact hp
  obtain ⟨-, -, ht⟩ := compare_parts P q first hcmp hmatch
  have ht' : ChainTick true (ChainVM.watch w) vs.chain := by rw [← hw]; exact ht
  rcases watchTick_true_shape ht' with ⟨w', hv⟩ | ⟨w', hv⟩
  · exact ⟨w', by rw [afterCompare_chain]; exact hv⟩
  · exact absurd hv (hnb s vs w hw hcmp hmt w')

/-- **Derived — the search state is constant along a watch segment.**  On a
non-idle chain `searchEffect P b s vq` is `vq = searchLens.get s`, so neither
the background ticks nor the comparisons move the DP. -/
theorem searchGet_watchSegE_const (P : Shared) (q : ℕ) (first : Fin 9)
    (hkeep : CompareKeepsWatchC P q first)
    {es : List Bool} {c c' : Control} {s t : GalilVM}
    (h : WatchSegE P q first 2048 es c s c' t)
    (hw : ∃ w : GalilScaffoldChainWatch.State, s.chain = ChainVM.watch w) :
    searchLens.get t = searchLens.get s ∧
      ∃ w' : GalilScaffoldChainWatch.State, t.chain = ChainVM.watch w' := by
  induction h with
  | stop c s => exact ⟨rfl, hw⟩
  | wait c s s' hm hr hn hb rest ih =>
      obtain ⟨w, hwe⟩ := hw
      have hne : s.chain ≠ ChainVM.idle := by rw [hwe]; intro h0; cases h0
      have htick : ChainTick false (ChainVM.watch w) s'.chain := by
        rw [← hwe]; exact backgroundS_chainTick P q first hb hne
      obtain ⟨w', hw'⟩ := watchClosed w s'.chain htick
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hse⟩ := backgroundS_fields P q first hb
      have hget : searchLens.get s' = searchLens.get s := by
        rcases hse with ⟨hi, -⟩ | ⟨-, he⟩
        · exact absurd hi hne
        · exact he
      obtain ⟨hg, hend⟩ := ih ⟨w', hw'⟩
      exact ⟨hg.trans hget, hend⟩
  | count c s s' hm hr ha hc hb rest ih =>
      obtain ⟨w, hwe⟩ := hw
      have hne : s.chain ≠ ChainVM.idle := by rw [hwe]; intro h0; cases h0
      have htick : ChainTick false (ChainVM.watch w) s'.chain := by
        rw [← hwe]; exact backgroundS_chainTick P q first hb hne
      obtain ⟨w', hw'⟩ := watchClosed w s'.chain htick
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hse⟩ := backgroundS_fields P q first hb
      have hget : searchLens.get s' = searchLens.get s := by
        rcases hse with ⟨hi, -⟩ | ⟨-, he⟩
        · exact absurd hi hne
        · exact he
      obtain ⟨hg, hend⟩ := ih ⟨w', hw'⟩
      exact ⟨hg.trans hget, hend⟩
  | «match» c s vs vq o hm hr ha hc hne hcmp hmt hq ho rest ih =>
      obtain ⟨w, hwe⟩ := hw
      obtain ⟨w', hw'⟩ := hkeep s vs vq w hwe hcmp hmt
      have hget : searchLens.get (afterCompare s vs vq) = searchLens.get s := by
        have hvq : vq = searchLens.get s := by
          rcases hq with ⟨hi, -⟩ | ⟨-, he⟩
          · exact absurd hi hne
          · exact he
        rw [hvq]; rfl
      obtain ⟨hg, hend⟩ := ih ⟨w', hw'⟩
      exact ⟨hg.trans hget, hend⟩
  | matchIdle c s vs vq o hm hr ha hc hidle hl hrr hvs hmt hq hnf ho rest ih =>
      obtain ⟨w, hwe⟩ := hw
      rw [hidle] at hwe; exact absurd hwe (by intro h0; cases h0)
  | countR c s s' hm hr hc hidle hb rest ih =>
      obtain ⟨w, hwe⟩ := hw
      rw [hidle] at hwe; exact absurd hwe (by intro h0; cases h0)
  | matchIdleR c s vs vq o hm hr hc ha hidle hl hrr hvs hmt hq hnf ho rest ih =>
      obtain ⟨w, hwe⟩ := hw
      rw [hidle] at hwe; exact absurd hwe (by intro h0; cases h0)

/-- **Derived — the watch counterpart of
`CloseoutReadyStage.readyIface_watchSegE`.**  That lemma needs the chain idle
and pays clock slack per tick; here the DP does not move at all, so the paced
closure transports with *no* change of budget. -/
theorem readyPacedS_watchSegE_watch (P : Shared) (q : ℕ) (first : Fin 9)
    (hkeep : CompareKeepsWatchC P q first)
    {es : List Bool} {c c' : Control} {s t : GalilVM}
    (h : WatchSegE P q first 2048 es c s c' t)
    (hw : ∃ w : GalilScaffoldChainWatch.State, s.chain = ChainVM.watch w)
    (n k : ℕ) (h0 : ReadyPacedS (searchLens.get s) n k) :
    ReadyPacedS (searchLens.get t) n k := by
  obtain ⟨hg, -⟩ := searchGet_watchSegE_const P q first hkeep h hw
  rw [hg]; exact h0

/-! ## 5. `TerminalTailsC'`, split into three -/

/-- The shift family of exits: the fuel is spent or the shift guard holds. -/
def TerminalRunShiftC (P : Shared) (q : ℕ) (first : Fin 9) (h : ℕ)
    (cP : Control) (sP : GalilVM) : Prop :=
  ∀ (es : List Bool) (c2 : Control) (s2 : GalilVM),
    WatchSegE P q first 2048 es cP sP c2 s2 → LiveScanWatch c2 s2 →
      ∃ (cT : Control) (sT : GalilVM),
        WatchSeg P q first 2048 c2 s2 cT sT ∧ LiveScanWatch cT sT ∧
          (roundFuel h sT = 0 ∨ shiftGuardVM sT)

/-- The break family of exits: the right head is exhausted or the round breaks. -/
def TerminalRunBreakC (P : Shared) (q : ℕ) (first : Fin 9) (h : ℕ)
    (cP : Control) (sP : GalilVM) : Prop :=
  ∀ (es : List Bool) (c2 : Control) (s2 : GalilVM),
    WatchSegE P q first 2048 es cP sP c2 s2 → LiveScanWatch c2 s2 →
      ∃ (cT : Control) (sT : GalilVM),
        WatchSeg P q first 2048 c2 s2 cT sT ∧ LiveScanWatch cT sT ∧
          (¬ canRight sT.right ∨ BreakEndC P q first cT sT)

/-- **NAMED (open) — the classifier.**  The watch phase takes one family of
exits *uniformly*, i.e. the per-segment disjunction of `TerminalC` can be
pulled out of the quantifier.  On the machine this is the shift guard's own
dichotomy: either the chain survives to `4h ≤ distance` (shift) or it breaks /
runs out of input first. -/
def ExitSplitC (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (h : ℕ) (cP : Control) (sP : GalilVM) : Prop :=
  TerminalRunC (PofC centre place entry raw) qq first h cP sP →
    TerminalRunShiftC (PofC centre place entry raw) qq first h cP sP ∨
      TerminalRunBreakC (PofC centre place entry raw) qq first h cP sP

/-- **NAMED (open) — the shift tail alone.** -/
def ShiftExitTailC (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m h : ℕ) (c0 : Control) (r : GalilVM)
    (cP : Control) (sP : GalilVM) : Prop :=
  FoundCompareCtxC centre place entry qq first raw c0 r cP sP →
    TerminalRunShiftC (PofC centre place entry raw) qq first h cP sP →
      ShiftTailC centre place entry qq first raw m c0 r cP sP

/-- **NAMED (open) — the break tail alone.** -/
def BreakExitTailC (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m h : ℕ) (c0 : Control) (r : GalilVM)
    (cP : Control) (sP : GalilVM) : Prop :=
  FoundCompareCtxC centre place entry qq first raw c0 r cP sP →
    TerminalRunBreakC (PofC centre place entry raw) qq first h cP sP →
      NoShiftTailC0 centre place entry qq first raw m c0 r cP sP

/-- **`TerminalTailsC'` discharged** on the classifier and the two tails. -/
theorem terminalTailsC'_of_split (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m h : ℕ) (c0 : Control) (r : GalilVM)
    (cP : Control) (sP : GalilVM)
    (hsplit : ExitSplitC centre place entry qq first raw h cP sP)
    (hshift : ShiftExitTailC centre place entry qq first raw m h c0 r cP sP)
    (hbreak : BreakExitTailC centre place entry qq first raw m h c0 r cP sP) :
    TerminalTailsC' centre place entry qq first raw m h c0 r cP sP := by
  intro hT
  obtain ⟨hctx, hrun⟩ := hT
  rcases hsplit hrun with hs | hb
  · exact Or.inl (hshift hctx hs)
  · exact Or.inr (hbreak hctx hb)

/-- **Derived.**  On the shift family the fuel-zero exit gives the place count
`4h ≤ distance` that `GalilWatchPhase` / `GalilLastLowerBreak` ask for. -/
theorem places_of_shift_exit (hnn : DistanceNonnegC) (h : ℕ) {sT : GalilVM}
    {w : GalilScaffoldChainWatch.State} (hw : sT.chain = ChainVM.watch w)
    (h0 : roundFuel h sT = 0) :
    4 * (h : ℤ) ≤ value w.machine.control.distance :=
  places_of_fuel_zero h hw (hnn sT w hw) h0

/-! ## 6. The composition, on the split contracts -/

open PalPeg.CloseoutPrepInputs2 (MismatchExitG)
open PalPeg.CloseoutPrepInputs3 (PrepInputsG3)

/-- **Derived — `CloseoutWatchRound2.foundExit_compare_final` re-derived.**
`MatchTickC`, `LandingReadyC` and `TerminalTailsC'` are all gone; what is left
is `WatchLedgerC`, `CaughtAtMatchC`, `PredictC`, `LandingCanRightC`,
`DistanceNonnegC`, `ExitSplitC`, `ShiftExitTailC`, `BreakExitTailC`, the chain
tickability, and the entry data. -/
theorem foundExit_compare_final3 (centreC : GalilVM → Fin 3)
    (placeC : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (m h : ℕ)
    (hP : Decodes (PofC centreC placeC entry w))
    (hex : ∀ s, (PofC centreC placeC entry w).replayExhausted s = zero s.replay)
    (hready : PalPeg.GalilReplayChainSeg.ChainTickable)
    (hled : WatchLedgerC) (hcaught : CaughtAtMatchC) (hpred : PredictC)
    (havail : LandingCanRightC) (hnn : DistanceNonnegC)
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
  PalPeg.CloseoutWatchRound2.foundExit_compare_final centreC placeC entry q first w m h
    hP hex hready (matchTickC_of_parts hled hcaught hpred)
    (landingReadyC_of_parts hled havail hnn) hE hsW hLR a ls rs qw gap hprep hmis hctx
    (terminalTailsC'_of_split centreC placeC entry q first w m h c r cP sP
      hsplit hshift hbreak)

end PalPeg.CloseoutWatchRound3

#print axioms PalPeg.CloseoutWatchRound3.zero_of_canonical_value
#print axioms PalPeg.CloseoutWatchRound3.canRight_of_chainReady_zero
#print axioms PalPeg.CloseoutWatchRound3.good_of_ready_predict
#print axioms PalPeg.CloseoutWatchRound3.lag_zero_of_ledgers
#print axioms PalPeg.CloseoutWatchRound3.matchTickC_of_parts
#print axioms PalPeg.CloseoutWatchRound3.landingReadyC_of_parts
#print axioms PalPeg.CloseoutWatchRound3.watchTick_true_shape
#print axioms PalPeg.CloseoutWatchRound3.compareKeepsWatch_of_noBreak
#print axioms PalPeg.CloseoutWatchRound3.searchGet_watchSegE_const
#print axioms PalPeg.CloseoutWatchRound3.readyPacedS_watchSegE_watch
#print axioms PalPeg.CloseoutWatchRound3.terminalTailsC'_of_split
#print axioms PalPeg.CloseoutWatchRound3.places_of_shift_exit
#print axioms PalPeg.CloseoutWatchRound3.foundExit_compare_final3
