import PalPeg.CloseoutWatchPhase3
import PalPeg.GalilCatchUpDistance

/-!
# The watch phase as a *run*: rounds by fuel induction

Every watch-phase statement in the closeout so far is **consumptive**: the
tails (`CloseoutWatchPhase2.ShiftTailC`, `CloseoutWatchPhase3.NoShiftTailC0`)
and the routes (`WatchRouteLPraw`) all quantify over a `WatchSegE` that the
caller is expected to supply, and then read off what happens at its terminal
comparison.  Nothing in the repository *builds* the sequence of watch rounds
that reaches such a terminal: `GalilSegmentConstruct.watchSegE_construct` and
`CloseoutReadyStage.watchSegE_constructS` build only the **chain-idle** prefix
(they stop as soon as the chain leaves `ChainVM.idle`), and
`GalilScaffoldTopRoundBreak.rounds_break` takes the rounds as a hypothesis
(`Rounds … m c s c' s'`).  This file supplies the missing constructive step.

## What is proved here (unconditionally)

1. `watchSeg_append` — `WatchSeg` is transitive.  Surprisingly absent: the
   repository has `watchSegE_trans` for the chain-idle segment but nothing for
   the general watch segment, which is why rounds could never be chained.
2. `watchRun_construct` — **the fuel induction.**  Given a per-round contract
   `RoundStepC` which, at every live scan landing, either declares the landing
   terminal or produces *one* `WatchSeg` round to a new live scan landing with
   a strictly smaller measure, a landing with measure `≤ n` reaches a terminal
   landing by a single `WatchSeg`.  The measure is the fuel; no well-founded
   recursion is needed because each round is one `WatchSeg`.
3. `roundFuel`, `watchRun_of_distance` — the concrete fuel: the chain's
   catch-up `distance` counts *up* to the shift guard's threshold `4*h`, so
   `(4*h+1) - distance` counts down.  `places_of_fuel_zero` says fuel zero is
   exactly the `4*h ≤ distance` that `GalilWatchPhase.phase_at_terminal_of_-`
   `distance` and `GalilLastLowerBreak.stageEntry_after_found_of_places` ask
   for, and `margin_of_fuel_zero` converts it to `0 ≤ margin` along a watch run
   out of `watchStart` (`GalilCatchUpDistance.places_iff_margin`).  So the
   number of rounds is bounded by `4*h+1`, which is the fuel bound the task
   statement names.
4. `watchRouteLPraw_of_terminal` — the wiring: either terminal tail gives the
   disjunctive raw route of `CloseoutWatchPhase3`.

## Still open, NAMED with exact types

* `RoundStepC P q first meas Term` at `Term := TerminalC` (below) — **the
  per-round step**.  Discharging it means, at a live scan landing `(c, s)`
  with `s.chain = ChainVM.watch w`:
  - the idle interval to the next comparison (clock `c.clock` down to `1`),
    which is `WatchSeg.count` repeated — this is the part
    `watchSegE_constructS` does for an *idle* chain and which here must run the
    chain's background `ChainTick false` instead (`GalilScaffoldChainCredits`
    paces it, `GalilReplaySpan.chain_runW` keeps it live);
  - the comparison itself: on a match, `WatchSeg.match` with the `Outer` tick
    advancing `distance` by one, hence `roundFuel` down by one; on a mismatch,
    `TerminalC` with the guard `shiftGuardVM (afterMismatch s vs vq)` decided
    — `true` gives the shift tail, `false` the break tail.
  None of this is a function of `(c, s)` alone: whether the outer symbols agree
  is input data, so `RoundStepC` is genuinely an obligation about the run and
  is left NAMED.  Its *shape*, however, is now fixed, and §2 shows that shape
  suffices.
* `TerminalC c s → ShiftTailC … ∨ NoShiftTailC0 …` — the terminal landing
  produced by §2 still has to be recognised as one of the two tails; the tails
  additionally record the *preparation* data (`es.count true = 0`, the DP
  candidate, the `freshWatch` shape) which the abstract run does not carry.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutWatchRun

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.CloseoutContracts
open PalPeg.GalilRunSkeleton
open PalPeg.CloseoutWatchPhase2 (ShiftTailC NoShiftTailC)
open PalPeg.CloseoutWatchPhase3 (NoShiftTailC0 WatchRouteLPraw noShiftTailC_of_0
  watchRouteLPraw_of_tails)

/-! ## 1. `WatchSeg` is transitive -/

/-- **Derived.**  Two consecutive watch segments compose.  (`watchSegE_trans`
is the chain-idle analogue; the general segment had none, which is exactly why
watch rounds could not be chained.) -/
theorem watchSeg_append {P : Shared} {q : ℕ} {first : Fin 9} {delay : ℕ}
    {c1 c2 c3 : Control} {s1 s2 s3 : GalilVM}
    (h1 : WatchSeg P q first delay c1 s1 c2 s2)
    (h2 : WatchSeg P q first delay c2 s2 c3 s3) :
    WatchSeg P q first delay c1 s1 c3 s3 := by
  induction h1 with
  | stop c s => exact h2
  | wait c s s' hm hr hn hb _ ih => exact .wait c s s' hm hr hn hb (ih h2)
  | count c s s' hm hr ha hc hb _ ih => exact .count c s s' hm hr ha hc hb (ih h2)
  | «match» c s vs vq o hm hr ha hc hne hcmp hmt hq ho _ ih =>
      exact .match c s vs vq o hm hr ha hc hne hcmp hmt hq ho (ih h2)

/-! ## 2. The fuel induction -/

/-- A *live scan landing*: scan mode, not replaying, positive clock, and a
watching chain.  This is the state shape the preparation lands in
(`CloseoutPrepInputs3.prep_of_prepInputsG3`, branch A) and the shape every
watch round must restore. -/
def LiveScanWatch (c : Control) (s : GalilVM) : Prop :=
  c.mode = .scan ∧ c.replaying = false ∧ 1 ≤ c.clock ∧
    ∃ w : GalilScaffoldChainWatch.State, s.chain = ChainVM.watch w

/-- **`LiveScanWatch` の chain 条件を「非 idle」に弱めた版。**

不一致からの fallback に chain の watch は要らない——`.copy` 相でも
`shiftGuardVM` が立たず `scan_fallback` へ行く
（`FoundPackCorrected.no_shift_from_copyChain`）。fallback 系の契約
（`WatchFallbackC` / `WatchMismatchNoShiftC` / `FallbackReachS` …）はこちらで足りる。

**`TerminalRunC` / `TerminalRunFallbackC` の `LiveScanWatch` は弱めてはいけない**
（watch 無しではラウンドが回らない）。 -/
def LiveScanNonIdle (c : Control) (s : GalilVM) : Prop :=
  c.mode = .scan ∧ c.replaying = false ∧ 1 ≤ c.clock ∧ s.chain ≠ ChainVM.idle

theorem liveScanNonIdle_of_liveScanWatch {c : Control} {s : GalilVM}
    (h : LiveScanWatch c s) : LiveScanNonIdle c s := by
  obtain ⟨hm, hr, hc, w, hw⟩ := h
  exact ⟨hm, hr, hc, by rw [hw]; exact ChainVM.noConfusion⟩

/-- **NAMED (open), per instance.**  One watch round: at a live scan landing,
either the landing is terminal, or the machine performs a `WatchSeg` reaching
the next live scan landing with a strictly smaller measure. -/
def RoundStepC (P : Shared) (q : ℕ) (first : Fin 9) (meas : GalilVM → ℕ)
    (Term : Control → GalilVM → Prop) (c : Control) (s : GalilVM) : Prop :=
  Term c s ∨
    ∃ (c' : Control) (s' : GalilVM),
      WatchSeg P q first 2048 c s c' s' ∧ LiveScanWatch c' s' ∧ meas s' < meas s

/-- **Derived — the watch phase as a run.**  From a live scan landing with
measure at most `n`, the per-round contract reaches a terminal live landing by
a single `WatchSeg`.  The induction is on the fuel `n`; each round contributes
one `WatchSeg`, composed by `watchSeg_append`. -/
theorem watchRun_construct (P : Shared) (q : ℕ) (first : Fin 9) (meas : GalilVM → ℕ)
    (Term : Control → GalilVM → Prop)
    (hstep : ∀ (c : Control) (s : GalilVM), LiveScanWatch c s →
      RoundStepC P q first meas Term c s) :
    ∀ (n : ℕ) (c : Control) (s : GalilVM), meas s ≤ n → LiveScanWatch c s →
      ∃ (c' : Control) (s' : GalilVM),
        WatchSeg P q first 2048 c s c' s' ∧ LiveScanWatch c' s' ∧ Term c' s' := by
  intro n
  induction n with
  | zero =>
    intro c s hfuel hL
    rcases hstep c s hL with ht | ⟨c', s', hseg, hL', hlt⟩
    · exact ⟨c, s, .stop _ _, hL, ht⟩
    · omega
  | succ n ih =>
    intro c s hfuel hL
    rcases hstep c s hL with ht | ⟨c', s', hseg, hL', hlt⟩
    · exact ⟨c, s, .stop _ _, hL, ht⟩
    · obtain ⟨c'', s'', hseg2, hL'', ht⟩ := ih c' s' (by omega) hL'
      exact ⟨c'', s'', watchSeg_append hseg hseg2, hL'', ht⟩

/-! ## 3. The concrete fuel: the catch-up `distance` -/

/-- The fuel of the watch phase at half-period `h`: how far the chain's
catch-up `distance` still is from the shift guard's threshold `4*h`.  Every
matched outer comparison raises `distance` by one
(`GalilCatchUpDistance.distance_at_terminal`, second identity), so a round that
matches lowers `roundFuel` by one; hence at most `4*h+1` rounds. -/
def roundFuel (h : ℕ) (s : GalilVM) : ℕ :=
  match s.chain with
  | ChainVM.watch w => (4 * h + 1) - (value w.machine.control.distance).toNat
  | _ => 0

/-- **Derived.**  Fuel zero at a watching chain is exactly the `4*h ≤ distance`
that the place-count hypotheses of `GalilWatchPhase` and `GalilLastLowerBreak`
ask for. -/
theorem places_of_fuel_zero (h : ℕ) {s : GalilVM} {w : GalilScaffoldChainWatch.State}
    (hw : s.chain = ChainVM.watch w)
    (hnn : 0 ≤ value w.machine.control.distance)
    (h0 : roundFuel h s = 0) :
    4 * (h : ℤ) ≤ value w.machine.control.distance := by
  have h1 : (4 * h + 1) - (value w.machine.control.distance).toNat = 0 := by
    simpa [roundFuel, hw] using h0
  omega

/-- **Derived.**  Along a watch run out of the fresh `watchStart`, fuel zero at
zero lag gives the nonnegative margin — i.e. the shift guard's own ledger
condition (`GalilCatchUpDistance.places_iff_margin`). -/
theorem margin_of_fuel_zero (cen : GalilScaffoldInputHead.PlaceHead) (c : Fin 3)
    (ys : List (Fin 3)) (b : Fin 3) (radius : Counter) (hrc : Canonical radius)
    (sm dm : Bool) (bs cs : List Bool) (hbl : bs.length = ys.length + 1)
    {es : List Bool} {w : GalilScaffoldChainWatch.State} {s : GalilVM}
    (hr : GalilScaffoldChainWatch.Run
      (GalilScaffoldChainInputSupply.watchStart cen c ys b
        (GalilScaffoldChainCredits.run (GalilScaffoldChainCredits.start radius)
          (GalilScaffoldChainCredits.prepEvents sm dm bs cs))) es w)
    (hz : zero w.lag = true)
    (hw : s.chain = ChainVM.watch w)
    (hnn : 0 ≤ value w.machine.control.distance)
    (h0 : roundFuel (ys.length + 1) s = 0) :
    0 ≤ value w.margin := by
  refine (PalPeg.GalilCatchUpDistance.places_iff_margin cen c ys b radius hrc sm dm bs cs
    hbl hr hz).mp ?_
  have := places_of_fuel_zero (ys.length + 1) hw hnn h0
  push_cast at this ⊢
  linarith

/-- **Derived.**  The watch phase run with the concrete fuel: at most
`4*h + 1` rounds. -/
theorem watchRun_of_distance (P : Shared) (q : ℕ) (first : Fin 9) (h : ℕ)
    (Term : Control → GalilVM → Prop)
    (hstep : ∀ (c : Control) (s : GalilVM), LiveScanWatch c s →
      RoundStepC P q first (roundFuel h) Term c s)
    (c : Control) (s : GalilVM) (hL : LiveScanWatch c s) :
    ∃ (c' : Control) (s' : GalilVM),
      WatchSeg P q first 2048 c s c' s' ∧ LiveScanWatch c' s' ∧ Term c' s' := by
  refine watchRun_construct P q first (roundFuel h) Term hstep (4 * h + 1) c s ?_ hL
  cases hch : s.chain <;> simp [roundFuel, hch]

/-! ## 4. Wiring: a terminal tail gives the raw route -/

/-- **Derived.**  Whichever terminal tail the watch run lands in — the shift
tail or the reduced break tail — the cycle has the disjunctive raw route of
`CloseoutWatchPhase3`. -/
theorem watchRouteLPraw_of_terminal (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m : ℕ)
    (hex : ∀ s, (PofC centre place entry raw).replayExhausted s = zero s.replay)
    {c0 cP : Control} {r sP : GalilVM}
    (hE : StageEntryC (PofC centre place entry raw) qq first raw c0 r)
    (htail : ShiftTailC centre place entry qq first raw m c0 r cP sP ∨
      NoShiftTailC0 centre place entry qq first raw m c0 r cP sP) :
    WatchRouteLPraw (PofC centre place entry raw) qq first raw m c0 r cP sP := by
  refine watchRouteLPraw_of_tails centre place entry qq first raw m hex hE ?_
  rcases htail with hs | hn
  · exact Or.inl hs
  · exact Or.inr (noShiftTailC_of_0 centre place entry qq first raw m hn)

end PalPeg.CloseoutWatchRun

#print axioms PalPeg.CloseoutWatchRun.watchSeg_append
#print axioms PalPeg.CloseoutWatchRun.watchRun_construct
#print axioms PalPeg.CloseoutWatchRun.places_of_fuel_zero
#print axioms PalPeg.CloseoutWatchRun.margin_of_fuel_zero
#print axioms PalPeg.CloseoutWatchRun.watchRun_of_distance
#print axioms PalPeg.CloseoutWatchRun.watchRouteLPraw_of_terminal
