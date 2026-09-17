import PalPeg.CloseoutWatchRound45

/-!
# Closeout watch round 47 — the drain leaf reduced to the match clock

Round 45 left two leaves of `foundExit_compare_final17`: `PrepBirthLagC'`
(the birth lag across the preparation segment) and `WatchDrainC'` (the
radius-ledger growth along the watch segment).  This round closes the second
one **modulo the match clock**, and reports on the first.

* `sumRel_ticks` — the radius ledger `SumRel` transports along `ChainTicks`
  with `R ↦ R + es.count true` (`GalilChainCoupling.step_inv` /
  `matched_inv`, with the `WatchOK` slot instantiated trivially).
* `sumRel_internal` — the internal half of a watch tick preserves the ledger.
* `watchDrainC'_of_clock` — `WatchDrainC'` from `WatchClockC`, the single
  remaining hypothesis: along a watch segment the matched events are paced by
  the 2048-tick match clock (`2047 * count true ≤ count false`), and the birth
  chain satisfies the block invariant.  The growth witness is
  `m' := es2.count true`, `d1 := 0`, and `Rnow = value w0.lag + m'` is exactly
  the transported ledger, using `value w0.machine.control.distance = 0` at the
  birth and `w'.machine.control.broken = false` at the landing (the two inputs
  Round 44 showed to be missing).

`PrepBirthLagC'` is **not** closed here.  Its birth clause is
`value w0.lag = value sF.radius + m` with `2048 * m ≤ 2h + 2`; by
`GalilScaffoldChainCredits.prep_value` the growth `m` is exactly the matched
count of `prepEvents sm dm bs cs`, whose length is `2h + 3`
(`found_to_watchStart`: `bs.length = h`, `cs.length = h + 1`).  So the bound
`2048 * m ≤ 2h + 2` is again a *match-clock* statement about the preparation
segment, of the same shape as `WatchClockC`; what is additionally missing is
the transport of `found_to_watchStart` onto a `WatchSegE` from the found tick
to the landing.  Reported, not proved.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

namespace PalPeg.CloseoutWatchRound47

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.CloseoutContracts
open PalPeg.GalilRunSkeleton PalPeg.GalilInvPlus PalPeg.GalilInvPlus2
open PalPeg.GalilFoundStage PalPeg.GalilTraceCost
open PalPeg.GalilChainCoupling (SumRel step_inv matched_inv WatchOK)
open PalPeg.GalilBranchInvariants (BlockInv blockInv_step blockInv_tick)
open PalPeg.CloseoutWatchRound45 (WatchDrainC')

/-! ## 1. The ledger transports along chain ticks -/

/-- The trivial `WatchOK` slot, so that `step_inv`/`matched_inv` can be used
for their `SumRel` half alone. -/
theorem watchOK_triv (x : ChainVM) : WatchOK x True (fun _ => True) := by
  intro w hx hb; exact Or.inr trivial

theorem sumRel_tick {a : Bool} {x z : ChainVM} {R : ℤ} (h : ChainTick a x z)
    (hb : BlockInv x) (hs : SumRel x R) :
    SumRel z (R + (if a then 1 else 0)) := by
  obtain ⟨y, hstep, hm⟩ := h
  obtain ⟨hs', hw'⟩ := step_inv hstep trivial hb hs (watchOK_triv x)
  cases a with
  | false =>
    change z = y at hm
    subst hm
    simpa using hs'
  | true =>
    change ChainMatched y z at hm
    simpa using (matched_inv hm (blockInv_step hstep hb) hs' hw').1

theorem blockInv_ticks {es : List Bool} : ∀ {x z : ChainVM}, ChainTicks es x z →
    BlockInv x → BlockInv z := by
  induction es with
  | nil => intro x z h hb; cases h; exact hb
  | cons a es ih =>
    intro x z h hb
    cases h with
    | cons ht hr => exact ih hr (blockInv_tick ht hb)

/-- **The radius ledger along a chain tick run.** -/
theorem sumRel_ticks {es : List Bool} : ∀ {x z : ChainVM} {R : ℤ}, ChainTicks es x z →
    BlockInv x → SumRel x R → SumRel z (R + (es.count true : ℤ)) := by
  induction es with
  | nil => intro x z R h hb hs; cases h; simpa using hs
  | cons a es ih =>
    intro x z R h hb hs
    cases h with
    | cons ht hr =>
      have hnext := ih hr (blockInv_tick ht hb) (sumRel_tick ht hb hs)
      have harith : R + (if a then (1:ℤ) else 0) + (es.count true : ℤ)
          = R + ((a :: es).count true : ℤ) := by
        cases a <;> simp [List.count_cons] <;> omega
      rw [harith] at hnext
      exact hnext

/-- The internal half of a watch tick preserves the ledger. -/
theorem sumRel_internal {w w' : GalilScaffoldChainWatch.State} {R : ℤ}
    (hi : GalilScaffoldChainWatch.Internal w w') (hb : BlockInv (ChainVM.watch w))
    (hs : SumRel (ChainVM.watch w) R) : SumRel (ChainVM.watch w') R :=
  (step_inv (ChainStep.watchStep w w' hi) trivial hb hs (watchOK_triv _)).1

/-! ## 2. The remaining leaf: the match clock along the watch segment -/

/-- **NAMED — the watch-segment match clock.**  Matched events on a watch
segment are paced by the 2048-tick match clock, and the chain at the birth end
satisfies the block invariant (it is born by `watchStart`). -/
def WatchClockC (P : Shared) (q : ℕ) (first : Fin 9) : Prop :=
  ∀ (es2 : List Bool) (cb c1 : Control) (sb s1 : GalilVM)
    (w0 w : GalilScaffoldChainWatch.State),
    WatchSegE P q first 2048 es2 cb sb c1 s1 → sb.chain = ChainVM.watch w0 →
    s1.chain = ChainVM.watch w →
    BlockInv (ChainVM.watch w0) ∧ 2047 * (es2.count true : ℤ) ≤ (es2.count false : ℤ)

/-! ## 3. `WatchDrainC'` from the clock -/

/-- **(3') CLOSED modulo `WatchClockC`.**  The growth is the matched count of
the segment: the ledger `distance + lag` starts at `value w0.lag` (the birth
distance vanishes) and gains one per matched event. -/
theorem watchDrainC'_of_clock (P : Shared) (q : ℕ) (first : Fin 9)
    (hclk : WatchClockC P q first) : WatchDrainC' P q first := by
  intro es2 cb c1 sb s1 w0 w w' Rnow hseg hsb hd0 hbr hw hint hs
  obtain ⟨hblock, hpace⟩ := hclk es2 cb c1 sb s1 w0 w hseg hsb hw
  -- the chain ticks of the segment
  have hne : sb.chain ≠ ChainVM.idle := by rw [hsb]; exact fun h => ChainVM.noConfusion h
  obtain ⟨hct, -, -, -, -, -, -⟩ := watchSegE_events P q first 2048 hseg hne
  rw [hsb, hw] at hct
  -- the ledger at the birth
  have hs0 : SumRel (ChainVM.watch w0) (value w0.lag) := by
    intro _; rw [hd0]; omega
  have hs1 : SumRel (ChainVM.watch w) (value w0.lag + (es2.count true : ℤ)) :=
    sumRel_ticks hct hblock hs0
  have hbw : BlockInv (ChainVM.watch w) := blockInv_ticks hct hblock
  have hs2 : SumRel (ChainVM.watch w') (value w0.lag + (es2.count true : ℤ)) :=
    sumRel_internal hint hbw hs1
  have heq : value w'.machine.control.distance + value w'.lag
      = value w0.lag + (es2.count true : ℤ) := hs2 hbr
  have heq' : value w'.machine.control.distance + value w'.lag = Rnow := hs hbr
  refine ⟨(es2.count true : ℤ), 0, by positivity, le_refl 0, by simpa using hpace, ?_⟩
  omega

/-! ## 4. The route with the drain leaf replaced by the clock -/

open PalPeg.CloseoutWatchRound2 (FoundCompareCtxC)
open PalPeg.CloseoutWatchRound3 (DistanceNonnegC)
open PalPeg.CloseoutWatchRound6 (RightCanC RightSaneC StartLeC LedgerOriginC PeriodMatchC)
open PalPeg.CloseoutWatchRound4 (ZeroLagAtMatchC)
open PalPeg.CloseoutWatchRound7 (PrepLandingWatchC ShiftReachC ShiftRoundAtC BreakTermData)
open PalPeg.CloseoutWatchRound10 (FoundDpAtC)
open PalPeg.CloseoutPrepInputs2 (MismatchExitG)
open PalPeg.CloseoutPrepInputs3 (PrepInputsG3)
open PalPeg.CloseoutWatchRound30 (ShiftCopyIdleC MismatchClassifierTieC)
open PalPeg.CloseoutWatchRound31 (FoundExitLPS FallbackReachS)
open PalPeg.CloseoutWatchRound33 (ShiftRunCL)
open PalPeg.CloseoutWatchRound34 (ShiftBreakOracleC ShiftBreakFitC)
open PalPeg.CloseoutWatchRound37 (ShiftRoundInvCL ShiftOriginRestCL)
open PalPeg.CloseoutWatchRound44 (LandingFreshC')
open PalPeg.CloseoutWatchRound45 (PrepBirthLagC' foundExit_compare_final17)
open PalPeg.CloseoutWatchRun (LiveScanWatch roundFuel)

/-- **`foundExit_compare_final17` with `WatchDrainC'` discharged from the
match clock.**  The only watch-segment leaf left is `PrepBirthLagC'`. -/
theorem foundExit_compare_final18 (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (m h lower span : ℕ) (μ : ℕ → Control → GalilVM → ℕ)
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
    (hfbS : FallbackReachS (PofC centre place entry w) q first w m c r cP sP)
    (hstage : ReplayStage w (PofC centre place entry w) q first c r)
    (hmP : cP.mode = .scan) (hrP : cP.replaying = false) (hcP : 1 ≤ cP.clock)
    (hwatch : PrepLandingWatchC (PofC centre place entry w) q first cP sP)
    (hat : FoundDpAtC centre place entry q first w lower span h c r)
    (hreach : ShiftReachC centre place entry q first w h)
    (hround : ShiftRoundAtC centre place entry q first w m h lower)
    (h3 : ShiftCopyIdleC) (h4 : ShiftRunCL)
    (hinv : ShiftRoundInvCL w)
    (horacle : ∀ h', ShiftBreakOracleC centre place entry q first w h' (μ h'))
    (hfit : ∀ h', ShiftBreakFitC centre place entry q first w m h')
    (hrest : ShiftOriginRestCL centre place entry q first w lower)
    (htie : MismatchClassifierTieC (PofC centre place entry w) q first)
    (hbirth : PrepBirthLagC' (PofC centre place entry w) q first c r cP sP)
    (hclock : WatchClockC (PofC centre place entry w) q first)
    (hfresh : LandingFreshC' (PofC centre place entry w) q first cP sP)
    (hland : ∀ sF : GalilVM,
      PalPeg.CloseoutWatchRound5.BreakLandingC centre place entry q first w h sF cP sP)
    (hstepBreak : ∀ (c0 : Control) (s0 : GalilVM), LiveScanWatch c0 s0 →
      PalPeg.CloseoutWatchRun.RoundStepC (PofC centre place entry w) q first (roundFuel h)
        (BreakTermData centre place entry q first w m h) c0 s0) :
    FoundExitLPS (PofC centre place entry w) q first w m c r :=
  foundExit_compare_final17 centre place entry q first w m h lower span μ hP hex hready hcan hsane hstart hor hzl hnn
    hpm hE hsW a ls rs qw gap hprep hmis hctx hfbS hstage hmP hrP hcP hwatch hat hreach hround
    h3 h4 hinv horacle hfit hrest htie hbirth (watchDrainC'_of_clock _ _ _ hclock) hfresh
    hland hstepBreak

end PalPeg.CloseoutWatchRound47

#print axioms PalPeg.CloseoutWatchRound47.sumRel_ticks
#print axioms PalPeg.CloseoutWatchRound47.sumRel_internal
#print axioms PalPeg.CloseoutWatchRound47.watchDrainC'_of_clock
#print axioms PalPeg.CloseoutWatchRound47.foundExit_compare_final18
