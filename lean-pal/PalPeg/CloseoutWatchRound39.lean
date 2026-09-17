import PalPeg.CloseoutWatchRound37

/-!
# Closeout watch round 39 — `MismatchLandingLagZeroC`: verdict

**As a global proposition it is FALSE** (`not_mismatchLandingLagZeroC`): any
watching state with `Good w`, positive lag, an outer mismatch and a
guard-passing post-compare chain `caught w` refutes it — the same shape as
Round 33's `not_shiftLagZeroC`; the guard's `zero` clause reads the
POST-`Internal` chain, so the pre-compare lag may be `1`.  The model reaches
such states: `chainStart` seeds the chain with `lag = radius` (the found
radius `R_f`), copy/back add one unit per matched compare (`m` of them), and
the watch drains one unit per background tick.  With `R_f = 3069`, `h = 512`
the first watch compare has lag `2048`, and after one matched round (net `0`)
and `2047` count ticks the second compare arrives with lag `1`, distance
`3069 ≥ 4h`, phase `4`: a guard-passing mismatch landing with pre-lag `1`.

**At the landings that occur it is TRUE only through the found-radius
budget.**  `pre_lag_le_one`: a passing guard forces pre-lag `≤ 1`.
`watchSegE_lag`: along a `WatchSegE` the watch lag is `≤ max 0 (L − #false)`
(`chainTicks_watch_run` + `run_lag`).  `fresh_phase4_budget`: the guard's
`phase = 4` on a fresh chain gives `4h ≤ R_now` (`SumRel`).  With
`L = R_f + m`, `#false ≥ 2047·m' + d1`, `R_now = R_f + m + m'` and
`2048·m ≤ 2h+2` (prep length), `lag_zero_of_budget` shows lag `0` **iff the
found radius satisfies `R_f ≤ 2h`** — Round 37's hypotheses
(`PrepLandingLiveC`, `FoundDpShiftC`, `TerminalRunMismatchShiftC`) contain no
such bound; it is `GalilReplayBudgetProof.found_radius_le_two_period`, which
needs `Decodes`/`Restarted`/`StageEntry` (available one level up, from
`StageEntryC`).  So: (A) holds at the route level, (B) is not needed, but the
leaf cannot be discharged from `shiftTailC_of_dataL`'s own hypotheses.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutWatchRound39

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.CloseoutWatchRun (LiveScanWatch)
open PalPeg.CloseoutWatchRound23 (MismatchGuardFails)
open PalPeg.CloseoutWatchRound37 (MismatchLandingLagZeroC)
open PalPeg.GalilScaffoldChainLag (run_lag catches)
open PalPeg.GalilChainCoupling (FreshC SumRel)

/-! ## 1. The global proposition is false -/

/-- **`MismatchLandingLagZeroC` is false** whenever some live clock-`1` state
has a `Good` watching chain with positive lag, an outer mismatch, and a
guard-passing post-compare chain `caught w` (see the header for the reachable
instance). -/
theorem not_mismatchLandingLagZeroC
    (hex : ∃ (c1 : Control) (s1 : GalilVM) (w : GalilScaffoldChainWatch.State) (vq : SearchVM),
      LiveScanWatch c1 s1 ∧ c1.clock = 1 ∧ canRight s1.right ∧
      read (left s1.left) ≠ read (right s1.right) ∧
      s1.chain = ChainVM.watch w ∧ GalilScaffoldChainWatch.Good w ∧ positive w.lag = true ∧
      shiftGuardVM (afterMismatch s1
        ⟨left s1.left, right s1.right, ChainVM.watch (GalilScaffoldChainWatch.caught w)⟩ vq)) :
    ¬ MismatchLandingLagZeroC := by
  intro hlag
  obtain ⟨c1, s1, w, vq, hlive, hclk, hav, hne, hw, hg, hp, hguard⟩ := hex
  have htick : ChainTick false s1.chain (ChainVM.watch (GalilScaffoldChainWatch.caught w)) := by
    rw [hw]
    refine ⟨_, ChainStep.watchStep _ _ (GalilScaffoldChainWatch.Internal.take w hp hg), ?_⟩
    simp
  have hnG : ¬ MismatchGuardFails s1 := by
    intro hG
    exact hG.2 ⟨left s1.left, right s1.right, ChainVM.watch (GalilScaffoldChainWatch.caught w)⟩
      vq htick hguard
  have h0 := hlag c1 s1 w hlive hclk hav hne hnG hw
  rw [positive_of_zero h0] at hp
  exact Bool.noConfusion hp

/-! ## 2. What a passing guard says about the pre-compare lag -/

/-- A guard-passing landing has pre-compare lag `0` or `1`. -/
theorem pre_lag_le_one {w w' : GalilScaffoldChainWatch.State}
    (hi : GalilScaffoldChainWatch.Internal w w') (hz : zero w'.lag = true)
    (hc : GalilScaffoldChainWatch.CanonicalState w) :
    0 ≤ value w.lag ∧ value w.lag ≤ 1 := by
  have hc' := GalilScaffoldChainWatch.internal_canonical hi hc
  have hv := (zero_iff w'.lag hc'.1).mp hz
  cases hi with
  | idle _ => omega
  | take hp hg =>
    have hp' := (positive_iff w.lag hc.1).mp hp
    simp only [GalilScaffoldChainWatch.caught, dec_value] at hv
    omega

/-! ## 3. Lag drain along a `WatchSegE` -/

/-- Along an event-indexed segment whose chain watches throughout, the watch
lag is bounded by the initial lag minus the number of disabled ticks. -/
theorem watchSegE_lag (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) {es : List Bool}
    {c c' : Control} {s t : GalilVM} (h : WatchSegE P q first delay es c s c' t)
    {w0 w : GalilScaffoldChainWatch.State} (hs : s.chain = ChainVM.watch w0)
    (ht : t.chain = ChainVM.watch w) (hc : GalilScaffoldChainWatch.CanonicalState w0)
    (hn : 0 ≤ value w0.lag) :
    0 ≤ value w.lag ∧ value w.lag ≤ max 0 (value w0.lag - (es.count false : ℤ)) := by
  have hne : s.chain ≠ ChainVM.idle := by rw [hs]; exact fun h => ChainVM.noConfusion h
  obtain ⟨hct, -, -, -, -, -, -⟩ := watchSegE_events P q first delay h hne
  rw [hs, ht] at hct
  exact run_lag (chainTicks_watch_run es hct) hc hn

/-- Enough disabled ticks drain the lag to zero. -/
theorem watchSegE_zero_lag (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) {es : List Bool}
    {c c' : Control} {s t : GalilVM} (h : WatchSegE P q first delay es c s c' t)
    {w0 w : GalilScaffoldChainWatch.State} (hs : s.chain = ChainVM.watch w0)
    (ht : t.chain = ChainVM.watch w) (hc : GalilScaffoldChainWatch.CanonicalState w0)
    (hn : 0 ≤ value w0.lag) (hsupply : value w0.lag ≤ (es.count false : ℤ)) :
    zero w.lag = true := by
  have hne : s.chain ≠ ChainVM.idle := by rw [hs]; exact fun h => ChainVM.noConfusion h
  obtain ⟨hct, -, -, -, -, -, -⟩ := watchSegE_events P q first delay h hne
  rw [hs, ht] at hct
  exact catches (chainTicks_watch_run es hct) hc hn hsupply

/-! ## 4. The guard's radius budget and the arithmetic -/

/-- On a fresh chain with zero lag at phase `4`, the radius ledger gives
`4h ≤ R` (`guard_budget`'s fresh branch, without the `h ≤ R+1` weakening). -/
theorem fresh_phase4_budget {w : GalilScaffoldChainWatch.State} {R : ℤ}
    (hf : FreshC w.machine.control) (hph : w.machine.control.phase = 4)
    (hbr : w.machine.control.broken = false) (hs : SumRel (.watch w) R)
    (hz : zero w.lag = true) : 4 * (periodLength w : ℤ) ≤ R := by
  have hd : value w.machine.control.distance + value w.lag = R := hs hbr
  rw [PalPeg.GalilChainCoupling.value_zero_of_zero hz] at hd
  have hpv : (w.machine.control.phase.val : ℤ) = 4 := by rw [hph]; rfl
  have hpl : periodLength w = w.machine.control.period.left.length +
      w.machine.control.period.right.length := rfl
  obtain ⟨hf1, hf2⟩ := hf
  cases hfw : w.machine.control.forward with
  | true =>
    obtain ⟨h1, h2⟩ := hf1 hfw
    rw [hpv, ← hpl] at h2
    have : (1 : ℤ) ≤ w.machine.control.period.left.length := by exact_mod_cast h1
    linarith
  | false =>
    obtain ⟨h1, h2⟩ := hf2 hfw
    rw [hpv, ← hpl] at h2
    rw [← hpl] at h1
    have : (w.machine.control.period.left.length : ℤ) + 1 ≤ (periodLength w : ℤ) := by
      exact_mod_cast h1
    linarith

/-- **The arithmetic of the landing.**  Birth lag `R_f + m` (`chainStart` seeds
`lag = radius`, copy/back add one per matched compare), at least `2047·m' + d1`
disabled ticks before the landing (`2047` count ticks per matched round),
`R_now = R_f + m + m'`, the guard's `4h − 1 ≤ R_now`, the prep length
`2048·m ≤ 2h + 2`, and the found-radius budget `R_f ≤ 2h`: the landing lag is
`0`.  Without `R_f ≤ 2h` the conclusion fails (`R_f = 3069`, `h = 512`,
`m = 0`, `m' = 1`, `d1 = 1021`, lag `1`). -/
theorem lag_zero_of_budget (Rf m m' d1 h lag : ℤ) (hh : 1 ≤ h) (hRf : Rf ≤ 2 * h)
    (hm : 2048 * m ≤ 2 * h + 2) (hm0 : 0 ≤ m) (hm'0 : 0 ≤ m') (hd1 : 0 ≤ d1)
    (hlag0 : 0 ≤ lag) (hlag : lag ≤ max 0 (Rf + m - (2047 * m' + d1)))
    (hguard : 4 * h - 1 ≤ Rf + m + m') : lag = 0 := by
  rcases le_or_gt (Rf + m - (2047 * m' + d1)) 0 with h0 | h0
  · rw [max_eq_left h0] at hlag; omega
  · rw [max_eq_right h0.le] at hlag; omega

/-- The counter-instance from the header, checked: the same data with
`R_f = 3069`, `h = 512` admits lag `1`. -/
theorem budget_counterexample :
    ∃ (Rf m m' d1 h lag : ℤ), 1 ≤ h ∧ 2048 * m ≤ 2 * h + 2 ∧ 0 ≤ m ∧ 0 ≤ m' ∧ 0 ≤ d1 ∧
      0 ≤ lag ∧ lag ≤ max 0 (Rf + m - (2047 * m' + d1)) ∧ 4 * h - 1 ≤ Rf + m + m' ∧
      lag = 1 :=
  ⟨3069, 0, 1, 1021, 512, 1, by norm_num, by norm_num, le_rfl, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, rfl⟩

/-- **(A) at the landing, modulo the run accounting.**  A guard-passing
landing (`Internal w w'`, `zero w'.lag`, fresh phase-`4` chain `w'` with the
ledger `SumRel (.watch w') R_now`) whose pre-compare watch `w` was born with
lag `R_f + m` and drained through `k ≥ 2047·m' + d1` disabled ticks, with
`R_now = R_f + m + m'`, `2048·m ≤ 2h+2` and `R_f ≤ 2h`, has `zero w.lag`. -/
theorem landing_lag_zero_of_budget {w w' : GalilScaffoldChainWatch.State} {Rnow : ℤ} {h k : ℕ}
    (hi : GalilScaffoldChainWatch.Internal w w') (hz : zero w'.lag = true)
    (hc : GalilScaffoldChainWatch.CanonicalState w)
    (hf : FreshC w'.machine.control) (hph : w'.machine.control.phase = 4)
    (hbr : w'.machine.control.broken = false) (hs : SumRel (.watch w') (Rnow : ℤ))
    (hper : periodLength w' = h)
    (Rf m m' d1 : ℤ) (hk : (k : ℤ) ≥ 2047 * m' + d1)
    (hdrain : value w.lag ≤ max 0 (Rf + m - k))
    (hnow : Rnow = Rf + m + m') (hh : 1 ≤ (h : ℤ)) (hRf : Rf ≤ 2 * h)
    (hm : 2048 * m ≤ 2 * h + 2) (hm0 : 0 ≤ m) (hm'0 : 0 ≤ m') (hd1 : 0 ≤ d1) :
    zero w.lag = true := by
  have hpre := pre_lag_le_one hi hz hc
  have hbud := fresh_phase4_budget hf hph hbr hs hz
  rw [hper] at hbud
  have hlag' : value w.lag ≤ max 0 (Rf + m - (2047 * m' + d1)) := by
    refine le_trans hdrain (max_le_max le_rfl ?_)
    linarith
  have := lag_zero_of_budget Rf m m' d1 h (value w.lag) hh hRf hm hm0 hm'0 hd1 hpre.1 hlag'
    (by omega)
  exact (zero_iff w.lag hc.1).mpr this

#print axioms PalPeg.CloseoutWatchRound39.not_mismatchLandingLagZeroC
#print axioms PalPeg.CloseoutWatchRound39.pre_lag_le_one
#print axioms PalPeg.CloseoutWatchRound39.watchSegE_lag
#print axioms PalPeg.CloseoutWatchRound39.watchSegE_zero_lag
#print axioms PalPeg.CloseoutWatchRound39.fresh_phase4_budget
#print axioms PalPeg.CloseoutWatchRound39.lag_zero_of_budget
#print axioms PalPeg.CloseoutWatchRound39.budget_counterexample
#print axioms PalPeg.CloseoutWatchRound39.landing_lag_zero_of_budget

end PalPeg.CloseoutWatchRound39
