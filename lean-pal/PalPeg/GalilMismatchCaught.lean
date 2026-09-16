import PalPeg.GalilSegmentConstruct2
import PalPeg.GalilLiveCentreMismatch
import PalPeg.GalilCandidatePeriod

/-!
# Closing `WatchStop.mismatchOther`: a scan mismatch only after the chain caught up

`PalPeg/GalilSegmentConstruct2.lean` lists `WatchStop.mismatchOther` — a scan
mismatch while the chain is still copying, walking back, or watching with a
positive lag — as an open disjunct.  This module supplies the two halves that
rule it out.

**Extent.**  A found DP candidate with semiperiod `h`
(`GalilDpCorrect.Candidate`: `w.take (4*h+1)` palindromic) yields, through
`candidate_palAt`, `PalAt (encoded raw) (C - 2*h) (2*h)` on the real scan word.
`match_of_palAt` turns any such palindrome into "the comparison at radius `k`
matches" for every `k+1 ≤ 2*h`: a mismatch would make the centre dead at the
next place (`not_live_of_mismatch`), which the palindrome forbids.  So the scan
cannot mismatch at all during the first `2*h` places after the start.

**Catch-up.**  `tick_lag_zero` / `run_lag_zero`: a watch tick can never lift a
zero lag — `Internal.take` needs `positive lag`, `Outer.queued` needs
`zero lag = false`, and `Outer.immediate` leaves the lag alone.  Combined with
`GalilScaffoldChainLag.clock_catches` (`2*k+2` ticks pay down an entry lag `k`),
`lag_zero_before_bound` gives zero lag at the end of the phase and at every
point after the catch-up leg.

**Gaps (stated, not hidden).**

* That the chain is a `.watch` at all at the mismatch — i.e. that the copy
  (`copy_run_to_back`, `n+1` ticks) and back walk (`GalilScaffoldChainPeriod.back_exact`,
  `ls.length+2` ticks) are finished by then — is *not* proved here: it needs the
  tick-position bookkeeping of the round.  It travels as the single named
  hypothesis `hcaught` of `mismatchOther_impossible`, which packages "outside
  the candidate's extent the chain is a zero-lag `.watch`".
* The entry lag bound (`value s.lag ≤ k` with `k ≈ 2*h`) feeding
  `lag_zero_before_bound` is a hypothesis; `GalilScaffoldChainCredits.prep_value`
  computes it from the prelude's match counts, which this module does not carry.
* `match_of_palAt` assumes `k + 1 < C` (the left head has not reached the origin);
  this is the same `n < 2*c` side condition as `Live`.
-/

set_option autoImplicit false

namespace PalPeg.GalilMismatchCaught

open Manacher PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-! ## 1. No mismatch inside the guaranteed palindrome extent -/

theorem match_of_palAt {raw : List (Fin 2)} {C k R : ℕ} {l r : PlaceHead}
    (hi : ScanInvariant raw C k l r) (hav : canRight r)
    (hpal : PalAt (encoded raw) C R) (hkR : k + 1 ≤ R) (hkC : k + 1 < C) :
    read (left l) = read (right r) := by
  by_contra hmis
  refine not_live_of_mismatch hi hav hmis ?_
  have hpr := hi.rightPos
  refine ⟨by omega, by omega, ?_⟩
  have e : position r + 1 - C = k + 1 := by omega
  rw [e]
  exact hpal.mono hkR

/-! ## 2. Zero lag is preserved by watch ticks -/

theorem positive_false_of_zero {c : Counter} (hz : zero c = true) : positive c = false := by
  unfold zero at hz
  unfold positive
  simp only [Bool.and_eq_true] at hz
  rw [hz.1]
  rfl

theorem internal_lag_zero {s t : GalilScaffoldChainWatch.State}
    (hi : GalilScaffoldChainWatch.Internal s t) (hz : zero s.lag = true) :
    zero t.lag = true := by
  cases hi with
  | idle => exact hz
  | take hp _ => rw [positive_false_of_zero hz] at hp; exact absurd hp (by simp)

theorem outer_lag_zero {s t : GalilScaffoldChainWatch.State} {b : Bool}
    (ho : GalilScaffoldChainWatch.Outer s b t) (hz : zero s.lag = true) :
    zero t.lag = true := by
  cases ho with
  | idle => exact hz
  | queued hz0 => rw [hz0] at hz; exact absurd hz (by simp)
  | immediate => exact hz

theorem tick_lag_zero {s t : GalilScaffoldChainWatch.State} {b : Bool}
    (ht : GalilScaffoldChainWatch.Tick s b t) (hz : zero s.lag = true) : zero t.lag = true := by
  cases ht with
  | step hi ho => exact outer_lag_zero ho (internal_lag_zero hi hz)

theorem run_lag_zero {s t : GalilScaffoldChainWatch.State} {bs : List Bool}
    (hr : GalilScaffoldChainWatch.Run s bs t) (hz : zero s.lag = true) : zero t.lag = true := by
  induction hr with
  | stop _ => exact hz
  | next ht _ ih => exact ih (tick_lag_zero ht hz)

/-! ## 3. Lag is zero from the catch-up bound onwards -/

/-- **Catch-up.**  A watch run whose first leg is at least `2k+2` ticks long
(`k` an upper bound on the entry lag) ends with zero lag, and so does every
continuation of it: `GalilScaffoldChainLag.clock_catches` supplies the first
leg, `run_lag_zero` carries the conclusion through the rest. -/
theorem lag_zero_before_bound {s m t : GalilScaffoldChainWatch.State} {bs cs : List Bool}
    (h1 : GalilScaffoldChainWatch.Run s bs m) (h2 : GalilScaffoldChainWatch.Run m cs t)
    (hc : GalilScaffoldChainWatch.CanonicalState s) (hn : 0 ≤ value s.lag)
    (k clock : ℕ) (hk : value s.lag ≤ k) (hclock : 1 ≤ clock ∧ clock ≤ 2048)
    (available : List Bool) (hlen : available.length = bs.length)
    (hmatched : bs.count true ≤ (GalilScaffoldMatchClock.run 2048 clock available).2)
    (hticks : 2*k+2 ≤ bs.length) : zero t.lag = true :=
  run_lag_zero h2
    (GalilScaffoldChainLag.clock_catches h1 hc hn k clock hk hclock available hlen hmatched hticks)

/-! ## 4. The candidate's extent, instantiated -/

/-- **No mismatch before the chain has caught up.**  At the centre `C - 2h`
chosen from a found DP candidate with semiperiod `h`, every comparison at a
radius `k` with `k+1 ≤ 2h` *matches*: the candidate guarantees
`PalAt (encoded raw) (C - 2h) (2h)` (`candidate_palAt`), and a mismatch there
would kill a centre that palindrome keeps alive (`not_live_of_mismatch`). -/
theorem no_mismatch_before_caught (a : Fin 2) (ls rs q : List (Fin 2)) (gap : Bool)
    (span lower h : ℕ)
    (hc : GalilDpCorrect.Candidate
      ((GalilScaffoldPlace.stream ⟨a :: ls, gap⟩).take (span+1)) lower h)
    {k : ℕ} {l r : PlaceHead}
    (hi : ScanInvariant ((a :: ls).reverse ++ rs ++ q)
      (position (represent ⟨a :: ls, gap⟩ (rs.map some) q) - 2*h) k l r)
    (hav : canRight r) (hk : k + 1 ≤ 2*h)
    (hkC : k + 1 < position (represent ⟨a :: ls, gap⟩ (rs.map some) q) - 2*h) :
    read (left l) = read (right r) :=
  match_of_palAt hi hav (candidate_palAt a ls rs q gap span lower h hc).2 hk hkC

/-! ## 5. Ruling out `WatchStop.mismatchOther` -/

/-- **The gap, closed under the two bounds.**  The field list of
`GalilSegmentConstruct2.WatchStop.mismatchOther` is contradictory as soon as

* inside the candidate's extent (`k+1 ≤ R`) the scan invariant holds — then the
  comparison matches, contradicting `hmt`; and
* outside it the chain has caught up (`hcaught`) — a zero-lag `.watch`,
  contradicting the constructor's own `hno`.

`hcaught` is discharged by `lag_zero_before_bound` together with the (still
hypothetical) fact that the copy/back prelude is over by then. -/
theorem mismatchOther_impossible (P : Shared) (q : ℕ) (first : Fin 9)
    {s : GalilVM} {vs : ScanVM}
    {raw : List (Fin 2)} {C k R : ℕ}
    (hi : ScanInvariant raw C k s.left s.right)
    (hkC : k + 1 < C)
    (hpal : PalAt (encoded raw) C R)
    (hcaught : ¬ (k + 1 ≤ R) → ∃ w : GalilScaffoldChainWatch.State,
      s.chain = .watch w ∧ zero w.lag = true)
    (ha : canRight s.right)
    (hno : ¬ ∃ w : GalilScaffoldChainWatch.State, s.chain = .watch w ∧ zero w.lag = true)
    (hcmp : (galilFrame P q first).compare s (scanLens.set s vs))
    (hmt : ¬ (galilFrame P q first).matched (scanLens.set s vs)) : False := by
  by_cases hk : k + 1 ≤ R
  · have hl : vs.left = left s.left := hcmp.1.1
    have hr : vs.right = right s.right := hcmp.1.2.1
    have hmis : ¬ read vs.left = read vs.right := hmt
    rw [hl, hr] at hmis
    exact hmis (match_of_palAt hi ha hpal hk hkC)
  · exact hno (hcaught hk)


/-- `mismatchOther_impossible` with the extent supplied by the found candidate:
`R := 2*h`, centre `C - 2*h`.  The one remaining hypothesis is `hcaught` — that
past `2*h` places from the found tick the chain is a zero-lag watch. -/
theorem mismatchOther_impossible_of_candidate (P : Shared) (q : ℕ) (first : Fin 9)
    {s : GalilVM} {vs : ScanVM}
    (a : Fin 2) (ls rs qs : List (Fin 2)) (gap : Bool) (span lower h : ℕ)
    (hc : GalilDpCorrect.Candidate
      ((GalilScaffoldPlace.stream ⟨a :: ls, gap⟩).take (span+1)) lower h)
    {k : ℕ}
    (hi : ScanInvariant ((a :: ls).reverse ++ rs ++ qs)
      (position (represent ⟨a :: ls, gap⟩ (rs.map some) qs) - 2*h) k s.left s.right)
    (hkC : k + 1 < position (represent ⟨a :: ls, gap⟩ (rs.map some) qs) - 2*h)
    (hcaught : ¬ (k + 1 ≤ 2*h) → ∃ w : GalilScaffoldChainWatch.State,
      s.chain = .watch w ∧ zero w.lag = true)
    (ha : canRight s.right)
    (hno : ¬ ∃ w : GalilScaffoldChainWatch.State, s.chain = .watch w ∧ zero w.lag = true)
    (hcmp : (galilFrame P q first).compare s (scanLens.set s vs))
    (hmt : ¬ (galilFrame P q first).matched (scanLens.set s vs)) : False :=
  mismatchOther_impossible P q first hi hkC
    (candidate_palAt a ls rs qs gap span lower h hc).2 hcaught ha hno hcmp hmt

#print axioms match_of_palAt
#print axioms positive_false_of_zero
#print axioms internal_lag_zero
#print axioms outer_lag_zero
#print axioms tick_lag_zero
#print axioms run_lag_zero
#print axioms lag_zero_before_bound
#print axioms no_mismatch_before_caught
#print axioms mismatchOther_impossible
#print axioms mismatchOther_impossible_of_candidate

end PalPeg.GalilMismatchCaught
