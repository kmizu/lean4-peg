import PalPeg.GalilMoveLemma
import PalPeg.GalilPredictability

/-!
# Real-time ledger obligations 1, 2 and 5

`lean-pal/ASSEMBLY_PLAN.md` §"実時間台帳の紙スケッチ" lists eight proof
obligations that together turn the Scala source (`SCA_GALIL.md`,
`GALIL_CLOCK.md`) into an unconditional real-time recognizer.  Obligation 7
(telescoping/FIFO) is already Lean-side in `PalPeg.GalilPredictability`:
`realtime_of_predictable` needs exactly three source contracts,

* `hmono : ∀ m, C m ≤ C (m+1)`               (centres never decrease),
* `hC    : ∀ m, m ≤ C m`                     (centres never lag the input),
* `hd    : ∀ m, d (m+1) ≤ c * (C (m+1) - C m + 1)`  (the work ledger),

and `hd` is where obligations 1–5 live.  This module states obligations 1, 2
and 5 as arithmetic propositions over the quantities of `GALIL_CLOCK.md` and
discharges everything that is pure arithmetic, leaving in each case a single
named machine hypothesis.

* **Obligation 1 (stage deadline).**  `stageCost` is the cost formula
  `max(r,1) + 2r + 2m + 7 + ⌈(327m+224)/q⌉` of `GALIL_CLOCK.md` §"DP stages".
  `stageCost_le_factor` proves the uniform factor `stage cost ≤ K·ell`
  (`K ≥ 400`, the `q = 1` worst case; the documented `K = 10` is the `q = 64`
  specialisation), and `stage_meets_barrier` proves that with `M ≥ 24K` and
  entry radius `rad ≤ 5r/3` the stage is finished by its barrier `2r`.  The
  machine input is `hcost` in `stage_deadline`: the actual tick count of a
  stage is bounded by `stageCost`.  Supplier: `GalilScaffoldTimingCost`
  (`delay_calibration`) together with the segment counters of
  `GalilSegmentCount` (`watchSegE_steps_length`, `watchSegE_clock_le`).

* **Obligation 2 (DP discovery and verifier catch-up).**  `vlag` is the
  documented arrival/service model of the verifier lag: one already-matched
  place is cleared per transition, at most one new place arrives per `M`
  transitions.  `vlag_zero` proves the catch-up latency `2·L`, and
  `verifier_catchup` proves that with `M ≥ 8` the catch-up is complete before
  the radius reaches `4h` when discovery is before `2h` and the semiperiod
  copy costs `2h+2`.  The machine input is `hmodel`: the real verifier lag is
  dominated by `vlag`.  Supplier: the chain-verifier `credit/lag/margin`
  accounting of `GalilScaffoldChainVerifier`.

* **Obligation 5 (replay).**  `replay_cost_le` turns "≤ `2M` transitions per
  replayed place" plus Galil's move inequality `k ≤ 4δ` into the `8M`
  coefficient of `alpha` in `GALIL_CLOCK.md` §"Cost between consecutive
  outputs".  `replay_cost_le_window` instantiates the move inequality on the
  real fallback window through `galil_move_of_contract`, so the remaining
  inputs are `hreplay` (the per-place tick bound; supplier:
  `GalilFallbackCost`, whose `fallback_ticks_le` already carries explicit tick
  counts, and `GalilScaffoldTopFallbackAll`'s `fallback_replay`/`replay_scan`
  for "no mismatch inside the FPP-selected palindrome") and `contract` (the
  search contract of `galil_move_of_contract`, i.e. obligation 3).

Finally `hd_of_interval_ledger` / `realtime_of_interval_ledger` show that the
interval form `d ≤ α·δ + β` these obligations feed is literally the `hd`
hypothesis of `realtime_of_predictable` with `c = α + β`.
-/

set_option autoImplicit false

namespace PalPeg.GalilLedger

/-! ## Obligation 1: the stage deadline -/

/-- The first-stage cost formula of `GALIL_CLOCK.md`: `q` finite instructions
per source transition, main lower bound `r`, copied window length `m`.  The
ceiling `⌈(327m+224)/q⌉` is written `(327m+224)/q + 1`. -/
def stageCost (q r m : ℕ) : ℕ := max r 1 + 2*r + 2*m + 7 + ((327*m + 224)/q + 1)

/-- **Obligation 1, uniform factor.**  With `ell = 8·max(r,1)` and
`m ≤ ell + 1`, the stage cost is at most `K·ell` for any `K ≥ 400`.  `400` is
the `q = 1` worst case (`3196/8`), so it holds for every quantum `q ≥ 1`;
`GALIL_CLOCK.md`'s `K = 10` is the `q = 64` specialisation. -/
theorem stageCost_le_factor (q K r m ell : ℕ) (hq : 0 < q) (hell : ell = 8 * max r 1)
    (hm : m ≤ ell + 1) (hK : 400 ≤ K) : stageCost q r m ≤ K * ell := by
  have hdiv : (327*m + 224)/q ≤ 327*m + 224 := Nat.div_le_self _ _
  have ha : 1 ≤ max r 1 := le_max_right _ _
  have hr : r ≤ max r 1 := le_max_left _ _
  have hbase : stageCost q r m ≤ 3196 * max r 1 := by
    unfold stageCost
    omega
  have hscale : 3196 * max r 1 ≤ (8*K) * max r 1 := Nat.mul_le_mul_right _ (by omega)
  have hKell : (8*K) * max r 1 = K * ell := by rw [hell]; ring
  omega

/-- **Obligation 1, the barrier.**  For `r ≥ 1` the stage span is `ell = 8r`,
the first barrier sits at radius `2r`, and the main entry radius satisfies
`3·rad ≤ 5·r` (the hypothesis `3·Rad ≤ 5·k` already exposed by the scaffold).
Choosing the match interval `M ≥ 24K` makes the stage cost fit in the
remaining slack `2r - rad` times `M`, i.e. the stage completes by its
barrier. -/
theorem stage_meets_barrier (q K M r m ell rad : ℕ) (hq : 0 < q) (hr : 1 ≤ r)
    (hell : ell = 8*r) (hm : m ≤ ell + 1) (hK : 400 ≤ K) (hM : 24*K ≤ M)
    (hentry : 3*rad ≤ 5*r) : stageCost q r m ≤ M * (2*r - rad) := by
  have hmax : max r 1 = r := max_eq_left hr
  have hbase : stageCost q r m ≤ 3196 * r := by
    have hdiv : (327*m + 224)/q ≤ 327*m + 224 := Nat.div_le_self _ _
    unfold stageCost
    rw [hmax]
    omega
  have hslack : r ≤ 3 * (2*r - rad) := by omega
  have hrate : 9600 * (2*r - rad) ≤ M * (2*r - rad) := Nat.mul_le_mul_right _ (by omega)
  have : 3196 * r ≤ 9600 * (2*r - rad) := by omega
  omega

/-- **Obligation 1 as used.**  The single machine input is `hcost`: the actual
number of source transitions a stage spends is bounded by the instruction-table
formula `stageCost`.  Supplier: `GalilScaffoldTimingCost.delay_calibration`
plus `GalilSegmentCount`. -/
theorem stage_deadline (q K M r m ell rad cost : ℕ) (hq : 0 < q) (hr : 1 ≤ r)
    (hell : ell = 8*r) (hm : m ≤ ell + 1) (hK : 400 ≤ K) (hM : 24*K ≤ M)
    (hentry : 3*rad ≤ 5*r) (hcost : cost ≤ stageCost q r m) :
    cost ≤ K * ell ∧ cost ≤ M * (2*r - rad) := by
  refine ⟨le_trans hcost ?_, le_trans hcost (stage_meets_barrier q K M r m ell rad hq hr hell hm hK hM hentry)⟩
  exact stageCost_le_factor q K r m ell hq (by rw [hell, max_eq_left hr]) hm hK

/-! ## Obligation 2: DP discovery and verifier catch-up -/

/-- The documented arrival/service model of the chain verifier's lag: each
transition clears one already-matched place, and at most one new place arrives
per `M` transitions (`n/M` arrivals in `n` transitions). -/
def vlag (M L : ℕ) : ℕ → ℕ
  | 0 => L
  | n+1 => (vlag M L n + ((n+1)/M - n/M)) - 1

/-- One step of the lag recursion, as pure arithmetic on the arrival counts
`A = n/M` and `B = (n+1)/M`. -/
theorem vlag_step (v L n A B : ℕ) (hA : A ≤ B) (hB : B ≤ A + 1)
    (h : v + n ≤ L + A ∨ v = 0) :
    (v + (B - A)) - 1 + (n + 1) ≤ L + B ∨ (v + (B - A)) - 1 = 0 := by
  omega

/-- The lag never exceeds "initial lag plus arrivals minus service" (and once
it reaches `0` it stays there, arrivals being at most one per step). -/
theorem vlag_le (M L : ℕ) : ∀ n, vlag M L n + n ≤ L + n/M ∨ vlag M L n = 0 := by
  intro n
  induction n with
  | zero => left; simp [vlag]
  | succ n ih =>
    have hA : n/M ≤ (n+1)/M := Nat.div_le_div_right (by omega)
    have hB : (n+1)/M ≤ n/M + 1 := by
      rcases Nat.eq_zero_or_pos M with hM | hM
      · simp [hM]
      · calc (n+1)/M ≤ (n+M)/M := Nat.div_le_div_right (by omega)
          _ = n/M + 1 := Nat.add_div_right n hM
    have h : vlag M L (n+1) = (vlag M L n + ((n+1)/M - n/M)) - 1 := rfl
    rw [h]
    exact vlag_step (vlag M L n) L n (n/M) ((n+1)/M) hA hB ih

/-- **Obligation 2, catch-up latency.**  With at most one new place per `M ≥ 2`
transitions, a lag of `L` places is cleared within `2L` transitions. -/
theorem vlag_zero (M L : ℕ) (hM : 2 ≤ M) : vlag M L (2*L) = 0 := by
  have hdiv : (2*L)/M ≤ (2*L)/2 := Nat.div_le_div_left hM (by omega)
  have h2 : (2*L)/2 = L := by omega
  rcases vlag_le M L (2*L) with h | h
  · omega
  · exact h

/-- **Obligation 2.**  The smallest DP found has step `h`; its discovery is
before radius `2h` (`hdisc`), copying the `h`-symbol semiperiod and returning
its head costs `2h+2` transitions, and the verifier then clears its lag
`lag0 ≤ 2h+2` at one place per transition against at most one new place per
`M` transitions.  With `M ≥ 8` the verifier has caught up (`actualLag = 0`)
and the radius has not yet reached `4h`.

The single machine input is `hmodel`: the real verifier lag is dominated by
the arrival/service model `vlag`.  Supplier: the `credit`/`lag`/`margin`
accounting of `GalilScaffoldChainVerifier`. -/
theorem verifier_catchup (M h disc lag0 : ℕ) (hM : 8 ≤ M) (hh : 1 ≤ h)
    (actualLag : ℕ → ℕ) (hmodel : ∀ n, actualLag n ≤ vlag M lag0 n)
    (hdisc : disc ≤ 2*h) (hlag0 : lag0 ≤ 2*h + 2) :
    actualLag (2*lag0) = 0 ∧ disc + (2*h + 2)/M + (2*lag0)/M ≤ 4*h := by
  refine ⟨?_, ?_⟩
  · have h0 := hmodel (2*lag0)
    have := vlag_zero M lag0 (by omega)
    omega
  · have hcopy : (2*h + 2)/M ≤ (2*h + 2)/8 := Nat.div_le_div_left hM (by omega)
    have hcatch : (2*lag0)/M ≤ (2*lag0)/8 := Nat.div_le_div_left hM (by omega)
    have hcatch' : (2*lag0)/8 ≤ (4*h + 4)/8 := Nat.div_le_div_right (by omega)
    omega

/-! ## Obligation 5: replay -/

/-- **Obligation 5.**  Replay costs at most `2M` transitions per replayed
place (including a possible confirmed-chain restart after each comparison),
there are `k` such places (the old radius), and Galil's move inequality gives
`k ≤ 4δ`; hence replay contributes at most `8M·δ`, the `8M` coefficient of
`alpha` in `GALIL_CLOCK.md`. -/
theorem replay_cost_le (M k δ replay : ℕ) (hreplay : replay ≤ 2*M*k) (hmove : k ≤ 4*δ) :
    replay ≤ 8*M*δ := by
  have h1 : 2*M*k ≤ 2*M*(4*δ) := Nat.mul_le_mul_left _ hmove
  have h2 : 2*M*(4*δ) = 8*M*δ := by ring
  omega

/-- **Obligation 5 on the real fallback window.**  `P` is the matched
palindrome of radius `k`, the fallback window is `x :: P`, and the centre
advance is `δ = k + 1 - chosenRadius (x :: P)`.  The move inequality is
discharged by `galil_move_of_contract`, so the remaining inputs are `hreplay`
(the per-place tick bound; supplier: `GalilFallbackCost`, together with
`fallback_replay`/`replay_scan` for "replay cannot mismatch inside the
FPP-selected palindrome") and `contract` (the search contract, i.e. ledger
obligation 3). -/
theorem replay_cost_le_window (M : ℕ) (x : Fin 3) (P : List (Fin 3)) (hP : IsPal P) (k replay : ℕ)
    (hlen : P.length = 2*k + 1) (hreplay : replay ≤ 2*M*k)
    (contract : ∀ p, 0 < p → HasPeriod P p → k < 2*p) :
    replay ≤ 8*M*(k + 1 - GalilScaffoldChainInputSupply.chosenRadius (x :: P)) :=
  replay_cost_le M k _ replay hreplay (galil_move_of_contract x P hP k hlen contract)

/-! ## Plugging the interval ledger into `realtime_of_predictable` -/

/-- The move coefficient of `GALIL_CLOCK.md` §"Cost between consecutive
outputs": `8M` for replay (obligation 5), `40` for copy/home/marker/rewind
(`5m + 6` with `m = 2k ≤ 8δ`), and `⌈8·296/q⌉` for the marked FPP. -/
def alphaCoef (q M : ℕ) : ℕ := 8*M + 40 + ((8*296)/q + 1)

/-- The residual overhead of an interval: the two new-place comparisons
(`4M`), two residual move overheads `6 + ⌈190/q⌉`, and two dispatch units. -/
def betaCoef (q M : ℕ) : ℕ := 4*M + 2*(6 + (190/q + 1)) + 2

/-- `c = α + β`, the FIFO service constant (`2c` per external input round). -/
def serviceRate (q M : ℕ) : ℕ := alphaCoef q M + betaCoef q M

/-- The interval ledger `d ≤ α·δ + β` is exactly the `hd` hypothesis of
`realtime_of_predictable` with `c = α + β`. -/
theorem hd_of_interval_ledger (q M : ℕ) (d C : ℕ → ℕ) (hmono : ∀ m, C m ≤ C (m+1))
    (hledger : ∀ m, d (m+1) ≤ alphaCoef q M * (C (m+1) - C m) + betaCoef q M) :
    ∀ m, (d (m+1) : ℤ) ≤ (serviceRate q M : ℤ) * ((C (m+1) : ℤ) - C m + 1) := by
  intro m
  have hsub : ((C (m+1) - C m : ℕ) : ℤ) = (C (m+1) : ℤ) - C m := by
    have := hmono m
    push_cast [this]
    ring
  have hl : (d (m+1) : ℤ) ≤ (alphaCoef q M : ℤ) * ((C (m+1) : ℤ) - C m) + betaCoef q M := by
    have := hledger m
    have hcast : (d (m+1) : ℤ) ≤ (alphaCoef q M : ℤ) * ((C (m+1) - C m : ℕ) : ℤ) + betaCoef q M := by
      exact_mod_cast this
    rwa [hsub] at hcast
  have hδ : (0 : ℤ) ≤ (C (m+1) : ℤ) - C m := by
    have := hmono m
    have : (C m : ℤ) ≤ C (m+1) := by exact_mod_cast this
    linarith
  have hβ : (0 : ℤ) ≤ (betaCoef q M : ℤ) := by positivity
  have hα : (0 : ℤ) ≤ (alphaCoef q M : ℤ) := by positivity
  have hc : (serviceRate q M : ℤ) = (alphaCoef q M : ℤ) + betaCoef q M := by
    unfold serviceRate
    push_cast
    ring
  rw [hc]
  nlinarith

/-- **The ledger closes the real-time argument.**  With the centre contracts
and the interval ledger, the FIFO server of rate `2c` has no backlog at any
round with a positive answer. -/
theorem realtime_of_interval_ledger (q M : ℕ) (d C : ℕ → ℕ) (hmono : ∀ m, C m ≤ C (m+1))
    (hC : ∀ m, m ≤ C m)
    (hledger : ∀ m, d (m+1) ≤ alphaCoef q M * (C (m+1) - C m) + betaCoef q M)
    {i : ℕ} (hi : C i = i) : Predictability.backlog d (serviceRate q M) i = 0 :=
  Predictability.realtime_of_predictable d C (serviceRate q M) hmono hC
    (hd_of_interval_ledger q M d C hmono hledger) hi

#print axioms stageCost_le_factor
#print axioms stage_meets_barrier
#print axioms stage_deadline
#print axioms vlag_step
#print axioms vlag_le
#print axioms vlag_zero
#print axioms verifier_catchup
#print axioms replay_cost_le
#print axioms replay_cost_le_window
#print axioms hd_of_interval_ledger
#print axioms realtime_of_interval_ledger

end PalPeg.GalilLedger
