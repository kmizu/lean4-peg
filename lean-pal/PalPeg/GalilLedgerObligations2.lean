import PalPeg.GalilLedgerObligations
import PalPeg.GalilFallbackCost
import PalPeg.GalilStructuredSkeleton

/-!
# Real-time ledger obligations 4, 7 and 8

`lean-pal/ASSEMBLY_PLAN.md` §"実時間台帳の紙スケッチ" lists eight obligations.
Obligations 1, 2 and 5 are `PalPeg.GalilLedger` (`GalilLedgerObligations.lean`),
obligation 3 is `PalPeg.GalilSearchContract`, obligation 6 (the centre
invariant) is `MInv` (`GalilLiveCentre*`).  This module does the three that
were left:

* **Obligation 4 (fallback cost).**  `fallbackWindowCost q m = 5m + 6 +
  ⌈(296m+190)/q⌉` is the resource ledger of `FPP_COST.md`
  (copy/home/marker/rewind plus the marked FPP) on a fallback window of length
  `m`.  `fallbackWindowCost_le_interval` turns it into the `40 + ⌈8·296/q⌉`
  share of `alphaCoef` and the `6 + ⌈190/q⌉ + 1` share of `betaCoef` using
  `m = 2k` and Galil's move inequality `k ≤ 4δ`.  `fallback_cost_move` is the
  *machine-side* version: it re-exports `GalilFallbackCost.fallback_ticks_le`
  with its tick bound rewritten in terms of the centre advance `δ`, so on the
  real fallback window this obligation needs **no** cost hypothesis at all —
  only the window-length bookkeeping and obligation 3.

* **Obligation 7 (telescoping).**  `work_le_interval` telescopes the interval
  ledger over a busy window, `telescope_busy` is the `Σd ≤ 2c(i−j)+c` of the
  plan, and `realtime_of_telescope` closes `backlog = 0` through
  `Predictability.backlog_zero_of_bounds` entirely inside `ℕ` (the existing
  `realtime_of_interval_ledger` goes through `ℤ`).  No hypotheses beyond the
  ledger and the two centre contracts.

* **Obligation 8 (SCA wrapper).**  `buffer_transparent`: at a round whose
  centre sits at the input, the FIFO buffer/dispatcher of rate `2c` is the
  identity on the source's answer.  `pal_in_peg_of_galil_buffered` is the
  assembly: with the ledger in hand, the buffered wrapper discharges the
  `H_realize` half of `GalilStructuredSkeleton.pal_in_peg_of_galil`, leaving
  `H_run` (the scaffold reaches a refreshed report point) and `H_buffer` (the
  machine *is* the buffered scaffold) as the only machine inputs.

Finally `hledger_of_obligations` assembles obligations 1–5, 7, 8 into the
`hledger` premise of `hd_of_interval_ledger` / `realtime_of_interval_ledger`
under an explicit per-interval decomposition of the work.
-/

set_option autoImplicit false

namespace PalPeg.GalilLedger2

open PalPeg PalPeg.GalilLedger PalPeg.Predictability PalPeg.GalilScaffoldTop
  PalPeg.GalilScaffoldController PalPeg.GalilScaffoldChainInputSupply

/-! ## Two ceiling lemmas -/

/-- `⌈a·δ/q⌉ ≤ ⌈a/q⌉·δ` in the `x/q + 1` spelling of the ceiling. -/
theorem div_mul_le (q a δ : ℕ) (hq : 0 < q) : (a*δ)/q ≤ (a/q + 1)*δ := by
  have ha : a ≤ q*(a/q + 1) := by
    have h := Nat.lt_div_mul_add (a := a) hq
    have e : q*(a/q + 1) = a/q*q + q := by ring
    omega
  have h : a*δ ≤ q*((a/q + 1)*δ) := by
    calc a*δ ≤ (q*(a/q + 1))*δ := Nat.mul_le_mul_right _ ha
      _ = q*((a/q + 1)*δ) := by ring
  calc (a*δ)/q ≤ (q*((a/q + 1)*δ))/q := Nat.div_le_div_right h
    _ = (a/q + 1)*δ := Nat.mul_div_cancel_left _ hq

/-- Splitting a ceiling over a sum costs one unit. -/
theorem add_div_le (q a b : ℕ) (hq : 0 < q) : (a + b)/q ≤ a/q + b/q + 1 := by
  rw [Nat.add_div hq]
  split <;> omega

/-! ## Obligation 4: the fallback cost -/

/-- The resource ledger of `FPP_COST.md` for a fallback window of length `m`:
the four linear scans copy/home/marker/rewind cost `5m + 6`, and the marked FPP
costs `⌈(296m+190)/q⌉` (written `(296m+190)/q + 1`). -/
def fallbackWindowCost (q m : ℕ) : ℕ := 5*m + 6 + ((296*m + 190)/q + 1)

/-- **Obligation 4, in interval form.**  On a fallback window of length `2k`
(the matched palindrome of radius `k` plus its mirror), Galil's move inequality
`k ≤ 4δ` turns the fallback cost into exactly the `40 + ⌈8·296/q⌉` share of
`alphaCoef` and the `6 + ⌈190/q⌉ + 1` share of `betaCoef`. -/
theorem fallbackWindowCost_le_interval (q k δ : ℕ) (hq : 0 < q) (hmove : k ≤ 4*δ) :
    fallbackWindowCost q (2*k) ≤ (40 + ((8*296)/q + 1))*δ + (6 + (190/q + 1) + 1) := by
  have hsplit : (296*(2*k) + 190)/q ≤ (296*(2*k))/q + 190/q + 1 := add_div_le q _ _ hq
  have hk : 296*(2*k) ≤ (8*296)*δ := by omega
  have hmono : (296*(2*k))/q ≤ ((8*296)*δ)/q := Nat.div_le_div_right hk
  have hceil : ((8*296)*δ)/q ≤ ((8*296)/q + 1)*δ := div_mul_le q (8*296) δ hq
  have hlin : 5*(2*k) ≤ 40*δ := by omega
  have hd : (40 + ((8*296)/q + 1))*δ = 40*δ + ((8*296)/q + 1)*δ := by ring
  unfold fallbackWindowCost
  omega

/-- **Obligation 4 on the real fallback window.**  `GalilFallbackCost.fallback_ticks_le`
already carries an explicit tick count for the whole copy → home → FPP →
markEnd → choose → rewind chain; with the window length `ℓ+1 = 2k+2` and the
move inequality `k ≤ 4δ` (obligation 3, `galil_move_of_contract`) that count is
an affine function of the centre advance.  No cost hypothesis is needed. -/
theorem fallback_cost_move (P : Shared) (q : ℕ) (hq : 0 < q) (first : Fin 9)
    (h7 : first ≠ 7) (h8 : first ≠ 8) (delay : ℕ) (c : Control) (hm : c.mode = .copy)
    (s : GalilVM) (hi : ShiftIdle s)
    (old : GalilScaffoldControl.Machine 9) (p : GalilScaffoldPlace.Place)
    (length : GalilScaffoldCounter.Counter) (hc : GalilScaffoldCounter.Canonical length)
    (ℓ : ℕ) (hv : GalilScaffoldCounter.value length = ℓ)
    (hs : s.fpp = FppControl.beginFallback old p length)
    (hne : (GalilScaffoldPlace.stream p) ≠ [])
    (heven : ((GalilScaffoldPlace.stream p).take (ℓ+1)).length % 2 = 0)
    (k δ : ℕ) (hwin : ℓ + 1 = 2*k + 2) (hmove : k ≤ 4*δ) :
    let w := (GalilScaffoldPlace.stream p).take (ℓ+1)
    let r := chosenRadius w
    ∃ (n : ℕ) (y : RewindVM),
      Steps (galilFrameS P q first) delay n ⟨c, s⟩
        ⟨{c with mode := .replayStart, odd := oddAt false (w.length - (2*r+1)), pair := pairAt (2*r)},
          rewindLens.set s y⟩ ∧
      n ≤ 12704*δ + 4012 := by
  intro w r
  obtain ⟨n, y, hsteps, hb, _⟩ :=
    fallback_ticks_le P q hq first h7 h8 delay c hm s hi old p length hc ℓ hv hs hne heven
  exact ⟨n, y, hsteps, by omega⟩


/-! ## Obligation 7: telescoping over a busy window -/

/-- Monotonicity of the centre sequence, from the one-step contract. -/
theorem centre_mono {C : ℕ → ℕ} (hmono : ∀ m, C m ≤ C (m+1)) : ∀ a b, a ≤ b → C a ≤ C b := by
  intro a b hab
  induction b with
  | zero => have : a = 0 := by omega
            subst this; exact le_rfl
  | succ b ih =>
    rcases Nat.lt_or_ge a (b+1) with h | h
    · exact le_trans (ih (by omega)) (hmono b)
    · have : a = b+1 := by omega
      subst this; exact le_rfl

/-- **Obligation 7, the telescoping itself.**  The interval ledger
`d ≤ α·δ + β` sums over a window `j+1 .. i` to `α·(C i − C j) + β·(i − j)`:
the centre advances telescope exactly. -/
theorem work_le_interval (q M : ℕ) (d C : ℕ → ℕ) (hmono : ∀ m, C m ≤ C (m+1))
    (hledger : ∀ m, d (m+1) ≤ alphaCoef q M * (C (m+1) - C m) + betaCoef q M) :
    ∀ i j, j ≤ i → work d j i ≤ alphaCoef q M * (C i - C j) + betaCoef q M * (i - j) := by
  intro i
  induction i with
  | zero => intro j h
            have : j = 0 := by omega
            subst this; simp [work_self]
  | succ i ih =>
    intro j h
    rcases Nat.eq_or_lt_of_le h with heq | hlt
    · subst heq; simp [work_self]
    · have hij : j ≤ i := by omega
      have hIH := ih j hij
      have hstep := hledger i
      rw [work_succ d hij]
      have hCji : C j ≤ C i := centre_mono hmono j i hij
      have hCi : C i ≤ C (i+1) := hmono i
      have e1 : (C i - C j) + (C (i+1) - C i) = C (i+1) - C j := by omega
      have e2 : (i - j) + 1 = (i+1) - j := by omega
      have ea : alphaCoef q M * (C i - C j) + alphaCoef q M * (C (i+1) - C i)
          = alphaCoef q M * (C (i+1) - C j) := by
        rw [← Nat.mul_add, e1]
      have eb : betaCoef q M * (i - j) + betaCoef q M * 1 = betaCoef q M * ((i+1) - j) := by
        rw [← Nat.mul_add, e2]
      have eb' : betaCoef q M * 1 = betaCoef q M := by ring
      omega

/-- **Obligation 7 as stated in the plan.**  In a busy window ending at a round
whose answer is positive (`C i = i`), the arriving work is at most
`2c·(i−j) + c` for the service constant `c = α + β`. -/
theorem telescope_busy (q M : ℕ) (d C : ℕ → ℕ) (hmono : ∀ m, C m ≤ C (m+1))
    (hC : ∀ m, m ≤ C m)
    (hledger : ∀ m, d (m+1) ≤ alphaCoef q M * (C (m+1) - C m) + betaCoef q M)
    {i : ℕ} (hi : C i = i) :
    ∀ j, j ≤ i → work d j i ≤ 2*(serviceRate q M)*(i - j) + serviceRate q M := by
  intro j hj
  have hw := work_le_interval q M d C hmono hledger i j hj
  have hCj : j ≤ C j := hC j
  have hδ : C i - C j ≤ i - j := by omega
  have h1 : alphaCoef q M * (C i - C j) ≤ alphaCoef q M * (i - j) := Nat.mul_le_mul_left _ hδ
  have h2 : alphaCoef q M * (i - j) + betaCoef q M * (i - j) = serviceRate q M * (i - j) := by
    unfold serviceRate; ring
  have h3 : serviceRate q M * (i - j) ≤ 2*(serviceRate q M)*(i - j) := by
    have : serviceRate q M ≤ 2*(serviceRate q M) := by omega
    exact Nat.mul_le_mul_right _ this
  omega

/-- **Obligation 7 closes real time, inside `ℕ`.**  Same conclusion as
`realtime_of_interval_ledger` but through `backlog_zero_of_bounds` and the
telescoped window bound, with no cast to `ℤ`. -/
theorem realtime_of_telescope (q M : ℕ) (d C : ℕ → ℕ) (hmono : ∀ m, C m ≤ C (m+1))
    (hC : ∀ m, m ≤ C m)
    (hledger : ∀ m, d (m+1) ≤ alphaCoef q M * (C (m+1) - C m) + betaCoef q M)
    {i : ℕ} (hi : C i = i) : backlog d (serviceRate q M) i = 0 := by
  refine backlog_zero_of_bounds d (serviceRate q M) i (fun j hj => ?_)
  have hw := work_le_interval q M d C hmono hledger i j hj
  have hCj : j ≤ C j := hC j
  have hδ : C i - C j ≤ i - j := by omega
  have h1 : alphaCoef q M * (C i - C j) ≤ alphaCoef q M * (i - j) := Nat.mul_le_mul_left _ hδ
  have h2 : alphaCoef q M * (i - j) + betaCoef q M * (i - j) = serviceRate q M * (i - j) := by
    unfold serviceRate; ring
  have h3 : serviceRate q M * (i - j) ≤ 2*(serviceRate q M)*(i - j) := by
    have : serviceRate q M ≤ 2*(serviceRate q M) := by omega
    exact Nat.mul_le_mul_right _ this
  omega


/-! ## Obligation 8: the SCA wrapper (buffer and dispatcher) -/

/-- **Obligation 8, the buffer is transparent.**  The wrapper answers the
source's flag when the FIFO buffer is caught up and rejects while behind; the
ledger says it is caught up at every round whose centre sits at the input, so
there the wrapper is the identity. -/
theorem buffer_transparent (q M : ℕ) (d C : ℕ → ℕ) (hmono : ∀ m, C m ≤ C (m+1))
    (hC : ∀ m, m ≤ C m)
    (hledger : ∀ m, d (m+1) ≤ alphaCoef q M * (C (m+1) - C m) + betaCoef q M)
    (out : Bool) {i : ℕ} (hi : C i = i) :
    (if backlog d (serviceRate q M) i = 0 then out else false) = out := by
  rw [if_pos (realtime_of_telescope q M d C hmono hC hledger hi)]

/-- **Obligation 8, assembled.**  The buffered/dispatched wrapper discharges
the `H_realize` half of `GalilStructuredSkeleton.pal_in_peg_of_galil`: given the
interval ledger (obligations 1–5, 7), the centre contracts, obligation 6 in the
form `hcentre` (a positive answer has the centre at the input), the scaffold
run `H_run`, and the single machine input `H_buffer` (the machine *is* the
scaffold read through the FIFO buffer of rate `2c`), `PAL ∈ PEG` follows. -/
theorem pal_in_peg_of_galil_buffered {Q Γ : Type} [Fintype Q] [DecidableEq Q]
    [Fintype Γ] [DecidableEq Γ] {t B : ℕ} (hB : 0 < B)
    (Mach : PalPeg.Program.StructuredMachine (Fin 2) Q Γ t B)
    (Pof : List (Fin 2) → Shared) (qof : List (Fin 2) → ℕ)
    (firstOf : List (Fin 2) → Fin 9) (delay : ℕ)
    (H_letter : ∀ w : List (Fin 2), (Pof w).onLetter = onLetterVM w)
    (H_first : ∀ w : List (Fin 2), (Pof w).leftFirst = leftFirstVM)
    (H_run : ∀ w : List (Fin 2), 0 < w.length → ∃ y : State GalilVM,
      GalilStructuredSkeleton.ScaffoldRun Pof qof firstOf delay w y ∧
      GalilStructuredSkeleton.ReportPoint w y ∧
      GalilStructuredSkeleton.Refreshed (Pof w) (qof w) (firstOf w) y)
    (q M : ℕ) (d C : List (Fin 2) → ℕ → ℕ)
    (hmono : ∀ w m, C w m ≤ C w (m+1)) (hC : ∀ w m, m ≤ C w m)
    (hledger : ∀ w m, d w (m+1) ≤ alphaCoef q M * (C w (m+1) - C w m) + betaCoef q M)
    (hcentre : ∀ w : List (Fin 2), w ∈ PAL → C w w.length = w.length)
    (H_buffer : ∀ w : List (Fin 2), 0 < w.length → ∀ y : State GalilVM,
      GalilStructuredSkeleton.ScaffoldRun Pof qof firstOf delay w y →
      GalilStructuredSkeleton.ReportPoint w y →
      (Mach.SAccepts w ↔
        (if backlog (d w) (serviceRate q M) w.length = 0 then y.ctl.output else false) = true))
    (H_empty : Mach.SAccepts []) : PegSeparation.RecognizedByTotalPEG PAL := by
  refine GalilStructuredSkeleton.pal_in_peg_of_galil hB Mach Pof qof firstOf delay
    H_letter H_first ?_ H_empty
  intro w hw
  obtain ⟨y, hrun, hrp, hfr⟩ := H_run w hw
  obtain ⟨n, x, hx, hsteps⟩ := hrun
  refine ⟨n, x, y, hx, hsteps, hrp, hfr, ?_⟩
  have hb := H_buffer w hw y ⟨n, x, hx, hsteps⟩ hrp
  have hpal := GalilStructuredSkeleton.output_iff_pal w (Pof w) (H_letter w) (H_first w)
    (qof w) (firstOf w) y hrp hfr
  by_cases hz : backlog (d w) (serviceRate q M) w.length = 0
  · rw [if_pos hz] at hb; exact hb
  · rw [if_neg hz] at hb
    constructor
    · intro h
      exact absurd (hb.mp h) (by simp)
    · intro h
      exact absurd (realtime_of_telescope q M (d w) (C w) (hmono w) (hC w) (hledger w)
        (hcentre w (hpal.mp h))) hz

/-! ## The interval ledger from obligations 1-5, 7, 8 -/

/-- The per-interval arithmetic behind `hledger_of_obligations`, with the two
ceilings `X = ⌈8·296/q⌉ - 1` and `Y = ⌈190/q⌉ - 1` abstracted as opaque
naturals. -/
theorem ledger_sum (A B X Y M δ dm rep ws fp cm dp : ℕ)
    (hA : A = 8*M*δ + (40 + (X+1))*δ) (hB : B = 4*M + 2*(6 + (Y+1)) + 2)
    (hdec : dm = rep + ws + fp + cm + dp) (hrep : rep ≤ 8*M*δ)
    (hfb : ws + fp ≤ (40 + (X+1))*δ + (6 + (Y+1) + 1))
    (hcm : cm ≤ 4*M) (hdp : dp ≤ 2) : dm ≤ A + B := by
  omega

/-- **The assembly.**  Under the per-interval decomposition `hdecomp` — the
work of the interval between outputs `m` and `m+1` splits into the *replay* of
the old radius (obligation 5), the *window scans* copy/home/marker/rewind and
the *marked FPP* of the fallback (obligation 4), the two *new-place comparisons*
of the DP/verifier interface (obligations 1 and 2) and the *dispatch* units of
the SCA wrapper (obligation 8) — together with Galil's move inequality
(obligation 3) and the per-summand bounds, the work ledger
`d ≤ alphaCoef·δ + betaCoef` holds, which is exactly the `hledger` premise of
`hd_of_interval_ledger` and `realtime_of_interval_ledger` (obligation 7). -/
theorem hledger_of_obligations (q M : ℕ) (hq : 0 < q)
    (d C k replay windowScan fppCost compare dispatch : ℕ → ℕ)
    (hdecomp : ∀ m, d (m+1) = replay m + windowScan m + fppCost m + compare m + dispatch m)
    (hmove : ∀ m, k m ≤ 4*(C (m+1) - C m))
    (hreplay : ∀ m, replay m ≤ 2*M*(k m))
    (hwindow : ∀ m, windowScan m ≤ 5*(2*(k m)) + 6)
    (hfpp : ∀ m, fppCost m ≤ (296*(2*(k m)) + 190)/q + 1)
    (hcompare : ∀ m, compare m ≤ 4*M)
    (hdispatch : ∀ m, dispatch m ≤ 2) :
    ∀ m, d (m+1) ≤ alphaCoef q M * (C (m+1) - C m) + betaCoef q M := by
  intro m
  have hfb : windowScan m + fppCost m
      ≤ (40 + ((8*296)/q + 1))*(C (m+1) - C m) + (6 + (190/q + 1) + 1) := by
    have h := fallbackWindowCost_le_interval q (k m) (C (m+1) - C m) hq (hmove m)
    unfold fallbackWindowCost at h
    have h1 := hwindow m
    have h2 := hfpp m
    omega
  refine ledger_sum (alphaCoef q M * (C (m+1) - C m)) (betaCoef q M) ((8*296)/q) (190/q) M
    (C (m+1) - C m) (d (m+1)) (replay m) (windowScan m) (fppCost m) (compare m) (dispatch m)
    ?_ rfl (hdecomp m)
    (replay_cost_le M (k m) (C (m+1) - C m) (replay m) (hreplay m) (hmove m))
    hfb (hcompare m) (hdispatch m)
  unfold alphaCoef
  ring

#print axioms div_mul_le
#print axioms add_div_le
#print axioms fallbackWindowCost_le_interval
#print axioms fallback_cost_move
#print axioms centre_mono
#print axioms work_le_interval
#print axioms telescope_busy
#print axioms realtime_of_telescope
#print axioms buffer_transparent
#print axioms pal_in_peg_of_galil_buffered
#print axioms ledger_sum
#print axioms hledger_of_obligations

end PalPeg.GalilLedger2
