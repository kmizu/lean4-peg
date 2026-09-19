import PalPeg.GalilTrailChain
import PalPeg.GalilTrailScan

/-!
# The lag ledger, `ChainBudget`, and `H_trailF`

`GalilTrailChain.ChainBudget` is the place-arithmetic obligation that the chain half
of `GalilTrailProof.TrailF` leaves open at the *target* of every tick.  Its two
non-trivial fields are `pos` (the verifier is no further right than the checkpoint
place `2(m+1)-1`) and `lagPos` (one place further left on a positive-lag watch).
Both are consequences of one ledger: **the verifier trails the scan head `R` by its
lag**.

This file carries that ledger — `LagLe`, `position verifier + lag ≤ position R` on a
canonical non-negative lag — along every tick of `galilFrameS`, reads `ChainBudget`
off it, and assembles `H_trailF` from `GalilTrailScan.h_trailF_of_parts`,
`GalilTrailChain.trailChain_scanTick` and `GalilTrailChain.trailF_of_verF`.

The ledger is stated as an inequality, not as `position verifier + lag = position R`.
The two agree on the real machine, but the inequality is the half that travels with
*no* `canRight` side condition on the verifier: a right move of a place head never
gains more than one place (`position_right_le`), whichever of the four shapes of
`GalilScaffoldChainVerifier.right` it takes.  That is what lets `beginShiftVM`'s
immediate consume — the one verifier move in the frame whose `canRight` the
transition does not hand over (`Good`/`BreakStep` supply it everywhere else) — go
through unassisted.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace PalPeg.GalilTrailAssembly

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open PalPeg.GalilThrottledRun PalPeg.GalilTrailProof PalPeg.GalilFinalAssembly
open PalPeg.GalilTrailChain PalPeg.GalilTrailScan

abbrev PH := GalilScaffoldInputHead.PlaceHead
abbrev Ctr := GalilScaffoldCounter.Counter

/-! ## 1. The verifier and its lag -/

/-- The chain's trailing pair: its verifier together with the lag counter that says
how far behind the scan head `R` the verifier is.  The same case split as
`GalilThrottledRun.verOf` and `GalilChainCoupling.SumRel`. -/
def lagOf : ChainVM → Option (PH × Ctr)
  | .idle => none
  | .copy _ _ _ _ lag _ ver => some (ver, lag)
  | .back _ _ lag _ ver => some (ver, lag)
  | .watch w => some (w.machine.verifier, w.lag)
  | .broken w => some (w.machine.verifier, GalilScaffoldCounter.reset)

theorem exists_lag {x : ChainVM} {p : PH} (h : verOf x = some p) :
    ∃ lag, lagOf x = some (p, lag) := by
  cases x with
  | idle => exact absurd h (by simp [verOf])
  | copy _ _ _ _ lag _ ver =>
    obtain rfl : ver = p := Option.some.inj h
    exact ⟨lag, rfl⟩
  | back _ _ lag _ ver =>
    obtain rfl : ver = p := Option.some.inj h
    exact ⟨lag, rfl⟩
  | watch w =>
    obtain rfl : w.machine.verifier = p := Option.some.inj h
    exact ⟨w.lag, rfl⟩
  | broken w =>
    obtain rfl : w.machine.verifier = p := Option.some.inj h
    exact ⟨GalilScaffoldCounter.reset, rfl⟩

/-! ## 2. A right move gains at most one place -/

/-- **The unconditional half of `GalilFrontMono.right_sane`.**  All four shapes of
`GalilScaffoldChainVerifier.right` (raise the gap, pop the right stack, pop the
incoming FIFO, or — with `canRight` false — stand still and drop the gap) advance the
place by at most one.  Only the equality needs `canRight`. -/
theorem position_right_le (p : PH) :
    position (GalilScaffoldChainVerifier.right p) ≤ position p + 1 := by
  rcases p with ⟨⟨f, ls, rs, qs⟩, g⟩
  cases g with
  | false =>
    simp [position, GalilScaffoldChainVerifier.right]
    omega
  | true =>
    cases rs with
    | cons a rs =>
      simp [position, GalilScaffoldChainVerifier.right, GalilScaffoldChainVerifier.headRight,
        GalilScaffoldInputTrace.moveRight]
      omega
    | nil =>
      cases qs with
      | nil =>
        simp [position, GalilScaffoldChainVerifier.right, GalilScaffoldChainVerifier.headRight,
          GalilScaffoldInputTrace.moveRight]
        omega
      | cons a qs =>
        simp [position, GalilScaffoldChainVerifier.right, GalilScaffoldChainVerifier.headRight,
          GalilScaffoldInputTrace.moveRight]
        omega

#print axioms position_right_le

/-! ## 3. The ledger -/

/-- **The lag ledger.**  The chain verifier trails the place `r` by its lag: the lag
counter is canonical and non-negative, and `position verifier + lag ≤ r`.  On the real
machine this is an equality (`GalilChainCoupling.SumRel` composed with the scan
invariant `position C + radius = position R`); the `≤` half is the one that needs no
`canRight`. -/
structure LagLe (x : ChainVM) (r : ℕ) : Prop where
  canon : ∀ p lag, lagOf x = some (p, lag) → GalilScaffoldCounter.Canonical lag
  nonneg : ∀ p lag, lagOf x = some (p, lag) → 0 ≤ GalilScaffoldCounter.value lag
  le : ∀ p lag, lagOf x = some (p, lag) →
    (position p : ℤ) + GalilScaffoldCounter.value lag ≤ r

theorem lagLe_get {x : ChainVM} {r : ℕ} {p : PH} {lag : Ctr} (h : LagLe x r)
    (hx : lagOf x = some (p, lag)) :
    GalilScaffoldCounter.Canonical lag ∧ 0 ≤ GalilScaffoldCounter.value lag ∧
      (position p : ℤ) + GalilScaffoldCounter.value lag ≤ r :=
  ⟨h.canon p lag hx, h.nonneg p lag hx, h.le p lag hx⟩

theorem lagLe_of_some {z : ChainVM} {r : ℕ} {p : PH} {lag : Ctr}
    (hz : lagOf z = some (p, lag)) (hc : GalilScaffoldCounter.Canonical lag)
    (hn : 0 ≤ GalilScaffoldCounter.value lag)
    (hl : (position p : ℤ) + GalilScaffoldCounter.value lag ≤ r) : LagLe z r := by
  have key : ∀ p' lag', lagOf z = some (p', lag') → p' = p ∧ lag' = lag := by
    intro p' lag' h
    have he := Option.some.inj (h.symm.trans hz)
    exact ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩
  refine ⟨fun p' lag' h => ?_, fun p' lag' h => ?_, fun p' lag' h => ?_⟩
  · obtain ⟨rfl, rfl⟩ := key p' lag' h; exact hc
  · obtain ⟨rfl, rfl⟩ := key p' lag' h; exact hn
  · obtain ⟨rfl, rfl⟩ := key p' lag' h; exact hl

/-- **The equality ledger implies the inequality one.**  This is the bridge to
`GalilChainCoupling.SumRel` (`lag = radius` in copy/back, `distance + lag = radius` on
an unbroken watch) composed with the scan invariant `position C + radius = position R`:
whoever proves the equality form gets `LagLe` for free. -/
theorem lagLe_of_eq {x : ChainVM} {r : ℕ}
    (h : ∀ p lag, lagOf x = some (p, lag) → GalilScaffoldCounter.Canonical lag ∧
      0 ≤ GalilScaffoldCounter.value lag ∧
      (position p : ℤ) + GalilScaffoldCounter.value lag = r) : LagLe x r :=
  ⟨fun p lag hp => (h p lag hp).1, fun p lag hp => (h p lag hp).2.1,
    fun p lag hp => le_of_eq (h p lag hp).2.2⟩

theorem lagLe_idle (r : ℕ) : LagLe .idle r :=
  ⟨fun p lag h => absurd h (by simp [lagOf]), fun p lag h => absurd h (by simp [lagOf]),
    fun p lag h => absurd h (by simp [lagOf])⟩

/-- **A break keeps the ledger.**  The verifier moved one place right and the lag was
positive, so `position (right ver) ≤ position ver + 1 ≤ position ver + lag ≤ r`; the
broken chain's ledger reads its lag as `reset`. -/
theorem lagLe_break {w : GalilScaffoldChainWatch.State} {r : ℕ} (hx : LagLe (.watch w) r)
    (hp : GalilScaffoldCounter.positive w.lag = true) :
    LagLe (.broken ⟨⟨GalilScaffoldChainVerifier.right w.machine.verifier, w.machine.control⟩,
      w.lag, w.margin⟩) r := by
  obtain ⟨hc, hn, hl⟩ := lagLe_get hx (p := w.machine.verifier) (lag := w.lag) rfl
  have h1 : 0 < GalilScaffoldCounter.value w.lag :=
    (GalilScaffoldCounter.positive_iff w.lag hc).mp hp
  have hr := position_right_le w.machine.verifier
  refine ⟨?_, ?_, ?_⟩
  · intro p lag h; injection h with h; injection h with hp' hl'; subst hl'; exact Or.inl rfl
  · intro p lag h; injection h with h; injection h with hp' hl'; subst hl'; exact le_rfl
  · intro p lag h; injection h with h; injection h with hp' hl'; subst hp'; subst hl'
    have h0 : GalilScaffoldCounter.value GalilScaffoldCounter.reset = 0 := rfl
    show (position (GalilScaffoldChainVerifier.right w.machine.verifier) : ℤ) +
      GalilScaffoldCounter.value GalilScaffoldCounter.reset ≤ r
    rw [h0]
    omega

/-- **The lag-zero break keeps the ledger one place further** (the verifier consumed). -/
theorem lagLe_breaks {w w' : GalilScaffoldChainWatch.State} {r : ℕ} (hx : LagLe (.watch w) r)
    (hb : BreakStep w w') : LagLe (.broken w') (r + 1) := by
  obtain ⟨-, -, -, -, -, rfl⟩ := hb
  obtain ⟨hc, hn, hl⟩ := lagLe_get hx (p := w.machine.verifier) (lag := w.lag) rfl
  have hr := position_right_le w.machine.verifier
  refine ⟨?_, ?_, ?_⟩
  · intro p lag h; injection h with h; injection h with hp' hl'; subst hl'; exact Or.inl rfl
  · intro p lag h; injection h with h; injection h with hp' hl'; subst hl'; exact le_rfl
  · intro p lag h; injection h with h; injection h with hp' hl'; subst hp'; subst hl'
    have h0 : GalilScaffoldCounter.value GalilScaffoldCounter.reset = 0 := rfl
    show (position (GalilScaffoldChainVerifier.right w.machine.verifier) : ℤ) +
      GalilScaffoldCounter.value GalilScaffoldCounter.reset ≤ r + 1
    rw [h0]
    omega

theorem lagLe_of_idle {x : ChainVM} {r : ℕ} (h : x = .idle) : LagLe x r := by
  rw [h]; exact lagLe_idle r

theorem lagLe_mono {x : ChainVM} {r r' : ℕ} (h : LagLe x r) (hr : r ≤ r') : LagLe x r' :=
  ⟨h.canon, h.nonneg, fun p lag hp => by have := h.le p lag hp; omega⟩

theorem lagLe_congr {x z : ChainVM} {r : ℕ} (h : LagLe x r) (hz : lagOf z = lagOf x) :
    LagLe z r :=
  ⟨fun p lag hp => h.canon p lag (hz ▸ hp), fun p lag hp => h.nonneg p lag (hz ▸ hp),
    fun p lag hp => h.le p lag (hz ▸ hp)⟩

/-- The verifier stays, the lag grows by one: the trailed place grows by one too (a
matched comparison on a chain that does not catch up). -/
theorem lagLe_inc {x z : ChainVM} {r : ℕ} {p : PH} {lag : Ctr}
    (hx : lagOf x = some (p, lag)) (hz : lagOf z = some (p, GalilScaffoldCounter.inc lag))
    (h : LagLe x r) : LagLe z (r + 1) := by
  obtain ⟨hc, hn, hl⟩ := lagLe_get h hx
  have hv := GalilScaffoldCounter.inc_value lag
  exact lagLe_of_some hz (GalilScaffoldCounter.inc_canonical _ hc) (by omega) (by omega)

/-- The verifier moves one place right, the lag stays: the trailed place grows by one
(the immediate consume of a matched comparison, a break, `beginShiftVM`). -/
theorem lagLe_right {x z : ChainVM} {r : ℕ} {p : PH} {lag : Ctr}
    (hx : lagOf x = some (p, lag))
    (hz : lagOf z = some (GalilScaffoldChainVerifier.right p, lag)) (h : LagLe x r) :
    LagLe z (r + 1) := by
  obtain ⟨hc, hn, hl⟩ := lagLe_get h hx
  have hp := position_right_le p
  exact lagLe_of_some hz hc hn (by omega)

/-- The verifier moves one place right and a positive lag is decremented: the trailed
place is unchanged (the watch's background consume). -/
theorem lagLe_catch {x z : ChainVM} {r : ℕ} {p : PH} {lag : Ctr}
    (hx : lagOf x = some (p, lag))
    (hz : lagOf z = some (GalilScaffoldChainVerifier.right p, GalilScaffoldCounter.dec lag))
    (hpos : GalilScaffoldCounter.positive lag = true) (h : LagLe x r) : LagLe z r := by
  obtain ⟨hc, hn, hl⟩ := lagLe_get h hx
  have h1 := (GalilScaffoldCounter.positive_iff lag hc).mp hpos
  have hv := GalilScaffoldCounter.dec_value lag
  have hp := position_right_le p
  exact lagLe_of_some hz (GalilScaffoldCounter.dec_canonical _ hc) (by omega) (by omega)

#print axioms lagLe_of_eq
#print axioms lagLe_inc
#print axioms lagLe_right
#print axioms lagLe_catch

/-! ## 4. The ledger along the chain -/

/-- **One background chain step keeps the ledger.**  The copy and back phases do not
move the verifier at all; the watch's `take` moves it one place right against a
decrement of its (positive) lag, so the sum is unchanged. -/
theorem lagLe_step {x y : ChainVM} {r : ℕ} (h : ChainStep x y) (hx : LagLe x r) :
    LagLe y r := by
  cases h with
  | idle => exact hx
  | brokenIdle w => exact hx
  | copyBit t hh p v lag margin ver a one legal present => exact lagLe_congr hx rfl
  | copyEnd t hh p v lag margin ver b hleft hp hv => exact lagLe_congr hx rfl
  | backStep v hh lag margin ver hf => exact lagLe_congr hx rfl
  | backDone v hh lag margin ver hf => exact lagLe_congr hx rfl
  | watchStep w w' hi =>
    cases hi with
    | idle hz => exact hx
    | take hp hg => exact lagLe_catch (x := .watch w) rfl rfl hp hx
  | watchBreak w hb => exact lagLe_break hx hb.1

/-- **The match credit advances the trailed place by one.**  `copy`/`back` and the
queued watch increment the lag; the immediate watch and the break move the verifier
instead. -/
theorem lagLe_matched {y z : ChainVM} {r : ℕ} (h : ChainMatched y z) (hy : LagLe y r) :
    LagLe z (r + 1) := by
  cases h with
  | idle => exact lagLe_idle _
  | copy t hh p v lag margin ver => exact lagLe_inc rfl rfl hy
  | back v hh lag margin ver => exact lagLe_inc rfl rfl hy
  | watch w w' ho =>
    cases ho with
    | queued hz => exact lagLe_inc (x := .watch w) rfl rfl hy
    | immediate hz hg => exact lagLe_right (x := .watch w) rfl rfl hy
  | breaks w w' hb => exact lagLe_breaks hy hb
  | brokenMatched w => exact lagLe_mono (lagLe_congr hy rfl) (Nat.le_succ _)

theorem lagLe_chainTick_false {x z : ChainVM} {r : ℕ} (ht : ChainTick false x z)
    (hx : LagLe x r) : LagLe z r := by
  obtain ⟨y, hs, hm⟩ := ht
  simp only [Bool.false_eq_true, if_false] at hm
  subst hm
  exact lagLe_step hs hx

theorem lagLe_chainTick {b : Bool} {x z : ChainVM} {r : ℕ} (ht : ChainTick b x z)
    (hx : LagLe x r) : LagLe z (r + 1) := by
  obtain ⟨y, hs, hm⟩ := ht
  cases b with
  | false =>
    simp only [Bool.false_eq_true, if_false] at hm
    subst hm
    exact lagLe_mono (lagLe_step hs hx) (by omega)
  | true =>
    simp only [if_true] at hm
    exact lagLe_matched hm (lagLe_step hs hx)

/-- **The start data of a fresh chain.**  `chain.start()` copies the centre head into
the verifier and the radius into the lag, so the ledger at the start is exactly
`position C + radius ≤ position R` — the `≤` half of the `rightPos` field of
`GalilScaffoldChainInputSupply.ScanInvariant`. -/
def StartLe (ver : PH) (rad : Ctr) (r : ℕ) : Prop :=
  GalilScaffoldCounter.Canonical rad ∧ 0 ≤ GalilScaffoldCounter.value rad ∧
    (position ver : ℤ) + GalilScaffoldCounter.value rad ≤ r

theorem lagLe_chainStart {r : ℕ} (ans : GalilScaffoldTape.Tape) (c : Fin 3)
    (wk : GalilScaffoldPlace.Place) (ver : PH) (rad : Ctr) (h : StartLe ver rad r) :
    LagLe (chainStart ans c wk ver rad) r :=
  lagLe_of_some rfl h.1 h.2.1 h.2.2

/-- **The chain effect of a scan background keeps the ledger.** -/
theorem lagLe_chainAt_false {found : Bool} {ans : GalilScaffoldTape.Tape} {c : Fin 3}
    {wk : GalilScaffoldPlace.Place} {ver : PH} {rad : Ctr} {x z : ChainVM} {r : ℕ}
    (h : chainAt false found ans c wk ver rad x z) (hx : LagLe x r)
    (hs : x = .idle → StartLe ver rad r) : LagLe z r := by
  rcases h with ⟨-, ht⟩ | ⟨-, -, rfl⟩ | ⟨hi, -, hz⟩
  · exact lagLe_chainTick_false ht hx
  · exact lagLe_idle _
  · simp only [Bool.false_eq_true, if_false] at hz
    subst hz
    exact lagLe_chainStart ans c wk ver rad (hs hi)

/-- **The chain effect of a comparison advances the trailed place by at most one.**
The match credit is counted whether or not the comparison matched: the mismatched tick
only needs the weaker bound, because `R` moves right in both cases. -/
theorem lagLe_chainAt {b found : Bool} {ans : GalilScaffoldTape.Tape} {c : Fin 3}
    {wk : GalilScaffoldPlace.Place} {ver : PH} {rad : Ctr} {x z : ChainVM} {r : ℕ}
    (h : chainAt b found ans c wk ver rad x z) (hx : LagLe x r)
    (hs : x = .idle → StartLe ver rad r) : LagLe z (r + 1) := by
  rcases h with ⟨-, ht⟩ | ⟨-, -, rfl⟩ | ⟨hi, -, hz⟩
  · exact lagLe_chainTick ht hx
  · exact lagLe_idle _
  · cases b with
    | false =>
      simp only [Bool.false_eq_true, if_false] at hz
      subst hz
      exact lagLe_mono (lagLe_chainStart ans c wk ver rad (hs hi)) (by omega)
    | true =>
      simp only [if_true] at hz
      exact lagLe_matched hz (lagLe_chainStart ans c wk ver rad (hs hi))

#print axioms lagLe_step
#print axioms lagLe_matched
#print axioms lagLe_chainAt

/-! ## 5. Lifting to a tick of `galilFrameS` -/

/-- **(Named, at the source of a tick) the scan-side data the ledger needs.**  `R` can
move right and is sane — that is the equality `position (right R) = position R + 1`
which a comparison consumes — and a fresh `chain.start()` copies a centre head that
trails `R` by the radius (`ScanInvariant.rightPos`, in `≤` form). -/
structure LagStep (s : GalilVM) : Prop where
  rightCan : GalilScaffoldChainVerifier.canRight s.right
  rightSane : GalilFrontMono.Sane s.right
  start : s.chain = ChainVM.idle → StartLe s.center s.radius (position s.right)

theorem lagStep_right {s : GalilVM} (h : LagStep s) :
    position (GalilScaffoldChainVerifier.right s.right) = position s.right + 1 :=
  (GalilFrontMono.right_sane h.rightCan h.rightSane).1

section Tick
variable (onLetter leftFirst : GalilVM → Prop) (centre : GalilVM → Fin 3)
  (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9) (delay : ℕ)

/-- **The ledger survives every tick of `galilFrameS`.**  The case split is that of
`GalilChainCoupling.coupled_tick` and `GalilTrailChain.trailChain_scanTick`: `init`,
`restart`, a fallback entry and `replayStart` leave the chain idle; the scan
background acts through `chainAt false` with `R` fixed; a comparison acts through
`chainAt` and moves `R` one place right; the shift entry adds the immediate consume
after the comparison; a shift unit keeps verifier, lag and `R`; and every other mode
leaves both the chain and `R` alone. -/
theorem lagLe_tick {c c' : Control} {s t : GalilVM}
    (hL : LagLe s.chain (position s.right)) (hS : LagStep s)
    (h : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay
      ⟨c, s⟩ ⟨c', t⟩) : LagLe t.chain (position t.right) := by
  cases h
  case init =>
    rename_i hm hi
    obtain ⟨-, -, -, -, -, -, -, -, -, hch, -⟩ : initVM entry s t := hi
    exact lagLe_of_idle hch
  case scan_wait =>
    rename_i hm hav hb
    obtain ⟨-, hr, hch, -⟩ :=
      backgroundS_fields (sharedC onLetter leftFirst centre place entry) q first hb
    rw [hr]
    exact lagLe_chainAt_false hch hL hS.start
  case scan_count =>
    rename_i hm hc hav hb
    obtain ⟨-, hr, hch, -⟩ :=
      backgroundS_fields (sharedC onLetter leftFirst centre place entry) q first hb
    rw [hr]
    exact lagLe_chainAt_false hch hL hS.start
  case restart =>
    rename_i hm hb
    obtain ⟨w, -, -, -, -, ht⟩ : restartVM entry s t := hb
    exact lagLe_of_idle (by rw [ht])
  case scan_match =>
    rename_i s' o hmt hm hc hcmp hav hpl ho
    obtain ⟨a, found, ans, cc, wk, hch, -⟩ :=
      compare_chainAt onLetter leftFirst centre place entry q first hcmp
    obtain ⟨-, hr2, -⟩ :=
      compare_heads onLetter leftFirst centre place entry q first hcmp
    have hpl' : t = (if c.replaying then
        {s' with replay := GalilScaffoldCounter.dec s'.replay} else s') := hpl
    have htc : t.chain = s'.chain := by rw [hpl']; cases c.replaying <;> rfl
    have htr : t.right = s'.right := by rw [hpl']; cases c.replaying <;> rfl
    rw [htc, htr, hr2, lagStep_right hS]
    exact lagLe_chainAt hch hL hS.start
  case scan_shift =>
    rename_i s' hmt hg hm hc hr hcmp hav hb
    obtain ⟨a, found, ans, cc, wk, hch, ha⟩ :=
      compare_chainAt onLetter leftFirst centre place entry q first hcmp
    obtain rfl : a = false := ha hmt
    obtain ⟨-, hr2, -⟩ :=
      compare_heads onLetter leftFirst centre place entry q first hcmp
    obtain ⟨w, hs0, ht⟩ : beginShiftVM' s' t := hb
    have htc : t.chain = ChainVM.watch (GalilScaffoldChainWatch.immediate w) := by rw [ht]
    have htr : t.right = s'.right := by rw [ht]
    rw [htc, htr, hr2, lagStep_right hS]
    refine lagLe_right (x := ChainVM.watch w) rfl rfl ?_
    rw [← hs0]
    exact lagLe_chainAt_false hch hL hS.start
  case scan_fallback =>
    rename_i s' hmt hm hc hg hr hcmp hav hb
    obtain ⟨pl, ht, -⟩ : beginFallbackVM' s' t := hb
    exact lagLe_of_idle (by rw [ht])
  case shift_one =>
    rename_i hm hp hi
    obtain ⟨-, -, -, w, hw, hv⟩ := hi.1
    have ht := hi.2
    rw [hv] at ht
    have hws : s.chain = ChainVM.watch w := hw
    have htr : t.right = s.right := by rw [ht]; rfl
    rw [htr]
    exact lagLe_congr hL (by rw [ht, hws]; rfl)
  case shift_done =>
    rename_i o hm hp ho
    exact hL
  case replayStart =>
    rename_i o hm ho ho' hi
    obtain ⟨-, -, -, -, -, -, -, -, -, hch, -⟩ : replayStartVM entry s t := hi
    exact lagLe_of_idle hch
  all_goals
    (rename_i hi
     have hch : t.chain = s.chain := (congrArg GalilVM.chain hi.2).trans rfl
     have htr : t.right = s.right := by
       first
       | exact (congrArg GalilVM.right hi.2).trans rfl
       | exact (congrArg GalilVM.right hi.2).trans (by rw [hi.1.2]; rfl)
       | exact (congrArg GalilVM.right hi.2).trans (by rw [hi.1]; rfl)
     rw [hch, htr]
     exact hL)

#print axioms lagLe_tick

end Tick

/-! ## 6. `ChainBudget` from the ledger -/

/-- **(Named, at every state) the rest of `ChainBudget`.**  `R` stands no further right
than the checkpoint place `2(m+1)-1`, and the chain verifier is sane.  The place bound
is `Trails.pos` of `ScanT.right` when `R`'s right stack is empty (`lagAt_of_scanT`),
and `GalilTrailScan.position_right_le_of_front` — front monotonicity plus the
checkpoint report — in general. -/
structure LagAt (m : ℕ) (s : GalilVM) : Prop where
  rightPlace : position s.right ≤ 2 * (m + 1) - 1
  verSane : ∀ p, verOf s.chain = some p → GalilFrontMono.Sane p

theorem lagAt_of_scanT {raw : List (Fin 2)} {m : ℕ} {x : State GalilVM} (hS : ScanT raw m x)
    (hstack : x.vm.right.head.right = [])
    (hver : ∀ p, verOf x.vm.chain = some p → GalilFrontMono.Sane p) : LagAt m x.vm :=
  ⟨by have := hS.right.pos hstack; omega, hver⟩

/-- **The ledger delivers `ChainBudget`.**  `pos` is `position ver ≤ position ver + lag
≤ position R ≤ 2(m+1)-1` (the lag is non-negative), and `lagPos` is the same chain with
`1 ≤ lag` from `positive` on a canonical counter — the derivation
`GalilTrailChain.trails_one_of_lag` performs on the equality ledger. -/
theorem chainBudget_of_lagLe {m : ℕ} {s : GalilVM} (hL : LagLe s.chain (position s.right))
    (hA : LagAt m s) : ChainBudget m s.chain := by
  refine ⟨hA.verSane, fun p hp hstack => ?_, fun w hw hpos hstack => ?_⟩
  · obtain ⟨lag, hlag⟩ := exists_lag hp
    obtain ⟨hc, hn, hl⟩ := lagLe_get hL hlag
    have hR := hA.rightPlace
    omega
  · have hlag : lagOf s.chain = some (w.machine.verifier, w.lag) := by rw [hw]; rfl
    obtain ⟨hc, hn, hl⟩ := lagLe_get hL hlag
    have h1 := (GalilScaffoldCounter.positive_iff w.lag hc).mp hpos
    have hR := hA.rightPlace
    omega

/-! ## 7. Along a pre-loaded trace -/

section Trace
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **The ledger up to the checkpoint `Tc (m+1)`.**  The boot state has an idle chain,
so the base case is vacuous. -/
theorem lagLe_trace {raw : List (Fin 2)} {st : ℕ → State GalilVM} {Tc : ℕ → ℕ} {m : ℕ}
    (hP : PreTrace centre place entry q first raw st Tc) (hm : m < raw.length)
    (hstep : ∀ i, i < Tc (m+1) → LagStep (st i).vm) :
    ∀ i, i ≤ Tc (m+1) → LagLe (st i).vm.chain (position (st i).vm.right) := by
  have hle : Tc (m+1) ≤ Tc raw.length := hP.mono (m+1) raw.length (by omega) le_rfl
  intro i
  induction i with
  | zero => intro _; rw [hP.start]; exact lagLe_of_idle rfl
  | succ i ih =>
    intro hi
    have hlt : i < Tc (m+1) := by omega
    exact lagLe_tick (onLetterVM raw) leftFirstVM centre place entry q first 2048
      (ih (by omega)) (hstep i hlt) (hP.trace.tick i (by omega))

/-- **`ChainBudget` at every state up to the checkpoint.** -/
theorem chainBudget_trace {raw : List (Fin 2)} {st : ℕ → State GalilVM} {Tc : ℕ → ℕ} {m : ℕ}
    (hP : PreTrace centre place entry q first raw st Tc) (hm : m < raw.length)
    (hstep : ∀ i, i < Tc (m+1) → LagStep (st i).vm)
    (hat : ∀ i, i ≤ Tc (m+1) → LagAt m (st i).vm) :
    ∀ i, i ≤ Tc (m+1) → ChainBudget m (st i).vm.chain :=
  fun i hi =>
    chainBudget_of_lagLe (lagLe_trace centre place entry q first hP hm hstep i hi) (hat i hi)

/-- **The two chain clauses of `TrailF` up to the checkpoint**, by
`GalilTrailChain.trailChain_scanTick` against the target budget. -/
theorem verF_trace {raw : List (Fin 2)} {st : ℕ → State GalilVM} {Tc : ℕ → ℕ} {m : ℕ}
    (hP : PreTrace centre place entry q first raw st Tc) (hm : m < raw.length)
    (hscan : ∀ i, i ≤ Tc (m+1) → ScanT raw m (st i))
    (hbud : ∀ i, i ≤ Tc (m+1) → ChainBudget m (st i).vm.chain) :
    ∀ i, i ≤ Tc (m+1) → VerF raw m (st i).vm.chain := by
  have hle : Tc (m+1) ≤ Tc raw.length := hP.mono (m+1) raw.length (by omega) le_rfl
  intro i
  induction i with
  | zero => intro _; rw [hP.start]; exact verF_idle raw m
  | succ i ih =>
    intro hi
    have hlt : i < Tc (m+1) := by omega
    exact trailChain_scanTick (onLetterVM raw) leftFirstVM centre place entry q first 2048
      (ih (by omega)) (hscan i (by omega)).center (hP.trace.tick i (by omega)) (hbud (i+1) hi)

end Trace

/-! ## 8. `H_trailF` -/

/-- `GalilTrailChain.trailF_of_verF` fed with the scan-head clauses. -/
theorem trailF_of_scanT_verF {raw : List (Fin 2)} {m : ℕ} {x : State GalilVM}
    (hS : ScanT raw m x) (hV : VerF raw m x.vm.chain) : TrailF raw m x :=
  trailF_of_verF (scanT_left hS) (scanT_center hS) hS.right hV

section Hyps
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **(Named) the chain-side data of the lag ledger along every pre-loaded trace.**
`LagStep` at every tick source: `R` can move right and is sane, and a fresh
`chain.start()` copies a centre head trailing `R` by the radius (the `≤` half of
`ScanInvariant.rightPos`).  `LagAt` at every state: `R` is left of the checkpoint
place, and the chain verifier is sane. -/
def H_lagSide : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTrace centre place entry q first w st Tc →
    ∀ m, m < w.length →
      (∀ i, i < Tc (m+1) → LagStep (st i).vm) ∧ (∀ i, i ≤ Tc (m+1) → LagAt m (st i).vm)

/-- **The verifier half of `H_trailF`, from the two named hypotheses.** -/
theorem h_trailVer_of_lagSide (hbud : H_tickBudget centre place entry q first)
    (hside : H_lagSide centre place entry q first) :
    ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc,
      PreTrace centre place entry q first w st Tc → ∀ m, m < w.length → ∀ i, i ≤ Tc (m+1) →
        (∀ p, verOf (st i).vm.chain = some p → Trails w m 0 p) ∧
        (∀ v, (st i).vm.chain = .watch v → GalilScaffoldCounter.positive v.lag = true →
          Trails w m 1 v.machine.verifier) := by
  intro w hw st Tc hP m hm i hi
  obtain ⟨hstep, hat⟩ := hside w hw st Tc hP m hm
  have hscan := scanT_trace centre place entry q first hP hm
    (fun j hj => hbud w hw st Tc hP m hm j hj)
  have hB := chainBudget_trace centre place entry q first hP hm hstep hat
  have hV := verF_trace centre place entry q first hP hm hscan hB i hi
  exact ⟨hV.ver, hV.lagPos⟩

/-- **(B'') `H_trailF` from the scan-head place budget and the chain-side ledger
data.**  `GalilTrailScan.h_trailF_of_parts` glues the two halves; the scan half is
`h_trailScan_of_budget`, the chain half is the lag ledger of this file. -/
theorem h_trailF_of_lagSide (hbud : H_tickBudget centre place entry q first)
    (hside : H_lagSide centre place entry q first) :
    H_trailF centre place entry q first :=
  h_trailF_of_parts centre place entry q first
    (h_trailScan_of_budget centre place entry q first hbud)
    (h_trailVer_of_lagSide centre place entry q first hbud hside)

end Hyps

#print axioms chainBudget_of_lagLe
#print axioms lagLe_trace
#print axioms chainBudget_trace
#print axioms verF_trace
#print axioms trailF_of_scanT_verF
#print axioms h_trailVer_of_lagSide
#print axioms h_trailF_of_lagSide

end PalPeg.GalilTrailAssembly
