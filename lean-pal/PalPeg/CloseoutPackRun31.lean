import PalPeg.CloseoutPackRun29

/-!
# `CloseoutPackRun31`: `ShiftPal` from a chain-round invariant

`CloseoutPackRun29.ShiftPal` asks, at a comparison target watching `wch`
that passes `shiftGuardVM`, for the palindrome of radius `r₀ + 1 − h` at the
destination centre `C + h` (`h = periodLength wch`).  Its content is
`GalilScaffoldChainReadOrigin.reshift_palindrome`, whose whole-round data
(`ReadOrigin` / `OnlyScan` / `Trace`) is not a one-state fact.

The one-state datum that *does* carry it is `GalilRoundPeriod.RoundScan
w C R h used s wch` — the loop invariant of a re-shift round (the origin's
palindrome `PalAt C R`, the caught scan at `C + h`, the countdown `2h − used`,
and the chain's prediction one period behind its verifier).  Here:

* §1 `terminal_palindrome`: at the terminal of a round (`singlePositive
  cycle`), with the prediction agreeing with the right read, the palindrome
  `PalAt (C + 2h) (R + 1)` follows from `RoundScan` alone (the two palindromes
  at `C` and `C + h` give the period `2h` up to `C + R`, the guard gives it at
  `C + R + 1`, then `reshift_from_right`).
* §2 `ChainRound`: the named chain-round invariant — in scan mode, not
  replaying, `periodOnly`, every watching chain is in a `RoundScan`.
  `shiftPal_of_chainRound` discharges `ShiftPal` from it and `WatchShift`
  (which supplies `canRight` of the right head), modulo two named branches:
  `H_matched` (the guard at a *matched* comparison target, which
  `shiftEntry_of_guard` never uses but `ShiftPal` quantifies over) and
  `H_born` (a chain born *during* the comparison, `ChainStep.backDone`).
  `shiftPal_of_readOrigin` adds the `periodOnly = false` branch `H_fresh`
  (the first shift of a fresh chain, `GalilScaffoldTopFreshEntry`).
* §3 `chainRound_tick`: preservation along a `galilFrameS` tick.  Idle
  chains, mode changes and replay are vacuous; background ticks and matched
  non-terminal comparisons are proved (the latter via `roundScan_step`);
  a terminal matched comparison is shown to break the chain.  Named
  branches: `H_advance` (the chain's prediction after `immediate`,
  `roundScan_step`'s own named hypothesis), `H_shiftDone` (the birth of the
  next round at the `shift_done` exit), `H_birth` (a chain born in the
  background or a comparison while `periodOnly`).

Standard axioms only; unconditional `PAL ∈ PEG` remains open.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPackRun31

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton PalPeg.GalilFrontMono
open PalPeg.CloseoutLPack3 PalPeg.CloseoutPackRun24 PalPeg.CloseoutPackRun29
open PalPeg.GalilRoundPeriod PalPeg.GalilChainCoupling

/-! ## 0. Small facts about counters and chain steps -/

theorem positive_eq_false_of_zero {x : Counter} (h : zero x = true) : positive x = false := by
  rcases x with ⟨pos, neg⟩
  simp only [zero, Bool.and_eq_true, List.isEmpty_iff] at h
  simp [positive, h.1]

/-- An `Internal` step at lag zero is the identity. -/
theorem internal_of_zero {w w' : GalilScaffoldChainWatch.State} (hz : zero w.lag = true)
    (h : GalilScaffoldChainWatch.Internal w w') : w' = w := by
  cases h with
  | idle => rfl
  | take hp _ => rw [positive_eq_false_of_zero hz] at hp; cases hp

/-- An `Outer true` step at lag zero is the immediate consume of a `Good` watch. -/
theorem outer_of_zero {w w' : GalilScaffoldChainWatch.State} (hz : zero w.lag = true)
    (h : GalilScaffoldChainWatch.Outer w true w') :
    GalilScaffoldChainWatch.Good w ∧ w' = GalilScaffoldChainWatch.immediate w := by
  cases h with
  | queued hz' => rw [hz] at hz'; cases hz'
  | immediate _ hg => exact ⟨hg, rfl⟩

/-- The source of a watch after `chainAt false`: either a watch stepped
`Internal`, or not a watch at all (a birth, `ChainStep.backDone`). -/
theorem chainAt_false_watch {found : Bool} {ans : GalilScaffoldTape.Tape} {cc : Fin 3}
    {walker : GalilScaffoldPlace.Place} {ver : PlaceHead} {radius : Counter} {x z : ChainVM}
    (h : chainAt false found ans cc walker ver radius x z)
    {wch : GalilScaffoldChainWatch.State} (hz : z = .watch wch) :
    (∃ w0, x = .watch w0 ∧ GalilScaffoldChainWatch.Internal w0 wch) ∨
      (∀ w0, x ≠ .watch w0) := by
  rcases h with ⟨-, y, hstep, hzy⟩ | ⟨-, -, rfl⟩ | ⟨-, -, hzc⟩
  · rw [if_neg (by simp)] at hzy
    subst hzy
    subst hz
    cases hstep with
    | watchStep w w' ht => exact Or.inl ⟨w, rfl, ht⟩
    | backDone v h lag margin ver hf => exact Or.inr (fun _ h => by cases h)
  · cases hz
  · rw [if_neg (by simp)] at hzc
    subst hzc
    unfold chainStart at hz
    cases hz

/-- The source of a watch after `chainAt true`: a watch stepped `Internal`
then `Outer true`, or not a watch at all. -/
theorem chainAt_true_watch {found : Bool} {ans : GalilScaffoldTape.Tape} {cc : Fin 3}
    {walker : GalilScaffoldPlace.Place} {ver : PlaceHead} {radius : Counter} {x z : ChainVM}
    (h : chainAt true found ans cc walker ver radius x z)
    {wch : GalilScaffoldChainWatch.State} (hz : z = .watch wch) :
    (∃ w0 w1, x = .watch w0 ∧ GalilScaffoldChainWatch.Internal w0 w1 ∧
      GalilScaffoldChainWatch.Outer w1 true wch) ∨
      (∀ w0, x ≠ .watch w0) := by
  rcases h with ⟨-, y, hstep, hzy⟩ | ⟨-, -, rfl⟩ | ⟨-, -, hzc⟩
  · rw [if_pos rfl] at hzy
    subst hz
    cases hzy with
    | watch w w' ho =>
      cases hstep with
      | watchStep w0 w1 ht => exact Or.inl ⟨w0, w, rfl, ht, ho⟩
      | backDone v h lag margin ver hf => exact Or.inr (fun _ h => by cases h)
  · cases hz
  · rw [if_pos rfl] at hzc
    unfold chainStart at hzc
    cases hzc
    cases hz

/-- `RoundScan` only reads the chain, the two heads and the cycle counter. -/
theorem roundScan_transport {w : List (Fin 2)} {C R h used : ℕ} {s t : GalilVM}
    {wch : GalilScaffoldChainWatch.State} (hI : RoundScan w C R h used s wch)
    (hch : t.chain = .watch wch) (hl : t.left = s.left) (hr : t.right = s.right)
    (hc : t.cycle = s.cycle) : RoundScan w C R h used t wch :=
  ⟨hch, by rw [hl, hr]; exact hI.caught, by rw [hc]; exact hI.canon,
    by rw [hc]; exact hI.count, hI.fresh, hI.size, hI.posH, hI.pal, hI.room, hI.origin, hI.pred⟩

/-! ## 1. The palindrome at the terminal of a round -/

/-- **The whole-round palindrome from `RoundScan` at the terminal.**  With the
prediction agreeing with the right read (`shiftGuardVM`), the palindrome of
radius `R + 1` is known at `C + 2h`. -/
theorem terminal_palindrome {w : List (Fin 2)} {C R h used : ℕ} {s : GalilVM}
    {wch : GalilScaffoldChainWatch.State}
    (hI : RoundScan w C R h used s wch) (hend : singlePositive s.cycle = true)
    (hc : canRight s.right)
    (hpred : GalilScaffoldChainConsume.symbol wch.machine.control.period.focus =
      read (right s.right)) :
    Manacher.PalAt (encoded w) (C + 2 * h) (R + 1) := by
  have hterm := hI.terminal_iff.mp hend
  have hsize := hI.size
  have hposH := hI.posH
  have hroom := hI.room
  have hscan := hI.caught.scan
  have hcur : Manacher.PalAt (encoded w) (C + h) (R + h) := by
    have hp := hscan.palindrome
    rw [show R + 1 - h + used = R + h by omega] at hp
    exact hp
  have hrpos : position s.right = C + R + 1 + used := hI.rightPos
  have hrr := right_read_index s.right w hscan.rightRep hscan.rightPresent hc
  have hbound := position_bound (right s.right) w (right_word _ w hscan.rightRep hc)
    (right_present _ w hscan.rightRep hscan.rightPresent hc)
  have hrp1 := right_position s.right hc
    (represented_position _ w hscan.rightRep hscan.rightPresent).1
  rw [hrp1, hrpos] at hbound
  apply reshift_from_right (encoded w) C R h hI.pal hcur hposH (by omega) (by omega)
  intro j hj1 hj2
  by_cases hjle : j ≤ C + R
  · have e1 := Manacher.mirror_getElem? hI.pal (show C - R ≤ j by omega) hjle
    have e2 := Manacher.mirror_getElem? hcur (show C + h - (R + h) ≤ 2 * C - j by omega)
      (show 2 * C - j ≤ C + h + (R + h) by omega)
    rw [e1, e2]
    congr 1
    omega
  · have hj : j = C + R + 1 := by omega
    subst hj
    have hp := hI.pred
    rw [show C + R + 2 + used - 2 * h = C + R + 1 by omega] at hp
    rw [← hp, hpred, hrr, hrpos]
    congr 1
    omega

/-! ## 2. The chain-round invariant and `ShiftPal` -/

section Entry
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **The chain-round invariant.**  In scan mode, not replaying, after a
shift (`periodOnly`): every watching chain is in a re-shift round
(`RoundScan`) with `h` its period length. -/
def ChainRound (w : List (Fin 2)) (c : Control) (s : GalilVM) : Prop :=
  c.mode = Mode.scan → c.replaying = false → s.periodOnly = true →
  ∀ wch : GalilScaffoldChainWatch.State, s.chain = .watch wch →
    ∃ C R used : ℕ, RoundScan w C R (periodLength wch) used s wch

/-- The conclusion of `ShiftPal` at one comparison target. -/
def ShiftPalAt (w : List (Fin 2)) (s s' : GalilVM) : Prop :=
  ∀ wch : GalilScaffoldChainWatch.State, s'.chain = .watch wch →
    shiftGuardVM s' →
    ∀ r₀ : ℕ, ScanInvariant w (position s.center) r₀ s.left s.right →
      1 ≤ periodLength wch ∧ periodLength wch ≤ r₀ + 1 ∧
      Manacher.PalAt (encoded w) (position s.center + periodLength wch)
        (r₀ + 1 - periodLength wch)

/-- **`ShiftPal` from `ChainRound` and `WatchShift`**, modulo the two named
branches `H_matched` (a matched comparison target — never used by
`shiftEntry_of_guard`) and `H_born` (a chain born during the comparison). -/
theorem shiftPal_of_chainRound {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (hm : c.mode = Mode.scan) (hr : c.replaying = false) (hpo : s.periodOnly = true)
    (hCR : ChainRound w c s)
    (hws : WatchShift centre place entry q first w ⟨c, s⟩)
    (H_matched : ∀ s' : GalilVM,
      (galilFrameS (PofC centre place entry w) q first).compare s s' →
      (galilFrameS (PofC centre place entry w) q first).matched s' → ShiftPalAt w s s')
    (H_born : ∀ s' : GalilVM,
      (galilFrameS (PofC centre place entry w) q first).compare s s' →
      (∀ w0, s.chain ≠ .watch w0) → ShiftPalAt w s s') :
    ShiftPal centre place entry q first w s := by
  intro s' hcmp wch hchain hg r₀ hi
  have hcf : compareFound (PofC centre place entry w) q first s s' := hcmp
  obtain ⟨vs, vq, a, hvl, hvr, hiff, -, hch, hteq⟩ := hcf
  cases a with
  | true =>
    rw [if_pos rfl] at hteq
    exact H_matched s' hcmp (hteq ▸ hiff.1 rfl) wch hchain hg r₀ hi
  | false =>
    rw [if_neg (by simp)] at hteq
    have hchain' : vs.chain = .watch wch := by rw [hteq] at hchain; exact hchain
    rcases chainAt_false_watch hch hchain' with ⟨w0, hw0, hint⟩ | hnot
    · -- the chain was watching `w0` at `s`
      obtain ⟨C, R, used, hI⟩ := hCR hm hr hpo w0 hw0
      have hz := hI.caught.lagZero
      have hwe : wch = w0 := internal_of_zero hz hint
      subst hwe
      -- the guard
      obtain ⟨w1, hw1, -, -, -, hif, hsym⟩ := hg
      have hw1' : wch = w1 := by
        rw [hchain] at hw1
        cases hw1
        rfl
      subst hw1'
      have hpo' : s'.periodOnly = true := by rw [hteq]; exact hpo
      rw [hpo', if_pos rfl] at hif
      have hend : singlePositive s.cycle = true := by rw [hteq] at hif; exact hif
      have hpred : GalilScaffoldChainConsume.symbol wch.machine.control.period.focus =
          read (right s.right) := by
        rw [← hvr]; rw [hteq] at hsym; exact hsym
      -- `canRight` of the right head, from `WatchShift`
      have hni : s.chain ≠ ChainVM.idle := by rw [hw0]; exact fun h => by cases h
      have hcan : canRight s.right := (hws hni s' hcmp wch hchain).2.1
      -- the geometry: `r₀` and the centre
      have hterm := hI.terminal_iff.mp hend
      have hsize := hI.size
      have hposH := hI.posH
      have hroom := hI.room
      have hlp := hi.leftPos
      have hrp := hi.rightPos
      have hlp' := hI.caught.scan.leftPos
      have hrp' := hI.caught.scan.rightPos
      have hr₀ : r₀ = R + periodLength wch := by omega
      have hcen : position s.center = C + periodLength wch := by omega
      refine ⟨hposH, by omega, ?_⟩
      have hpal := terminal_palindrome hI hend hcan hpred
      rw [hcen, show C + periodLength wch + periodLength wch = C + 2 * periodLength wch by omega,
        show r₀ + 1 - periodLength wch = R + 1 by omega]
      exact hpal
    · exact H_born s' hcmp hnot wch hchain hg r₀ hi

/-- **The target theorem.**  `ShiftPal` at a scan state, not replaying, from
`ChainRound` and `WatchShift`; the `periodOnly = false` branch (the first
shift of a fresh chain, whose content is `GalilScaffoldTopFreshEntry`) is the
named `H_fresh`. -/
theorem shiftPal_of_readOrigin {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (hm : c.mode = Mode.scan) (hr : c.replaying = false)
    (hCR : ChainRound w c s)
    (hws : WatchShift centre place entry q first w ⟨c, s⟩)
    (H_matched : ∀ s' : GalilVM,
      (galilFrameS (PofC centre place entry w) q first).compare s s' →
      (galilFrameS (PofC centre place entry w) q first).matched s' → ShiftPalAt w s s')
    (H_born : ∀ s' : GalilVM,
      (galilFrameS (PofC centre place entry w) q first).compare s s' →
      (∀ w0, s.chain ≠ .watch w0) → ShiftPalAt w s s')
    (H_fresh : s.periodOnly = false → ShiftPal centre place entry q first w s) :
    ShiftPal centre place entry q first w s := by
  cases hpo : s.periodOnly with
  | false => exact H_fresh hpo
  | true => exact shiftPal_of_chainRound centre place entry q first hm hr hpo hCR hws H_matched H_born

/-! ## 3. `ChainRound` along a tick -/

/-- **(NAMED) the prediction after a matched comparison.**  `roundScan_step`'s
own named hypothesis: after the immediate consume the chain predicts the next
encoded symbol one period behind. -/
def H_advance (w : List (Fin 2)) (s : GalilVM) : Prop :=
  ∀ (C R used : ℕ) (w0 : GalilScaffoldChainWatch.State),
    RoundScan w C R (periodLength w0) used s w0 →
    GalilScaffoldChainWatch.Good w0 → singlePositive s.cycle = false →
    GalilScaffoldChainConsume.symbol
        (GalilScaffoldChainWatch.immediate w0).machine.control.period.focus =
      (encoded w)[C + R + 2 + (used + 1) - 2 * periodLength w0]?

/-- **(NAMED) the birth of the next round at the `shift_done` exit.** -/
def H_shiftDone (w : List (Fin 2)) (c : Control) (s : GalilVM) : Prop :=
  c.mode = Mode.shift → c.replaying = false → s.periodOnly = true →
  ¬ (galilFrameS (PofC centre place entry w) q first).remainingPos s →
  ∀ wch : GalilScaffoldChainWatch.State, s.chain = .watch wch →
    ∃ C R used : ℕ, RoundScan w C R (periodLength wch) used s wch

/-- **(NAMED) a chain born while `periodOnly`** (in the background or during a
comparison, `ChainStep.backDone`), or a chain watching while replaying whose
replay ends at this tick: its round datum at the target. -/
def H_birth (w : List (Fin 2)) (c : Control) (s t : GalilVM) : Prop :=
  (c.replaying = true ∨ ∀ w0, s.chain ≠ .watch w0) → t.periodOnly = true →
  ∀ wch : GalilScaffoldChainWatch.State, t.chain = .watch wch →
    ∃ C R used : ℕ, RoundScan w C R (periodLength wch) used t wch

/-- A terminal matched comparison breaks the chain: the watching `w0` is not
`Good`. -/
theorem not_good_of_terminal_match {w : List (Fin 2)} {C R h used : ℕ} {s : GalilVM}
    {w0 : GalilScaffoldChainWatch.State}
    (hI : RoundScan w C R h used s w0) (hav : canRight s.right)
    (hend : singlePositive s.cycle = true)
    (hmatch : read (GalilScaffoldInputHead.left s.left) = read (right s.right)) :
    ¬ GalilScaffoldChainWatch.Good w0 := by
  intro hg
  obtain ⟨hvc, a, ha, hra⟩ := hg
  have hc := hI.caught
  have hs := hc.scan
  have hrrep := right_word s.right w hs.rightRep hav
  have hrpres := right_present s.right w hs.rightRep hs.rightPresent hav
  have hrpos := right_position s.right hav
    (represented_position s.right.head w hs.rightRep hs.rightPresent).1
  have hvrep := right_word _ w hc.verifierRep hvc
  have hvpres := right_present _ w hc.verifierRep hc.verifierPresent hvc
  have hvpos := right_position w0.machine.verifier hvc
    (represented_position w0.machine.verifier.head w hc.verifierRep hc.verifierPresent).1
  have hread : read (right w0.machine.verifier) = read (right s.right) := by
    rw [represented_read _ w hvrep hvpres, represented_read _ w hrrep hrpres,
      hvpos, hrpos, hc.aligned]
  apply hI.prediction_terminal hend
  rw [hmatch, ← hread, hra, ha]

/-- **`ChainRound` along one tick of `galilFrameS`.**  Proved: idle chains
(`init`, `restart`, `replayStart`), every mode other than scan, replay,
background ticks (`scan_wait`, `scan_count`) and matched comparisons
(`scan_match`; the terminal case breaks the chain).  Named: `H_advance`,
`H_shiftDone`, `H_birth`. -/
theorem chainRound_tick {w : List (Fin 2)} {delay : ℕ} {x y : State GalilVM}
    (hCR : ChainRound w x.ctl x.vm)
    (hA : H_advance w x.vm)
    (hS : H_shiftDone centre place entry q first w x.ctl x.vm)
    (hB : H_birth w x.ctl x.vm y.vm)
    (hblk : GalilBranchInvariants.BlockInv x.vm.chain)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) delay x y) :
    ChainRound w y.ctl y.vm := by
  obtain ⟨c, s⟩ := x
  obtain ⟨c', t⟩ := y
  cases h with
  | init c s t hm hi =>
    intro _ _ _ wch hchain
    obtain ⟨-, -, -, -, -, -, -, -, -, hch, -⟩ : initVM entry s t := hi
    rw [hch] at hchain
    cases hchain
  | scan_wait c s t hm hav hb =>
    intro hm' hr' hpo' wch hchain
    obtain ⟨hl, hr, hch, -, hpo, -, -, hcyc, -, -, -, -⟩ :=
      backgroundS_fields (PofC centre place entry w) q first hb
    rcases chainAt_false_watch hch hchain with ⟨w0, hw0, hint⟩ | hnot
    · obtain ⟨C, R, used, hI⟩ := hCR hm' hr' (hpo ▸ hpo') w0 hw0
      have hwe := internal_of_zero hI.caught.lagZero hint
      subst hwe
      exact ⟨C, R, used, roundScan_transport hI hchain hl hr hcyc⟩
    · exact hB (Or.inr hnot) hpo' wch hchain
  | scan_count c s t hm hav hc hb =>
    intro hm' hr' hpo' wch hchain
    obtain ⟨hl, hr, hch, -, hpo, -, -, hcyc, -, -, -, -⟩ :=
      backgroundS_fields (PofC centre place entry w) q first hb
    rcases chainAt_false_watch hch hchain with ⟨w0, hw0, hint⟩ | hnot
    · obtain ⟨C, R, used, hI⟩ := hCR hm' hr' (hpo ▸ hpo') w0 hw0
      have hwe := internal_of_zero hI.caught.lagZero hint
      subst hwe
      exact ⟨C, R, used, roundScan_transport hI hchain hl hr hcyc⟩
    · exact hB (Or.inr hnot) hpo' wch hchain
  | restart c s t hm hb =>
    intro _ _ _ wch hchain
    obtain ⟨w0, -, -, -, -, ht⟩ : restartVM entry s t := hb
    subst ht
    cases hchain
  | scan_match c s s' t o hm hav hc hcmp hmt hpl ho =>
    intro hm' hr' hpo' wch hchain
    cases hrep : c.replaying with
    | true => exact hB (Or.inl hrep) hpo' wch hchain
    | false =>
    have hav' : canRight s.right := by
      rcases hav with hav | hav
      · rw [hrep] at hav; cases hav
      · exact hav
    have hpl' : t = (if c.replaying then
        {s' with replay := GalilScaffoldCounter.dec s'.replay} else s') := hpl
    rw [hrep, if_neg (by simp)] at hpl'
    clear hpl
    subst t
    have hcf : compareFound (PofC centre place entry w) q first s s' := hcmp
    obtain ⟨vs, vq, a, hvl, hvr, hiff, -, hch, hteq⟩ := hcf
    cases a with
    | false =>
      rw [if_neg (by simp)] at hteq
      subst hteq
      exact absurd (hiff.2 hmt) (by simp)
    | true =>
      rw [if_pos rfl] at hteq
      subst hteq
      have hchain' : vs.chain = .watch wch := hchain
      have hpo : s.periodOnly = true := hpo'
      rcases chainAt_true_watch hch hchain' with ⟨w0, w1, hw0, hint, hout⟩ | hnot
      · obtain ⟨C, R, used, hI⟩ := hCR hm hrep hpo w0 hw0
        have hz := hI.caught.lagZero
        have hwe := internal_of_zero hz hint
        subst w1
        obtain ⟨hg, hwch⟩ := outer_of_zero hz hout
        subst hwch
        have hmatch : read (GalilScaffoldInputHead.left s.left) = read (right s.right) := by
          have hm2 : read vs.left = read vs.right := hmt
          rw [hvl, hvr] at hm2
          exact hm2
        cases hend : singlePositive s.cycle with
        | true => exact absurd hg (not_good_of_terminal_match hI hav' hend hmatch)
        | false =>
          have hadv := hA C R used w0 hI hg hend
          have hcyc : (afterCompare s vs vq).cycle = dec s.cycle := by
            show cycleAfter s = dec s.cycle
            unfold cycleAfter
            rw [hpo, if_pos rfl]
          have hstep := roundScan_step hI hav' hend hmatch hchain
            (show (afterCompare s vs vq).left = GalilScaffoldInputHead.left s.left from hvl)
            (show (afterCompare s vs vq).right = right s.right from hvr) hcyc hadv
          have hblk' : GalilBranchInvariants.OnBlock w0.machine.control.period := by
            have hb0 : GalilBranchInvariants.BlockInv s.chain := hblk
            rw [hw0] at hb0
            exact hb0
          have hper : periodLength (GalilScaffoldChainWatch.immediate w0) = periodLength w0 :=
            periodLength_consume w0.machine w0.lag w0.margin w0.lag (inc w0.margin) hblk'
          refine ⟨C, R, used + 1, ?_⟩
          rw [hper]
          exact hstep
      · exact hB (Or.inr hnot) hpo' wch hchain
  | scan_shift c s s' t hm h hc hcmp hmt hr hg hb =>
    intro hm' _ _ _ _
    exact absurd hm' (by simp)
  | scan_fallback c s s' t hm h hc hcmp hmt hg hr hb =>
    intro hm' _ _ _ _
    exact absurd hm' (by simp)
  | shift_one c s t hm hp hs =>
    intro hm' _ _ _ _
    exact absurd hm' (by simp [hm])
  | shift_done c s o hm hp ho =>
    intro _ hr' hpo' wch hchain
    exact hS hm hr' hpo' hp wch hchain
  | copy_one c s t hm hp hs =>
    intro hm' _ _ _ _
    exact absurd hm' (by simp [hm])
  | copy_done c s t hm hp hs =>
    intro hm' _ _ _ _
    exact absurd hm' (by simp)
  | home_start c s t hm hl hs =>
    intro hm' _ _ _ _
    exact absurd hm' (by simp)
  | home_step c s t hm hl hs =>
    intro hm' _ _ _ _
    exact absurd hm' (by simp [hm])
  | fpp_slice c s t hm hs =>
    intro hm' _ _ _ _
    exact absurd hm' (by simp [hm])
  | fpp_done c s t hm hs =>
    intro hm' _ _ _ _
    exact absurd hm' (by simp)
  | markEnd_found c s t hm he hs =>
    intro hm' _ _ _ _
    exact absurd hm' (by simp)
  | markEnd_step c s t hm he hs =>
    intro hm' _ _ _ _
    exact absurd hm' (by simp [hm])
  | choose_select c s t hm ho hs h =>
    intro hm' _ _ _ _
    exact absurd hm' (by simp)
  | choose_step c s t hm hs h =>
    intro hm' _ _ _ _
    exact absurd hm' (by simp [hm])
  | rewind_done c s t hm hf h =>
    intro hm' _ _ _ _
    exact absurd hm' (by simp)
  | rewind_one c s t hm hf hp h =>
    intro hm' _ _ _ _
    exact absurd hm' (by simp [hm])
  | rewind_pair c s t hm hf hp h =>
    intro hm' _ _ _ _
    exact absurd hm' (by simp [hm])
  | replayStart c s t o hm hrs ho ho' =>
    intro _ _ _ wch hchain
    obtain ⟨-, -, -, -, -, -, -, -, -, hch, -⟩ : replayStartVM entry s t := hrs
    rw [hch] at hchain
    cases hchain

end Entry

#print axioms terminal_palindrome
#print axioms shiftPal_of_chainRound
#print axioms shiftPal_of_readOrigin
#print axioms chainRound_tick

end PalPeg.CloseoutPackRun31
