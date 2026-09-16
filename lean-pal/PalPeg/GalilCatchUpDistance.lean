import PalPeg.GalilLastLowerBreak
import PalPeg.GalilWatchPhase
import PalPeg.GalilScaffoldTopGuards
import PalPeg.GalilScaffoldTopOnly

/-!
# The chain's `distance` at a zero-lag watch state

`GalilLastLowerBreak.stageEntry_after_found_of_places` (`hplaces`) and
`GalilWatchPhase.phase_at_terminal_of_distance` (`hdist`) both ask for
`4*h ≤ value distance`.  This file computes `distance` exactly from the
catch-up ledger, and shows what does and does not follow.

## The exact identity (unconditional)

`distance_at_terminal`: along a `GalilScaffoldChainWatch.Run` out of the fresh
`watchStart` (the landing state of `prep_watch_start_trace`), at a state with
zero lag,

* `distance = 4*h + margin`  (conservation of `balance`, lag `= 0`), and
* `distance = radius + #matched(prep) + #matched(watch)`  (margin ledger:
  `prep_value` and `run_margin`, every outer matched event raises `margin`).

The second line is the scan radius at that point (`watch_period_guard` states
the same identity through `ScanInvariant`).  So `4*h ≤ distance` is literally
"the scan radius about the found centre has reached `4*h - 1`" — it is **not**
a consequence of the DP candidate: the candidate only gives the palindrome
extent `2*h` (`candidate_palAt`; and the extent of `extent_of_mismatch` is
about the centre `C - 2*h`, not the found centre `C = position ver` where the
chain's `distance` is anchored).  A mismatch at the found centre at a radius in
`[2h, 4h-1)` with the chain caught up is consistent with every ledger fact;
there `margin < 0`, the controller's `shiftGuardVM` is false and the cycle
takes the fallback (`GuardFail`).

## What discharges the gap

* `places_iff_margin`: `4*h ≤ distance ↔ 0 ≤ margin` at zero lag — no
  circularity: this is the identity, used in the direction *margin ⇒ distance*.
* `places_of_guard`: on the shift branch the guard `shiftGuardVM
  (afterMismatch s1 vs vq)` (with `periodOnly = false`, the fresh watch) carries
  `negative margin = false`, hence `hdist`.  `hdist_of_guard` /
  `phase_of_guard` feed `phase_at_terminal_of_distance` (the guard also carries
  `phase = 4` verbatim; both routes are given).
* `break_distance_lower`: at the break of a found cycle,
  `(S+3)*h + n ≤ distance` with `S = org.shifts + m` (`ReadOrigin.length`
  through `break_offset`'s offset).  Hence `hplaces` holds as soon as
  `h ≤ (org.shifts + m)*h + n`, i.e. unless the break happens in the very first
  round after the first shift within fewer than `h` matched comparisons.
  `stageEntry_after_found_of_rounds` is `stageEntry_after_found_of_places` with
  `hplaces` replaced by that one named hypothesis `hmore`.
-/

set_option autoImplicit false

namespace PalPeg.GalilCatchUpDistance

open GalilScaffoldCounter

/-! ## 1. The margin ledger during watch -/

theorem tick_margin {s t : GalilScaffoldChainWatch.State} {b : Bool}
    (ht : GalilScaffoldChainWatch.Tick s b t) :
    value t.margin = value s.margin + (if b then 1 else 0) := by
  cases ht with
  | step hi ho =>
    have hm : ∀ {x y : GalilScaffoldChainWatch.State}, GalilScaffoldChainWatch.Internal x y →
        y.margin = x.margin := by
      intro x y hi
      cases hi with
      | idle => rfl
      | take => rfl
    cases ho with
    | idle => simp [hm hi]
    | queued => simp [GalilScaffoldChainWatch.queued, inc_value, hm hi]
    | immediate => simp [GalilScaffoldChainWatch.immediate, inc_value, hm hi]

/-- Every outer matched event raises `margin` by one; nothing else touches it. -/
theorem run_margin {s t : GalilScaffoldChainWatch.State} {es : List Bool}
    (hr : GalilScaffoldChainWatch.Run s es t) :
    value t.margin = value s.margin + (es.count true : ℤ) := by
  induction hr with
  | stop => simp
  | @next s m t b bs ht _ ih =>
    rw [ih, tick_margin ht]
    cases b <;> (simp; try ring)

/-! ## 2. The exact distance at zero lag -/

open PalPeg.GalilScaffoldChainInputSupply in
/-- **`distance_at_terminal`.**  Along any watch run out of the fresh
`watchStart` of `prep_watch_start_trace`, at zero lag the chain's `distance`
equals `4*h + margin`, and equals the scan radius
`radius + #matched(prep) + #matched(watch)`. -/
theorem distance_at_terminal (cen : GalilScaffoldInputHead.PlaceHead) (c : Fin 3)
    (ys : List (Fin 3)) (b : Fin 3) (radius : Counter) (hrc : Canonical radius)
    (sm dm : Bool) (bs cs : List Bool) (hbl : bs.length = ys.length + 1)
    {es : List Bool} {w : GalilScaffoldChainWatch.State}
    (hr : GalilScaffoldChainWatch.Run (watchStart cen c ys b (GalilScaffoldChainCredits.run
      (GalilScaffoldChainCredits.start radius) (GalilScaffoldChainCredits.prepEvents sm dm bs cs)))
      es w)
    (hz : zero w.lag = true) :
    value w.machine.control.distance = 4*((ys.length : ℤ)+1) + value w.margin ∧
    value w.machine.control.distance =
      value radius + ((sm :: (bs ++ dm :: cs)).count true : ℤ) + (es.count true : ℤ) ∧
    GalilScaffoldChainWatch.CanonicalState w := by
  set final := GalilScaffoldChainCredits.run (GalilScaffoldChainCredits.start radius)
    (GalilScaffoldChainCredits.prepEvents sm dm bs cs) with hfinal
  have hcf := GalilScaffoldChainCredits.run_canonical (GalilScaffoldChainCredits.start radius)
    (GalilScaffoldChainCredits.prepEvents sm dm bs cs) hrc hrc
  have hcs : GalilScaffoldChainWatch.CanonicalState (watchStart cen c ys b final) :=
    ⟨hcf.2, hcf.1⟩
  have hcw := GalilScaffoldChainWatch.run_canonical hr hcs
  have hl0 : value w.lag = 0 := (zero_iff _ hcw.1).mp hz
  have hb0 := GalilScaffoldChainWatch.prepared_balance
    ⟨cen, GalilScaffoldChainConsume.ready c ys b⟩ rfl radius sm dm bs cs
  have hb := GalilScaffoldChainWatch.run_balance hr
  have hbs : GalilScaffoldChainWatch.balance (watchStart cen c ys b final) = 4*(bs.length : ℤ) :=
    hb0
  rw [hbs] at hb
  unfold GalilScaffoldChainWatch.balance at hb
  have hpv := GalilScaffoldChainCredits.prep_value radius sm dm bs cs
  dsimp only at hpv
  have hm := run_margin hr
  have hm0 : value (watchStart cen c ys b final).margin = value final.margin := rfl
  rw [hm0] at hm
  rw [hbl] at hb hpv
  refine ⟨by push_cast at hb ⊢; linarith, ?_, hcw⟩
  have e1 : value final.margin = value radius - 4*((ys.length + 1 : ℕ) : ℤ) +
      ((sm :: (bs ++ dm :: cs)).count true : ℤ) := hpv.1
  push_cast at hb e1 ⊢
  linarith

open PalPeg.GalilScaffoldChainInputSupply in
/-- **`4*h` places ↔ nonnegative margin**, at zero lag.  Used left-to-right
from the guard; this is not `caught_margin` run backwards. -/
theorem places_iff_margin (cen : GalilScaffoldInputHead.PlaceHead) (c : Fin 3)
    (ys : List (Fin 3)) (b : Fin 3) (radius : Counter) (hrc : Canonical radius)
    (sm dm : Bool) (bs cs : List Bool) (hbl : bs.length = ys.length + 1)
    {es : List Bool} {w : GalilScaffoldChainWatch.State}
    (hr : GalilScaffoldChainWatch.Run (watchStart cen c ys b (GalilScaffoldChainCredits.run
      (GalilScaffoldChainCredits.start radius) (GalilScaffoldChainCredits.prepEvents sm dm bs cs)))
      es w)
    (hz : zero w.lag = true) :
    4*((ys.length : ℤ)+1) ≤ value w.machine.control.distance ↔ 0 ≤ value w.margin := by
  have hd := (distance_at_terminal cen c ys b radius hrc sm dm bs cs hbl hr hz).1
  constructor <;> intro h0 <;> linarith

/-! ## 3. The guard discharges `hdist` at the first terminal -/

open GalilScaffoldTop GalilScaffoldController GalilScaffoldInputHead
  GalilScaffoldChainVerifier PalPeg.GalilScaffoldChainInputSupply

/-- At a zero-lag mismatching comparison the chain tick is idle. -/
theorem mismatch_chain_same (P : Shared) (q : ℕ) (first : Fin 9) {s1 : GalilVM}
    {w : GalilScaffoldChainWatch.State} (hs1 : s1.chain = .watch w) (hz : zero w.lag = true)
    {vs : ScanVM}
    (hcmp : (galilFrame P q first).compare s1 (scanLens.set s1 vs))
    (hmis : ¬ (galilFrame P q first).matched (scanLens.set s1 vs)) :
    vs.chain = .watch w := by
  obtain ⟨⟨hl, hr, ht⟩, _⟩ := hcmp
  rw [scanLens.get_set] at hl hr ht
  have hmatch0 : ¬ read (left s1.left) = read (right s1.right) := by
    intro h0
    apply hmis
    show read (scanLens.get (scanLens.set s1 vs)).left = read (scanLens.get (scanLens.set s1 vs)).right
    rw [scanLens.get_set]
    have hl' : vs.left = left s1.left := hl
    have hr' : vs.right = right s1.right := hr
    show read vs.left = read vs.right
    rw [hl', hr']; exact h0
  have ht' : ChainTick (decide (read (left s1.left) = read (right s1.right))) s1.chain vs.chain := ht
  rw [decide_eq_false hmatch0, hs1] at ht'
  exact chainTick_false_idle hz ht'

/-- **The guard gives the place count.**  On the shift branch of a fresh
(`periodOnly = false`) watch, `shiftGuardVM` carries `negative margin = false`,
which by `places_iff_margin` is `4*h ≤ distance`. -/
theorem places_of_guard (P : Shared) (qq : ℕ) (first : Fin 9)
    (cen : PlaceHead) (c : Fin 3) (ys : List (Fin 3)) (b : Fin 3)
    (radius : Counter) (hrc : Canonical radius)
    (sm dm : Bool) (bs cs : List Bool) (hbl : bs.length = ys.length + 1)
    {es : List Bool} {w : GalilScaffoldChainWatch.State}
    (hr : GalilScaffoldChainWatch.Run (watchStart cen c ys b (GalilScaffoldChainCredits.run
      (GalilScaffoldChainCredits.start radius) (GalilScaffoldChainCredits.prepEvents sm dm bs cs)))
      es w)
    (hz : zero w.lag = true)
    {s1 : GalilVM} (hs1 : s1.chain = .watch w) (hpo : s1.periodOnly = false)
    {vs : ScanVM} {vq : SearchVM}
    (hcmp : (galilFrame P qq first).compare s1 (scanLens.set s1 vs))
    (hmis : ¬ (galilFrame P qq first).matched (scanLens.set s1 vs))
    (hg : shiftGuardVM (afterMismatch s1 vs vq)) :
    4*((ys.length : ℤ)+1) ≤ value w.machine.control.distance ∧
      w.machine.control.phase = 4 := by
  have hvs := mismatch_chain_same P qq first hs1 hz hcmp hmis
  obtain ⟨w', hw', _, hph, _, hif, _⟩ := hg
  have hc : (afterMismatch s1 vs vq).chain = vs.chain := rfl
  rw [hc, hvs] at hw'
  cases hw'
  have hpo' : (afterMismatch s1 vs vq).periodOnly = false := hpo
  rw [hpo', if_neg (by simp)] at hif
  have hcw := (distance_at_terminal cen c ys b radius hrc sm dm bs cs hbl hr hz).2.2
  have hnn : 0 ≤ value w.margin := by
    cases hn : negative w.margin
    · have := (negative_iff _ hcw.2)
      by_contra hlt
      have : negative w.margin = true := this.mpr (by omega)
      rw [hn] at this; exact absurd this (by simp)
    · rw [hn] at hif; exact absurd hif (by simp)
  exact ⟨(places_iff_margin cen c ys b radius hrc sm dm bs cs hbl hr hz).mpr hnn, hph⟩

/-- `hdist` of `GalilWatchPhase.phase_at_terminal_of_distance`, in its own shape. -/
theorem hdist_of_guard (P : Shared) (qq : ℕ) (first : Fin 9)
    (cen : PlaceHead) (c : Fin 3) (ys : List (Fin 3)) (b : Fin 3) (h : ℕ)
    (hh : h = ys.length + 1)
    (radius : Counter) (hrc : Canonical radius)
    (sm dm : Bool) (bs cs : List Bool) (hbl : bs.length = h)
    {es : List Bool} {w : GalilScaffoldChainWatch.State}
    (hr : GalilScaffoldChainWatch.Run (watchStart cen c ys b (GalilScaffoldChainCredits.run
      (GalilScaffoldChainCredits.start radius) (GalilScaffoldChainCredits.prepEvents sm dm bs cs)))
      es w)
    (hz : zero w.lag = true)
    {s1 : GalilVM} (hs1 : s1.chain = .watch w) (hpo : s1.periodOnly = false)
    {vs : ScanVM} {vq : SearchVM}
    (hcmp : (galilFrame P qq first).compare s1 (scanLens.set s1 vs))
    (hmis : ¬ (galilFrame P qq first).matched (scanLens.set s1 vs))
    (hg : shiftGuardVM (afterMismatch s1 vs vq)) :
    4*(h : ℤ) ≤ value w.machine.control.distance := by
  subst hh
  have := (places_of_guard P qq first cen c ys b radius hrc sm dm bs cs hbl hr hz hs1 hpo
    hcmp hmis hg).1
  push_cast
  linarith

/-- `phase_at_terminal_of_distance` with `hdist` discharged by the guard. -/
theorem phase_of_guard (P : Shared) (qq : ℕ) (first : Fin 9)
    (cen : PlaceHead) (c : Fin 3) (ys : List (Fin 3)) (b : Fin 3) (h : ℕ)
    (hh : h = ys.length + 1)
    (radius : Counter) (hrc : Canonical radius)
    (sm dm : Bool) (bs cs : List Bool) (hbl : bs.length = h)
    {es : List Bool} {w : GalilScaffoldChainWatch.State}
    (hr : GalilScaffoldChainWatch.Run (watchStart cen c ys b (GalilScaffoldChainCredits.run
      (GalilScaffoldChainCredits.start radius) (GalilScaffoldChainCredits.prepEvents sm dm bs cs)))
      es w)
    (hz : zero w.lag = true)
    (zs : List (Fin 3))
    (htrace : w.machine.control
      = GalilScaffoldChainSweep.run (GalilScaffoldChainConsume.ready c ys b) zs)
    (hnb : w.machine.control.broken = false)
    {s1 : GalilVM} (hs1 : s1.chain = .watch w) (hpo : s1.periodOnly = false)
    {vs : ScanVM} {vq : SearchVM}
    (hcmp : (galilFrame P qq first).compare s1 (scanLens.set s1 vs))
    (hmis : ¬ (galilFrame P qq first).matched (scanLens.set s1 vs))
    (hg : shiftGuardVM (afterMismatch s1 vs vq)) :
    w.machine.control.phase = 4 :=
  PalPeg.GalilWatchPhase.phase_at_terminal_of_distance c b ys h hh w zs htrace hnb
    (hdist_of_guard P qq first cen c ys b h hh radius hrc sm dm bs cs hbl hr hz hs1 hpo
      hcmp hmis hg)

/-! ## 4. The break of a found cycle -/

open GalilScaffoldChainConsume GalilLastRadius

variable {raw : List (Fin 2)}

/-- **`break_distance_lower`.**  At the break of `m` chained rounds and `n`
matched comparisons, `(S+3)*h + n ≤ distance` with `S = o.shifts + m`: the
origin carries `2*(S+2)*h ≤ pre.length` (`ReadOrigin.length`) and the control is
lowered by `(S+1)*h`. -/
theorem break_distance_lower {h m n : ℕ} {s s' t : OnlyCompareState}
    (o : ReadOrigin raw) (hh : o.interior.length + 1 = h) (he : Entry raw o s)
    (hrounds : CompareRounds h s m s') (hmatched : OnlyMatchedRun s' n t) :
    (((o.shifts + m + 3) * h + n : ℕ) : ℤ) ≤ value t.watch.machine.control.distance := by
  obtain ⟨o', he', -, hinterior, -, -, hshifts, -, -⟩ := rounds_origin hrounds o hh he
  have hh' : o'.interior.length + 1 = h := by rw [hinterior]; exact hh
  have ht0 : GalilScaffoldChainWatchTrace.Trace o'.shifted.machine [] s'.watch.machine := by
    rw [he'.machine]; exact GalilScaffoldChainWatchTrace.empty _
  have hl0 : LeftMoves o'.resumeLeft 0 s'.left := by rw [he'.left]; exact .stop _
  have checked := o'.matched_checked hmatched [] he'.scan he'.credit he'.radius ht0 hl0
  obtain ⟨-, finalExtra, hlen, htrace, -⟩ :=
    only_compare_history checked [] he'.scan he'.credit he'.radius ht0 hl0
  have hshift := (chain_shift_values o'.shiftRun).1
  have hdist := htrace.distance
  have hod := PalPeg.GalilRadiusConsumed.origin_distance o'
  have hlen' : (finalExtra.length : ℤ) = (n : ℤ) := by simp [hlen]
  have hpre := o'.length
  rw [hh', hshifts] at hpre
  rw [hshift, hh', hod, hh', hshifts] at hdist
  rw [hlen'] at hdist
  have hpreZ : ((2*(o.shifts + m + 2)*h : ℕ) : ℤ) ≤ (o'.pre.length : ℤ) := by exact_mod_cast hpre
  push_cast at hpreZ hdist ⊢
  nlinarith

/-- `hplaces` at the break, from the single residual `hmore`. -/
theorem places_at_break {h m n : ℕ} {s s' t : OnlyCompareState}
    (o : ReadOrigin raw) (hh : o.interior.length + 1 = h) (he : Entry raw o s)
    (hrounds : CompareRounds h s m s') (hmatched : OnlyMatchedRun s' n t)
    (hmore : h ≤ (o.shifts + m) * h + n) :
    (4 * h : ℤ) ≤ value t.watch.machine.control.distance := by
  have hb := break_distance_lower o hh he hrounds hmatched
  have : 4 * h ≤ (o.shifts + m + 3) * h + n := by nlinarith
  have hz : ((4 * h : ℕ) : ℤ) ≤ (((o.shifts + m + 3) * h + n : ℕ) : ℤ) := by exact_mod_cast this
  push_cast at hz hb ⊢
  linarith

open GalilScaffoldChainVerifier in
/-- **`stageEntry_after_found_of_places` with `hplaces` discharged** down to
`hmore : h ≤ (org.shifts + m)*h + n`. -/
theorem stageEntry_after_found_of_rounds (P : Shared) (qq : ℕ) (first : Fin 9) (delay h : ℕ)
    {raw : List (Fin 2)} (org : ReadOrigin raw) (hint : org.interior.length + 1 = h)
    {s2' : GalilVM} {t' : ShiftState} {v : GalilScaffoldChainWatch.State} {cycle : Counter}
    (hpo : (shiftLens.set s2' ⟨t', .watch v, cycle⟩).periodOnly = true)
    (hzv : zero v.lag = true)
    (hee : Entry raw org (toOnly (shiftLens.set s2' ⟨t', .watch v, cycle⟩) v))
    {m : ℕ} {c1 c' : Control} {o : Bool} {s' : GalilVM}
    (hrounds : Rounds P qq first delay h m {c1 with mode := .scan, clock := delay, output := o}
      (shiftLens.set s2' ⟨t', .watch v, cycle⟩) c' s')
    {n : ℕ} {c3 : Control} {s3 : GalilVM} (hseg3 : ScanSeg P qq first delay n c' s' c3 s3)
    (w3 : GalilScaffoldChainWatch.State) (hs3 : s3.chain = .watch w3)
    (w3' : GalilScaffoldChainWatch.State) (hw3' : w3' = GalilScaffoldChainWatch.immediate w3)
    (ha : PalPeg.GalilRadiusConsumed.Aligned org)
    (hbroken : w3'.machine.control.broken = true)
    (hmore : h ≤ (org.shifts + m) * h + n) :
    StageEntry (foundRestartRadius org.radius h m n) w3'.machine.control.last := by
  refine PalPeg.GalilLastLowerBreak.stageEntry_after_found_of_places P qq first delay h org hint
    hpo hzv hee hrounds hseg3 w3 hs3 w3' hw3' ha hbroken ?_
  obtain ⟨-, w', hw', hz', hp', hcr⟩ := rounds_lift P qq first delay h hrounds v hpo rfl hzv
  obtain ⟨w'', hw'', -, -, hrun⟩ := scanSeg_only P qq first delay hseg3 w' hp' hw' hz'
  have hww : w'' = w3 := by rw [hs3] at hw''; injection hw'' with e; exact e.symm
  subst hww
  subst hw3'
  have hpl := places_at_break org hint hee hcr hrun hmore
  have hpre : w''.machine.control.broken = false := by
    obtain ⟨-, -, -, -, -, -, -, -, hp⟩ :=
      PalPeg.GalilLastLowerBreak.break_offset org hint hee hcr hrun
    exact hp
  obtain ⟨hdist, -⟩ := break_gap w''.machine.control (read (right w''.machine.verifier)) hpre hbroken
  show (4 * h : ℤ) ≤ value (consume w''.machine.control (read (right w''.machine.verifier))).distance
  rw [hdist]
  exact hpl

#print axioms tick_margin
#print axioms run_margin
#print axioms distance_at_terminal
#print axioms places_iff_margin
#print axioms mismatch_chain_same
#print axioms places_of_guard
#print axioms hdist_of_guard
#print axioms phase_of_guard
#print axioms break_distance_lower
#print axioms places_at_break
#print axioms stageEntry_after_found_of_rounds

end PalPeg.GalilCatchUpDistance
