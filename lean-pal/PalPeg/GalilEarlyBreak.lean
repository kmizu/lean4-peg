import PalPeg.GalilCatchUpDistance

/-!
# The early-break corner of `stageEntry_after_found_of_rounds`

`GalilCatchUpDistance.stageEntry_after_found_of_rounds` leaves
`hmore : h ≤ (org.shifts + m)*h + n`.  It can fail only for
`org.shifts + m = 0` and `n < h`.

* At the cycle terminal the corner is impossible: the round after the last
  shift starts at `used = 0` (`Entry.scan`), every matched comparison of the
  final `OnlyMatchedRun` raises `used` by one (`only_compare_history`), so at
  the break state `used = n`, and `singlePositive cycle ↔ used + 1 = 2*h`
  (`only_scan_dispatch`).  Hence a terminal break has `n = 2*h - 1 ≥ h`
  (`n_of_terminal`, `hmore_of_terminal`).
* Off the terminal the corner is *not* excluded by the hypotheses of
  `stageEntry_after_found_of_rounds`: there the chain prediction equals the
  left symbol (`ReadOrigin.check_pair`), so the watch breaks exactly on an
  outer mismatch, which may occur at `n = 0`.  The found cycle, however,
  breaks at the terminal (`hend3 : singlePositive s3.cycle = true`, the same
  named fact `radiusRep_at_break` already takes), so
  `stageEntry_after_found_final` takes that controller fact in place of `hmore`.
-/

set_option autoImplicit false

namespace PalPeg.GalilEarlyBreak

open GalilScaffoldCounter GalilScaffoldChainConsume GalilLastRadius
  PalPeg.GalilScaffoldChainInputSupply

variable {raw : List (Fin 2)}

/-- **`n_of_terminal`.**  A final matched run of the last round that ends at the
cycle terminal has exactly `2*h - 1` comparisons. -/
theorem n_of_terminal {h m n : ℕ} {s s' t : OnlyCompareState}
    (o : ReadOrigin raw) (hh : o.interior.length + 1 = h) (he : Entry raw o s)
    (hrounds : CompareRounds h s m s') (hmatched : OnlyMatchedRun s' n t)
    (hend : singlePositive t.cycle = true) : n + 1 = 2 * h := by
  obtain ⟨o', he', -, hinterior, -, -, -, -, -⟩ := rounds_origin hrounds o hh he
  have hh' : o'.interior.length + 1 = h := by rw [hinterior]; exact hh
  have ht0 : GalilScaffoldChainWatchTrace.Trace o'.shifted.machine [] s'.watch.machine := by
    rw [he'.machine]; exact GalilScaffoldChainWatchTrace.empty _
  have hl0 : LeftMoves o'.resumeLeft 0 s'.left := by rw [he'.left]; exact .stop _
  have checked := o'.matched_checked hmatched [] he'.scan he'.credit he'.radius ht0 hl0
  obtain ⟨-, finalExtra, hlen, -, -, hscan, -, -⟩ :=
    only_compare_history checked [] he'.scan he'.credit he'.radius ht0 hl0
  have hd := (only_scan_dispatch hscan).2.1 hend
  simp only [List.length_nil, Nat.zero_add] at hlen
  rw [hlen, hh'] at hd
  exact hd

/-- **`hmore_of_terminal`.** -/
theorem hmore_of_terminal {h m n : ℕ} {s s' t : OnlyCompareState}
    (o : ReadOrigin raw) (hh : o.interior.length + 1 = h) (he : Entry raw o s)
    (hrounds : CompareRounds h s m s') (hmatched : OnlyMatchedRun s' n t)
    (hend : singlePositive t.cycle = true) : h ≤ (o.shifts + m) * h + n := by
  have := n_of_terminal o hh he hrounds hmatched hend
  have : 1 ≤ h := by omega
  have : 0 ≤ (o.shifts + m) * h := Nat.zero_le _
  omega

open Manacher GalilScaffoldTop GalilScaffoldController GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-- **`hmore_of_break`** at the controller level: the final segment ends at the
cycle terminal. -/
theorem hmore_of_break (P : Shared) (qq : ℕ) (first : Fin 9) (delay h : ℕ)
    (org : ReadOrigin raw) (hint : org.interior.length + 1 = h)
    {s2' : GalilVM} {t' : ShiftState} {v : GalilScaffoldChainWatch.State} {cycle : Counter}
    (hpo : (shiftLens.set s2' ⟨t', .watch v, cycle⟩).periodOnly = true)
    (hzv : zero v.lag = true)
    (hee : Entry raw org (toOnly (shiftLens.set s2' ⟨t', .watch v, cycle⟩) v))
    {m : ℕ} {c1 c' : Control} {o : Bool} {s' : GalilVM}
    (hrounds : Rounds P qq first delay h m {c1 with mode := .scan, clock := delay, output := o}
      (shiftLens.set s2' ⟨t', .watch v, cycle⟩) c' s')
    {n : ℕ} {c3 : Control} {s3 : GalilVM} (hseg3 : ScanSeg P qq first delay n c' s' c3 s3)
    (hend3 : singlePositive s3.cycle = true) :
    h ≤ (org.shifts + m) * h + n := by
  obtain ⟨-, w', hw', hz', hp', hcr⟩ := rounds_lift P qq first delay h hrounds v hpo rfl hzv
  obtain ⟨w'', -, -, -, hrun⟩ := scanSeg_only P qq first delay hseg3 w' hp' hw' hz'
  exact hmore_of_terminal org hint hee hcr hrun hend3

/-- **`stageEntry_after_found_final`.**  `stageEntry_after_found_of_rounds`
with `hmore` discharged by the terminal fact of the found cycle's break. -/
theorem stageEntry_after_found_final (P : Shared) (qq : ℕ) (first : Fin 9) (delay h : ℕ)
    (org : ReadOrigin raw) (hint : org.interior.length + 1 = h)
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
    (hend3 : singlePositive s3.cycle = true) :
    StageEntry (foundRestartRadius org.radius h m n) w3'.machine.control.last :=
  PalPeg.GalilCatchUpDistance.stageEntry_after_found_of_rounds P qq first delay h org hint
    hpo hzv hee hrounds hseg3 w3 hs3 w3' hw3' ha hbroken
    (hmore_of_break P qq first delay h org hint hpo hzv hee hrounds hseg3 hend3)

#print axioms n_of_terminal
#print axioms hmore_of_terminal
#print axioms hmore_of_break
#print axioms stageEntry_after_found_final

end PalPeg.GalilEarlyBreak
