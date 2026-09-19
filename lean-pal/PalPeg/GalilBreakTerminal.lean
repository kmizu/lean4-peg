import PalPeg.GalilEarlyBreak

/-!
# A found cycle's break happens at the cycle terminal

`GalilEarlyBreak.stageEntry_after_found_final` takes the controller fact
`hend3 : singlePositive s3.cycle = true`.  Here it is derived from the matched
comparison (`hmt3`) and the break (`hbr3 : vs3.chain = .broken w3'`):
off the terminal the chain prediction equals the left read
(`ReadOrigin.check_pair`), the comparison matched so it equals the right read,
which is also the verifier's read (`CaughtScan.aligned`); a breaking consume
(`BreakStep`) needs the verifier's read to differ from the prediction.
-/

set_option autoImplicit false

namespace PalPeg.GalilBreakTerminal

open GalilScaffoldCounter GalilScaffoldChainConsume GalilLastRadius
  PalPeg.GalilScaffoldChainInputSupply Manacher GalilScaffoldTop GalilScaffoldController
  GalilScaffoldInputHead GalilScaffoldChainVerifier

variable {raw : List (Fin 2)}

/-- The verifier of a caught scan reads what the right scan head reads after a
move right. -/
theorem caught_verifier_read {center radius : ℕ} {l r : PlaceHead}
    {s : GalilScaffoldChainWatch.State} (hi : CaughtScan raw center radius l r s)
    (hc : canRight r) : read (right s.machine.verifier) = read (right r) := by
  have hrrep := right_word r raw hi.scan.rightRep hc
  have hrpres := right_present r raw hi.scan.rightRep hi.scan.rightPresent hc
  have hrpos := right_position r hc
    (represented_position r.head raw hi.scan.rightRep hi.scan.rightPresent).1
  have hbound := position_bound (right r) raw hrrep hrpres
  have hvc := canRight_of_bound s.machine.verifier raw hi.verifierRep hi.verifierPresent
    (by rw [hi.aligned]; omega)
  have hvrep := right_word _ raw hi.verifierRep hvc
  have hvpres := right_present _ raw hi.verifierRep hi.verifierPresent hvc
  have hvpos := right_position s.machine.verifier hvc
    (represented_position s.machine.verifier.head raw hi.verifierRep hi.verifierPresent).1
  rw [represented_read _ raw hvrep hvpres, represented_read _ raw hrrep hrpres,
    hvpos, hrpos, hi.aligned]

/-- **`terminal_of_break_step`** at the `OnlyCompareState` level (hypotheses
`hi ht hl` as in `break_prediction_mismatch`). -/
theorem terminal_of_break_step (o : ReadOrigin raw)
    {center radius : ℕ} {s : OnlyCompareState} (extra : List (Fin 3))
    (hi : OnlyScan raw center radius (2*(o.interior.length+1)) extra.length
      s.left s.right s.watch s.cycle)
    (ht : GalilScaffoldChainWatchTrace.Trace o.shifted.machine extra s.watch.machine)
    (hl : LeftMoves o.resumeLeft extra.length s.left)
    (hc : canRight s.right)
    (hmatch : read (left s.left) = read (right s.right))
    {w' : GalilScaffoldChainWatch.State} (hbreak : BreakStep s.watch w') :
    singlePositive s.cycle = true := by
  cases hsp : singlePositive s.cycle with
  | true => rfl
  | false =>
    exfalso
    have hpred := (o.check_pair extra hi ht hl).mpr hsp
    obtain ⟨-, -, a, ha, hne, -⟩ := hbreak
    apply hne
    rw [caught_verifier_read hi.caught hc, ← hmatch, hpred, ha]

/-- **`hend3_of_matched_break`.**  The found cycle's breaking comparison is
at the cycle terminal. -/
theorem hend3_of_matched_break (P : Shared) (qq : ℕ) (first : Fin 9) (delay h : ℕ)
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
    (hz3 : GalilScaffoldCounter.zero w3.lag = true) (hav3 : canRight s3.right)
    (vs3 : ScanVM)
    (hcmp3 : (galilFrame P qq first).compare s3 (scanLens.set s3 vs3))
    (hmt3 : (galilFrame P qq first).matched (scanLens.set s3 vs3))
    (w3' : GalilScaffoldChainWatch.State) (hbr3 : vs3.chain = .broken w3') :
    singlePositive s3.cycle = true := by
  obtain ⟨-, w1, hw1, hz1, hp1, hcr⟩ := rounds_lift P qq first delay h hrounds v hpo rfl hzv
  obtain ⟨w2, hw2, hz2, -, hrun⟩ := scanSeg_only P qq first delay hseg3 w1 hp1 hw1 hz1
  have hww : w2 = w3 := by rw [hs3] at hw2; injection hw2 with e; exact e.symm
  subst hww
  have hmatch : read (left s3.left) = read (right s3.right) := by
    obtain ⟨⟨hl0, hr0, _⟩, _⟩ := hcmp3
    rw [scanLens.get_set] at hl0 hr0
    have := matched_parts P qq first hmt3
    rw [hl0, hr0] at this; exact this
  obtain ⟨-, -, htick⟩ := compare_parts P qq first hcmp3 hmatch
  rw [hs3, hbr3] at htick
  obtain ⟨-, hbreak⟩ := chainTick_true_broken hz2 htick
  obtain ⟨o', he', -, hinterior, -, -, -, -, -⟩ := rounds_origin hcr org hint hee
  have ht0 : GalilScaffoldChainWatchTrace.Trace o'.shifted.machine [] (toOnly s' w1).watch.machine := by
    rw [he'.machine]; exact GalilScaffoldChainWatchTrace.empty _
  have hl0 : LeftMoves o'.resumeLeft 0 (toOnly s' w1).left := by rw [he'.left]; exact .stop _
  have checked := o'.matched_checked hrun [] he'.scan he'.credit he'.radius ht0 hl0
  obtain ⟨-, finalExtra, -, htrace, hleft, hscan, -, -⟩ :=
    only_compare_history checked [] he'.scan he'.credit he'.radius ht0 hl0
  exact terminal_of_break_step o' finalExtra hscan htrace hleft hav3 hmatch hbreak

/-- **`stageEntry_after_found_closed`.**  `stageEntry_after_found_final` with
`hend3` replaced by the matched comparison and the break. -/
theorem stageEntry_after_found_closed (P : Shared) (qq : ℕ) (first : Fin 9) (delay h : ℕ)
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
    (hz3 : GalilScaffoldCounter.zero w3.lag = true)
    (w3' : GalilScaffoldChainWatch.State) (hw3' : w3' = GalilScaffoldChainWatch.immediate w3)
    (ha : PalPeg.GalilRadiusConsumed.Aligned org)
    (hbroken : w3'.machine.control.broken = true)
    (hav3 : canRight s3.right) (vs3 : ScanVM)
    (hcmp3 : (galilFrame P qq first).compare s3 (scanLens.set s3 vs3))
    (hmt3 : (galilFrame P qq first).matched (scanLens.set s3 vs3))
    (hbr3 : vs3.chain = .broken w3') :
    StageEntry (foundRestartRadius org.radius h m n) w3'.machine.control.last :=
  PalPeg.GalilEarlyBreak.stageEntry_after_found_final P qq first delay h org hint hpo hzv hee
    hrounds hseg3 w3 hs3 hz3 w3' hw3' ha hbroken
    (hend3_of_matched_break P qq first delay h org hint hpo hzv hee hrounds hseg3 w3 hs3 hz3 hav3
      vs3 hcmp3 hmt3 w3' hbr3)

#print axioms caught_verifier_read
#print axioms terminal_of_break_step
#print axioms hend3_of_matched_break
#print axioms stageEntry_after_found_closed

end PalPeg.GalilBreakTerminal
