import PalPeg.RestartCertificate
import PalPeg.LowerExcludedAtBreak

/-!
# The lower bound installed by a broken restart

The inputs of `LowerExcludedAtBreak.lowerExcluded_of_break`, read off the verified window of the
watch that breaks: the period of the whole scan span and the one-place mismatch.
-/

set_option autoImplicit false

namespace PalPeg.RestartLower

open PalPeg GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open GalilScaffoldChainInputSupply GalilBranchInvariants
open PalPeg.ShiftPalAlongTrace PalPeg.GalilReplaySpan PalPeg.GalilReplayGeneral2
open PalPeg.RestartBoundary PalPeg.LowerExcludedAtBreak

/-- The verifier of a lag-zero watch stands on the right scan head. -/
theorem verifier_at_right {raw : List (Fin 2)} {cen₀ P : ℕ} {cc b : Fin 3} {xs : List (Fin 3)}
    {w : GalilScaffoldChainWatch.State}
    (hwindow : WatchWindow raw cen₀ P cc b xs (.watch w)) (hzero : zero w.lag = true) :
    position w.machine.verifier = P := by
  obtain ⟨⟨-, hposition⟩, -, -⟩ := hwindow
  have hlagEmpty : w.lag.pos = [] := by
    rcases hw : w.lag with ⟨pos, neg⟩
    rw [hw] at hzero
    simp only [zero, Bool.and_eq_true, List.isEmpty_iff] at hzero
    exact hzero.1
  rw [hlagEmpty] at hposition
  simpa using hposition

/-- The whole scan span of a caught-up watch has period `2h`. -/
theorem spanPeriod_of_window {raw : List (Fin 2)} {cen₀ C d m : ℕ} {cc b : Fin 3}
    {xs : List (Fin 3)} {w : GalilScaffoldChainWatch.State}
    (hwindow : WatchWindow raw cen₀ (C + d) cc b xs (.watch w)) (hzero : zero w.lag = true)
    (hcentre : (encoded raw)[cen₀]? = some cc) (hk : C = cen₀ + m * (xs.length + 1))
    (hpal : Manacher.PalAt (encoded raw) C d) (hhd : 2 * (xs.length + 1) ≤ d) :
    PeriodOn (encoded raw) (2 * (xs.length + 1)) (C - d) (C + d) := by
  have hverifier := verifier_at_right hwindow hzero
  obtain ⟨-, hblock, -⟩ := hwindow
  rw [hverifier] at hblock
  have hlen : C + d < (encoded raw).length := hpal.2.1
  have hfromCentre : PeriodOn (encoded raw) (2 * (xs.length + 1)) cen₀ (C + d) :=
    periodOn_extend_left (periodOn_of_blockOn hblock)
      (by rw [hcentre, block_last_of_blockOn hblock (by omega)])
  have hblockPal := palAt_block_periodic hblock hcentre hlen m (by omega)
  rw [← hk] at hblockPal
  exact periodOn_span_of_halves hpal hhd (hfromCentre.mono (by omega) (le_refl _)) hblockPal

/-- The place a lag-zero break reads differs from the place two semiperiods back. -/
theorem break_mismatch_of_window {raw : List (Fin 2)} {cen₀ P : ℕ} {cc b : Fin 3}
    {xs : List (Fin 3)} {w w' : GalilScaffoldChainWatch.State}
    (hwindow : WatchWindow raw cen₀ P cc b xs (.watch w))
    (hsize : cen₀ + 1 + 2 * (xs.length + 1) ≤ P + 1) (hbreak : BreakStep w w') :
    (encoded raw)[P + 1 - 2 * (xs.length + 1)]? ≠ (encoded raw)[P + 1]? := by
  intro heq
  have hback : P + 1 - 2 * (xs.length + 1) + 2 * (xs.length + 1) = P + 1 := by omega
  exact not_breakStep_of_text (leftPlace := P + 1 - 2 * (xs.length + 1)) hwindow hsize
    (by rw [hback]; exact heq) (by rw [hback]; exact heq) heq hbreak

open GalilScaffoldTop GalilScaffoldController GalilRunSkeleton GalilInvPlus3
open PalPeg.WindowPack PalPeg.WindowRun PalPeg.WindowInv PalPeg.GalilChainCoupling
open PalPeg.RestartStageRun PalPeg.RestartStageLedger PalPeg.CanonicalChainMinimal
open PalPeg.CanonicalSearchProgram

/-- **The lower bound a broken restart installs is excluded.**  At a lag-zero break of a
window-packed scan state whose margin is nonnegative afterwards: the old chain's minimal period,
the verified span and the mark ledger exclude every semiperiod `δ ≤ last` on every span that
contains the break (radius at least `Rad`, the radius the restart sees). -/
theorem lowerExcluded_at_break {Move : ℕ → ℕ → Prop} {raw : List (Fin 2)} {c : Control}
    {s : GalilVM} {w1 w' : GalilScaffoldChainWatch.State} {R L : ℕ}
    (hwin : WindowRunPack raw c s) (hm : c.mode = Mode.scan)
    (hscan : ScanInvariant raw (position s.center) R s.left s.right)
    (hradius : RadiusRep s.radius R)
    (hledger : ChainLedger 0 s.chain) (hminimal : ScanMinimal Move raw s)
    (hstep : ChainStep s.chain (.watch w1)) (hbreak : BreakStep w1 w')
    (hmargin : negative w'.margin = false)
    (hinterior : value w1.machine.control.distance ≠ 4 * (periodLength w1 : ℤ) - 1)
    (hlast : value w'.machine.control.last = (L : ℤ))
    {Rad : ℕ} (hRad : (Rad : ℤ) = value w1.machine.control.distance + 1) :
    Rad ≤ 4 * (L + 1) ∧ LowerExcludedFrom raw (position s.center) L Rad := by
  have hunbroken0 := watch_unbroken_of_window hwin
  have hunbroken1 := unbroken_of_step hstep hunbroken0
  have hledger1 : WatchLedger 0 w1 := chainLedger_step hstep hwin.coupled.block hledger hunbroken1
  have hmarginValue : 0 ≤ value w1.margin + 1 := by
    have h0 := value_nonneg_of_not_negative hmargin
    obtain ⟨-, -, -, -, -, hweq⟩ := hbreak
    rw [hweq] at h0
    change 0 ≤ value (inc w1.margin) at h0
    rwa [inc_value] at h0
  have hfour := hledger1.four_of_break hbreak.1 hmarginValue hinterior
  obtain ⟨hlastLow, hlastHigh⟩ := hledger1.last_bounds hfour
  have hlastEq : w'.machine.control.last = w1.machine.control.last := by
    obtain ⟨-, -, a, hsymbol, hread, hweq⟩ := hbreak
    rw [hweq]
    show (GalilScaffoldChainVerifier.consume w1.machine).control.last = _
    have hcontrol : (GalilScaffoldChainVerifier.consume w1.machine).control
        = {w1.machine.control with broken := true} :=
      GalilScaffoldChainConsume.mismatch w1.machine.control a _ hsymbol hread
    rw [hcontrol]
  rw [hlastEq] at hlast
  generalize hy : ChainVM.watch w1 = y at hstep
  generalize hx : s.chain = x at hstep
  cases hstep with
  | idle => cases hy
  | brokenIdle => cases hy
  | copyBit => cases hy
  | copyEnd => cases hy
  | backStep => cases hy
  | watchBreak => cases hy
  | backDone v h lag margin ver hf =>
    cases hy
    exfalso
    have hzero : value (watchControl v).distance = 0 := rfl
    have hd : value (⟨⟨ver, watchControl v⟩, lag, margin⟩ :
        GalilScaffoldChainWatch.State).machine.control.distance = 0 := hzero
    rw [hd] at hlastLow hfour
    have hfwd := hledger1.marks.forward rfl
    have hsize := hledger1.marks.size
    have hpos : (1 : ℤ) ≤ (periodLength (⟨⟨ver, watchControl v⟩, lag, margin⟩ :
        GalilScaffoldChainWatch.State) : ℤ) := by
      have : 1 ≤ periodLength (⟨⟨ver, watchControl v⟩, lag, margin⟩ :
          GalilScaffoldChainWatch.State) := by omega
      exact_mod_cast this
    linarith
  | watchStep w0 w1' hinternal =>
    cases hy
    have hchain : s.chain = .watch w0 := hx
    obtain ⟨cen₀, cc, hcentre, hinv, hk, -, -⟩ := hwin.window
    rw [hchain] at hinv
    obtain ⟨b, xs, hW0⟩ := hinv
    have hW1 := watchWindow_step hW0 hinternal
    have hlength1 : periodLength w1 = xs.length + 1 := periodLength_of_coreP hW1.2.2
    have hlength0 : periodLength w0 = xs.length + 1 := periodLength_of_coreP hW0.2.2
    obtain ⟨m, hk⟩ := (hk w0 hchain).2 (by rw [hm]; decide)
    rw [hlength0] at hk
    -- the radius is the distance
    have hsum0 : SumRel (.watch w0) (value s.radius) := by
      have := hwin.coupled.sum; rwa [hchain] at this
    have hblock0 : BlockInv (.watch w0) := by
      have := hwin.coupled.block; rwa [hchain] at this
    have hsum1 : SumRel (.watch w1) (value s.radius) :=
      (step_inv (.watchStep w0 w1 hinternal) (F := True) trivial (O := fun _ => True) hblock0
        hsum0 (fun _ _ _ => Or.inr trivial)).1
    have hd := hsum1 hunbroken1
    rw [value_zero_of_zero hbreak.1, add_zero, hradius.2] at hd
    have hRadEq : Rad = R + 1 := by
      rw [hd] at hRad
      exact_mod_cast hRad
    subst hRadEq
    rw [hd, hlength1, hlast] at hlastLow
    rw [hd, hlast] at hlastHigh
    rw [hd, hlength1] at hfour
    have hfourN : 4 * (xs.length + 1) ≤ R := by exact_mod_cast hfour
    have hlowN : L + (xs.length + 1) ≤ R := by exact_mod_cast hlastLow
    have hhighN : R + 1 ≤ 4 * (L + 1) := by exact_mod_cast hlastHigh
    have hRC := scan_radius_lt hscan
    have hpal := hscan.palindrome
    have hright : position s.right = position s.center + R := hscan.rightPos
    rw [hright] at hW1
    have hperiod := spanPeriod_of_window hW1 hbreak.1 hcentre hk hpal (by omega)
    have hmismatch := break_mismatch_of_window hW1 (by rw [hk]; nlinarith) hbreak
    have hperiodSpan : HasPeriod (Span raw (position s.center) R) (2 * periodLength w0) := by
      rw [hlength0]
      unfold Span
      rw [show 2*R+1 = (position s.center + R) + 1 - (position s.center - R) from by omega]
      exact (hasPeriod_slice_iff (x := encoded raw) (p := 2 * (xs.length + 1)) hpal.2.1
        (by omega)).mpr hperiod
    have hnoShort := scanMinimal_watch_no_short hminimal hchain hright hRC hpal
      (by rw [hlength0]; exact hfourN) hperiodSpan
    rw [hlength0] at hnoShort
    exact ⟨hhighN,
      lowerExcluded_of_break hpal hperiod hnoShort hmismatch (by omega) (by omega) hlowN⟩

/-- **The fallback move inequality when a caught-up watch mispredicts.**  The scan span has the
chain's period `2h` (verified window), that period is minimal there (`hnoShortOf`: the birth
payload in the first round, the thresholded minimality after a shift), and the place the
fallback window adds breaks it, because the prediction is the text two semiperiods back and
differs from the place just read. -/
theorem move_of_prediction_break {raw : List (Fin 2)} {c : Control}
    {s : GalilVM} {w0 w1 : GalilScaffoldChainWatch.State} {R : ℕ} {vq : SearchVM} {z : ChainVM}
    (hwin : WindowRunPack raw c s) (hm : c.mode = Mode.scan)
    (hscan : ScanInvariant raw (position s.center) R s.left s.right)
    (hcan : canRight s.right) (hlen : value s.length = (2*R+1 : ℕ))
    (hchain : s.chain = .watch w0) (hinternal : GalilScaffoldChainWatch.Internal w0 w1)
    (hzero : zero w1.lag = true) (htwo : 2 * periodLength w1 ≤ R)
    (hnoShortOf : periodLength w0 = periodLength w1 →
      HasPeriod (Span raw (position s.center) R) (2 * periodLength w0) →
      ∀ p, 0 < p → p < 2 * periodLength w0 → ¬ HasPeriod (Span raw (position s.center) R) p)
    (hprediction : GalilScaffoldChainConsume.symbol w1.machine.control.period.focus
      ≠ read (right s.right)) :
    let s1 := afterBirth (chainBorn (decide (vq.search.mode = .found)) s.chain)
      (afterMismatch s ⟨left s.left,right s.right,z⟩ vq)
    let ℓ := (value s.length).toNat
    let radius := chosenRadius
      ((GalilScaffoldPlace.stream (PalPeg.GalilTickFair.rightPlace s1)).take (ℓ+1))
    ℓ / 2 ≤ 4 * (ℓ / 2 + 1 - radius) := by
  obtain ⟨cen₀, cc, hcentre, hinv, hk, -, -⟩ := hwin.window
  rw [hchain] at hinv
  obtain ⟨b, xs, hW0⟩ := hinv
  have hW1 := watchWindow_step hW0 hinternal
  have hlength0 : periodLength w0 = xs.length + 1 := periodLength_of_coreP hW0.2.2
  have hlength1 : periodLength w1 = xs.length + 1 := periodLength_of_coreP hW1.2.2
  obtain ⟨m, hk⟩ := (hk w0 hchain).2 (by rw [hm]; decide)
  rw [hlength0] at hk
  rw [hlength1] at htwo
  have hRC := scan_radius_lt hscan
  have hpal := hscan.palindrome
  have hright : position s.right = position s.center + R := hscan.rightPos
  rw [hright] at hW1
  have hsize : cen₀ + 1 + 2 * (xs.length + 1) ≤ position s.center + R + 1 := by
    rw [hk]; nlinarith
  have hperiod := spanPeriod_of_window hW1 hzero hcentre hk hpal (by omega)
  have hperiodSpan : HasPeriod (Span raw (position s.center) R) (2 * (xs.length + 1)) := by
    unfold Span
    rw [show 2*R+1 = (position s.center + R) + 1 - (position s.center - R) from by omega]
    exact (hasPeriod_slice_iff (x := encoded raw) (p := 2 * (xs.length + 1)) hpal.2.1
      (by omega)).mpr hperiod
  have hnoShort := hnoShortOf (hlength0.trans hlength1.symm)
    (by rw [hlength0]; exact hperiodSpan)
  rw [hlength0] at hnoShort
  obtain ⟨-, hpredictionText⟩ := prediction_eq_text hW1 hzero hsize
  have hleft0 : 0 < s.right.head.left.length :=
    (represented_position _ raw hscan.rightRep hscan.rightPresent).1
  have hnextRead : read (right s.right) = (encoded raw)[position s.center + R + 1]? := by
    rw [represented_read _ raw (right_word _ raw hscan.rightRep hcan)
      (right_present _ raw hscan.rightRep hscan.rightPresent hcan),
      right_position _ hcan hleft0, hright]
  refine PalPeg.CanonicalFallbackInput.move_of_activePeriodBreak (c := c) hscan hcan hlen hRC
    (by omega) (by omega) hperiodSpan hnoShort ?_ rfl
  intro x hx hper
  apply hprediction
  rw [hpredictionText, hnextRead]
  -- the head of the fallback window is the place just read
  have hrrep : GalilScaffoldInputTrace.Represents (right s.right).head raw :=
    right_word _ raw hscan.rightRep hcan
  have hrpres : (right s.right).head.focus ≠ none :=
    right_present _ raw hscan.rightRep hscan.rightPresent hcan
  obtain ⟨a, ys, rs, q', hdec, hraw⟩ := represents_decompose (right s.right) raw hrrep hrpres
  have hstream : (GalilScaffoldPlace.stream ⟨a :: ys,(right s.right).gap⟩).length
      = position s.center + R + 1 := by
    rw [stream_length_of_place a ys rs q' hdec, right_position s.right hcan hleft0, hright]
  have hplace : PalPeg.GalilTickFair.rightPlace
      (afterBirth (chainBorn (decide (vq.search.mode = .found)) s.chain)
        (afterMismatch s ⟨left s.left,right s.right,z⟩ vq)) = ⟨a :: ys,(right s.right).gap⟩ := by
    apply PalPeg.GalilTickFair.rightPlace_of_represent _ (rs.map some) q'
    rw [show (afterBirth (chainBorn (decide (vq.search.mode = .found)) s.chain)
      (afterMismatch s ⟨left s.left,right s.right,z⟩ vq)).right = right s.right from by
        simp [afterBirth_right, afterMismatch_right]]
    exact hdec
  rw [hplace] at hx
  have hhead : (GalilScaffoldPlace.stream ⟨a :: ys,(right s.right).gap⟩)[0]? = some x := by
    have := congrArg (fun l => l[0]?) hx
    simpa [List.getElem?_take] using this
  have hindex := stream_index a ys rs q' (right s.right).gap 0 (by rw [hstream]; omega)
  rw [hstream, ← hraw, hhead] at hindex
  -- period `2h` of `x :: span` reads `x` again inside the span, at the mirror of `P + 1 − 2h`
  have hspanLength : (Span raw (position s.center) R).length = 2*R+1 :=
    length_span_of_palAt hpal
  have hperiodHead := hper 0 (by rw [List.length_cons, hspanLength]; omega)
  have hinside : (x :: Span raw (position s.center) R)[0 + 2 * (xs.length + 1)]?
      = (encoded raw)[position s.center - R + (2 * (xs.length + 1) - 1)]? := by
    rw [show 0 + 2 * (xs.length + 1) = (2 * (xs.length + 1) - 1) + 1 from by omega,
      List.getElem?_cons_succ]
    unfold Span
    rw [List.getElem?_take, if_pos (by omega), List.getElem?_drop]
  have hmirror := hpal.2.2 (R + 1 - 2 * (xs.length + 1)) (by omega)
  rw [show position s.center - (R + 1 - 2 * (xs.length + 1))
      = position s.center - R + (2 * (xs.length + 1) - 1) from by omega,
    show position s.center + (R + 1 - 2 * (xs.length + 1))
      = position s.center + R + 1 - 2 * (xs.length + 1) from by omega] at hmirror
  rw [← hmirror, ← hinside, ← hperiodHead]
  simpa using hindex

end PalPeg.RestartLower
