import PalPeg.GalilRoundsLeftmost
import PalPeg.GalilNoBelowFirst
import PalPeg.GalilLiveCentreSegs
import PalPeg.GalilScaffoldTopOutputLifeAll

/-!
# The centre invariant across a chain's life

`life_minv` carries `MInv` — the controller's centre is the leftmost live
centre at the right head — from the found tick of a chain to the restart
state at the end of its life.

The refresh points are the found comparison (`minv_match`), the preparation
segment (`minv_watchSegE`, replay steps included), the watch segment
(`minv_watchSeg`), the first shift, the re-shift rounds
(`rounds_leftmost`), the final scan segment (`minv_scanSeg`) and the
breaking comparison (`minv_match` again); the restart tick keeps the right
head, the centre and the replay counter (`minv_same`).

The first shift is the only place where the leftmost centre actually moves,
and it needs the minimality of the span's period: the DP result of the
found tick gives it through `noBelow_first_of_result`, and
`periodOn_span_of_next` globalises the `2h`-periodicity that the rounds then
carry on.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open Manacher GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-- The centre invariant holds at every refresh point of a chain's life. -/
theorem life_minv (raw : List (Fin 2)) (P : Shared)
    (hex : ∀ s, P.replayExhausted s = zero s.replay)
    (qq : ℕ) (first : Fin 9) (delay : ℕ)
    (a : Fin 2) (ls rs q : List (Fin 2)) (gap : Bool)
    (hraw : raw = (a :: ls).reverse ++ rs ++ q)
    -- the found tick
    {cF : Control} {sF : GalilVM} (hmF : cF.mode = .scan) (hrF : cF.replaying = false)
    (hcF : cF.clock = 1) (havF : canRight sF.right) (hidle : sF.chain = .idle)
    {R : ℕ} (hscan : ScanInvariant raw (position sF.center) R sF.left sF.right)
    (hM0 : MInv raw cF sF) (hCen : sF.center = represent ⟨a :: ls,gap⟩ (rs.map some) q)
    (vq : SearchVM) (hq : searchEffect P true sF vq) (hfound : vq.search.mode = .found)
    (hmt : read (left sF.left) = read (right sF.right))
    (ch : ChainVM)
    (hch : ChainMatched (chainStart (vq.dp.config.tapes 11) (P.centre sF) (P.place sF) sF.center sF.radius) ch)
    (hchne : ch ≠ .idle) (oF : Bool)
    (hoF : refresh (galilFrame P qq first) (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq) cF.output oF)
    -- the preparation and the watch
    {es : List Bool} {c2 : Control} {s2 : GalilVM}
    (hprepSeg : WatchSegE P qq first delay es {cF with clock := delay, output := oF, replaying := false}
      (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq) c2 s2)
    {c1 : Control} {s1 : GalilVM} (hseg : WatchSeg P qq first delay c2 s2 c1 s1)
    -- the terminal comparison and the first shift
    (h : ℕ) (hm1 : c1.mode = .scan) (hr1 : c1.replaying = false) (hc1 : c1.clock = 1)
    (w : GalilScaffoldChainWatch.State) (hs1 : s1.chain = .watch w) (hz : zero w.lag = true)
    (hav : canRight s1.right) (vs : ScanVM) (vq' : SearchVM)
    (hcmp : (galilFrame P qq first).compare s1 (scanLens.set s1 vs))
    (hmis : ¬ (galilFrame P qq first).matched (scanLens.set s1 vs))
    (hq' : searchEffect P false s1 vq')
    (hg : P.shiftGuard (afterMismatch s1 vs vq'))
    (s2' : GalilVM) (hb : P.beginShift (afterMismatch s1 vs vq') s2')
    (hs2' : beginShiftVM h w (afterMismatch s1 vs vq') s2') (hi2 : CopyIdle s2')
    {t' : ShiftState} {v : GalilScaffoldChainWatch.State} {cycle : Counter}
    (hchain : ChainShiftRun ⟨s1.center, left s1.left, ofNat h, inc s1.radius, inc (inc s1.length)⟩
      (GalilScaffoldChainWatch.immediate w) reset h t' v cycle)
    (o : Bool)
    (ho : refresh (galilFrameS P qq first) (shiftLens.set s2' ⟨t', .watch v, cycle⟩) c1.output o)
    (org : ReadOrigin raw) (hint : org.interior.length+1 = h)
    (he : Entry raw org (toOnly (shiftLens.set s2' ⟨t', .watch v, cycle⟩) v))
    -- the origin's centre, the DP result of the found tick and the short periods
    (hoc : org.center = position sF.center)
    {lower span : ℕ}
    (hres : GalilDpCorrect.Result ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (span+1)) lower 0
      (GalilScaffoldProgram.denote vq.dp.config))
    (hpc : (GalilScaffoldProgram.denote vq.dp.config).pc = 346)
    (hout : (GalilScaffoldProgram.denote vq.dp.config).pos 11 = h)
    (hlow : ∀ δ, 0 < δ → δ ≤ lower → ¬ HasPeriod (Span raw org.center org.radius) (2*δ))
    -- the re-shift rounds
    {m : ℕ} {c' : Control} {s' : GalilVM}
    (hrounds : Rounds P qq first delay h m {c1 with mode := .scan, clock := delay, output := o}
      (shiftLens.set s2' ⟨t', .watch v, cycle⟩) c' s')
    -- the final segment and the breaking comparison
    {n : ℕ} {c3 : Control} {s3 : GalilVM} (hseg3 : ScanSeg P qq first delay n c' s' c3 s3)
    (hm3 : c3.mode = .scan) (hr3 : c3.replaying = false) (hc3 : c3.clock = 1)
    (w3 : GalilScaffoldChainWatch.State) (hs3 : s3.chain = .watch w3) (hav3 : canRight s3.right)
    (vs3 : ScanVM) (vq3 : SearchVM)
    (hcmp3 : (galilFrame P qq first).compare s3 (scanLens.set s3 vs3))
    (hmt3 : (galilFrame P qq first).matched (scanLens.set s3 vs3))
    (hq3 : searchEffect P true s3 vq3)
    (o3 : Bool) (ho3 : refresh (galilFrame P qq first) (afterCompare s3 vs3 vq3) c3.output o3)
    -- the restart tick
    (w3' : GalilScaffoldChainWatch.State) (hbroken : (afterCompare s3 vs3 vq3).chain = .broken w3')
    (entry : ℕ) :
    MInv raw {c3 with clock := delay, output := o3, replaying := false}
      {(afterCompare s3 vs3 vq3) with chain := .idle, lower := w3'.machine.control.last, search := GalilScaffoldSearchFinish.begin w3'.machine.control.last (afterCompare s3 vs3 vq3).radius, dp := GalilScaffoldControl.reset entry (afterCompare s3 vs3 vq3).dp} := by
  subst hraw
  -- the found comparison
  have hM1 : MInv _ {cF with clock := delay, output := oF, replaying := false}
      (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq) :=
    minv_match oF delay hrF rfl rfl havF hmt hscan hM0
  have hinv1 : ScanInvariant ((a :: ls).reverse ++ rs ++ q) (position sF.center) (R+1)
      (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq).left
      (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq).right :=
    matched_invariant' _ vq rfl rfl hmt havF hscan
  -- the preparation segment
  have hM2 := minv_watchSegE _ P hex qq first delay hprepSeg (R+1) hinv1 hM1
  have hcen2 : s2.center = sF.center := by
    have h0 := watchSegE_center P qq first delay hprepSeg
    rw [afterCompare_center] at h0; exact h0
  have hinv2 : ScanInvariant ((a :: ls).reverse ++ rs ++ q) (position sF.center)
      (R+1+es.count true) s2.left s2.right :=
    scan_events_invariant ((watchSegE_heads P qq first delay hprepSeg).1 _ (position sF.center) (R+1))
      hinv1
  -- the watch segment
  have hne2 : s2.chain ≠ .idle :=
    watchSegE_ne_idle P qq first delay hprepSeg (by rw [afterCompare_chain]; exact hchne)
  obtain ⟨es2, _, hsc2, hcen21, _⟩ := watchSeg_events P qq first delay hseg hne2
  have hM3 := minv_watchSeg _ P qq first delay hseg _ (by rw [hcen2]; exact hinv2) hM2
  have hi1 : ScanInvariant ((a :: ls).reverse ++ rs ++ q) (position sF.center)
      (R+1+es.count true+es2.count true) s1.left s1.right :=
    scan_events_invariant (hsc2 _ (position sF.center) (R+1+es.count true)) hinv2
  have hcen1 : s1.center = sF.center := by rw [hcen21, hcen2]
  -- the terminal mismatch
  have hcmpl : vs.left = left s1.left ∧ vs.right = right s1.right := by
    obtain ⟨⟨hl0, hr0, _⟩, _⟩ := hcmp
    rw [scanLens.get_set] at hl0 hr0
    exact ⟨hl0, hr0⟩
  have hmatch0 : read (left s1.left) ≠ read (right s1.right) := by
    intro h0
    apply hmis
    show read (scanLens.get (scanLens.set s1 vs)).left = read (scanLens.get (scanLens.set s1 vs)).right
    rw [scanLens.get_set]
    show read vs.left = read vs.right
    rw [hcmpl.1, hcmpl.2]; exact h0
  -- the places of the two heads
  have hrpos : position (right s1.right) = position s1.right + 1 :=
    right_position s1.right hav (represented_position s1.right.head _ hi1.rightRep hi1.rightPresent).1
  have hSright : s2'.right = right s1.right := by
    rw [hs2'.2]; simp [afterMismatch, searchLens, scanLens, hcmpl.2]
  have hposR : position s2'.right = position s1.right + 1 := by rw [hSright]; exact hrpos
  -- the origin's sizes and palindromes
  have hh : 0 < h := by omega
  have hk : 2*h ≤ org.radius := by have h0 := org.size; omega
  have hpal0 : PalAt (encoded ((a :: ls).reverse ++ rs ++ q)) org.center org.radius := org.scan.palindrome
  have hRA : org.radius ≤ org.center := hpal0.1
  have hlenX : org.center + org.radius < (encoded ((a :: ls).reverse ++ rs ++ q)).length := hpal0.2.1
  have hi' : ScanInvariant ((a :: ls).reverse ++ rs ++ q) (org.center + h) (org.radius+1-h)
      t'.left s2'.right := by
    have h0 := entry_scanInvariant he
    rw [hint] at h0
    exact h0
  have hcp' : position t'.center = org.center + h := by
    have h0 := he.centerPos; rw [hint] at h0; exact h0
  have hprA : position s1.right = org.center + org.radius := by
    have e1 := hi'.rightPos; omega
  -- no short period of the span at the first terminal comparison
  have hnb := noBelow_first_of_result a ls rs q gap org (by rw [hoc, hCen]) he hres hpc
    (by rw [hout]; exact hint.symm) hlow
  have hmin0 : ∀ p, 0 < p → p < 2*h →
      ¬ PeriodOn (encoded ((a :: ls).reverse ++ rs ++ q)) p
        (org.center - org.radius) (org.center + org.radius) := by
    intro p hp0 hp2 hcon
    apply hnb p hp0 (by omega)
    unfold Span
    have ea : 2*org.radius+1 = (org.center + org.radius) + 1 - (org.center - org.radius) := by omega
    rw [ea]
    exact (hasPeriod_slice_iff (x := encoded ((a :: ls).reverse ++ rs ++ q)) (p := p) hlenX
      (by omega)).mpr hcon
  -- the `2h` period of the whole span
  have hpal1 : PalAt (encoded ((a :: ls).reverse ++ rs ++ q)) (org.center + h) (org.radius + 1 - h) :=
    hi'.palindrome
  have hright : PeriodOn (encoded ((a :: ls).reverse ++ rs ++ q)) (2*h)
      (org.center+1) (org.center+org.radius+1) := by
    have h2 := org.origin_periodOn_right; rw [hint] at h2; exact h2
  have hper0 : PeriodOn (encoded ((a :: ls).reverse ++ rs ++ q)) (2*h)
      (org.center - org.radius) (org.center + org.radius) :=
    (periodOn_span_of_next hh hk hpal0 hpal1 hright).mono (le_refl _) (by omega)
  -- the first shift moves the leftmost live centre by `h`
  have hL1 : Leftmost ((a :: ls).reverse ++ rs ++ q) (position s1.right) (position sF.center) := by
    have h0 := minv_leftmost hM3 hr1
    rw [hcen1] at h0; exact h0
  have hdead : ¬ Live ((a :: ls).reverse ++ rs ++ q) (position s1.right + 1) (position sF.center) :=
    not_live_of_mismatch hi1 hav hmatch0
  have hlive : Live ((a :: ls).reverse ++ rs ++ q) (position s1.right + 1) (position sF.center + h) := by
    have h0 := live_of_scanInvariant hi'
    rw [hposR] at h0
    rw [← hoc]; exact h0
  have hmin : ∀ p, 0 < p → p < 2*h →
      ¬ HasPeriod (Span ((a :: ls).reverse ++ rs ++ q) (position sF.center)
        (position s1.right - position sF.center)) p := by
    intro p hp0 hp2 hcon
    apply hnb p hp0 (by omega)
    have e2 : position s1.right - position sF.center = org.radius := by omega
    rw [e2, ← hoc] at hcon
    exact hcon
  have hLS : Leftmost ((a :: ls).reverse ++ rs ++ q)
      (position (shiftLens.set s2' ⟨t', .watch v, cycle⟩).right)
      (position (shiftLens.set s2' ⟨t', .watch v, cycle⟩).center) := by
    show Leftmost _ (position s2'.right) (position t'.center)
    rw [hposR, hcp', hoc]
    exact leftmost_shift hL1 hdead hlive hmin
  have hMs : MInv _ {c1 with mode := .scan, clock := delay, output := o}
      (shiftLens.set s2' ⟨t', .watch v, cycle⟩) := minv_of_leftmost hLS hr1
  -- the re-shift rounds
  have hp2 : (shiftLens.set s2' ⟨t', .watch v, cycle⟩).periodOnly = true := by
    show s2'.periodOnly = true; rw [hs2'.2]
  have hz2 : zero v.lag = true := by rw [chain_shift_lag hchain]; exact hz
  obtain ⟨org', w', hint', _, _, _, _, _, he', _, _, hr', hM'⟩ :=
    rounds_leftmost _ P qq first delay h hrounds v hp2 rfl hz2 org hint he hper0 hmin0 hr1 hMs
  -- the final segment
  have hcp3 : position s'.center = org'.center + h := by
    have h0 := he'.centerPos; rw [hint'] at h0; exact h0
  have hinv' : ScanInvariant ((a :: ls).reverse ++ rs ++ q) (position s'.center)
      (org'.radius+1-h) s'.left s'.right := by
    have h0 := entry_scanInvariant he'
    rw [hint'] at h0
    rw [hcp3]; exact h0
  have hM3' := minv_scanSeg _ P qq first delay hseg3 _ hinv' hM'
  -- the breaking comparison
  have hmatch3 : read (left s3.left) = read (right s3.right) := by
    obtain ⟨⟨hl0, hr0, _⟩, _⟩ := hcmp3
    rw [scanLens.get_set] at hl0 hr0
    have hp0 := matched_parts P qq first hmt3
    rw [hl0, hr0] at hp0; exact hp0
  obtain ⟨hl3, hrr3, _⟩ := compare_parts P qq first hcmp3 hmatch3
  obtain ⟨es3, hsc3⟩ := scanSeg_heads P qq first delay hseg3
  have hi3 : ScanInvariant ((a :: ls).reverse ++ rs ++ q) (position s3.center)
      (org'.radius+1-h+es3.count true) s3.left s3.right := by
    have h0 := scan_events_invariant (hsc3 _ (position s'.center) (org'.radius+1-h)) hinv'
    rw [scanSeg_center P qq first delay hseg3]
    exact h0
  have hM4 := minv_match (vq := vq3) o3 delay hr3 hl3 hrr3 hav3 hmatch3 hi3 hM3'
  exact minv_same rfl rfl rfl rfl hM4

#print axioms life_minv

end PalPeg.GalilScaffoldChainInputSupply
