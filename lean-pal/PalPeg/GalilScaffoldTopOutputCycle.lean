import PalPeg.GalilScaffoldTopOutputInit

/-!
# The main loop's two cycles as sound runs

From a restarted state (the chain idle, the search begun), an idle segment
leads either to a found comparison — then the chain's life and the restart
tick — or to a mismatch with the chain idle — then the fallback cycle. Both
return to a restarted state, and every state in scan mode and not replaying
has a sound output. The main loop is the iteration of these two cycles
(`stepsAll_trans`); which cycle applies at each checkpoint is the branch
exhaustiveness still to be established.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-- One main-loop cycle through a found comparison: from a restarted state,
an idle segment, the found tick, the chain's life and the restart tick.
Every state in scan mode and not replaying has a sound output. -/
theorem cycle_found_stepsAll (raw : List (Fin 2)) (P : Shared) (hP : P.onLetter = onLetterVM raw)
    (hP' : P.leftFirst = leftFirstVM) (qq : ℕ) (first : Fin 9) (delay : ℕ)
    -- the restarted state and the idle segment
    {Rad : ℕ} {last : Counter} {r : GalilVM} (hR : Restarted raw r Rad last)
    {c0 : Control} (hout0 : OutputRel raw c0 r)
    {es0 : List Bool} {cF : Control} {sF : GalilVM} (hseg0 : WatchSegE P qq first delay es0 c0 r cF sF)
    -- the found tick
    (hmF : cF.mode = .scan) (hrF : cF.replaying = false)
    (hcF : cF.clock = 1) (havF : canRight sF.right) (hidle : sF.chain = .idle)
    (vq : SearchVM) (hq : searchEffect P true sF vq) (hfound : vq.search.mode = .found)
    (hmt : read (left sF.left) = read (right sF.right))
    (ch : ChainVM)
    (hch : ChainMatched (chainStart (vq.dp.config.tapes 11) (P.centre sF) (P.place sF) sF.center sF.radius) ch)
    (hchne : ch ≠ .idle) (oF : Bool)
    (hoF : refresh (galilFrame P qq first)
      (afterBirth true (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq)) cF.output oF)
    -- the preparation and the watch
    {es : List Bool} {c2 : Control} {s2 : GalilVM}
    (hprepSeg : WatchSegE P qq first delay es {cF with clock := delay, output := oF, replaying := false}
      (afterBirth true (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq)) c2 s2)
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
    {cen3 r3 : ℕ}
    (hinv3 : ScanInvariant raw cen3 r3 (afterCompare s3 vs3 vq3).left (afterCompare s3 vs3 vq3).right)
    -- the restart tick
    (w3' : GalilScaffoldChainWatch.State) (hbroken : (afterCompare s3 vs3 vq3).chain = .broken w3')
    (hmargin : negative w3'.margin = false) (hlast : positive w3'.machine.control.last = true)
    (hlag : zero w3'.lag = true) (entry : ℕ) (hres : ∀ s t, restartVM entry s t → P.restart s t) :
    ∃ k, StepsAll (galilFrameS P qq first) delay (SoundScanNR raw) k ⟨c0, r⟩
      ⟨{c3 with clock := delay, output := o3, replaying := false}, {(afterCompare s3 vs3 vq3) with chain := .idle, lower := w3'.machine.control.last, search := GalilScaffoldSearchFinish.begin w3'.machine.control.last (afterCompare s3 vs3 vq3).radius, dp := GalilScaffoldControl.reset entry (afterCompare s3 vs3 vq3).dp}⟩ := by
  obtain ⟨_, _, _, hscanR, _⟩ := hR
  obtain ⟨k1, h1⟩ := watchSegE_stepsAll raw P hP hP' qq first delay hseg0 (position r.center) Rad hscanR hout0
  have hinvF : ScanInvariant raw (position r.center) (Rad + es0.count true) sF.left sF.right :=
    scan_events_invariant ((watchSegE_heads P qq first delay hseg0).1 raw (position r.center) Rad) hscanR
  have houtF : OutputRel raw cF sF := stepsAll_last h1
  obtain ⟨k2, h2⟩ := life_stepsAll raw P hP hP' qq first delay hmF hrF hcF havF hidle hinvF houtF vq hq hfound
    hmt ch hch hchne oF hoF hprepSeg hseg h hm1 hr1 hc1 w hs1 hz hav vs vq' hcmp hmis hq' hg s2' hb hs2' hi2 hchain o ho org hint he hrounds hseg3 hm3 hr3 hc3 w3 hs3 hav3 vs3 vq3 hcmp3 hmt3 hq3 o3 ho3 hinv3
  have htick : Tick (galilFrameS P qq first) delay
      ⟨{c3 with clock := delay, output := o3, replaying := false}, afterCompare s3 vs3 vq3⟩
      ⟨{c3 with clock := delay, output := o3, replaying := false}, {(afterCompare s3 vs3 vq3) with chain := .idle, lower := w3'.machine.control.last, search := GalilScaffoldSearchFinish.begin w3'.machine.control.last (afterCompare s3 vs3 vq3).radius, dp := GalilScaffoldControl.reset entry (afterCompare s3 vs3 vq3).dp}⟩ :=
    .restart _ _ _ hm3 (hres _ _ ⟨w3', hbroken, hmargin, hlast, hlag, rfl⟩)
  have lift1 : ∀ st, SoundOut raw st → SoundScanNR raw st := fun st h0 _ _ => h0
  have lift2 : ∀ st, SoundScan raw st → SoundScanNR raw st := fun st h0 hm _ => h0 hm
  exact ⟨_, stepsAll_keep_tick raw P qq first delay
    (stepsAll_trans (stepsAll_mono lift1 h1) (stepsAll_mono lift2 h2)) htick rfl⟩

/-- One main-loop cycle through a mismatching comparison with the chain
idle: from a restarted state, an idle segment, the mismatch and the
fallback cycle back to a restarted state. -/
theorem cycle_fallback_stepsAll (onLetter leftFirst : GalilVM → Prop) (rs : GalilVM → GalilVM → Prop)
    (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place) (entry : ℕ)
    (q : ℕ) (hq0 : 0 < q) (first : Fin 9) (h7 : first ≠ 7) (h8 : first ≠ 8) (delay : ℕ)
    {raw : List (Fin 2)} (honL : onLetter = onLetterVM raw) (hlF : leftFirst = leftFirstVM)
    -- the restarted state and the idle segment
    {Rad : ℕ} {last : Counter} {r : GalilVM} (hR : Restarted raw r Rad last) (hi0 : ShiftIdle r)
    {c0 : Control} (hout0 : OutputRel raw c0 r)
    {es0 : List Bool} {cF : Control} {sF : GalilVM}
    (hseg0 : WatchSegE (galilShared onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' rs centre place entry)
      q first delay es0 c0 r cF sF)
    -- the mismatching comparison
    (hm : cF.mode = .scan) (hr : cF.replaying = false) (hc : cF.clock = 1) (hav : canRight sF.right)
    (vs : ScanVM) (vq : SearchVM) (hl : vs.left = left sF.left) (hrr : vs.right = right sF.right)
    (hmis : read (left sF.left) ≠ read (right sF.right))
    (hq : searchEffect (galilShared onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' rs centre place entry)
      false sF vq)
    (hch : chainAt false (decide (vq.search.mode = .found)) (vq.dp.config.tapes 11) (centre sF) (place sF)
      sF.center sF.radius sF.chain vs.chain)
    (hg : ¬ shiftGuardVM (afterMismatch sF vs vq))
    (ℓ : ℕ) (hv : value sF.length = ℓ)
    (heven : ∀ (a : Fin 2) (xs rs' q' : List (Fin 2)),
      right sF.right = represent ⟨a :: xs,(right sF.right).gap⟩ (rs'.map some) q' →
      ((GalilScaffoldPlace.stream ⟨a :: xs,(right sF.right).gap⟩).take (ℓ+1)).length % 2 = 0) :
    ∃ (a : Fin 2) (xs rs' q' : List (Fin 2)),
      right sF.right = represent ⟨a :: xs,(right sF.right).gap⟩ (rs'.map some) q' ∧
      raw = (a :: xs).reverse ++ rs' ++ q' ∧
      ∃ (k : ℕ) (o : Bool) (t : GalilVM),
        StepsAll (galilFrameS (galilShared onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' rs centre place entry) q first) delay (SoundScanNR raw) k ⟨c0, r⟩
          ⟨{cF with mode := .scan, clock := delay, output := o, replaying := decide (0 < chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right sF.right).gap⟩).take (ℓ+1))), odd := oddAt false (((GalilScaffoldPlace.stream ⟨a :: xs,(right sF.right).gap⟩).take (ℓ+1)).length - (2*chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right sF.right).gap⟩).take (ℓ+1))+1)), pair := pairAt (2*chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right sF.right).gap⟩).take (ℓ+1)))}, t⟩ ∧
        Restarted raw t 0 reset := by
  have hscanR := hR.2.2.2.1
  obtain ⟨k1, h1⟩ := watchSegE_stepsAll raw _ honL hlF q first delay hseg0 (position r.center) Rad hscanR hout0
  have houtF : OutputRel raw cF sF := stepsAll_last h1
  obtain ⟨hrep, hfoc, hcan, _, _⟩ := segment_mismatch_ready _ q first delay hR hseg0 hav
  have hiF : ShiftIdle sF := by
    rw [shiftIdle_iff, watchSegE_remaining _ q first delay hseg0]
    exact (shiftIdle_iff r).1 hi0
  obtain ⟨a, xs, rs', q', hdec, hraw, n, o, t, h2, hRst, _, _⟩ :=
    fallback_restarted_soundNR onLetter leftFirst rs centre place entry q hq0 first h7 h8 delay cF hm hr hc sF hiF hav
      vs vq hl hrr hmis hq hch hg hrep hfoc hcan ℓ hv heven honL hlF houtF
  have lift1 : ∀ st, SoundOut raw st → SoundScanNR raw st := fun st h0 _ _ => h0
  exact ⟨a, xs, rs', q', hdec, hraw, _, o, t, stepsAll_trans (stepsAll_mono lift1 h1) h2, hRst⟩

#print axioms cycle_found_stepsAll
#print axioms cycle_fallback_stepsAll

end PalPeg.GalilScaffoldChainInputSupply
