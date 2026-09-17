import PalPeg.GalilCostedFound
import PalPeg.GalilInvPlus
import PalPeg.GalilFoundLanding
import PalPeg.GalilCycleNoShift
import PalPeg.GalilCycleProgress
import PalPeg.GalilFrontMono
import PalPeg.GalilBreakTerminal
import PalPeg.GalilRadiusConsumed
import PalPeg.GalilCostedFallback

/-!
# Found routes with cost, landing in `InvLP`

Gaps 2–3 of `PalPeg.GalilCostedFound`: from an `InvLP` state and the found-cycle
data, a sound run of `k` ticks, a `CostedRun` of the same `k` ticks, and an
`InvLP` landing (`foundRouteMC_noshift`, `foundRouteMC_shift`).
-/

set_option autoImplicit false

namespace PalPeg.GalilFoundLandingL

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilRunSkeleton
open PalPeg.GalilOracleDischarge PalPeg.GalilOracleGlueB PalPeg.GalilGlueBLeaves
open PalPeg.GalilOracleLocal PalPeg.GalilInvPlus
open Manacher GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier
open PalPeg.GalilTraceCost PalPeg.GalilCostedFound

/-! ## Plumbing -/

/-- `watchSegE_stepsAll` with the tick count equal to the event count. -/
theorem watchSegE_stepsAll_len (raw : List (Fin 2)) (P : Shared) (hP : P.onLetter = onLetterVM raw)
    (hP' : P.leftFirst = leftFirstVM) (q : ℕ) (first : Fin 9) (delay : ℕ) {es : List Bool}
    {c c' : Control} {s t : GalilVM} (h : WatchSegE P q first delay es c s c' t) (cen : ℕ) :
    ∀ r : ℕ, ScanInvariant raw cen r s.left s.right → OutputRel raw c s →
      StepsAll (galilFrameS P q first) delay (SoundOut raw) es.length ⟨c, s⟩ ⟨c', t⟩ := by
  induction h with
  | stop c s => intro r _ ho; exact .zero _ ho
  | wait c s s' hm hr hn hb _ ih =>
    intro r hi ho
    obtain ⟨hl, hr', _, _⟩ := background_frame P q first hb
    exact .succ ho (.scan_wait c s s' hm ⟨hr, hn⟩ hb)
      (ih r (by rw [hl, hr']; exact hi) (outputRel_background raw P q first hb rfl ho))
  | count c s s' hm hr ha hc hb _ ih =>
    intro r hi ho
    obtain ⟨hl, hr', _, _⟩ := background_frame P q first hb
    exact .succ ho (.scan_count c s s' hm (Or.inr ha) hc hb)
      (ih r (by rw [hl, hr']; exact hi) (outputRel_background raw P q first hb rfl ho))
  | countR c s s' hm hr hc hidle hb _ ih =>
    intro r hi ho
    obtain ⟨hl, hr', _, _⟩ := background_frame P q first hb
    exact .succ ho (.scan_count c s s' hm (Or.inl hr) hc hb)
      (ih r (by rw [hl, hr']; exact hi) (outputRel_background raw P q first hb rfl ho))
  | «match» c s vs vq o hm hr ha hc hne hcmp hmt hq ho' _ ih =>
    intro r hi ho
    have hi' := matched_invariant raw P q first vq hcmp hmt ha hi
    exact .succ ho (scan_match_S P q first delay c s vs vq o hm hr ha hc hne hcmp hmt hq ho')
      (ih (r+1) hi' (outputRel_of_refresh' raw P hP hP' q first _ c.output o hi' ho' _ rfl))
  | matchIdle c s vs vq o hm hr ha hc hidle hl hrr hvs hmt hq hnf ho' _ ih =>
    intro r hi ho
    have hmatch : read (left s.left) = read (right s.right) := by
      have := matched_parts P q first hmt
      rw [hl, hrr] at this; exact this
    have hi' := matched_invariant' raw vq hl hrr hmatch ha hi
    exact .succ ho (scan_match_idle_S P q first delay c s vs vq o hm hr ha hc hidle hl hrr hvs hmt hq
      hnf ho') (ih (r+1) hi' (outputRel_of_refresh' raw P hP hP' q first _ c.output o hi' ho' _ rfl))
  | matchIdleR c s vs vq o hm hr hc ha hidle hl hrr hvs hmt hq hnf ho' _ ih =>
    intro r hi ho
    have hmatch : read (left s.left) = read (right s.right) := by
      have := matched_parts P q first hmt
      rw [hl, hrr] at this; exact this
    have hi' : ScanInvariant raw cen (r+1) (replayDec true (afterCompare s vs vq)).left
        (replayDec true (afterCompare s vs vq)).right := by
      rw [replayDec_left, replayDec_right, afterCompare_left, afterCompare_right, hl, hrr]
      exact scanInvariant_matched hi ha hmatch
    have ht := scan_match_idle_S' P q first delay c s vs vq o hm (Or.inl hr) hc hidle hl hrr hvs hmt hq
      hnf (by rw [hr]; exact ho')
    rw [hr] at ht
    exact .succ ho (by simpa using ht)
      (ih (r+1) hi' (outputRel_of_refresh' raw P hP hP' q first _ c.output o hi' ho' _ rfl))

/-- A general segment keeps the shift counter. -/
theorem watchSeg_remaining (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    {c c' : Control} {s t : GalilVM} (h : WatchSeg P q first delay c s c' t) :
    t.remaining = s.remaining := by
  induction h with
  | stop c s => rfl
  | wait c s s' _ _ _ hb _ ih =>
    obtain ⟨_, _, _, _, _, _, _, _, hrem, _⟩ := backgroundS_fields P q first hb
    rw [ih, hrem]
  | count c s s' _ _ _ _ hb _ ih =>
    obtain ⟨_, _, _, _, _, _, _, _, hrem, _⟩ := backgroundS_fields P q first hb
    rw [ih, hrem]
  | «match» c s vs vq o _ _ _ _ _ _ _ _ _ _ ih => rw [ih, afterCompare_remaining]

/-- A scan segment keeps the shift counter. -/
theorem scanSeg_remaining (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) {n : ℕ}
    {c c' : Control} {s t : GalilVM} (h : ScanSeg P q first delay n c s c' t) :
    t.remaining = s.remaining := by
  induction h with
  | stop c s => rfl
  | wait c s s' _ _ _ hb _ ih =>
    obtain ⟨_, _, _, _, _, _, _, _, hrem, _⟩ := backgroundS_fields P q first hb
    rw [ih, hrem]
  | count c s s' _ _ _ _ hb _ ih =>
    obtain ⟨_, _, _, _, _, _, _, _, hrem, _⟩ := backgroundS_fields P q first hb
    rw [ih, hrem]
  | «match» c s vs vq o _ _ _ _ _ _ _ _ _ _ _ ih => rw [ih, afterCompare_remaining]

/-- After a completed chain shift the shift counter is exhausted, and the
rounds keep it so. -/
theorem rounds_remaining (P : Shared) (q : ℕ) (first : Fin 9) (delay h : ℕ) {m : ℕ}
    {c c' : Control} {s s' : GalilVM} (hr : Rounds P q first delay h m c s c' s') :
    positive s.remaining = false → positive s'.remaining = false := by
  induction hr with
  | stop c s => exact id
  | next c s hseg _ _ _ w _ _ vs vq _ _ _ _ _ _ _ s2 _ hs2 _ hchain _ _ _ ih =>
    intro _
    exact ih (chain_shift_exhausts h rfl hchain)

#print axioms watchSegE_stepsAll_len
#print axioms watchSeg_remaining
#print axioms scanSeg_remaining
#print axioms rounds_remaining

/-! ## (a) The invariants at the found comparison -/

/-- From an `InvLP` state along the chain-idle segment to the found comparison:
the exact-length sound run, the scan invariant, `OutputRel`, and the counters. -/
theorem at_found (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    {c0 : Control} {r : GalilVM} (hI : InvLP raw c0 r)
    {es0 : List Bool} {cF : Control} {sF : GalilVM}
    (hseg0 : WatchSegE (PofC centre place entry raw) q first 2048 es0 c0 r cF sF) :
    ∃ R : ℕ,
      StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048 (SoundScanNR raw)
        es0.length ⟨c0, r⟩ ⟨cF, sF⟩ ∧
      ScanInvariant raw (position r.center) R r.left r.right ∧ RadiusRep r.radius R ∧
      Canonical r.length ∧ SpanRep r ∧
      ScanInvariant raw (position sF.center) (R + es0.count true) sF.left sF.right ∧
      OutputRel raw cF sF ∧ sF.center = r.center := by
  obtain ⟨R, hi, hRR, hS, hlc⟩ := hI.2
  have hst := watchSegE_stepsAll_len raw (PofC centre place entry raw) rfl rfl q first 2048 hseg0
    (position r.center) R hi hI.1.2
  have hcen : sF.center = r.center := watchSegE_center _ q first 2048 hseg0
  refine ⟨R, stepsAll_mono (fun _ h0 _ _ => h0) hst, hi, hRR, hlc, hS, ?_, stepsAll_last hst, hcen⟩
  rw [hcen]; exact scanInvariant_watchSegE _ q first 2048 hseg0 hi

#print axioms at_found

/-! ## (b) The no-shift landing -/

/-- `cycle_found_noshift_minv` from the scan invariant alone. -/
theorem noshift_minv (raw : List (Fin 2)) (P : Shared)
    (hex : ∀ s, P.replayExhausted s = zero s.replay)
    (qq : ℕ) (first : Fin 9) (delay : ℕ)
    {Rad : ℕ} {r : GalilVM} (hscanR : ScanInvariant raw (position r.center) Rad r.left r.right)
    {c0 : Control} (hM0 : MInv raw c0 r)
    {es0 : List Bool} {cF : Control} {sF : GalilVM} (hseg0 : WatchSegE P qq first delay es0 c0 r cF sF)
    (hrF : cF.replaying = false) (havF : canRight sF.right)
    (vq : SearchVM) (hmt : read (left sF.left) = read (right sF.right))
    (ch : ChainVM) (hchne : ch ≠ .idle) (oF : Bool)
    {es : List Bool} {c2 : Control} {s2 : GalilVM}
    (hprepSeg : WatchSegE P qq first delay es {cF with clock := delay, output := oF, replaying := false}
      (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq) c2 s2)
    {c3 : Control} {s3 : GalilVM} (hseg : WatchSeg P qq first delay c2 s2 c3 s3)
    (hr3 : c3.replaying = false) (hav3 : canRight s3.right)
    (vs3 : ScanVM) (vq3 : SearchVM)
    (hcmp3 : (galilFrame P qq first).compare s3 (scanLens.set s3 vs3))
    (hmt3 : (galilFrame P qq first).matched (scanLens.set s3 vs3))
    (o3 : Bool) (w3' : GalilScaffoldChainWatch.State) (entry : ℕ) :
    MInv raw (foundLandingControl c3 delay o3) (foundLandingVM (afterCompare s3 vs3 vq3) w3' entry) := by
  have hMF : MInv raw cF sF := minv_watchSegE raw P hex qq first delay hseg0 Rad hscanR hM0
  have hcen : sF.center = r.center := watchSegE_center P qq first delay hseg0
  have hinvF : ScanInvariant raw (position sF.center) (Rad + es0.count true) sF.left sF.right := by
    rw [hcen]
    exact scan_events_invariant ((watchSegE_heads P qq first delay hseg0).1 raw (position r.center) Rad)
      hscanR
  have hM1 : MInv raw {cF with clock := delay, output := oF, replaying := false}
      (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq) :=
    minv_match oF delay hrF rfl rfl havF hmt hinvF hMF
  have hinv1 : ScanInvariant raw (position sF.center) (Rad + es0.count true + 1)
      (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq).left
      (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq).right :=
    matched_invariant' raw vq rfl rfl hmt havF hinvF
  have hM2 := minv_watchSegE raw P hex qq first delay hprepSeg _ hinv1 hM1
  have hcen2 : s2.center = sF.center := by
    have h0 := watchSegE_center P qq first delay hprepSeg
    rw [afterCompare_center] at h0; exact h0
  have hinv2 : ScanInvariant raw (position sF.center) (Rad + es0.count true + 1 + es.count true)
      s2.left s2.right :=
    scan_events_invariant
      ((watchSegE_heads P qq first delay hprepSeg).1 raw (position sF.center) _) hinv1
  have hne2 : s2.chain ≠ .idle :=
    watchSegE_ne_idle P qq first delay hprepSeg (by rw [afterCompare_chain]; exact hchne)
  obtain ⟨es2, _, hsc2, hcen21, _, _, _, _⟩ := watchSeg_events P qq first delay hseg hne2
  have hM3 := minv_watchSeg raw P qq first delay hseg _ (by rw [hcen2]; exact hinv2) hM2
  have hi3 : ScanInvariant raw (position s3.center)
      (Rad + es0.count true + 1 + es.count true + es2.count true) s3.left s3.right := by
    rw [hcen21, hcen2]
    exact scan_events_invariant (hsc2 raw (position sF.center) _) hinv2
  have hmatch3 : read (left s3.left) = read (right s3.right) := by
    obtain ⟨⟨hl0, hr0, _⟩, _⟩ := hcmp3
    rw [scanLens.get_set] at hl0 hr0
    have hp0 := matched_parts P qq first hmt3
    rw [hl0, hr0] at hp0; exact hp0
  obtain ⟨hl3, hrr3, _⟩ := compare_parts P qq first hcmp3 hmatch3
  have hM4 := minv_match (vq := vq3) o3 delay hr3 hl3 hrr3 hav3 hmatch3 hi3 hM3
  exact minv_same rfl rfl rfl rfl hM4

/-- `cycle_found_noshift_restarted` from the counters of an `InvLP` state and
the centre representation, with the radius growth exported. -/
theorem noshift_restarted (raw : List (Fin 2)) (P : Shared)
    (qq : ℕ) (first : Fin 9) (delay : ℕ)
    {Rad : ℕ} {r : GalilVM}
    (hcenR : GalilScaffoldInputTrace.Represents r.center.head raw ∧ r.center.head.focus ≠ none)
    (hscanR : ScanInvariant raw (position r.center) Rad r.left r.right)
    (hRR : RadiusRep r.radius Rad) (hlc : Canonical r.length)
    {c0 : Control}
    {es0 : List Bool} {cF : Control} {sF : GalilVM} (hseg0 : WatchSegE P qq first delay es0 c0 r cF sF)
    (havF : canRight sF.right) (hmt : read (left sF.left) = read (right sF.right))
    (vq : SearchVM) (ch : ChainVM) (hchne : ch ≠ .idle) (oF : Bool)
    {es : List Bool} {c2 : Control} {s2 : GalilVM}
    (hprepSeg : WatchSegE P qq first delay es {cF with clock := delay, output := oF, replaying := false}
      (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq) c2 s2)
    {c3 : Control} {s3 : GalilVM} (hseg : WatchSeg P qq first delay c2 s2 c3 s3)
    (hav3 : canRight s3.right) (vs3 : ScanVM) (vq3 : SearchVM)
    (hcmp3 : (galilFrame P qq first).compare s3 (scanLens.set s3 vs3))
    (hmt3 : (galilFrame P qq first).matched (scanLens.set s3 vs3))
    (w3' : GalilScaffoldChainWatch.State) (hcanon : Canonical w3'.machine.control.last)
    (hlast : positive w3'.machine.control.last = true) (entry : ℕ) :
    ∃ Rad' : ℕ, Rad < Rad' ∧
      Restarted raw (foundLandingVM (afterCompare s3 vs3 vq3) w3' entry) Rad'
        w3'.machine.control.last := by
  obtain ⟨hrep, hfoc⟩ := hcenR
  obtain ⟨hrc, hrv⟩ := hRR
  obtain ⟨hsc0, _, hrad0, hrc0, hlc0⟩ := watchSegE_heads P qq first delay hseg0
  have hcen : sF.center = r.center := watchSegE_center P qq first delay hseg0
  have hinvF : ScanInvariant raw (position sF.center) (Rad + es0.count true) sF.left sF.right := by
    rw [hcen]
    exact scan_events_invariant (hsc0 raw (position r.center) Rad) hscanR
  have hRadF : RadiusRep sF.radius (Rad + es0.count true) := by
    refine ⟨hrc0 hrc, ?_⟩
    rw [hrad0, hrv]; push_cast; ring
  have hinv1 : ScanInvariant raw (position sF.center) (Rad + es0.count true + 1)
      (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq).left
      (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq).right :=
    matched_invariant' raw vq rfl rfl hmt havF hinvF
  have hRad1 : RadiusRep (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq).radius
      (Rad + es0.count true + 1) := by
    rw [afterCompare_radius]; exact radius_rep_inc hRadF
  have hlc1 : Canonical (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq).length := by
    rw [afterCompare_length]; exact inc_canonical _ (inc_canonical _ (hlc0 hlc))
  obtain ⟨hsc1, _, hrad1, hrc1, hlc1'⟩ := watchSegE_heads P qq first delay hprepSeg
  have hcen2 : s2.center = sF.center := by
    have h0 := watchSegE_center P qq first delay hprepSeg
    rw [afterCompare_center] at h0; exact h0
  have hinv2 : ScanInvariant raw (position sF.center) (Rad + es0.count true + 1 + es.count true)
      s2.left s2.right :=
    scan_events_invariant (hsc1 raw (position sF.center) _) hinv1
  have hRad2 : RadiusRep s2.radius (Rad + es0.count true + 1 + es.count true) := by
    refine ⟨hrc1 hRad1.1, ?_⟩
    rw [hrad1, hRad1.2]; push_cast; ring
  have hne2 : s2.chain ≠ .idle :=
    watchSegE_ne_idle P qq first delay hprepSeg (by rw [afterCompare_chain]; exact hchne)
  obtain ⟨es2, _, hsc2, hcen21, _, hrad2, hrc2, hlc2⟩ := watchSeg_events P qq first delay hseg hne2
  have hi3 : ScanInvariant raw (position s3.center)
      (Rad + es0.count true + 1 + es.count true + es2.count true) s3.left s3.right := by
    rw [hcen21, hcen2]
    exact scan_events_invariant (hsc2 raw (position sF.center) _) hinv2
  have hRad3 : RadiusRep s3.radius (Rad + es0.count true + 1 + es.count true + es2.count true) := by
    refine ⟨hrc2 hRad2.1, ?_⟩
    rw [hrad2, hRad2.2]; push_cast; ring
  have hinv3 := matched_invariant raw P qq first vq3 hcmp3 hmt3 hav3 hi3
  have hcenE : (afterCompare s3 vs3 vq3).center = r.center := by
    rw [afterCompare_center, hcen21, hcen2, hcen]
  refine ⟨Rad + es0.count true + 1 + es.count true + es2.count true + 1, by omega,
    rfl, ?_, ?_, ?_, ?_, ?_, rfl, rfl, hcanon, ((positive_iff _ hcanon).1 hlast).le⟩
  · show GalilScaffoldInputTrace.Represents (afterCompare s3 vs3 vq3).center.head raw
    rw [hcenE]; exact hrep
  · show (afterCompare s3 vs3 vq3).center.head.focus ≠ none
    rw [hcenE]; exact hfoc
  · show ScanInvariant raw (position (afterCompare s3 vs3 vq3).center) _
      (afterCompare s3 vs3 vq3).left (afterCompare s3 vs3 vq3).right
    rw [afterCompare_center, hcen21, hcen2] at *
    exact hinv3
  · show RadiusRep (afterCompare s3 vs3 vq3).radius _
    rw [afterCompare_radius]; exact radius_rep_inc hRad3
  · show Canonical (afterCompare s3 vs3 vq3).length
    rw [afterCompare_length]
    exact inc_canonical _ (inc_canonical _ (hlc2 (hlc1' hlc1)))

#print axioms noshift_minv
#print axioms noshift_restarted

/-- The frontier pack travels from an `InvLP` state along any run, given
`CentreLive` along it. -/
theorem front_of_run (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    {c0 : Control} {r : GalilVM} (hI : InvLP raw c0 r)
    (hlive : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (PofC centre place entry raw) q first) 2048 m ⟨c0, r⟩ z →
      CentreLive z.ctl z.vm)
    {k : ℕ} {cT : Control} {sT : GalilVM}
    (hst : StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048 (SoundScanNR raw) k
      ⟨c0, r⟩ ⟨cT, sT⟩) :
    Frontier sT ∧ ReplayRest cT sT := by
  have h := (PalPeg.GalilFrontMono.front_steps_mono (onLetterVM raw) leftFirstVM centre place entry
    q first 2048 (stepsAll_steps hst) hlive (PalPeg.GalilFrontMono.frontPack_of_invS hI.1.1)).1
  exact ⟨h.frontier, h.rest⟩

/-- **`foundRouteMC_noshift`.**  From an `InvLP` state, the idle segment, the
found comparison, the preparation and watch segments, and a breaking *match*
with its restart tick: a sound run of `k` ticks, a `CostedRun` of the same `k`
ticks, and an `InvLP` landing.  The centre does not move; the right head
strictly advances.

Named hypotheses: `hlive` (`CentreLive` along the run), `hcenR` (the centre
head represents the input — carried by `Inv` but not by `InvScan`), `hcanon`
(the new lower bound is canonical) and `hstage` (the stage budget at the new
radius). -/
theorem foundRouteMC_noshift (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2))
    (hex : ∀ s, (PofC centre place entry raw).replayExhausted s = zero s.replay)
    {c0 : Control} {r : GalilVM} (hI : InvLP raw c0 r)
    (hlive : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (PofC centre place entry raw) qq first) 2048 m ⟨c0, r⟩ z →
      CentreLive z.ctl z.vm)
    (hcenR : GalilScaffoldInputTrace.Represents r.center.head raw ∧ r.center.head.focus ≠ none)
    {es0 : List Bool} {cF : Control} {sF : GalilVM}
    (hseg0 : WatchSegE (PofC centre place entry raw) qq first 2048 es0 c0 r cF sF)
    (hmF : cF.mode = .scan) (hrF : cF.replaying = false)
    (hcF : cF.clock = 1) (havF : canRight sF.right) (hidle : sF.chain = .idle)
    (vq : SearchVM) (hq : searchEffect (PofC centre place entry raw) true sF vq)
    (hfound : vq.search.mode = .found)
    (hmt : read (left sF.left) = read (right sF.right))
    (ch : ChainVM)
    (hch : ChainMatched (chainStart (vq.dp.config.tapes 11) ((PofC centre place entry raw).centre sF)
      ((PofC centre place entry raw).place sF) sF.center sF.radius) ch)
    (hchne : ch ≠ .idle) (oF : Bool)
    (hoF : refresh (galilFrame (PofC centre place entry raw) qq first)
      (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq) cF.output oF)
    {es : List Bool} {c2 : Control} {s2 : GalilVM}
    (hprepSeg : WatchSegE (PofC centre place entry raw) qq first 2048 es
      {cF with clock := 2048, output := oF, replaying := false}
      (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq) c2 s2)
    {c3 : Control} {s3 : GalilVM}
    (hseg : WatchSeg (PofC centre place entry raw) qq first 2048 c2 s2 c3 s3)
    (hm3 : c3.mode = .scan) (hr3 : c3.replaying = false) (hc3 : c3.clock = 1)
    (w3 : GalilScaffoldChainWatch.State) (hs3 : s3.chain = .watch w3) (hav3 : canRight s3.right)
    (vs3 : ScanVM) (vq3 : SearchVM)
    (hcmp3 : (galilFrame (PofC centre place entry raw) qq first).compare s3 (scanLens.set s3 vs3))
    (hmt3 : (galilFrame (PofC centre place entry raw) qq first).matched (scanLens.set s3 vs3))
    (hq3 : searchEffect (PofC centre place entry raw) true s3 vq3)
    (o3 : Bool) (ho3 : refresh (galilFrame (PofC centre place entry raw) qq first)
      (afterCompare s3 vs3 vq3) c3.output o3)
    (w3' : GalilScaffoldChainWatch.State) (hbroken : (afterCompare s3 vs3 vq3).chain = .broken w3')
    (hmargin : negative w3'.margin = false) (hlast : positive w3'.machine.control.last = true)
    (hlag : zero w3'.lag = true)
    (hcanon : Canonical w3'.machine.control.last)
    (hstage : ∀ R : ℕ, RadiusRep (afterCompare s3 vs3 vq3).radius R →
      StageEntry R w3'.machine.control.last) :
    ∃ (cT : Control) (sT : GalilVM) (k : ℕ) (L : List Piece),
      StepsAll (galilFrameS (PofC centre place entry raw) qq first) 2048 (SoundScanNR raw) k
        ⟨c0, r⟩ ⟨cT, sT⟩ ∧
      CostedRun r sT k L ∧ InvLP raw cT sT ∧
      position sT.center = position r.center ∧ position r.right < position sT.right ∧
      sT.right = (afterCompare s3 vs3 vq3).right := by
  obtain ⟨R, hst0, hi0, hRR0, hlc0, hS0, hiF, houtF, hcenF⟩ := at_found centre place entry qq first raw hI hseg0
  have hM0 : MInv raw c0 r := hI.1.1.elim (fun h => h.minv) (fun ⟨_, h⟩ => h.minv)
  have hclk0 : c0.clock = 2048 := hI.1.1.elim (fun h => h.mode.2.2) (fun ⟨_, h⟩ => h.mode.2.2)
  obtain ⟨L0, k0, w1, hcr0, hk0, hw1⟩ :=
    PalPeg.GalilCostedFallback.costedRun_watchSegE_pend raw _ qq first hseg0 (position r.center) R 0 hi0
      (by rw [hclk0]) havF
  obtain ⟨k1, L1, hst1, hcr1, hcenE⟩ :=
    costedRun_found_noshift raw (PofC centre place entry raw) rfl rfl qq first 2048 le_rfl hmF hrF hcF
      havF hidle hiF houtF vq hq hfound hmt ch hch hchne oF hoF hprepSeg hseg hm3 hr3 hc3 w3 hs3 hav3
      vs3 vq3 hcmp3 hmt3 hq3 o3 ho3 w3' hbroken hmargin hlast hlag entry (fun _ _ h => h) w1
      (by rw [hcF]; omega)
  have hst := stepsAll_trans hst0 hst1
  have hcr := costedRun_trans hcr0 hcr1
  obtain ⟨Rad', hlt, hRst⟩ := noshift_restarted raw _ qq first 2048 hcenR hi0 hRR0 hlc0 hseg0 havF hmt
    vq ch hchne oF hprepSeg hseg hav3 vs3 vq3 hcmp3 hmt3 w3' hcanon hlast entry
  have hM := noshift_minv raw _ hex qq first 2048 hi0 hM0
    hseg0 hrF havF vq hmt ch hchne oF hprepSeg hseg hr3 hav3 vs3 vq3 hcmp3 hmt3 o3 w3' entry
  have hfr := front_of_run centre place entry qq first raw hI hlive hst
  have hsi0 : ShiftIdle r := hI.1.1.elim (fun h => h.shiftIdle) (fun ⟨_, h⟩ => h.shiftIdle)
  have hsi : ShiftIdle (foundLandingVM (afterCompare s3 vs3 vq3) w3' entry) := by
    refine PalPeg.GalilReplaySegment.shiftIdle_congr ?_ hsi0
    show s3.remaining = r.remaining
    rw [watchSeg_remaining _ qq first 2048 hseg, watchSegE_remaining _ qq first 2048 hprepSeg,
      afterCompare_remaining, watchSegE_remaining _ qq first 2048 hseg0]
  have hInv : Inv raw (foundLandingControl c3 2048 o3) (foundLandingVM (afterCompare s3 vs3 vq3) w3' entry) :=
    { rest := ⟨Rad', _, hRst⟩, minv := hM, mode := ⟨hm3, rfl, rfl⟩
      stage := fun Rad last h0 => by
        have hl : last = w3'.machine.control.last := h0.2.2.2.2.2.2.2.1.symm
        subst hl
        exact hstage Rad h0.2.2.2.2.1
      search := searchReady_of_restarted hRst
      block := blockInv_of_restarted hRst
      frontier := hfr.1, rest_replay := hfr.2
      input := input_of_restarted hRst
      shiftIdle := hsi }
  have hS := spanRep_found_noshift _ qq first 2048 hseg0 vq ch oF hprepSeg hseg vs3 vq3 w3' entry hS0
  have hcE : position (foundLandingVM (afterCompare s3 vs3 vq3) w3' entry).center =
      position r.center := by
    show position (afterCompare s3 vs3 vq3).center = _
    rw [hcenE, hcenF]
  refine ⟨_, _, _, L0 ++ L1, hst, ?_, invLP_of_landed hst hInv hS, hcE, ?_, rfl⟩
  · rw [show es0.length + k1 = k0 + (k1 + w1) by omega]; exact hcr
  · show position r.right < position (foundLandingVM (afterCompare s3 vs3 vq3) w3' entry).right
    have e1 : position (foundLandingVM (afterCompare s3 vs3 vq3) w3' entry).right =
        position (foundLandingVM (afterCompare s3 vs3 vq3) w3' entry).center + Rad' :=
      hRst.2.2.2.1.rightPos
    have e2 : position r.right = position r.center + R := hi0.rightPos
    rw [hcE] at e1
    omega

#print axioms front_of_run

/-- **`foundRouteMC_noshift` with the landing invariant exported.**  Identical to
`foundRouteMC_noshift` except that the landing's full `Inv` pack (`hInv`, built
in the proof before being weakened to `InvLP`) is part of the conclusion. -/
theorem foundRouteMC_noshift_Inv (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2))
    (hex : ∀ s, (PofC centre place entry raw).replayExhausted s = zero s.replay)
    {c0 : Control} {r : GalilVM} (hI : InvLP raw c0 r)
    (hlive : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (PofC centre place entry raw) qq first) 2048 m ⟨c0, r⟩ z →
      CentreLive z.ctl z.vm)
    (hcenR : GalilScaffoldInputTrace.Represents r.center.head raw ∧ r.center.head.focus ≠ none)
    {es0 : List Bool} {cF : Control} {sF : GalilVM}
    (hseg0 : WatchSegE (PofC centre place entry raw) qq first 2048 es0 c0 r cF sF)
    (hmF : cF.mode = .scan) (hrF : cF.replaying = false)
    (hcF : cF.clock = 1) (havF : canRight sF.right) (hidle : sF.chain = .idle)
    (vq : SearchVM) (hq : searchEffect (PofC centre place entry raw) true sF vq)
    (hfound : vq.search.mode = .found)
    (hmt : read (left sF.left) = read (right sF.right))
    (ch : ChainVM)
    (hch : ChainMatched (chainStart (vq.dp.config.tapes 11) ((PofC centre place entry raw).centre sF)
      ((PofC centre place entry raw).place sF) sF.center sF.radius) ch)
    (hchne : ch ≠ .idle) (oF : Bool)
    (hoF : refresh (galilFrame (PofC centre place entry raw) qq first)
      (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq) cF.output oF)
    {es : List Bool} {c2 : Control} {s2 : GalilVM}
    (hprepSeg : WatchSegE (PofC centre place entry raw) qq first 2048 es
      {cF with clock := 2048, output := oF, replaying := false}
      (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq) c2 s2)
    {c3 : Control} {s3 : GalilVM}
    (hseg : WatchSeg (PofC centre place entry raw) qq first 2048 c2 s2 c3 s3)
    (hm3 : c3.mode = .scan) (hr3 : c3.replaying = false) (hc3 : c3.clock = 1)
    (w3 : GalilScaffoldChainWatch.State) (hs3 : s3.chain = .watch w3) (hav3 : canRight s3.right)
    (vs3 : ScanVM) (vq3 : SearchVM)
    (hcmp3 : (galilFrame (PofC centre place entry raw) qq first).compare s3 (scanLens.set s3 vs3))
    (hmt3 : (galilFrame (PofC centre place entry raw) qq first).matched (scanLens.set s3 vs3))
    (hq3 : searchEffect (PofC centre place entry raw) true s3 vq3)
    (o3 : Bool) (ho3 : refresh (galilFrame (PofC centre place entry raw) qq first)
      (afterCompare s3 vs3 vq3) c3.output o3)
    (w3' : GalilScaffoldChainWatch.State) (hbroken : (afterCompare s3 vs3 vq3).chain = .broken w3')
    (hmargin : negative w3'.margin = false) (hlast : positive w3'.machine.control.last = true)
    (hlag : zero w3'.lag = true)
    (hcanon : Canonical w3'.machine.control.last)
    (hstage : ∀ R : ℕ, RadiusRep (afterCompare s3 vs3 vq3).radius R →
      StageEntry R w3'.machine.control.last) :
    ∃ (cT : Control) (sT : GalilVM) (k : ℕ) (L : List Piece),
      StepsAll (galilFrameS (PofC centre place entry raw) qq first) 2048 (SoundScanNR raw) k
        ⟨c0, r⟩ ⟨cT, sT⟩ ∧
      CostedRun r sT k L ∧ InvLP raw cT sT ∧
      position sT.center = position r.center ∧ position r.right < position sT.right ∧
      sT.right = (afterCompare s3 vs3 vq3).right ∧ Inv raw cT sT := by
  obtain ⟨R, hst0, hi0, hRR0, hlc0, hS0, hiF, houtF, hcenF⟩ := at_found centre place entry qq first raw hI hseg0
  have hM0 : MInv raw c0 r := hI.1.1.elim (fun h => h.minv) (fun ⟨_, h⟩ => h.minv)
  have hclk0 : c0.clock = 2048 := hI.1.1.elim (fun h => h.mode.2.2) (fun ⟨_, h⟩ => h.mode.2.2)
  obtain ⟨L0, k0, w1, hcr0, hk0, hw1⟩ :=
    PalPeg.GalilCostedFallback.costedRun_watchSegE_pend raw _ qq first hseg0 (position r.center) R 0 hi0
      (by rw [hclk0]) havF
  obtain ⟨k1, L1, hst1, hcr1, hcenE⟩ :=
    costedRun_found_noshift raw (PofC centre place entry raw) rfl rfl qq first 2048 le_rfl hmF hrF hcF
      havF hidle hiF houtF vq hq hfound hmt ch hch hchne oF hoF hprepSeg hseg hm3 hr3 hc3 w3 hs3 hav3
      vs3 vq3 hcmp3 hmt3 hq3 o3 ho3 w3' hbroken hmargin hlast hlag entry (fun _ _ h => h) w1
      (by rw [hcF]; omega)
  have hst := stepsAll_trans hst0 hst1
  have hcr := costedRun_trans hcr0 hcr1
  obtain ⟨Rad', hlt, hRst⟩ := noshift_restarted raw _ qq first 2048 hcenR hi0 hRR0 hlc0 hseg0 havF hmt
    vq ch hchne oF hprepSeg hseg hav3 vs3 vq3 hcmp3 hmt3 w3' hcanon hlast entry
  have hM := noshift_minv raw _ hex qq first 2048 hi0 hM0
    hseg0 hrF havF vq hmt ch hchne oF hprepSeg hseg hr3 hav3 vs3 vq3 hcmp3 hmt3 o3 w3' entry
  have hfr := front_of_run centre place entry qq first raw hI hlive hst
  have hsi0 : ShiftIdle r := hI.1.1.elim (fun h => h.shiftIdle) (fun ⟨_, h⟩ => h.shiftIdle)
  have hsi : ShiftIdle (foundLandingVM (afterCompare s3 vs3 vq3) w3' entry) := by
    refine PalPeg.GalilReplaySegment.shiftIdle_congr ?_ hsi0
    show s3.remaining = r.remaining
    rw [watchSeg_remaining _ qq first 2048 hseg, watchSegE_remaining _ qq first 2048 hprepSeg,
      afterCompare_remaining, watchSegE_remaining _ qq first 2048 hseg0]
  have hInv : Inv raw (foundLandingControl c3 2048 o3) (foundLandingVM (afterCompare s3 vs3 vq3) w3' entry) :=
    { rest := ⟨Rad', _, hRst⟩, minv := hM, mode := ⟨hm3, rfl, rfl⟩
      stage := fun Rad last h0 => by
        have hl : last = w3'.machine.control.last := h0.2.2.2.2.2.2.2.1.symm
        subst hl
        exact hstage Rad h0.2.2.2.2.1
      search := searchReady_of_restarted hRst
      block := blockInv_of_restarted hRst
      frontier := hfr.1, rest_replay := hfr.2
      input := input_of_restarted hRst
      shiftIdle := hsi }
  have hS := spanRep_found_noshift _ qq first 2048 hseg0 vq ch oF hprepSeg hseg vs3 vq3 w3' entry hS0
  have hcE : position (foundLandingVM (afterCompare s3 vs3 vq3) w3' entry).center =
      position r.center := by
    show position (afterCompare s3 vs3 vq3).center = _
    rw [hcenE, hcenF]
  refine ⟨_, _, _, L0 ++ L1, hst, ?_, invLP_of_landed hst hInv hS, hcE, ?_, rfl, hInv⟩
  · rw [show es0.length + k1 = k0 + (k1 + w1) by omega]; exact hcr
  · show position r.right < position (foundLandingVM (afterCompare s3 vs3 vq3) w3' entry).right
    have e1 : position (foundLandingVM (afterCompare s3 vs3 vq3) w3' entry).right =
        position (foundLandingVM (afterCompare s3 vs3 vq3) w3' entry).center + Rad' :=
      hRst.2.2.2.1.rightPos
    have e2 : position r.right = position r.center + R := hi0.rightPos
    rw [hcE] at e1
    omega

#print axioms foundRouteMC_noshift_Inv
#print axioms foundRouteMC_noshift

/-! ## (b) The landing with the shift -/

/-- **`foundRouteMC_shift`.**  From an `InvLP` state, the idle segment, the
found comparison, the preparation and watch segments, the first shift, the
re-shift rounds, the final segment and the breaking match with its restart
tick: a sound run of `k` ticks, a `CostedRun` of the same `k` ticks, an
`InvLP` landing, and strict progress of the centre.

Named hypotheses: `hlive` (`CentreLive` along the run) and `ha` (the read
origin of the first shift is aligned).  `Restarted`, the stage budget,
`ShiftIdle`, `Frontier`/`ReplayRest`, `SpanRep` and `OutputRel` are derived. -/
theorem foundRouteMC_shift (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2))
    (hex : ∀ s, (PofC centre place entry raw).replayExhausted s = zero s.replay)
    {c0 : Control} {r : GalilVM} (hI : InvLP raw c0 r)
    (hlive : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (PofC centre place entry raw) qq first) 2048 m ⟨c0, r⟩ z →
      CentreLive z.ctl z.vm)
    (a : Fin 2) (ls rs q : List (Fin 2)) (gap : Bool)
    (hraw : raw = (a :: ls).reverse ++ rs ++ q)
    {es0 : List Bool} {cF : Control} {sF : GalilVM}
    (hseg0 : WatchSegE (PofC centre place entry raw) qq first 2048 es0 c0 r cF sF)
    (hmF : cF.mode = .scan) (hrF : cF.replaying = false)
    (hcF : cF.clock = 1) (havF : canRight sF.right) (hidle : sF.chain = .idle)
    (hCen : sF.center = represent ⟨a :: ls,gap⟩ (rs.map some) q)
    (vq : SearchVM) (hq : searchEffect (PofC centre place entry raw) true sF vq)
    (hfound : vq.search.mode = .found)
    (hmt : read (left sF.left) = read (right sF.right))
    (ch : ChainVM)
    (hch : ChainMatched (chainStart (vq.dp.config.tapes 11) ((PofC centre place entry raw).centre sF)
      ((PofC centre place entry raw).place sF) sF.center sF.radius) ch)
    (hchne : ch ≠ .idle) (oF : Bool)
    (hoF : refresh (galilFrame (PofC centre place entry raw) qq first)
      (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq) cF.output oF)
    {es : List Bool} {c2 : Control} {s2 : GalilVM}
    (hprepSeg : WatchSegE (PofC centre place entry raw) qq first 2048 es
      {cF with clock := 2048, output := oF, replaying := false}
      (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq) c2 s2)
    {c1 : Control} {s1 : GalilVM}
    (hseg : WatchSeg (PofC centre place entry raw) qq first 2048 c2 s2 c1 s1)
    (h : ℕ) (hm1 : c1.mode = .scan) (hr1 : c1.replaying = false) (hc1 : c1.clock = 1)
    (w : GalilScaffoldChainWatch.State) (hs1 : s1.chain = .watch w) (hz : zero w.lag = true)
    (hav : canRight s1.right) (vs : ScanVM) (vq' : SearchVM)
    (hcmp : (galilFrame (PofC centre place entry raw) qq first).compare s1 (scanLens.set s1 vs))
    (hmis : ¬ (galilFrame (PofC centre place entry raw) qq first).matched (scanLens.set s1 vs))
    (hq' : searchEffect (PofC centre place entry raw) false s1 vq')
    (hg : (PofC centre place entry raw).shiftGuard (afterMismatch s1 vs vq'))
    (s2' : GalilVM) (hb : (PofC centre place entry raw).beginShift (afterMismatch s1 vs vq') s2')
    (hs2' : beginShiftVM h w (afterMismatch s1 vs vq') s2') (hi2 : CopyIdle s2')
    {t' : ShiftState} {v : GalilScaffoldChainWatch.State} {cycle : Counter}
    (hchain : ChainShiftRun ⟨s1.center, left s1.left, ofNat h, inc s1.radius, inc (inc s1.length)⟩
      (GalilScaffoldChainWatch.immediate w) reset h t' v cycle)
    (o : Bool)
    (ho : refresh (galilFrameS (PofC centre place entry raw) qq first)
      (shiftLens.set s2' ⟨t', .watch v, cycle⟩) c1.output o)
    (org : ReadOrigin raw) (hint : org.interior.length+1 = h)
    (he : Entry raw org (toOnly (shiftLens.set s2' ⟨t', .watch v, cycle⟩) v))
    (hoc : org.center = position sF.center)
    (ha : PalPeg.GalilRadiusConsumed.Aligned org)
    {lower span : ℕ}
    (hdp : GalilDpCorrect.Result ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (span+1)) lower 0
      (GalilScaffoldProgram.denote vq.dp.config))
    (hpc : (GalilScaffoldProgram.denote vq.dp.config).pc = 346)
    (hpos11 : (GalilScaffoldProgram.denote vq.dp.config).pos 11 = h)
    (hlow : ∀ δ, 0 < δ → δ ≤ lower → ¬ HasPeriod (Span raw org.center org.radius) (2*δ))
    {m : ℕ} {c' : Control} {s' : GalilVM}
    (hrounds : Rounds (PofC centre place entry raw) qq first 2048 h m
      {c1 with mode := .scan, clock := 2048, output := o}
      (shiftLens.set s2' ⟨t', .watch v, cycle⟩) c' s')
    {n : ℕ} {c3 : Control} {s3 : GalilVM}
    (hseg3 : ScanSeg (PofC centre place entry raw) qq first 2048 n c' s' c3 s3)
    (hm3 : c3.mode = .scan) (hr3 : c3.replaying = false) (hc3 : c3.clock = 1)
    (w3 : GalilScaffoldChainWatch.State) (hs3 : s3.chain = .watch w3) (hav3 : canRight s3.right)
    (vs3 : ScanVM) (vq3 : SearchVM)
    (hcmp3 : (galilFrame (PofC centre place entry raw) qq first).compare s3 (scanLens.set s3 vs3))
    (hmt3 : (galilFrame (PofC centre place entry raw) qq first).matched (scanLens.set s3 vs3))
    (hq3 : searchEffect (PofC centre place entry raw) true s3 vq3)
    (o3 : Bool) (ho3 : refresh (galilFrame (PofC centre place entry raw) qq first)
      (afterCompare s3 vs3 vq3) c3.output o3)
    (w3' : GalilScaffoldChainWatch.State) (hbroken : (afterCompare s3 vs3 vq3).chain = .broken w3')
    (hmargin : negative w3'.margin = false) (hlast : positive w3'.machine.control.last = true)
    (hlag : zero w3'.lag = true) :
    ∃ (cT : Control) (sT : GalilVM) (k : ℕ) (L : List Piece),
      StepsAll (galilFrameS (PofC centre place entry raw) qq first) 2048 (SoundScanNR raw) k
        ⟨c0, r⟩ ⟨cT, sT⟩ ∧
      CostedRun r sT k L ∧ InvLP raw cT sT ∧
      position r.center < position sT.center ∧
      sT.right = (afterCompare s3 vs3 vq3).right := by
  obtain ⟨R, hst0, hi0, hRR0, hlc0, hS0, hiF, houtF, hcenF⟩ := at_found centre place entry qq first raw hI hseg0
  have hM0 : MInv raw c0 r := hI.1.1.elim (fun h => h.minv) (fun ⟨_, h⟩ => h.minv)
  have hclk0 : c0.clock = 2048 := hI.1.1.elim (fun h => h.mode.2.2) (fun ⟨_, h⟩ => h.mode.2.2)
  obtain ⟨L0, k0, w1, hcr0, hk0, hw1⟩ :=
    PalPeg.GalilCostedFallback.costedRun_watchSegE_pend raw _ qq first hseg0 (position r.center) R 0 hi0
      (by rw [hclk0]) havF
  obtain ⟨k1, L1, hst1, hcr1, hh, hcentre⟩ :=
    costedRun_found_shift raw (PofC centre place entry raw) rfl rfl qq first 2048 le_rfl hmF hrF hcF
      havF hidle hiF houtF vq hq hfound hmt ch hch hchne oF hoF hprepSeg hseg h hm1 hr1 hc1 w hs1 hz
      hav vs vq' hcmp hmis hq' hg s2' hb hs2' hi2 hchain o ho org hint he hoc hrounds hseg3 hm3 hr3
      hc3 w3 hs3 hav3 vs3 vq3 hcmp3 hmt3 hq3 o3 ho3 w3' hbroken hmargin hlast hlag entry
      (fun _ _ h => h) w1 (by rw [hcF]; omega)
  have hst := stepsAll_trans hst0 hst1
  have hcr := costedRun_trans hcr0 hcr1
  -- the centre invariant
  have hMF : MInv raw cF sF :=
    minv_watchSegE raw _ hex qq first 2048 hseg0 R hi0 hM0
  have hM : MInv raw (foundLandingControl c3 2048 o3)
      (foundLandingVM (afterCompare s3 vs3 vq3) w3' entry) :=
    life_minv raw _ hex qq first 2048 a ls rs q gap hraw hmF hrF hcF havF hidle hiF hMF hCen vq hq
      hfound hmt ch hch hchne oF hoF hprepSeg hseg h hm1 hr1 hc1 w hs1 hz hav vs vq' hcmp hmis hq' hg
      s2' hb hs2' hi2 hchain o ho org hint he hoc hdp hpc hpos11 hlow hrounds hseg3 hm3 hr3 hc3 w3
      hs3 hav3 vs3 vq3 hcmp3 hmt3 hq3 o3 ho3 w3' hbroken entry
  -- the break data
  have hpo : (shiftLens.set s2' ⟨t', .watch v, cycle⟩).periodOnly = true := by
    show s2'.periodOnly = true; rw [hs2'.2]
  have hzv : zero v.lag = true := by rw [chain_shift_lag hchain]; exact hz
  have hbr3 : vs3.chain = .broken w3' := by rw [← afterCompare_chain s3 vs3 vq3]; exact hbroken
  have hend3 := PalPeg.GalilBreakTerminal.hend3_of_matched_break _ qq first 2048 h org hint hpo hzv
    he hrounds hseg3 w3 hs3 hav3 vs3 hcmp3 hmt3 w3' hbr3
  obtain ⟨hrep, hfoc, hposS⟩ := rounds_centerRep _ qq first 2048 h hrounds v hpo rfl hzv org hint he
  have hcenterS : read s'.center ≠ none := by
    intro h0; apply hfoc; unfold GalilScaffoldInputHead.read at h0; simpa using h0
  obtain ⟨_, hw3', _, hrest⟩ := rounds_break _ qq first 2048 h hrounds v hpo rfl hzv hseg3 hm3 hr3
    hc3 w3 hs3 hav3 vs3 vq3 hcmp3 hmt3 hq3 hend3 w3' hbr3 o3 ho3
  obtain ⟨hinv, hbrk, _, _, _, _, hrr3, _, _, hcanon⟩ := hrest raw org hint he hcenterS
  -- `Restarted` at the landing
  have hcen3 : s3.center = s'.center := scanSeg_center _ qq first 2048 hseg3
  have hcenE : (afterCompare s3 vs3 vq3).center = s'.center := by rw [afterCompare_center, hcen3]
  obtain ⟨_, _, _, hrcF, hlcF⟩ := watchSegE_heads _ qq first 2048 hseg0
  have hprepStart : Canonical (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq).radius ∧
      Canonical (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq).length := by
    rw [afterCompare_radius, afterCompare_length]
    exact ⟨inc_canonical _ (hrcF hRR0.1), inc_canonical _ (inc_canonical _ (hlcF hlc0))⟩
  obtain ⟨_, _, _, hrc2, hlc2⟩ := watchSegE_heads _ qq first 2048 hprepSeg
  obtain ⟨hrc1, hlc1⟩ := watchSeg_counters _ qq first 2048 hseg
  obtain ⟨_, hrt, hlt⟩ := shift_run_canonical (shiftRun_of_chain hchain)
    ⟨ofNat_canonical h, inc_canonical _ (hrc1 (hrc2 hprepStart.1)),
      inc_canonical _ (inc_canonical _ (hlc1 (hlc2 hprepStart.2)))⟩
  obtain ⟨_, hlcS'⟩ := rounds_counters _ qq first 2048 h hrounds hrt hlt
  obtain ⟨_, hlcS3⟩ := scanSeg_counters _ qq first 2048 hseg3
  have hRst : Restarted raw (foundLandingVM (afterCompare s3 vs3 vq3) w3' entry)
      (foundRestartRadius org.radius h m n) w3'.machine.control.last := by
    refine ⟨rfl, ?_, ?_, ?_, hrr3, ?_, rfl, rfl, hcanon, ((positive_iff _ hcanon).1 hlast).le⟩
    · show GalilScaffoldInputTrace.Represents (afterCompare s3 vs3 vq3).center.head _
      rw [hcenE]; exact hrep
    · show (afterCompare s3 vs3 vq3).center.head.focus ≠ none
      rw [hcenE]; exact hfoc
    · show ScanInvariant _ (position (afterCompare s3 vs3 vq3).center) _ (afterCompare s3 vs3 vq3).left
        (afterCompare s3 vs3 vq3).right
      rw [hcenE, hposS]
      have e1 : org.center + m*h + h = org.center + (m+1)*h := by ring
      rw [e1]; exact hinv
    · show Canonical (afterCompare s3 vs3 vq3).length
      rw [afterCompare_length]
      exact inc_canonical _ (inc_canonical _ (hlcS3 hlcS'))
  -- the stage budget
  have hstage : StageEntry (foundRestartRadius org.radius h m n) w3'.machine.control.last :=
    PalPeg.GalilBreakTerminal.stageEntry_after_found_closed _ qq first 2048 h org hint hpo hzv he
      hrounds hseg3 w3 hs3 w3' hw3' ha hbrk hav3 vs3 hcmp3 hmt3 hbr3
  -- the frontier and the shift counter
  have hfr := front_of_run centre place entry qq first raw hI hlive hst
  have hsi : ShiftIdle (foundLandingVM (afterCompare s3 vs3 vq3) w3' entry) := by
    rw [shiftIdle_iff]
    show positive s3.remaining = false
    rw [scanSeg_remaining _ qq first 2048 hseg3]
    exact rounds_remaining _ qq first 2048 h hrounds (chain_shift_exhausts h rfl hchain)
  have hInv : Inv raw (foundLandingControl c3 2048 o3)
      (foundLandingVM (afterCompare s3 vs3 vq3) w3' entry) :=
    { rest := ⟨_, _, hRst⟩, minv := hM, mode := ⟨hm3, rfl, rfl⟩
      stage := fun Rad last h0 => by
        obtain ⟨e1, e2⟩ := restarted_unique hRst h0
        subst e1; subst e2
        exact hstage
      search := searchReady_of_restarted hRst
      block := blockInv_of_restarted hRst
      frontier := hfr.1, rest_replay := hfr.2
      input := input_of_restarted hRst
      shiftIdle := hsi }
  have hS := spanRep_found_shift _ qq first 2048 hseg0 vq ch oF hprepSeg hseg h w s2' t' v cycle hchain
    hrounds hseg3 vs3 vq3 w3' entry hS0
  refine ⟨_, _, _, L0 ++ L1, hst, ?_, invLP_of_landed hst hInv hS, ?_, rfl⟩
  · rw [show es0.length + k1 = k0 + (k1 + w1) by omega]; exact hcr
  · show position r.center < position (afterCompare s3 vs3 vq3).center
    rw [hcentre, hcenF]
    have : h ≤ (m+1)*h := Nat.le_mul_of_pos_left h (Nat.succ_pos m)
    omega


/-- **`foundRouteMC_shift` with the landing invariant exported.**  Identical to
`foundRouteMC_shift` except that the landing's full `Inv` pack — which the proof
already builds (`hInv`) before weakening it to `InvLP` — is part of the
conclusion.  This is what `CloseoutWatchPhase2.landingRestart_of_inv` needs in
order to turn the constructed landing into a `LandingRestart`. -/
theorem foundRouteMC_shift_Inv (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2))
    (hex : ∀ s, (PofC centre place entry raw).replayExhausted s = zero s.replay)
    {c0 : Control} {r : GalilVM} (hI : InvLP raw c0 r)
    (hlive : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (PofC centre place entry raw) qq first) 2048 m ⟨c0, r⟩ z →
      CentreLive z.ctl z.vm)
    (a : Fin 2) (ls rs q : List (Fin 2)) (gap : Bool)
    (hraw : raw = (a :: ls).reverse ++ rs ++ q)
    {es0 : List Bool} {cF : Control} {sF : GalilVM}
    (hseg0 : WatchSegE (PofC centre place entry raw) qq first 2048 es0 c0 r cF sF)
    (hmF : cF.mode = .scan) (hrF : cF.replaying = false)
    (hcF : cF.clock = 1) (havF : canRight sF.right) (hidle : sF.chain = .idle)
    (hCen : sF.center = represent ⟨a :: ls,gap⟩ (rs.map some) q)
    (vq : SearchVM) (hq : searchEffect (PofC centre place entry raw) true sF vq)
    (hfound : vq.search.mode = .found)
    (hmt : read (left sF.left) = read (right sF.right))
    (ch : ChainVM)
    (hch : ChainMatched (chainStart (vq.dp.config.tapes 11) ((PofC centre place entry raw).centre sF)
      ((PofC centre place entry raw).place sF) sF.center sF.radius) ch)
    (hchne : ch ≠ .idle) (oF : Bool)
    (hoF : refresh (galilFrame (PofC centre place entry raw) qq first)
      (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq) cF.output oF)
    {es : List Bool} {c2 : Control} {s2 : GalilVM}
    (hprepSeg : WatchSegE (PofC centre place entry raw) qq first 2048 es
      {cF with clock := 2048, output := oF, replaying := false}
      (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq) c2 s2)
    {c1 : Control} {s1 : GalilVM}
    (hseg : WatchSeg (PofC centre place entry raw) qq first 2048 c2 s2 c1 s1)
    (h : ℕ) (hm1 : c1.mode = .scan) (hr1 : c1.replaying = false) (hc1 : c1.clock = 1)
    (w : GalilScaffoldChainWatch.State) (hs1 : s1.chain = .watch w) (hz : zero w.lag = true)
    (hav : canRight s1.right) (vs : ScanVM) (vq' : SearchVM)
    (hcmp : (galilFrame (PofC centre place entry raw) qq first).compare s1 (scanLens.set s1 vs))
    (hmis : ¬ (galilFrame (PofC centre place entry raw) qq first).matched (scanLens.set s1 vs))
    (hq' : searchEffect (PofC centre place entry raw) false s1 vq')
    (hg : (PofC centre place entry raw).shiftGuard (afterMismatch s1 vs vq'))
    (s2' : GalilVM) (hb : (PofC centre place entry raw).beginShift (afterMismatch s1 vs vq') s2')
    (hs2' : beginShiftVM h w (afterMismatch s1 vs vq') s2') (hi2 : CopyIdle s2')
    {t' : ShiftState} {v : GalilScaffoldChainWatch.State} {cycle : Counter}
    (hchain : ChainShiftRun ⟨s1.center, left s1.left, ofNat h, inc s1.radius, inc (inc s1.length)⟩
      (GalilScaffoldChainWatch.immediate w) reset h t' v cycle)
    (o : Bool)
    (ho : refresh (galilFrameS (PofC centre place entry raw) qq first)
      (shiftLens.set s2' ⟨t', .watch v, cycle⟩) c1.output o)
    (org : ReadOrigin raw) (hint : org.interior.length+1 = h)
    (he : Entry raw org (toOnly (shiftLens.set s2' ⟨t', .watch v, cycle⟩) v))
    (hoc : org.center = position sF.center)
    (ha : PalPeg.GalilRadiusConsumed.Aligned org)
    {lower span : ℕ}
    (hdp : GalilDpCorrect.Result ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (span+1)) lower 0
      (GalilScaffoldProgram.denote vq.dp.config))
    (hpc : (GalilScaffoldProgram.denote vq.dp.config).pc = 346)
    (hpos11 : (GalilScaffoldProgram.denote vq.dp.config).pos 11 = h)
    (hlow : ∀ δ, 0 < δ → δ ≤ lower → ¬ HasPeriod (Span raw org.center org.radius) (2*δ))
    {m : ℕ} {c' : Control} {s' : GalilVM}
    (hrounds : Rounds (PofC centre place entry raw) qq first 2048 h m
      {c1 with mode := .scan, clock := 2048, output := o}
      (shiftLens.set s2' ⟨t', .watch v, cycle⟩) c' s')
    {n : ℕ} {c3 : Control} {s3 : GalilVM}
    (hseg3 : ScanSeg (PofC centre place entry raw) qq first 2048 n c' s' c3 s3)
    (hm3 : c3.mode = .scan) (hr3 : c3.replaying = false) (hc3 : c3.clock = 1)
    (w3 : GalilScaffoldChainWatch.State) (hs3 : s3.chain = .watch w3) (hav3 : canRight s3.right)
    (vs3 : ScanVM) (vq3 : SearchVM)
    (hcmp3 : (galilFrame (PofC centre place entry raw) qq first).compare s3 (scanLens.set s3 vs3))
    (hmt3 : (galilFrame (PofC centre place entry raw) qq first).matched (scanLens.set s3 vs3))
    (hq3 : searchEffect (PofC centre place entry raw) true s3 vq3)
    (o3 : Bool) (ho3 : refresh (galilFrame (PofC centre place entry raw) qq first)
      (afterCompare s3 vs3 vq3) c3.output o3)
    (w3' : GalilScaffoldChainWatch.State) (hbroken : (afterCompare s3 vs3 vq3).chain = .broken w3')
    (hmargin : negative w3'.margin = false) (hlast : positive w3'.machine.control.last = true)
    (hlag : zero w3'.lag = true) :
    ∃ (cT : Control) (sT : GalilVM) (k : ℕ) (L : List Piece),
      StepsAll (galilFrameS (PofC centre place entry raw) qq first) 2048 (SoundScanNR raw) k
        ⟨c0, r⟩ ⟨cT, sT⟩ ∧
      CostedRun r sT k L ∧ InvLP raw cT sT ∧
      position r.center < position sT.center ∧
      sT.right = (afterCompare s3 vs3 vq3).right ∧ Inv raw cT sT := by
  obtain ⟨R, hst0, hi0, hRR0, hlc0, hS0, hiF, houtF, hcenF⟩ := at_found centre place entry qq first raw hI hseg0
  have hM0 : MInv raw c0 r := hI.1.1.elim (fun h => h.minv) (fun ⟨_, h⟩ => h.minv)
  have hclk0 : c0.clock = 2048 := hI.1.1.elim (fun h => h.mode.2.2) (fun ⟨_, h⟩ => h.mode.2.2)
  obtain ⟨L0, k0, w1, hcr0, hk0, hw1⟩ :=
    PalPeg.GalilCostedFallback.costedRun_watchSegE_pend raw _ qq first hseg0 (position r.center) R 0 hi0
      (by rw [hclk0]) havF
  obtain ⟨k1, L1, hst1, hcr1, hh, hcentre⟩ :=
    costedRun_found_shift raw (PofC centre place entry raw) rfl rfl qq first 2048 le_rfl hmF hrF hcF
      havF hidle hiF houtF vq hq hfound hmt ch hch hchne oF hoF hprepSeg hseg h hm1 hr1 hc1 w hs1 hz
      hav vs vq' hcmp hmis hq' hg s2' hb hs2' hi2 hchain o ho org hint he hoc hrounds hseg3 hm3 hr3
      hc3 w3 hs3 hav3 vs3 vq3 hcmp3 hmt3 hq3 o3 ho3 w3' hbroken hmargin hlast hlag entry
      (fun _ _ h => h) w1 (by rw [hcF]; omega)
  have hst := stepsAll_trans hst0 hst1
  have hcr := costedRun_trans hcr0 hcr1
  -- the centre invariant
  have hMF : MInv raw cF sF :=
    minv_watchSegE raw _ hex qq first 2048 hseg0 R hi0 hM0
  have hM : MInv raw (foundLandingControl c3 2048 o3)
      (foundLandingVM (afterCompare s3 vs3 vq3) w3' entry) :=
    life_minv raw _ hex qq first 2048 a ls rs q gap hraw hmF hrF hcF havF hidle hiF hMF hCen vq hq
      hfound hmt ch hch hchne oF hoF hprepSeg hseg h hm1 hr1 hc1 w hs1 hz hav vs vq' hcmp hmis hq' hg
      s2' hb hs2' hi2 hchain o ho org hint he hoc hdp hpc hpos11 hlow hrounds hseg3 hm3 hr3 hc3 w3
      hs3 hav3 vs3 vq3 hcmp3 hmt3 hq3 o3 ho3 w3' hbroken entry
  -- the break data
  have hpo : (shiftLens.set s2' ⟨t', .watch v, cycle⟩).periodOnly = true := by
    show s2'.periodOnly = true; rw [hs2'.2]
  have hzv : zero v.lag = true := by rw [chain_shift_lag hchain]; exact hz
  have hbr3 : vs3.chain = .broken w3' := by rw [← afterCompare_chain s3 vs3 vq3]; exact hbroken
  have hend3 := PalPeg.GalilBreakTerminal.hend3_of_matched_break _ qq first 2048 h org hint hpo hzv
    he hrounds hseg3 w3 hs3 hav3 vs3 hcmp3 hmt3 w3' hbr3
  obtain ⟨hrep, hfoc, hposS⟩ := rounds_centerRep _ qq first 2048 h hrounds v hpo rfl hzv org hint he
  have hcenterS : read s'.center ≠ none := by
    intro h0; apply hfoc; unfold GalilScaffoldInputHead.read at h0; simpa using h0
  obtain ⟨_, hw3', _, hrest⟩ := rounds_break _ qq first 2048 h hrounds v hpo rfl hzv hseg3 hm3 hr3
    hc3 w3 hs3 hav3 vs3 vq3 hcmp3 hmt3 hq3 hend3 w3' hbr3 o3 ho3
  obtain ⟨hinv, hbrk, _, _, _, _, hrr3, _, _, hcanon⟩ := hrest raw org hint he hcenterS
  -- `Restarted` at the landing
  have hcen3 : s3.center = s'.center := scanSeg_center _ qq first 2048 hseg3
  have hcenE : (afterCompare s3 vs3 vq3).center = s'.center := by rw [afterCompare_center, hcen3]
  obtain ⟨_, _, _, hrcF, hlcF⟩ := watchSegE_heads _ qq first 2048 hseg0
  have hprepStart : Canonical (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq).radius ∧
      Canonical (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq).length := by
    rw [afterCompare_radius, afterCompare_length]
    exact ⟨inc_canonical _ (hrcF hRR0.1), inc_canonical _ (inc_canonical _ (hlcF hlc0))⟩
  obtain ⟨_, _, _, hrc2, hlc2⟩ := watchSegE_heads _ qq first 2048 hprepSeg
  obtain ⟨hrc1, hlc1⟩ := watchSeg_counters _ qq first 2048 hseg
  obtain ⟨_, hrt, hlt⟩ := shift_run_canonical (shiftRun_of_chain hchain)
    ⟨ofNat_canonical h, inc_canonical _ (hrc1 (hrc2 hprepStart.1)),
      inc_canonical _ (inc_canonical _ (hlc1 (hlc2 hprepStart.2)))⟩
  obtain ⟨_, hlcS'⟩ := rounds_counters _ qq first 2048 h hrounds hrt hlt
  obtain ⟨_, hlcS3⟩ := scanSeg_counters _ qq first 2048 hseg3
  have hRst : Restarted raw (foundLandingVM (afterCompare s3 vs3 vq3) w3' entry)
      (foundRestartRadius org.radius h m n) w3'.machine.control.last := by
    refine ⟨rfl, ?_, ?_, ?_, hrr3, ?_, rfl, rfl, hcanon, ((positive_iff _ hcanon).1 hlast).le⟩
    · show GalilScaffoldInputTrace.Represents (afterCompare s3 vs3 vq3).center.head _
      rw [hcenE]; exact hrep
    · show (afterCompare s3 vs3 vq3).center.head.focus ≠ none
      rw [hcenE]; exact hfoc
    · show ScanInvariant _ (position (afterCompare s3 vs3 vq3).center) _ (afterCompare s3 vs3 vq3).left
        (afterCompare s3 vs3 vq3).right
      rw [hcenE, hposS]
      have e1 : org.center + m*h + h = org.center + (m+1)*h := by ring
      rw [e1]; exact hinv
    · show Canonical (afterCompare s3 vs3 vq3).length
      rw [afterCompare_length]
      exact inc_canonical _ (inc_canonical _ (hlcS3 hlcS'))
  -- the stage budget
  have hstage : StageEntry (foundRestartRadius org.radius h m n) w3'.machine.control.last :=
    PalPeg.GalilBreakTerminal.stageEntry_after_found_closed _ qq first 2048 h org hint hpo hzv he
      hrounds hseg3 w3 hs3 w3' hw3' ha hbrk hav3 vs3 hcmp3 hmt3 hbr3
  -- the frontier and the shift counter
  have hfr := front_of_run centre place entry qq first raw hI hlive hst
  have hsi : ShiftIdle (foundLandingVM (afterCompare s3 vs3 vq3) w3' entry) := by
    rw [shiftIdle_iff]
    show positive s3.remaining = false
    rw [scanSeg_remaining _ qq first 2048 hseg3]
    exact rounds_remaining _ qq first 2048 h hrounds (chain_shift_exhausts h rfl hchain)
  have hInv : Inv raw (foundLandingControl c3 2048 o3)
      (foundLandingVM (afterCompare s3 vs3 vq3) w3' entry) :=
    { rest := ⟨_, _, hRst⟩, minv := hM, mode := ⟨hm3, rfl, rfl⟩
      stage := fun Rad last h0 => by
        obtain ⟨e1, e2⟩ := restarted_unique hRst h0
        subst e1; subst e2
        exact hstage
      search := searchReady_of_restarted hRst
      block := blockInv_of_restarted hRst
      frontier := hfr.1, rest_replay := hfr.2
      input := input_of_restarted hRst
      shiftIdle := hsi }
  have hS := spanRep_found_shift _ qq first 2048 hseg0 vq ch oF hprepSeg hseg h w s2' t' v cycle hchain
    hrounds hseg3 vs3 vq3 w3' entry hS0
  refine ⟨_, _, _, L0 ++ L1, hst, ?_, invLP_of_landed hst hInv hS, ?_, rfl, hInv⟩
  · rw [show es0.length + k1 = k0 + (k1 + w1) by omega]; exact hcr
  · show position r.center < position (afterCompare s3 vs3 vq3).center
    rw [hcentre, hcenF]
    have : h ≤ (m+1)*h := Nat.le_mul_of_pos_left h (Nat.succ_pos m)
    omega

#print axioms foundRouteMC_shift_Inv
#print axioms foundRouteMC_shift

end PalPeg.GalilFoundLandingL
