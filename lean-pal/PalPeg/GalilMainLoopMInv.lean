import PalPeg.GalilLiveCentreCycle2

/-!
# The main loop as a composition of centre-invariant-preserving cycles

`FoundCycle` and `FallbackCycle` bundle the premises of the two main-loop
cycles (`cycle_found_stepsAll` / `cycle_found_minv` and
`cycle_fallback_stepsAll` / `cycle_fallback_minv`) as predicates on the state
a cycle starts from. `foundCycle_step` and `fallbackCycle_step` run one such
cycle: a sound run (`StepsAll … (SoundScanNR raw)`) to a state that carries
the centre invariant `MInv` and is again `Restarted`.

`Cycles` is the reflexive-transitive closure of those two steps, in
continuation style: the state a cycle lands in is produced by the step lemma,
not named by the constructor, so the continuation is a function of it.
`cycles_stepsAll_minv` is the composition: from `MInv` and `Restarted` at the
start, a sound run to the end, with `MInv` and `Restarted` there.

`init_minv` establishes the invariant at the first restarted state, using
`leftmost_one`: at right place `1` the leftmost live centre is `1`.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open Manacher GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-- The premises of one main-loop cycle through a found comparison, at the
state `⟨c0, r⟩` it starts from: the union of the hypothesis lists of
`cycle_found_stepsAll` and `cycle_found_minv`, together with the `Restarted`
fact at the state the cycle lands in (`hRnext`, supplied by `life_restarted`
at the call site). -/
def FoundCycle (P : Shared) (qq : ℕ) (first : Fin 9) (delay : ℕ) (raw : List (Fin 2))
    (c0 : Control) (r : GalilVM) : Prop :=
  ∃ (a : Fin 2) (ls rs q : List (Fin 2)) (gap : Bool)
    (es0 : List Bool) (cF : Control) (sF : GalilVM)
    (vq : SearchVM) (ch : ChainVM) (oF : Bool)
    (es : List Bool) (c2 : Control) (s2 : GalilVM) (cM : Control) (sM : GalilVM)
    (h : ℕ) (w : GalilScaffoldChainWatch.State) (vs : ScanVM) (vq' : SearchVM) (s2' : GalilVM)
    (t' : ShiftState) (v : GalilScaffoldChainWatch.State) (cycle : Counter) (o : Bool)
    (org : ReadOrigin raw) (lower span m : ℕ) (c' : Control) (s' : GalilVM)
    (n : ℕ) (c3 : Control) (s3 : GalilVM) (w3 : GalilScaffoldChainWatch.State)
    (vs3 : ScanVM) (vq3 : SearchVM) (o3 : Bool) (cen3 r3 : ℕ)
    (w3' : GalilScaffoldChainWatch.State) (entry : ℕ),
    P.onLetter = onLetterVM raw ∧ P.leftFirst = leftFirstVM ∧
    (∀ s, P.replayExhausted s = zero s.replay) ∧
    raw = (a :: ls).reverse ++ rs ++ q ∧
    OutputRel raw c0 r ∧
    WatchSegE P qq first delay es0 c0 r cF sF ∧
    cF.mode = .scan ∧ cF.replaying = false ∧ cF.clock = 1 ∧ canRight sF.right ∧
    sF.chain = .idle ∧
    sF.center = represent ⟨a :: ls,gap⟩ (rs.map some) q ∧
    searchEffect P true sF vq ∧ vq.search.mode = .found ∧
    read (left sF.left) = read (right sF.right) ∧
    ChainMatched (chainStart (vq.dp.config.tapes 11) (P.centre sF) (P.place sF) sF.center sF.radius) ch ∧
    ch ≠ .idle ∧
    refresh (galilFrame P qq first)
      (afterBirth true (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq)) cF.output oF ∧
    WatchSegE P qq first delay es {cF with clock := delay, output := oF, replaying := false}
      (afterBirth true (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq)) c2 s2 ∧
    WatchSeg P qq first delay c2 s2 cM sM ∧
    cM.mode = .scan ∧ cM.replaying = false ∧ cM.clock = 1 ∧
    sM.chain = .watch w ∧ zero w.lag = true ∧ canRight sM.right ∧
    (galilFrame P qq first).compare sM (scanLens.set sM vs) ∧
    ¬ (galilFrame P qq first).matched (scanLens.set sM vs) ∧
    searchEffect P false sM vq' ∧
    P.shiftGuard (afterMismatch sM vs vq') ∧
    P.beginShift (afterMismatch sM vs vq') s2' ∧
    beginShiftVM h w (afterMismatch sM vs vq') s2' ∧ CopyIdle s2' ∧
    ChainShiftRun ⟨sM.center, left sM.left, ofNat h, inc sM.radius, inc (inc sM.length)⟩
      (GalilScaffoldChainWatch.immediate w) reset h t' v cycle ∧
    refresh (galilFrameS P qq first) (shiftLens.set s2' ⟨t', .watch v, cycle⟩) cM.output o ∧
    org.interior.length+1 = h ∧
    Entry raw org (toOnly (shiftLens.set s2' ⟨t', .watch v, cycle⟩) v) ∧
    org.center = position sF.center ∧
    GalilDpCorrect.Result ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (span+1)) lower 0
      (GalilScaffoldProgram.denote vq.dp.config) ∧
    (GalilScaffoldProgram.denote vq.dp.config).pc = 346 ∧
    (GalilScaffoldProgram.denote vq.dp.config).pos 11 = h ∧
    (∀ δ, 0 < δ → δ ≤ lower → ¬ HasPeriod (Span raw org.center org.radius) (2*δ)) ∧
    Rounds P qq first delay h m {cM with mode := .scan, clock := delay, output := o}
      (shiftLens.set s2' ⟨t', .watch v, cycle⟩) c' s' ∧
    ScanSeg P qq first delay n c' s' c3 s3 ∧
    c3.mode = .scan ∧ c3.replaying = false ∧ c3.clock = 1 ∧
    s3.chain = .watch w3 ∧ canRight s3.right ∧
    (galilFrame P qq first).compare s3 (scanLens.set s3 vs3) ∧
    (galilFrame P qq first).matched (scanLens.set s3 vs3) ∧
    searchEffect P true s3 vq3 ∧
    refresh (galilFrame P qq first) (afterCompare s3 vs3 vq3) c3.output o3 ∧
    ScanInvariant raw cen3 r3 (afterCompare s3 vs3 vq3).left (afterCompare s3 vs3 vq3).right ∧
    (afterCompare s3 vs3 vq3).chain = .broken w3' ∧
    negative w3'.margin = false ∧ positive w3'.machine.control.last = true ∧ zero w3'.lag = true ∧
    (∀ s t, restartVM entry s t → P.restart s t) ∧
    (∃ Rad' : ℕ, Restarted raw {(afterCompare s3 vs3 vq3) with chain := .idle, lower := w3'.machine.control.last, search := GalilScaffoldSearchFinish.begin w3'.machine.control.last (afterCompare s3 vs3 vq3).radius, dp := GalilScaffoldControl.reset entry (afterCompare s3 vs3 vq3).dp} Rad' w3'.machine.control.last)

/-- One main-loop cycle through a found comparison: a sound run to a state
carrying the centre invariant and again `Restarted`. -/
theorem foundCycle_step (P : Shared) (qq : ℕ) (first : Fin 9) (delay : ℕ) (raw : List (Fin 2))
    (c0 : Control) (r : GalilVM) (hC : FoundCycle P qq first delay raw c0 r)
    (Rad : ℕ) (last : Counter) (hR : Restarted raw r Rad last) (hM0 : MInv raw c0 r) :
    ∃ (cT : Control) (sT : GalilVM),
      (∃ k, StepsAll (galilFrameS P qq first) delay (SoundScanNR raw) k ⟨c0, r⟩ ⟨cT, sT⟩) ∧
      MInv raw cT sT ∧ ∃ (Rad' : ℕ) (last' : Counter), Restarted raw sT Rad' last' := by
  obtain ⟨a, ls, rs, q, gap, es0, cF, sF, vq, ch, oF, es, c2, s2, cM, sM, h, w, vs, vq', s2',
    t', v, cycle, o, org, lower, span, m, c', s', n, c3, s3, w3, vs3, vq3, o3, cen3, r3, w3', entry,
    hP, hP', hex, hraw, hout0, hseg0, hmF, hrF, hcF, havF, hidle, hCen, hq, hfound, hmt, hch, hchne,
    hoF, hprepSeg, hseg, hm1, hr1, hc1, hs1, hz, hav, hcmp, hmis, hq', hg, hb, hs2', hi2, hchain,
    ho, hint, he, hoc, hdp, hpc, hposout, hlow, hrounds, hseg3, hm3, hr3, hc3, hs3, hav3, hcmp3,
    hmt3, hq3, ho3, hinv3, hbroken, hmargin, hlast, hlag, hrestart, Rad', hRnext⟩ := hC
  refine ⟨_, _, cycle_found_stepsAll raw P hP hP' qq first delay hR hout0 hseg0 hmF hrF hcF havF
    hidle vq hq hfound hmt ch hch hchne oF hoF hprepSeg hseg h hm1 hr1 hc1 w hs1 hz hav vs vq'
    hcmp hmis hq' hg s2' hb hs2' hi2 hchain o ho org hint he hrounds hseg3 hm3 hr3 hc3 w3 hs3 hav3
    vs3 vq3 hcmp3 hmt3 hq3 o3 ho3 hinv3 w3' hbroken hmargin hlast hlag entry hrestart,
    cycle_found_minv raw P hex qq first delay a ls rs q gap hraw hR hM0 hseg0 hmF hrF hcF havF
      hidle hCen vq hq hfound hmt ch hch hchne oF hoF hprepSeg hseg h hm1 hr1 hc1 w hs1 hz hav vs
      vq' hcmp hmis hq' hg s2' hb hs2' hi2 hchain o ho org hint he hoc hdp hpc hposout hlow hrounds
      hseg3 hm3 hr3 hc3 w3 hs3 hav3 vs3 vq3 hcmp3 hmt3 hq3 o3 ho3 w3' hbroken entry,
    Rad', _, hRnext⟩

/-- The premises of one main-loop cycle through a mismatching comparison with
the chain idle, at the state `⟨c0, r⟩` it starts from: the union of the
hypothesis lists of `cycle_fallback_stepsAll` and `cycle_fallback_minv`. -/
def FallbackCycle (P : Shared) (qq : ℕ) (first : Fin 9) (delay : ℕ) (raw : List (Fin 2))
    (c0 : Control) (r : GalilVM) : Prop :=
  ∃ (onLetter leftFirst : GalilVM → Prop) (rsl : GalilVM → GalilVM → Prop)
    (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place) (entry : ℕ)
    (es0 : List Bool) (cF : Control) (sF : GalilVM) (vs : ScanVM) (vq : SearchVM) (ℓ : ℕ),
    P = galilShared onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' rsl centre place entry ∧
    0 < qq ∧ first ≠ 7 ∧ first ≠ 8 ∧
    onLetter = onLetterVM raw ∧ leftFirst = leftFirstVM ∧
    ShiftIdle r ∧ SpanRep r ∧ OutputRel raw c0 r ∧
    WatchSegE P qq first delay es0 c0 r cF sF ∧
    cF.mode = .scan ∧ cF.replaying = false ∧ cF.clock = 1 ∧ canRight sF.right ∧
    vs.left = left sF.left ∧ vs.right = right sF.right ∧
    read (left sF.left) ≠ read (right sF.right) ∧
    searchEffect P false sF vq ∧
    chainAt false (decide (vq.search.mode = .found)) (vq.dp.config.tapes 11) (centre sF) (place sF)
      sF.center sF.radius sF.chain vs.chain ∧
    ¬ shiftGuardVM (afterMismatch sF vs vq) ∧
    value sF.length = ℓ ∧
    (∀ (a : Fin 2) (xs rs' q' : List (Fin 2)),
      right sF.right = represent ⟨a :: xs,(right sF.right).gap⟩ (rs'.map some) q' →
      ((GalilScaffoldPlace.stream ⟨a :: xs,(right sF.right).gap⟩).take (ℓ+1)).length % 2 = 0)

/-- One main-loop cycle through a mismatch: a sound run to a state carrying
the centre invariant and again `Restarted`. The two published lemmas
(`cycle_fallback_stepsAll`, `cycle_fallback_minv`) each quantify their own
landing state, so the joint statement is re-derived here from the single
`fallback_restarted_All`. -/
theorem fallbackCycle_step (P : Shared) (qq : ℕ) (first : Fin 9) (delay : ℕ) (raw : List (Fin 2))
    (c0 : Control) (r : GalilVM) (hC : FallbackCycle P qq first delay raw c0 r)
    (Rad : ℕ) (last : Counter) (hR : Restarted raw r Rad last) (hM0 : MInv raw c0 r) :
    ∃ (cT : Control) (sT : GalilVM),
      (∃ k, StepsAll (galilFrameS P qq first) delay (SoundScanNR raw) k ⟨c0, r⟩ ⟨cT, sT⟩) ∧
      MInv raw cT sT ∧ ∃ (Rad' : ℕ) (last' : Counter), Restarted raw sT Rad' last' := by
  obtain ⟨onLetter, leftFirst, rsl, centre, place, entry, es0, cF, sF, vs, vq, ℓ,
    hPeq, hq0, h7, h8, honL, hlF, hi0, hS0, hout0, hseg0, hm, hr, hc, hav, hl, hrr, hmis, hq,
    hch, hg, hv, heven⟩ := hC
  subst hPeq
  have hscan0 := hR.2.2.2.1
  have hRR0 := hR.2.2.2.2.1
  -- the centre invariant travels along the idle segment
  have hMF : MInv raw cF sF :=
    minv_watchSegE raw _ (fun _ => rfl) qq first delay hseg0 Rad hscan0 hM0
  have hLF : Leftmost raw (position sF.right) (position sF.center) := minv_leftmost hMF hr
  obtain ⟨hrep, hfoc, hcan, _, hinvF⟩ := segment_mismatch_ready _ qq first delay hR hseg0 hav
  have hcen : sF.center = r.center := watchSegE_center _ qq first delay hseg0
  have hinvF' : ScanInvariant raw (position sF.center) (Rad + es0.count true) sF.left sF.right := by
    rw [hcen]; exact hinvF
  obtain ⟨_, _, hradv, hradc, _⟩ := watchSegE_heads _ qq first delay hseg0
  have hRRF : RadiusRep sF.radius (Rad + es0.count true) := by
    refine ⟨hradc hRR0.1, ?_⟩
    rw [hradv, hRR0.2]; push_cast; ring
  have hSF : SpanRep sF := spanRep_watchSegE _ qq first delay hseg0 hS0
  have hrpos : position (right sF.right) = position sF.right + 1 :=
    right_position sF.right hav (represented_position _ raw hinvF'.rightRep hinvF'.rightPresent).1
  have hdead : ¬ Live raw (position (right sF.right)) (position sF.center) := by
    rw [hrpos]; exact not_live_of_mismatch hinvF' hav hmis
  have hiF : ShiftIdle sF := by
    rw [shiftIdle_iff, watchSegE_remaining _ qq first delay hseg0]
    exact (shiftIdle_iff r).1 hi0
  -- the sound run along the idle segment
  obtain ⟨k1, h1⟩ :=
    watchSegE_stepsAll raw _ honL hlF qq first delay hseg0 (position r.center) Rad hscan0 hout0
  have houtF : OutputRel raw cF sF := stepsAll_last h1
  have lift1 : ∀ st, SoundOut raw st → SoundScanNR raw st := fun st h0 _ _ => h0
  -- the fallback cycle itself
  obtain ⟨a, xs, rs', q', hdec, hraw, n, o, t, hstA, hRst, hrep', hpos, hpal, hmax, ho0⟩ :=
    fallback_restarted_All onLetter leftFirst rsl centre place entry qq hq0 first h7 h8 delay cF hm
      hr hc sF hiF hav vs vq hl hrr hmis hq hch hg hrep hfoc hcan ℓ hv heven
  have hL' := leftmost_after_fallback raw hinvF' hRRF hSF hLF hav hdead a xs rs' q' hdec ℓ hv hpal hmax
  rw [hrpos] at hpos hL'
  refine ⟨_, t, ⟨_, stepsAll_trans (stepsAll_mono lift1 h1)
      (hstA (SoundScanNR raw) (fun st hns hsc => absurd hsc hns) (fun _ _ => houtF) ?_)⟩,
    minv_after_fallback hRst hrep' hpos (by rw [hpos]; exact hL') rfl, 0, reset, hRst⟩
  intro _ hrepl
  have hr0 : chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right sF.right).gap⟩).take (ℓ+1)) = 0 := by
    simp at hrepl; omega
  obtain ⟨_, _, _, hscanT, _⟩ := hRst
  intro hout' k hk hk2 hrk
  refine output_sound raw t cF.output o hscanT k hk hk2 hrk ?_ hout'
  have hoo := ho0 hr0
  rw [honL, hlF] at hoo
  exact hoo

/-- The main loop: a chain of found and fallback cycles. The state a cycle
lands in is produced by the step lemma, so the continuation `rest` is a
function of it, carrying the two invariants it is handed. -/
inductive Cycles (P : Shared) (qq : ℕ) (first : Fin 9) (delay : ℕ) (raw : List (Fin 2)) :
    Control → GalilVM → Control → GalilVM → Prop
  | nil {c : Control} {s : GalilVM} (hsound : SoundScanNR raw ⟨c, s⟩) :
      Cycles P qq first delay raw c s c s
  | found {c0 : Control} {r : GalilVM} {cz : Control} {sz : GalilVM}
      (h : FoundCycle P qq first delay raw c0 r)
      (rest : ∀ (cT : Control) (sT : GalilVM), MInv raw cT sT →
        (∃ (Rad' : ℕ) (last' : Counter), Restarted raw sT Rad' last') →
        Cycles P qq first delay raw cT sT cz sz) :
      Cycles P qq first delay raw c0 r cz sz
  | fallback {c0 : Control} {r : GalilVM} {cz : Control} {sz : GalilVM}
      (h : FallbackCycle P qq first delay raw c0 r)
      (rest : ∀ (cT : Control) (sT : GalilVM), MInv raw cT sT →
        (∃ (Rad' : ℕ) (last' : Counter), Restarted raw sT Rad' last') →
        Cycles P qq first delay raw cT sT cz sz) :
      Cycles P qq first delay raw c0 r cz sz

theorem cycles_stepsAll_minv_aux {P : Shared} {qq : ℕ} {first : Fin 9} {delay : ℕ}
    {raw : List (Fin 2)} {c0 : Control} {s0 : GalilVM} {c1 : Control} {s1 : GalilVM}
    (hC : Cycles P qq first delay raw c0 s0 c1 s1) :
    MInv raw c0 s0 → (∃ (Rad : ℕ) (last : Counter), Restarted raw s0 Rad last) →
    ∃ k, StepsAll (galilFrameS P qq first) delay (SoundScanNR raw) k ⟨c0, s0⟩ ⟨c1, s1⟩ ∧
      MInv raw c1 s1 ∧ ∃ (Rad' : ℕ) (last' : Counter), Restarted raw s1 Rad' last' := by
  induction hC with
  | nil hsound => exact fun hM hR => ⟨0, .zero _ hsound, hM, hR⟩
  | found h _ ih =>
    intro hM hR
    obtain ⟨Rad, last, hR'⟩ := hR
    obtain ⟨cT, sT, ⟨k1, h1⟩, hMT, hRT⟩ := foundCycle_step _ _ _ _ _ _ _ h Rad last hR' hM
    obtain ⟨k2, h2, hM2, hR2⟩ := ih cT sT hMT hRT hMT hRT
    exact ⟨k1+k2, stepsAll_trans h1 h2, hM2, hR2⟩
  | fallback h _ ih =>
    intro hM hR
    obtain ⟨Rad, last, hR'⟩ := hR
    obtain ⟨cT, sT, ⟨k1, h1⟩, hMT, hRT⟩ := fallbackCycle_step _ _ _ _ _ _ _ h Rad last hR' hM
    obtain ⟨k2, h2, hM2, hR2⟩ := ih cT sT hMT hRT hMT hRT
    exact ⟨k1+k2, stepsAll_trans h1 h2, hM2, hR2⟩

/-- The main loop's composition: a chain of cycles from a restarted state
carrying the centre invariant is a sound run to a restarted state that
carries it again. -/
theorem cycles_stepsAll_minv {P : Shared} {qq : ℕ} {first : Fin 9} {delay : ℕ}
    {raw : List (Fin 2)} {c0 : Control} {s0 : GalilVM} {c1 : Control} {s1 : GalilVM}
    {Rad : ℕ} {last : Counter} (hC : Cycles P qq first delay raw c0 s0 c1 s1)
    (_hout0 : OutputRel raw c0 s0) (hM0 : MInv raw c0 s0) (hR0 : Restarted raw s0 Rad last) :
    ∃ k, StepsAll (galilFrameS P qq first) delay (SoundScanNR raw) k ⟨c0, s0⟩ ⟨c1, s1⟩ ∧
      MInv raw c1 s1 ∧ ∃ (Rad' : ℕ) (last' : Counter), Restarted raw s1 Rad' last' :=
  cycles_stepsAll_minv_aux hC hM0 ⟨Rad, last, hR0⟩

/-- At the first right place the leftmost live centre is `1`. -/
theorem leftmost_one (a : Fin 2) (rest : List (Fin 2)) : Leftmost (a :: rest) 1 1 := by
  have hlen : 1 < (encoded (a :: rest)).length := by
    rw [encoded, List.length_append, pairs_length]
    simp
  refine ⟨⟨le_refl 1, by omega, ?_⟩, fun c hc => ?_⟩
  · show PalAt (encoded (a :: rest)) 1 0
    exact palAt_zero hlen
  · have := hc.2.1; omega

/-- The centre invariant at the first restarted state, right after `init`. -/
theorem init_minv (onLetter leftFirst guard : GalilVM → Prop) (bs bf rs : GalilVM → GalilVM → Prop)
    (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place) (entry : ℕ)
    (q : ℕ) (first : Fin 9) (delay : ℕ) (c : Control) (hm : c.mode = .init)
    (hrepl : c.replaying = false) (s0 : GalilVM)
    (a : Fin 2) (rest : List (Fin 2)) (h0 : s0.right = initialHead (a :: rest))
    (hrad : s0.radius = reset) (hlen : s0.length = reset) :
    ∃ t : GalilVM,
      StepsAll (galilFrameS (galilShared onLetter leftFirst guard bs bf rs centre place entry) q first)
        delay (SoundScanNR (a :: rest)) 1 ⟨c, s0⟩ ⟨{c with mode := .scan, output := true}, t⟩ ∧
      Restarted (a :: rest) t 0 reset ∧
      MInv (a :: rest) {c with mode := .scan, output := true} t := by
  obtain ⟨t, hst, hR, hpos, _, hRt, _, _⟩ :=
    init_stepsAll onLetter leftFirst guard bs bf rs centre place entry q first delay c hm s0 a rest
      h0 hrad hlen
  refine ⟨t, hst, hR, minv_of_leftmost ?_ hrepl⟩
  rw [hRt, hpos]
  exact leftmost_one a rest

#print axioms foundCycle_step
#print axioms fallbackCycle_step
#print axioms cycles_stepsAll_minv
#print axioms leftmost_one
#print axioms init_minv

end PalPeg.GalilScaffoldChainInputSupply
