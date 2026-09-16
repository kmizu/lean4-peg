import PalPeg.GalilChainTickable
import PalPeg.GalilPrepTrace
import PalPeg.GalilCycleFoundBackground
import PalPeg.GalilSegmentConstruct

/-!
# The replay after a fallback, without `SearchQuiet`

`PalPeg.GalilReplaySegment.replay_after_fallback` assumes `SearchQuiet` (the
search never reports `found` while replaying).  `PalPeg.GalilReplayFound`
shows that is false: the first stage after the restart finishes inside the
first countdown, and `backgroundS`/`compareFound` start the chain regardless
of `replaying`.

`replay_after_fallback_general` drops the hypothesis.  At every tick of the
idle replay the search effect is split on `found`:

* (i) never `found` — the replay completes with the chain idle, landing in
  `InvScan` exactly as before;
* (ii) `found` at some tick (a background tick of a countdown, or a forced
  comparison) — the chain starts (`FoundTick`) while replaying, and the rest
  of the replay runs as a `ReplayChainSeg` until the counter hits zero.  The
  landing (`FoundLanding`) is a non-replaying scan state with a live chain,
  exporting `MInv`, `ScanInvariant`, `Frontier`, the `SoundScanNR` run and
  the `ChainTicks` trace of the replayed part from the started chain.

The chain side is `GalilChainTickable.no_break_during_replay`; its `WatchOk`
and `Good` hypotheses are kept named, and the one new chain obligation is
`StartOk` — the chain `chain.start()` installs is `ChainOk`.

`prep_watch_across_replay` / `_bg` feed that landing into
`life_from_prep_*`: for *any* `hprepSeg : WatchSegE … es3` leaving the landing,
the replayed trace followed by `hprepSeg`'s trace is a preparation trace, so
the end of `hprepSeg` is `watchStart` (via `prep_watch_start_trace`, the trace
form behind `prep_watch_start_of_replayChainSeg`).
-/

set_option autoImplicit false

namespace PalPeg.GalilReplayGeneral

open PalPeg PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilTickFun PalPeg.GalilTickFun2
  PalPeg.GalilBranchInvariants2 PalPeg.GalilSegmentConstruct PalPeg.GalilReplayChainSeg
  PalPeg.GalilChainTickable
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-! ## The found comparison while replaying -/

/-- A matched comparison on an idle chain whose search quantum lands in
`found`: `chain.start()` followed by the match credit. -/
theorem scan_match_found_S' (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) (c : Control)
    (s : GalilVM) (vs : ScanVM) (vq : SearchVM) (o : Bool) (hm : c.mode = .scan)
    (hav : c.replaying = true ∨ (galilFrame P q first).available s) (hc : c.clock = 1)
    (hidle : s.chain = .idle)
    (hl : vs.left = GalilScaffoldInputHead.left s.left)
    (hrr : vs.right = GalilScaffoldChainVerifier.right s.right)
    (hmt : (galilFrame P q first).matched (scanLens.set s vs))
    (hq : searchEffect P true s vq) (hf : vq.search.mode = .found)
    (hch : ChainMatched (chainStart (vq.dp.config.tapes 11) (P.centre s) (P.place s) s.center
      s.radius) vs.chain)
    (ho : refresh (galilFrame P q first) (replayDec c.replaying (afterCompare s vs vq)) c.output o) :
    Tick (galilFrameS P q first) delay ⟨c, s⟩
      ⟨{c with clock := delay, output := o, replaying := c.replaying && !P.replayExhausted (replayDec c.replaying (afterCompare s vs vq))}, replayDec c.replaying (afterCompare s vs vq)⟩ := by
  have hcmp' : (galilFrameS P q first).compare s (afterCompare s vs vq) :=
    ⟨vs, vq, true, hl, hrr, ⟨fun _ => hmt, fun _ => rfl⟩, hq,
      Or.inr (Or.inr ⟨hidle, by simp [hf], by simpa using hch⟩), rfl⟩
  have hmt' : (galilFrameS P q first).matched (afterCompare s vs vq) := by
    show (galilFrame P q first).matched (afterCompare s vs vq)
    exact hmt
  exact Tick.scan_match (F := galilFrameS P q first) (delay := delay) c s _ _ o hm hav hc
    hcmp' hmt' (matchedPlace_replayDec P q first _ _) ho

/-- The tick that starts the chain during a replay. -/
inductive FoundTick (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) :
    Control → GalilVM → Control → GalilVM → Prop
  | bg (c : Control) (s s' : GalilVM) (hm : c.mode = .scan) (hr : c.replaying = true)
      (hc : 1 < c.clock) (hidle : s.chain = .idle)
      (hb : (galilFrameS P q first).background s s')
      (hf : (searchLens.get s').search.mode = .found) :
      FoundTick P q first delay c s {c with clock := c.clock - 1} s'
  | cmp (c : Control) (s : GalilVM) (vs : ScanVM) (vq : SearchVM) (o : Bool)
      (hm : c.mode = .scan) (hr : c.replaying = true) (hc : c.clock = 1) (ha : canRight s.right)
      (hidle : s.chain = .idle) (hl : vs.left = left s.left) (hrr : vs.right = right s.right)
      (hmt : (galilFrame P q first).matched (scanLens.set s vs))
      (hq : searchEffect P true s vq) (hf : vq.search.mode = .found)
      (hch : ChainMatched (chainStart (vq.dp.config.tapes 11) (P.centre s) (P.place s) s.center
        s.radius) vs.chain)
      (ho : refresh (galilFrame P q first) (replayDec true (afterCompare s vs vq)) c.output o) :
      FoundTick P q first delay c s
        {c with clock := delay, output := o, replaying := !P.replayExhausted (replayDec true (afterCompare s vs vq))}
        (replayDec true (afterCompare s vs vq))

/-- What the found tick installs: `chainStart` plainly (background) or its
match credit (comparison). -/
theorem foundTick_start (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    {c1 c2 : Control} {s1 s2 : GalilVM} (h : FoundTick P q first delay c1 s1 c2 s2) :
    (∃ vq : SearchVM, vq.search.mode = .found ∧
      s2.chain = chainStart (vq.dp.config.tapes 11) (P.centre s1) (P.place s1) s1.center s1.radius) ∨
    (∃ vq : SearchVM, vq.search.mode = .found ∧
      ChainMatched (chainStart (vq.dp.config.tapes 11) (P.centre s1) (P.place s1) s1.center s1.radius)
        s2.chain) := by
  cases h with
  | bg _ hm hr hc hidle hb hf =>
    exact Or.inl ⟨_, hf, background_found_chain P q first hb hidle hf⟩
  | cmp vs vq o hm hr hc ha hidle hl hrr hmt hq hf hch ho =>
    refine Or.inr ⟨vq, hf, ?_⟩
    rw [replayDec_chain, afterCompare_chain]
    exact hch

/-! ## The chain-start obligation -/

/-- **Named hypothesis.**  The chain `chain.start()` installs on a found search
is `ChainOk`. -/
def StartOk (P : Shared) (Ok : WState → Prop) : Prop :=
  ∀ (s : GalilVM) (a : Bool) (vq : SearchVM), s.chain = .idle → SearchReady (searchLens.get s) →
    searchEffect P a s vq → vq.search.mode = .found →
    ChainOk Ok (chainStart (vq.dp.config.tapes 11) (P.centre s) (P.place s) s.center s.radius)

/-- The match credit of a started chain keeps `ChainOk` (it only bumps the
lag and margin of `.copy`). -/
theorem chainOk_matched_start {Ok : WState → Prop} {answer : GalilScaffoldTape.Tape} {cc : Fin 3}
    {walker : GalilScaffoldPlace.Place} {ver : PlaceHead} {radius : Counter} {z : ChainVM}
    (hx : ChainOk Ok (chainStart answer cc walker ver radius))
    (h : ChainMatched (chainStart answer cc walker ver radius) z) : ChainOk Ok z := by
  unfold chainStart at hx h
  cases h
  exact hx

/-! ## Replay with a live chain, under the frontier bound -/

section Chain

variable (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)

/-- The countdown with a live `ChainOk` chain. -/
theorem chain_countdown {Ok : WState → Prop} (hOk : WatchOk Ok)
    (hgood : ∀ w, Ok w → GalilScaffoldChainWatch.Good w) :
    ∀ (j : ℕ) (c : Control) (s : GalilVM), c.mode = .scan → c.replaying = true →
      c.clock = j + 1 → s.chain ≠ ChainVM.idle → ChainOk Ok s.chain →
      ∃ (es : List Bool) (s' : GalilVM),
        ReplayChainSeg P q first delay es c s {c with clock := 1} s' ∧ es.count true = 0 ∧
        s'.chain ≠ ChainVM.idle ∧ ChainOk Ok s'.chain ∧
        s'.left = s.left ∧ s'.right = s.right ∧ s'.center = s.center ∧ s'.replay = s.replay ∧
        s'.remaining = s.remaining := by
  intro j
  induction j with
  | zero =>
    intro c s hm hrp hclk hne hok
    have hc1 : c.clock = 1 := by omega
    have hc : ({c with clock := 1} : Control) = c := by rw [← hc1]
    refine ⟨[], s, ?_, rfl, hne, hok, rfl, rfl, rfl, rfl, rfl⟩
    rw [hc]; exact .stop _ _
  | succ j ih =>
    intro c s hm hrp hclk hne hok
    obtain ⟨z, htz, hokz, -, hnez⟩ := no_break_during_replay hOk hgood false hok hne
    have hstep : ChainStep s.chain z := by
      obtain ⟨y, hst, hy⟩ := htz
      have hzy : z = y := hy
      rw [hzy]; exact hst
    obtain ⟨s1, hb, hch1, hl1, hr1, hC1, hrep1⟩ :=
      GalilReplayChainSeg.active_background_exists P q first s hne hstep
    have hrem1 : s1.remaining = s.remaining :=
      (backgroundS_fields P q first hb).2.2.2.2.2.2.2.2.1
    obtain ⟨es, s2, hseg, hcnt, hne2, hok2, hl2, hr2, hC2, hrep2, hrem2⟩ :=
      ih {c with clock := c.clock - 1} s1 hm hrp (by simp; omega) (by rw [hch1]; exact hnez)
        (by rw [hch1]; exact hokz)
    refine ⟨false :: es, s2, ?_, by simpa using hcnt, hne2, hok2,
      by rw [hl2, hl1], by rw [hr2, hr1], by rw [hC2, hC1], by rw [hrep2, hrep1],
      by rw [hrem2, hrem1]⟩
    exact .countC c s s1 hm hrp (by omega) hne hb hseg

/-- The forced comparison with a live `ChainOk` chain. -/
theorem chain_compare (hex : ∀ s, P.replayExhausted s = zero s.replay) {Ok : WState → Prop}
    (hOk : WatchOk Ok) (hgood : ∀ w, Ok w → GalilScaffoldChainWatch.Good w)
    (c : Control) (s : GalilVM) (k m : ℕ)
    (hm : c.mode = .scan) (hr : c.replaying = true) (hc : c.clock = 1)
    (hne : s.chain ≠ .idle) (hok : ChainOk Ok s.chain)
    (hM : MInv raw c s) (hi : ScanInvariant raw (position s.center) k s.left s.right)
    (hrp : s.replay = ofNat (m+1)) (hfr : Frontier s) :
    ∃ (c1 : Control) (u : GalilVM),
      ReplayChainSeg P q first delay [true] c s c1 u ∧
      c1.mode = .scan ∧ c1.clock = delay ∧ c1.replaying = decide (0 < m) ∧
      u.chain ≠ .idle ∧ ChainOk Ok u.chain ∧ MInv raw c1 u ∧
      ScanInvariant raw (position u.center) (k+1) u.left u.right ∧
      u.replay = ofNat m ∧ position u.right = position s.right + 1 ∧
      u.center = s.center ∧ Frontier u ∧ u.remaining = s.remaining := by
  classical
  have hbound : position s.right + (m+1) ≤ 2 * arrived s.right := hfr (m+1) hrp
  have hav : canRight s.right := GalilReplaySegment.canRight_of_frontier (Nat.succ_pos m) hbound
  have hmatch : read (left s.left) = read (right s.right) := replay_match_of_minv hM hr hav hi
  obtain ⟨z, htz, hokz, -, hnez⟩ := no_break_during_replay hOk hgood true hok hne
  set vs : ScanVM := ⟨left s.left, right s.right, z⟩ with hvsdef
  have hcmp : (galilFrame P q first).compare s (scanLens.set s vs) := by
    refine ⟨?_, ?_⟩
    · rw [scanLens.get_set]
      refine ⟨rfl, rfl, ?_⟩
      show ChainTick (decide (read (left s.left) = read (right s.right))) s.chain vs.chain
      rw [decide_eq_true hmatch]; exact htz
    · rw [scanLens.get_set]
  have hmt : (galilFrame P q first).matched (scanLens.set s vs) := hmatch
  set vq : SearchVM := searchLens.get s with hvqdef
  have hq : searchEffect P true s vq := Or.inr ⟨hne, rfl⟩
  set u : GalilVM := replayDec true (afterCompare s vs vq) with hudef
  set o : Bool := if P.onLetter u then decide (P.leftFirst u) else c.output with hodef
  have ho : refresh (galilFrame P q first) u c.output o := by
    refine ⟨fun hl => ?_, fun hl => ?_⟩
    · have hl' : P.onLetter u := hl
      show (if P.onLetter u then decide (P.leftFirst u) else c.output) = true ↔ P.leftFirst u
      rw [if_pos hl']; exact decide_eq_true_iff
    · have hl' : ¬ P.onLetter u := hl
      show (if P.onLetter u then decide (P.leftFirst u) else c.output) = c.output
      rw [if_neg hl']
  have hurep : u.replay = ofNat m := by
    rw [hudef, replayDec_true_replay, afterCompare_replay, hrp, dec_ofNat_succ]
  have hflag : (!P.replayExhausted u) = decide (0 < m) := by
    rw [hex, hurep]
    cases m with
    | zero => rw [(zero_ofNat_iff 0).2 rfl]; simp
    | succ k => rw [zero_ofNat_succ k]; simp
  refine ⟨{c with clock := delay, output := o, replaying := !P.replayExhausted u}, u,
    .matchC c s vs vq o hm hr hc hav hne hcmp hmt hq ho (.stop _ _), hm, rfl, hflag,
    ?_, ?_, ?_, ?_, hurep, ?_, ?_, ?_, rfl⟩
  · rw [hudef, replayDec_chain, afterCompare_chain]; exact hnez
  · rw [hudef, replayDec_chain, afterCompare_chain]; exact hokz
  · exact minv_matchR P hex o delay hr rfl hav hi hM
  · have h0 := matched_invariant' raw vq (vs := vs) rfl rfl hmatch hav hi
    rw [hudef, replayDec_left, replayDec_right, replayDec_center, afterCompare_center]
    exact h0
  · have hpos : position (right s.right) = position s.right + 1 :=
      right_position s.right hav (represented_position _ raw hi.rightRep hi.rightPresent).1
    rw [hudef, replayDec_right, afterCompare_right]
    exact hpos
  · rw [hudef, replayDec_center, afterCompare_center]
  · intro m' hm'
    have hmm : m' = m := (ofNat_inj (hurep.symm.trans hm')).symm
    subst hmm
    have hur : u.right = right s.right := by rw [hudef, replayDec_right, afterCompare_right]
    rw [hur]
    exact right_frontier_step s.right m' hbound

/-- **The rest of the replay with a live chain.**  From a scan state `m`
places into a replay (`replaying = decide (0 < m)`), carrying a live `ChainOk`
chain, the replay runs to its end: `m` countdown-and-compare rounds, landing
at `replaying = false` with the chain still alive. -/
theorem chain_replay_finish (hex : ∀ s, P.replayExhausted s = zero s.replay) (hd : 1 ≤ delay)
    {Ok : WState → Prop} (hOk : WatchOk Ok)
    (hgood : ∀ w, Ok w → GalilScaffoldChainWatch.Good w) :
    ∀ (m : ℕ) (c : Control) (s : GalilVM) (k : ℕ),
      c.mode = .scan → 1 ≤ c.clock → c.replaying = decide (0 < m) → (m = 0 → c.clock = delay) →
      s.replay = ofNat m → s.chain ≠ .idle → ChainOk Ok s.chain →
      MInv raw c s → ScanInvariant raw (position s.center) k s.left s.right → Frontier s →
      ∃ (es : List Bool) (c' : Control) (t : GalilVM),
        ReplayChainSeg P q first delay es c s c' t ∧ es.count true = m ∧
        c'.mode = .scan ∧ c'.clock = delay ∧ c'.replaying = false ∧
        t.replay = reset ∧ t.chain ≠ .idle ∧ ChainOk Ok t.chain ∧
        MInv raw c' t ∧ ScanInvariant raw (position t.center) (k + m) t.left t.right ∧
        position t.right = position s.right + m ∧ t.center = s.center ∧
        Frontier t ∧ t.remaining = s.remaining := by
  intro m
  induction m with
  | zero =>
    intro c s k hm hclk hrp hc0 hrep hne hok hM hi hfr
    exact ⟨[], c, s, .stop _ _, rfl, hm, hc0 rfl, by simpa using hrp, hrep, hne, hok, hM,
      by simpa using hi, by simp, rfl, hfr, rfl⟩
  | succ n ih =>
    intro c s k hm hclk hrp hc0 hrep hne hok hM hi hfr
    have hrt : c.replaying = true := by rw [hrp]; simp
    obtain ⟨j, hj⟩ : ∃ j, c.clock = j + 1 := ⟨c.clock - 1, by omega⟩
    obtain ⟨es1, s1, hseg1, hcnt1, hne1, hok1, hl1, hr1, hC1, hrep1, hrem1⟩ :=
      chain_countdown P q first delay hOk hgood j c s hm hrt hj hne hok
    have hM1 : MInv raw {c with clock := 1} s1 := minv_same rfl hr1 hC1 hrep1 hM
    have hi1 : ScanInvariant raw (position s1.center) k s1.left s1.right := by
      rw [hl1, hr1, hC1]; exact hi
    have hfr1 : Frontier s1 := frontier_congr hr1 hrep1 hfr
    obtain ⟨c2, u, hseg2, hm2, hc2, hr2, hne2, hok2, hM2, hi2, hrep2, hpos2, hC2, hfr2, hrem2⟩ :=
      chain_compare raw P q first delay hex hOk hgood {c with clock := 1} s1 k n hm hrt rfl
        hne1 hok1 hM1 hi1 (by rw [hrep1, hrep]) hfr1
    obtain ⟨es3, c3, t3, hseg3, hcnt3, hm3, hc3, hr3, hrep3, hne3, hok3, hM3, hi3, hpos3, hC3,
        hfr3, hrem3⟩ :=
      ih c2 u (k+1) hm2 (by rw [hc2]; exact hd) hr2 (fun _ => hc2) hrep2 hne2 hok2 hM2 hi2 hfr2
    refine ⟨es1 ++ ([true] ++ es3), c3, t3,
      replayChainSeg_trans P q first delay hseg1 (replayChainSeg_trans P q first delay hseg2 hseg3),
      ?_, hm3, hc3, hr3, hrep3, hne3, hok3, hM3, ?_, ?_, ?_, hfr3, ?_⟩
    · simp only [List.count_append, hcnt1, hcnt3, List.count_singleton_self]; omega
    · have e : k + (n+1) = k+1+n := by omega
      rw [e]; exact hi3
    · rw [hpos3, hpos2, hr1]; omega
    · rw [hC3, hC2, hC1]
    · rw [hrem3, hrem2, hrem1]

end Chain

/-! ## The landing of branch (ii) -/

/-- **Branch (ii).**  From `(c, s)`: an idle replaying prefix `es1`, the tick
that starts the chain while replaying, the rest of the replay with the chain
live (`es2`), all a `SoundScanNR` run; the landing is a non-replaying scan state
with a live `ChainOk` chain, the scan invariant at radius `k + d` and the right
head `d` places further right. -/
def FoundLanding (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (Ok : WState → Prop) (c : Control) (s : GalilVM) (k d : ℕ) : Prop :=
  ∃ (es1 : List Bool) (c1 : Control) (s1 : GalilVM) (c2 : Control) (s2 : GalilVM)
    (es2 : List Bool) (c' : Control) (t : GalilVM) (n : ℕ),
    WatchSegE P q first delay es1 c s c1 s1 ∧ s1.chain = .idle ∧ c1.replaying = true ∧
    FoundTick P q first delay c1 s1 c2 s2 ∧
    ReplayChainSeg P q first delay es2 c2 s2 c' t ∧
    StepsAll (galilFrameS P q first) delay (SoundScanNR raw) n ⟨c, s⟩ ⟨c', t⟩ ∧
    ChainTicks es2 s2.chain t.chain ∧
    c'.mode = .scan ∧ c'.clock = delay ∧ c'.replaying = false ∧
    t.replay = reset ∧ t.chain ≠ .idle ∧ ChainOk Ok t.chain ∧
    MInv raw c' t ∧ ScanInvariant raw (position t.center) (k + d) t.left t.right ∧
    position t.right = position s.right + d ∧ t.center = s.center ∧
    Frontier t ∧ ReplayRest c' t ∧ t.remaining = s.remaining

/-- Prepending an idle segment to a found landing. -/
theorem foundLanding_prepend {raw : List (Fin 2)} {P : Shared} {q : ℕ} {first : Fin 9}
    {delay : ℕ} {Ok : WState → Prop} {es0 : List Bool} {n0 : ℕ} {c c1 : Control} {s s1 : GalilVM}
    {k d k1 d1 : ℕ}
    (hseg : WatchSegE P q first delay es0 c s c1 s1)
    (hst : StepsAll (galilFrameS P q first) delay (SoundScanNR raw) n0 ⟨c, s⟩ ⟨c1, s1⟩)
    (hkd : k1 + d1 = k + d) (hpd : position s1.right + d1 = position s.right + d)
    (hC : s1.center = s.center) (hrem : s1.remaining = s.remaining)
    (hL : FoundLanding raw P q first delay Ok c1 s1 k1 d1) :
    FoundLanding raw P q first delay Ok c s k d := by
  obtain ⟨es1, c2, s2, c3, s3, es2, c', t, n, hseg1, hidle, hrp, hft, hrc, hst1, htr, hm, hc, hr,
    hrep, hne, hok, hM, hi, hpos, hC', hfr, hrr, hrem'⟩ := hL
  exact ⟨es0 ++ es1, c2, s2, c3, s3, es2, c', t, n0 + n,
    watchSegE_trans P q first delay hseg hseg1, hidle, hrp, hft, hrc, stepsAll_trans hst hst1, htr,
    hm, hc, hr, hrep, hne, hok, hM, by rw [← hkd]; exact hi, by rw [hpos]; omega,
    by rw [hC', hC], hfr, hrr, by rw [hrem', hrem]⟩

/-! ## The idle replay, split on `found` -/

section Idle

variable (raw : List (Fin 2)) (P : Shared) (hP : P.onLetter = onLetterVM raw)
  (hP' : P.leftFirst = leftFirstVM) (q : ℕ) (first : Fin 9) (delay : ℕ)

include hP hP'

/-- **The countdown of an idle replay round**: either the whole countdown is
quiet (the old `countR_run` conclusion), or a background tick reports `found`
and the replay finishes with the chain live. -/
theorem idle_countdown (hex : ∀ s, P.replayExhausted s = zero s.replay) (hd : 1 ≤ delay)
    (hsearch : ∀ s : GalilVM, SearchReady (searchLens.get s) → ∀ a : Bool,
      ∃ v, searchEffect P a s v)
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s) → searchEffect P a s v → SearchReady v)
    {Ok : WState → Prop} (hOk : WatchOk Ok)
    (hgood : ∀ w, Ok w → GalilScaffoldChainWatch.Good w) (hstart : StartOk P Ok) :
    ∀ (j : ℕ) (c : Control) (s : GalilVM) (k m : ℕ), c.mode = .scan → c.replaying = true →
      c.clock = j + 1 → s.chain = ChainVM.idle → SearchReady (searchLens.get s) →
      s.replay = ofNat (m+1) → MInv raw c s →
      ScanInvariant raw (position s.center) k s.left s.right → Frontier s →
      (∃ (c1 : Control) (t : GalilVM),
        WatchSegE P q first delay (List.replicate j false) c s c1 t ∧
        StepsAll (galilFrameS P q first) delay (SoundScanNR raw) j ⟨c, s⟩ ⟨c1, t⟩ ∧
        c1.mode = c.mode ∧ c1.replaying = c.replaying ∧ c1.clock = 1 ∧
        t.chain = ChainVM.idle ∧ SearchReady (searchLens.get t) ∧
        t.left = s.left ∧ t.right = s.right ∧ t.center = s.center ∧
        t.replay = s.replay ∧ t.remaining = s.remaining) ∨
      FoundLanding raw P q first delay Ok c s k (m+1) := by
  intro j
  induction j with
  | zero =>
    intro c s k m hm hr hc hidle hsr _ _ _ _
    exact Or.inl ⟨c, s, .stop _ _, .zero _ (GalilReplaySegment.soundScanNR_replaying raw hr),
      rfl, rfl, hc, hidle, hsr, rfl, rfl, rfl, rfl, rfl⟩
  | succ j ih =>
    intro c s k m hm hr hc hidle hsr hrep hM hi hfr
    obtain ⟨v, hv⟩ := hsearch s hsr false
    have hclt : 1 < c.clock := by omega
    by_cases hf : v.search.mode = .found
    · -- the background tick starts the chain
      obtain ⟨s', hb, hch', hl', hr', hC', hrep', hget'⟩ :=
        background_found_step P q first s hidle hv hf
      have hrem' : s'.remaining = s.remaining :=
        (backgroundS_fields P q first hb).2.2.2.2.2.2.2.2.1
      have hne2 : s'.chain ≠ .idle := by rw [hch']; exact chainStart_ne_idle _ _ _ _ _
      have hok2 : ChainOk Ok s'.chain := by rw [hch']; exact hstart s false v hidle hsr hv hf
      have hM2 : MInv raw {c with clock := c.clock - 1} s' := minv_same rfl hr' hC' hrep' hM
      have hi2 : ScanInvariant raw (position s'.center) k s'.left s'.right := by
        rw [hl', hr', hC']; exact hi
      have hfr2 : Frontier s' := frontier_congr hr' hrep' hfr
      obtain ⟨es, c', t, hseg, -, hm', hc', hr'', hrep'', hne'', hok'', hM'', hi'', hpos'', hC'',
          hfr'', hrem''⟩ :=
        chain_replay_finish raw P q first delay hex hd hOk hgood (m+1) {c with clock := c.clock - 1}
          s' k hm (by show 1 ≤ c.clock - 1; omega)
          (by show c.replaying = decide (0 < m+1); rw [hr]; simp)
          (fun h => absurd h (Nat.succ_ne_zero m)) (by rw [hrep', hrep]) hne2 hok2 hM2 hi2 hfr2
      obtain ⟨n, hst⟩ := replayChainSeg_stepsAll raw P hP hP' q first delay hseg (position s'.center)
        k hi2 (GalilReplaySegment.soundScanNR_replaying raw hr)
      exact Or.inr ⟨[], c, s, {c with clock := c.clock - 1}, s', es, c', t, n+1, .stop _ _, hidle,
        hr, .bg c s s' hm hr hclt hidle hb (by rw [hget']; exact hf), hseg,
        .succ (GalilReplaySegment.soundScanNR_replaying raw hr)
          (.scan_count c s s' hm (Or.inl hr) hclt hb) hst,
        replayChainSeg_chain P q first delay hseg hne2, hm', hc', hr'', hrep'', hne'', hok'', hM'',
        hi'', by rw [hpos'', hr'], by rw [hC'', hC'], hfr'',
        replayRest_of_reset hrep'', by rw [hrem'', hrem']⟩
    · -- a quiet background tick
      obtain ⟨s', hb, hch', hl', hr', hC', hrep', hget'⟩ :=
        idle_background_exists P q first s hidle hv hf
      have hsr' : SearchReady (searchLens.get s') := by rw [hget']; exact hpres s false v hsr hv
      have hrem' : s'.remaining = s.remaining :=
        (backgroundS_fields P q first hb).2.2.2.2.2.2.2.2.1
      have hQ' : SoundScanNR raw ⟨{c with clock := c.clock - 1}, s'⟩ :=
        GalilReplaySegment.soundScanNR_replaying raw hr
      rcases ih {c with clock := c.clock - 1} s' k m hm hr (by simp; omega) hch' hsr'
          (by rw [hrep', hrep]) (minv_same rfl hr' hC' hrep' hM) (by rw [hl', hr', hC']; exact hi)
          (frontier_congr hr' hrep' hfr) with hA | hB
      · obtain ⟨c1, t, hseg, hst, hm1, hr1, hc1, hidle1, hsr1, hl1, hrr1, hC1, hrp1, hrem1⟩ := hA
        exact Or.inl ⟨c1, t, .countR c s s' hm hr hclt hidle hb hseg,
          .succ (GalilReplaySegment.soundScanNR_replaying raw hr)
            (.scan_count c s s' hm (Or.inl hr) hclt hb) hst,
          hm1, hr1, hc1, hidle1, hsr1, by rw [hl1, hl'], by rw [hrr1, hr'], by rw [hC1, hC'],
          by rw [hrp1, hrep'], by rw [hrem1, hrem']⟩
      · refine Or.inr (foundLanding_prepend
          (WatchSegE.countR c s s' hm hr hclt hidle hb (.stop _ _))
          (.succ (GalilReplaySegment.soundScanNR_replaying raw hr)
            (.scan_count c s s' hm (Or.inl hr) hclt hb) (.zero _ hQ'))
          rfl (by rw [hr']) hC' hrem' hB)

/-- **The comparison of an idle replay round**: either the search stays away
from `found` (the old `match_round` conclusion, now with the step run
unconditional), or the comparison's quantum reports `found`, the chain starts
with the match credit, and the replay finishes with the chain live. -/
theorem idle_compare (hex : ∀ s, P.replayExhausted s = zero s.replay) (hd : 1 ≤ delay)
    (hsearch : ∀ s : GalilVM, SearchReady (searchLens.get s) → ∀ a : Bool,
      ∃ v, searchEffect P a s v)
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s) → searchEffect P a s v → SearchReady v)
    {Ok : WState → Prop} (hOk : WatchOk Ok)
    (hgood : ∀ w, Ok w → GalilScaffoldChainWatch.Good w) (hstart : StartOk P Ok)
    (c : Control) (s : GalilVM) (k m : ℕ)
    (hm : c.mode = .scan) (hr : c.replaying = true) (hc : c.clock = 1)
    (hidle : s.chain = ChainVM.idle) (hsr : SearchReady (searchLens.get s))
    (hM : MInv raw c s) (hi : ScanInvariant raw (position s.center) k s.left s.right)
    (hrp : s.replay = ofNat (m+1)) (hfr : Frontier s) :
    (∃ (c1 : Control) (u : GalilVM),
      WatchSegE P q first delay [true] c s c1 u ∧
      StepsAll (galilFrameS P q first) delay (SoundScanNR raw) 1 ⟨c, s⟩ ⟨c1, u⟩ ∧
      c1.mode = .scan ∧ c1.clock = delay ∧ c1.replaying = decide (0 < m) ∧
      u.chain = ChainVM.idle ∧ SearchReady (searchLens.get u) ∧ MInv raw c1 u ∧
      ScanInvariant raw (position u.center) (k+1) u.left u.right ∧
      u.replay = ofNat m ∧ position u.right = position s.right + 1 ∧
      u.center = s.center ∧ Frontier u ∧ u.remaining = s.remaining) ∨
    FoundLanding raw P q first delay Ok c s k (m+1) := by
  classical
  have hbound : position s.right + (m+1) ≤ 2 * arrived s.right := hfr (m+1) hrp
  have hav : canRight s.right := GalilReplaySegment.canRight_of_frontier (Nat.succ_pos m) hbound
  have hmatch : read (left s.left) = read (right s.right) := replay_match_of_minv hM hr hav hi
  have hpos : position (right s.right) = position s.right + 1 :=
    right_position s.right hav (represented_position _ raw hi.rightRep hi.rightPresent).1
  obtain ⟨vq, hq⟩ := hsearch s hsr true
  by_cases hf : vq.search.mode = .found
  · -- the comparison starts the chain
    set z : ChainVM := ChainVM.copy (vq.dp.config.tapes 11) reset (P.place s)
      (GalilScaffoldChainPeriod.start (P.centre s)) (inc s.radius) (inc s.radius) s.center with hzdef
    have hch : ChainMatched (chainStart (vq.dp.config.tapes 11) (P.centre s) (P.place s) s.center
        s.radius) z := ChainMatched.copy _ _ _ _ _ _ _
    have hokz : ChainOk Ok z := chainOk_matched_start (hstart s true vq hidle hsr hq hf) hch
    have hnez : z ≠ ChainVM.idle := by rw [hzdef]; intro h0; cases h0
    set vs : ScanVM := ⟨left s.left, right s.right, z⟩ with hvsdef
    have hmt : (galilFrame P q first).matched (scanLens.set s vs) := hmatch
    set u : GalilVM := replayDec true (afterCompare s vs vq) with hudef
    set o : Bool := if P.onLetter u then decide (P.leftFirst u) else c.output with hodef
    have ho : refresh (galilFrame P q first) u c.output o := by
      refine ⟨fun hl => ?_, fun hl => ?_⟩
      · have hl' : P.onLetter u := hl
        show (if P.onLetter u then decide (P.leftFirst u) else c.output) = true ↔ P.leftFirst u
        rw [if_pos hl']; exact decide_eq_true_iff
      · have hl' : ¬ P.onLetter u := hl
        show (if P.onLetter u then decide (P.leftFirst u) else c.output) = c.output
        rw [if_neg hl']
    have hurep : u.replay = ofNat m := by
      rw [hudef, replayDec_true_replay, afterCompare_replay, hrp, dec_ofNat_succ]
    have hflag : (!P.replayExhausted u) = decide (0 < m) := by
      rw [hex, hurep]
      cases m with
      | zero => rw [(zero_ofNat_iff 0).2 rfl]; simp
      | succ k => rw [zero_ofNat_succ k]; simp
    have hiu : ScanInvariant raw (position u.center) (k+1) u.left u.right := by
      have h0 := matched_invariant' raw vq (vs := vs) rfl rfl hmatch hav hi
      rw [hudef, replayDec_left, replayDec_right, replayDec_center, afterCompare_center]
      exact h0
    have hMu : MInv raw {c with clock := delay, output := o, replaying := !P.replayExhausted u} u :=
      minv_matchR P hex o delay hr rfl hav hi hM
    have hneu : u.chain ≠ .idle := by rw [hudef, replayDec_chain, afterCompare_chain]; exact hnez
    have hoku : ChainOk Ok u.chain := by
      rw [hudef, replayDec_chain, afterCompare_chain]; exact hokz
    have hposu : position u.right = position s.right + 1 := by
      rw [hudef, replayDec_right, afterCompare_right]; exact hpos
    have hCu : u.center = s.center := by rw [hudef, replayDec_center, afterCompare_center]
    have hfru : Frontier u := by
      intro m' hm'
      have hmm : m' = m := (ofNat_inj (hurep.symm.trans hm')).symm
      subst hmm
      have hur : u.right = right s.right := by rw [hudef, replayDec_right, afterCompare_right]
      rw [hur]
      exact right_frontier_step s.right m' hbound
    obtain ⟨es, c', t, hseg, -, hm', hc', hr', hrep', hne', hok', hM', hi', hpos', hC', hfr',
        hrem'⟩ :=
      chain_replay_finish raw P q first delay hex hd hOk hgood m
        {c with clock := delay, output := o, replaying := !P.replayExhausted u} u (k+1) hm hd hflag
        (fun _ => rfl) hurep hneu hoku hMu hiu hfru
    have hQu : SoundScanNR raw
        ⟨{c with clock := delay, output := o, replaying := !P.replayExhausted u}, u⟩ :=
      fun _ _ => outputRel_of_refresh' raw P hP hP' q first u c.output o hiu ho _ rfl
    obtain ⟨n, hst⟩ := replayChainSeg_stepsAll raw P hP hP' q first delay hseg _ (k+1) hiu hQu
    have ht := scan_match_found_S' P q first delay c s vs vq o hm (Or.inl hr) hc hidle rfl rfl hmt
      hq hf hch (by rw [hr]; exact ho)
    rw [hr] at ht
    exact Or.inr ⟨[], c, s, _, u, es, c', t, n+1, .stop _ _, hidle, hr,
      .cmp c s vs vq o hm hr hc hav hidle rfl rfl hmt hq hf hch ho, hseg,
      .succ (GalilReplaySegment.soundScanNR_replaying raw hr) (by simpa using ht) hst,
      replayChainSeg_chain P q first delay hseg hneu, hm', hc', hr', hrep', hne', hok', hM',
      by have e : k + (m+1) = k+1+m := by omega
         rw [e]; exact hi',
      by rw [hpos', hposu]; omega, by rw [hC', hCu], hfr',
      replayRest_of_reset hrep', by rw [hrem']; rfl⟩
  · -- a quiet comparison
    set vs : ScanVM := ⟨left s.left, right s.right, ChainVM.idle⟩ with hvsdef
    have hmt : (galilFrame P q first).matched (scanLens.set s vs) := hmatch
    set u : GalilVM := replayDec true (afterCompare s vs vq) with hudef
    set o : Bool := if P.onLetter u then decide (P.leftFirst u) else c.output with hodef
    have ho : refresh (galilFrame P q first) u c.output o := by
      refine ⟨fun hl => ?_, fun hl => ?_⟩
      · have hl' : P.onLetter u := hl
        show (if P.onLetter u then decide (P.leftFirst u) else c.output) = true ↔ P.leftFirst u
        rw [if_pos hl']; exact decide_eq_true_iff
      · have hl' : ¬ P.onLetter u := hl
        show (if P.onLetter u then decide (P.leftFirst u) else c.output) = c.output
        rw [if_neg hl']
    have hurep : u.replay = ofNat m := by
      rw [hudef, replayDec_true_replay, afterCompare_replay, hrp, dec_ofNat_succ]
    have hflag : (!P.replayExhausted u) = decide (0 < m) := by
      rw [hex, hurep]
      cases m with
      | zero => rw [(zero_ofNat_iff 0).2 rfl]; simp
      | succ k => rw [zero_ofNat_succ k]; simp
    have hiu : ScanInvariant raw (position u.center) (k+1) u.left u.right := by
      have h0 := matched_invariant' raw vq (vs := vs) rfl rfl hmatch hav hi
      rw [hudef, replayDec_left, replayDec_right, replayDec_center, afterCompare_center]
      exact h0
    refine Or.inl ⟨{c with clock := delay, output := o, replaying := !P.replayExhausted u}, u,
      .matchIdleR c s vs vq o hm hr hc hav hidle rfl rfl rfl hmt hq hf ho (.stop _ _), ?_,
      hm, rfl, hflag, ?_, ?_, ?_, hiu, hurep, ?_, ?_, ?_, ?_⟩
    · have ht := scan_match_idle_S' P q first delay c s vs vq o hm (Or.inl hr) hc hidle rfl rfl rfl
        hmt hq hf (by rw [hr]; exact ho)
      rw [hr] at ht
      exact .succ (GalilReplaySegment.soundScanNR_replaying raw hr) (by simpa using ht)
        (.zero _ (fun _ _ => outputRel_of_refresh' raw P hP hP' q first u c.output o hiu ho _ rfl))
    · rw [hudef, replayDec_chain, afterCompare_chain]
    · have hgetU : searchLens.get u = vq := by rw [hudef, replayDec_search]; rfl
      rw [hgetU]; exact hpres s true vq hsr hq
    · exact minv_matchR P hex o delay hr rfl hav hi hM
    · rw [hudef, replayDec_right, afterCompare_right]; exact hpos
    · rw [hudef, replayDec_center, afterCompare_center]
    · intro m' hm'
      have hmm : m' = m := (ofNat_inj (hurep.symm.trans hm')).symm
      subst hmm
      have hur : u.right = right s.right := by rw [hudef, replayDec_right, afterCompare_right]
      rw [hur]
      exact right_frontier_step s.right m' hbound
    · rw [hudef]; rfl

/-- **`replay_segment_construct` without `SearchQuiet`.**  From a scan state
`r` places into a replay with an idle chain, either the whole replay is quiet
(the old conclusion verbatim), or the chain starts somewhere inside it and the
replay ends in a `FoundLanding`. -/
theorem replay_general_construct (hex : ∀ s, P.replayExhausted s = zero s.replay) (hd : 1 ≤ delay)
    (hsearch : ∀ s : GalilVM, SearchReady (searchLens.get s) → ∀ a : Bool,
      ∃ v, searchEffect P a s v)
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s) → searchEffect P a s v → SearchReady v)
    {Ok : WState → Prop} (hOk : WatchOk Ok)
    (hgood : ∀ w, Ok w → GalilScaffoldChainWatch.Good w) (hstart : StartOk P Ok) :
    ∀ (r : ℕ) (c : Control) (s : GalilVM) (k : ℕ),
      c.mode = .scan → c.clock = delay → c.replaying = decide (0 < r) →
      s.replay = ofNat r → s.chain = ChainVM.idle → SearchReady (searchLens.get s) →
      MInv raw c s → ScanInvariant raw (position s.center) k s.left s.right → Frontier s →
      (∃ (es : List Bool) (c' : Control) (t : GalilVM),
        WatchSegE P q first delay es c s c' t ∧
        (SoundScanNR raw ⟨c', t⟩ →
          StepsAll (galilFrameS P q first) delay (SoundScanNR raw) es.length ⟨c, s⟩ ⟨c', t⟩) ∧
        es.length = r * delay ∧ es.count true = r ∧
        c'.mode = .scan ∧ c'.clock = delay ∧ c'.replaying = false ∧
        t.replay = reset ∧ t.chain = ChainVM.idle ∧ SearchReady (searchLens.get t) ∧
        MInv raw c' t ∧ ScanInvariant raw (position t.center) (k + r) t.left t.right ∧
        position t.right = position s.right + r ∧ t.center = s.center ∧
        Frontier t ∧ ReplayRest c' t ∧ t.remaining = s.remaining) ∨
      FoundLanding raw P q first delay Ok c s k r := by
  intro r
  induction r with
  | zero =>
    intro c s k hm hc hrp hrep hidle hsr hM hi hfr
    have hrf : c.replaying = false := by rw [hrp]; simp
    exact Or.inl ⟨[], c, s, .stop _ _, fun hlast => .zero _ hlast, by simp, by simp, hm, hc, hrf,
      hrep, hidle, hsr, hM, by simpa using hi, by simp, rfl, hfr,
      replayRest_of_reset hrep, rfl⟩
  | succ n ih =>
    intro c s k hm hc hrp hrep hidle hsr hM hi hfr
    have hrt : c.replaying = true := by rw [hrp]; simp
    rcases idle_countdown raw P hP hP' q first delay hex hd hsearch hpres hOk hgood hstart
        (delay - 1) c s k n hm hrt (by omega) hidle hsr hrep hM hi hfr with hA | hB
    · obtain ⟨c1, t1, hseg1, hst1, hm1, hr1, hc1, hidle1, hsr1, hl1, hrr1, hC1, hrp1, hrem1⟩ := hA
      have hm1' : c1.mode = Mode.scan := by rw [hm1, hm]
      have hr1' : c1.replaying = true := by rw [hr1, hrt]
      have hM1 : MInv raw c1 t1 := minv_same (by rw [hr1]) hrr1 hC1 hrp1 hM
      have hi1 : ScanInvariant raw (position t1.center) k t1.left t1.right := by
        rw [hl1, hrr1, hC1]; exact hi
      have hfr1 : Frontier t1 := frontier_congr hrr1 hrp1 hfr
      rcases idle_compare raw P hP hP' q first delay hex hd hsearch hpres hOk hgood hstart c1 t1 k n
          hm1' hr1' hc1 hidle1 hsr1 hM1 hi1 (by rw [hrp1, hrep]) hfr1 with hA2 | hB2
      · obtain ⟨c2, u, hseg2, hst2, hm2, hc2, hr2, hidle2, hsr2, hM2, hi2, hrep2, hpos2, hC2, hfr2,
          hrem2⟩ := hA2
        rcases ih c2 u (k+1) hm2 hc2 hr2 hrep2 hidle2 hsr2 hM2 hi2 hfr2 with hA3 | hB3
        · obtain ⟨es3, c3, t3, hseg3, hst3, hlen3, hcnt3, hm3, hc3, hr3, hrep3, hidle3, hsr3, hM3,
            hi3, hpos3, hC3, hfr3, hrr3, hrem3⟩ := hA3
          refine Or.inl ⟨List.replicate (delay - 1) false ++ true :: es3, c3, t3,
            watchSegE_trans P q first delay hseg1 (watchSegE_trans P q first delay hseg2 hseg3),
            ?_, ?_, ?_, hm3, hc3, hr3, hrep3, hidle3, hsr3, hM3, ?_, ?_, ?_, hfr3, hrr3, ?_⟩
          · intro hlast
            have hcomp := stepsAll_trans hst1 (stepsAll_trans hst2 (hst3 hlast))
            have hlen : (List.replicate (delay - 1) false ++ true :: es3).length =
                delay - 1 + (1 + es3.length) := by simp; omega
            rw [hlen]
            exact hcomp
          · simp only [List.length_append, List.length_replicate, List.length_cons, hlen3]
            cases delay with
            | zero => omega
            | succ d => simp; ring
          · simp [hcnt3, List.count_replicate]
          · have e : k + (n + 1) = k + 1 + n := by omega
            rw [e]; exact hi3
          · rw [hpos3, hpos2, hrr1]; omega
          · rw [hC3, hC2, hC1]
          · rw [hrem3, hrem2, hrem1]
        · exact Or.inr (foundLanding_prepend (watchSegE_trans P q first delay hseg1 hseg2)
            (stepsAll_trans hst1 hst2) (by omega) (by rw [hpos2, hrr1]; omega)
            (by rw [hC2, hC1]) (by rw [hrem2, hrem1]) hB3)
      · exact Or.inr (foundLanding_prepend hseg1 hst1 rfl (by rw [hrr1]) hC1 hrem1 hB2)
    · exact Or.inr hB

end Idle

/-! ## The gap-1 cycle, general -/

/-- **`replay_after_fallback_general`.**  `replay_after_fallback` with
`SearchQuiet` removed.  Either (i) the replay completes with the chain idle and
lands in `InvScan` at radius `r`, or (ii) the search reports `found` inside the
replay, the chain starts while replaying, and the replay completes with the
chain live (`FoundLanding … 0 r`): a non-replaying scan state with `MInv`, the
scan invariant at radius `r`, `Frontier`, a `SoundScanNR` run from the entry,
and the `ChainTicks` trace of the post-start replay. -/
theorem replay_after_fallback_general (raw : List (Fin 2)) (P : Shared)
    (hP : P.onLetter = onLetterVM raw) (hP' : P.leftFirst = leftFirstVM) (q : ℕ) (first : Fin 9)
    (delay : ℕ) (hex : ∀ s, P.replayExhausted s = zero s.replay) (hd : 1 ≤ delay)
    (hsearch : ∀ s : GalilVM, SearchReady (searchLens.get s) → ∀ a : Bool,
      ∃ v, searchEffect P a s v)
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s) → searchEffect P a s v → SearchReady v)
    {Ok : WState → Prop} (hOk : WatchOk Ok)
    (hgood : ∀ w, Ok w → GalilScaffoldChainWatch.Good w) (hstart : StartOk P Ok)
    (r : ℕ) (hr0 : 0 < r) (c : Control) (t : GalilVM)
    (hm : c.mode = Mode.scan) (hc : c.clock = delay) (hrpl : c.replaying = true)
    (hR : Restarted raw t 0 reset) (hrep : t.replay = ofNat r)
    (hM : MInv raw c t) (hfr : Frontier t) (hsi : ShiftIdle t) :
    (∃ (es : List Bool) (c' : Control) (t' : GalilVM),
      WatchSegE P q first delay es c t c' t' ∧
      (SoundScanNR raw ⟨c', t'⟩ →
        StepsAll (galilFrameS P q first) delay (SoundScanNR raw) es.length ⟨c, t⟩ ⟨c', t'⟩) ∧
      es.length = r * delay ∧ es.count true = r ∧
      position t'.right = position t.right + r ∧ t'.center = t.center ∧
      GalilReplaySegment.InvScan delay raw c' t' r) ∨
    FoundLanding raw P q first delay Ok c t 0 r := by
  rcases replay_general_construct raw P hP hP' q first delay hex hd hsearch hpres hOk hgood hstart
      r c t 0 hm hc (by rw [hrpl]; simp [hr0]) hrep hR.1 (searchReady_of_restarted hR) hM
      hR.2.2.2.1 hfr with hA | hB
  · obtain ⟨es, c', t', hseg, hst, hlen, hcnt, hm', hc', hr', hrep', hidle', hsr', hM', hi',
        hpos', hC', hfr', hrr', hrem'⟩ := hA
    exact Or.inl ⟨es, c', t', hseg, hst, hlen, hcnt, hpos', hC',
      GalilReplaySegment.inv_after_replay delay raw c' t' r hm' hc' hr' hidle' (by simpa using hi')
        hM' hsr' hrep' (GalilReplaySegment.shiftIdle_congr hrem' hsi)⟩
  · exact Or.inr hB

/-- The landing of branch (ii) is `ShiftIdle` when the entry was. -/
theorem foundLanding_shiftIdle {raw : List (Fin 2)} {P : Shared} {q : ℕ} {first : Fin 9}
    {delay : ℕ} {Ok : WState → Prop} {c : Control} {s : GalilVM} {k d : ℕ}
    (hL : FoundLanding raw P q first delay Ok c s k d) (hsi : ShiftIdle s) :
    ∃ (c' : Control) (t : GalilVM) (n : ℕ),
      StepsAll (galilFrameS P q first) delay (SoundScanNR raw) n ⟨c, s⟩ ⟨c', t⟩ ∧
      c'.replaying = false ∧ t.chain ≠ .idle ∧ ShiftIdle t := by
  obtain ⟨-, -, -, -, -, -, c', t, n, -, -, -, -, -, hst, -, -, -, hr, -, hne, -, -, -, -, -, -, -,
    hrem⟩ := hL
  exact ⟨c', t, n, hst, hr, hne, GalilReplaySegment.shiftIdle_congr hrem hsi⟩

/-! ## Into `life_from_prep_*`: the preparation trace across the replay -/

/-- **Comparison start.**  The replayed trace out of the started chain,
followed by the trace of *any* `hprepSeg : WatchSegE … es3` leaving the landing,
is a preparation trace: if `es2 ++ es3 = bs ++ dm :: cs` the end of `hprepSeg`
is `watchStart`.  (`es3 = []`, i.e. `hprepSeg = .stop`, is the case where the
preparation ends inside the replay; `prep_watch_start_of_replayChainSeg` is
the `es3 = []` instance.) -/
theorem prep_watch_across_replay (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    {s t : GalilScaffoldSearchFinish.State} {x y : GalilScaffoldControl.Machine 12}
    {as : List Bool} {w : List (Fin 3)} {lower span : ℕ} (p : GalilScaffoldPlace.Place)
    (hw : w = (GalilScaffoldPlace.stream p).take (span+1))
    (hr : GalilScaffoldSearchRun.SafeQuanta s x as t y) (hs : s.mode = .run) (ht : t.mode = .found)
    (hv : GalilDpCorrect.Result w lower 0 (GalilScaffoldProgram.denote y.config))
    (ver : PlaceHead) (r0 : ℕ) (dm : Bool) :
    ∃ (h : ℕ) (c : Fin 3) (ys : List (Fin 3)) (b : Fin 3),
      GalilDpCorrect.Candidate w lower h ∧ GalilScaffoldPlace.read p = some c ∧ ys.length + 1 = h ∧
      ∀ (bs cs : List Bool), bs.length = h → cs.length = h+1 →
        ∀ (ch : ChainVM), ChainMatched (chainStart (y.config.tapes 11) c p ver (ofNat (r0+1))) ch →
        ∀ {es2 es3 : List Bool} {c2 c' c'' : Control} {s2 t' t'' : GalilVM},
          ReplayChainSeg P q first delay es2 c2 s2 c' t' → s2.chain = ch →
          WatchSegE P q first delay es3 c' t' c'' t'' → es2 ++ es3 = bs ++ dm :: cs →
          t''.chain = .watch (watchStart ver c ys b (GalilScaffoldChainCredits.run
            (GalilScaffoldChainCredits.start (ofNat (r0+1)))
            (GalilScaffoldChainCredits.prepEvents true dm bs cs))) := by
  obtain ⟨h, c, ys, b, hcand, hread, hlen, hrest⟩ := prep_watch_start_trace p hw hr hs ht hv ver r0 dm
  refine ⟨h, c, ys, b, hcand, hread, hlen, ?_⟩
  intro bs cs hbs hcs ch hch es2 es3 c2 c' c'' s2 t' t'' hseg2 hs2 hseg3 hes
  have hne2 : s2.chain ≠ .idle := by rw [hs2]; exact chainMatched_chainStart_ne_idle hch
  have hne' : t'.chain ≠ .idle := replayChainSeg_ne_idle P q first delay hseg2 hne2
  have h23 := chainTicks_trans (replayChainSeg_chain P q first delay hseg2 hne2)
    (watchSegE_chainTicks P q first delay hseg3 hne')
  rw [hes, hs2] at h23
  exact hrest bs cs hbs hcs ch t''.chain hch h23

/-- **Background start.**  The same with the chain installed plainly by a
background tick (`FoundTick.bg`): the start event is `false`. -/
theorem prep_watch_across_replay_bg (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    {s t : GalilScaffoldSearchFinish.State} {x y : GalilScaffoldControl.Machine 12}
    {as : List Bool} {w : List (Fin 3)} {lower span : ℕ} (p : GalilScaffoldPlace.Place)
    (hw : w = (GalilScaffoldPlace.stream p).take (span+1))
    (hr : GalilScaffoldSearchRun.SafeQuanta s x as t y) (hs : s.mode = .run) (ht : t.mode = .found)
    (hv : GalilDpCorrect.Result w lower 0 (GalilScaffoldProgram.denote y.config))
    (ver : PlaceHead) (r0 : ℕ) (dm : Bool) :
    ∃ (h : ℕ) (c : Fin 3) (ys : List (Fin 3)) (b : Fin 3),
      GalilDpCorrect.Candidate w lower h ∧ GalilScaffoldPlace.read p = some c ∧ ys.length + 1 = h ∧
      ∀ (bs cs : List Bool), bs.length = h → cs.length = h+1 →
        ∀ {es2 es3 : List Bool} {c2 c' c'' : Control} {s2 t' t'' : GalilVM},
          ReplayChainSeg P q first delay es2 c2 s2 c' t' →
          s2.chain = chainStart (y.config.tapes 11) c p ver (ofNat (r0+1)) →
          WatchSegE P q first delay es3 c' t' c'' t'' → es2 ++ es3 = bs ++ dm :: cs →
          t''.chain = .watch (watchStart ver c ys b (GalilScaffoldChainCredits.run
            (GalilScaffoldChainCredits.start (ofNat (r0+1)))
            (GalilScaffoldChainCredits.prepEvents false dm bs cs))) := by
  obtain ⟨h, c, ys, b, hcand, hread, hlen, hrest⟩ := found_to_watchStart p hw hr hs ht hv ver r0 false dm
  refine ⟨h, c, ys, b, hcand, hread, hlen, ?_⟩
  intro bs cs hbs hcs es2 es3 c2 c' c'' s2 t' t'' hseg2 hs2 hseg3 hes
  obtain ⟨x1, hx1, hticks'⟩ := hrest bs cs hbs hcs
  have hx1' : x1 = chainStart (y.config.tapes 11) c p ver (ofNat (r0+1)) := by simpa using hx1
  have hne2 : s2.chain ≠ .idle := by rw [hs2]; exact chainStart_ne_idle _ _ _ _ _
  have hne' : t'.chain ≠ .idle := replayChainSeg_ne_idle P q first delay hseg2 hne2
  have h23 := chainTicks_trans (replayChainSeg_chain P q first delay hseg2 hne2)
    (watchSegE_chainTicks P q first delay hseg3 hne')
  rw [hes, hs2, ← hx1'] at h23
  exact chainTicks_unique h23 hticks'

#print axioms scan_match_found_S'
#print axioms foundTick_start
#print axioms chainOk_matched_start
#print axioms chain_countdown
#print axioms chain_compare
#print axioms chain_replay_finish
#print axioms foundLanding_prepend
#print axioms idle_countdown
#print axioms idle_compare
#print axioms replay_general_construct
#print axioms replay_after_fallback_general
#print axioms foundLanding_shiftIdle
#print axioms prep_watch_across_replay
#print axioms prep_watch_across_replay_bg

end PalPeg.GalilReplayGeneral
