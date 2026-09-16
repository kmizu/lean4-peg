import PalPeg.GalilSegmentConstruct
import PalPeg.GalilReportReach
import PalPeg.GalilScaffoldTopReadyFound

/-!
# Gap 3 of `PalPeg.GalilReportReach`: the report point after the replay

`PalPeg.GalilReportReach` reaches the report point on the tick that consumes
the last letter, and its module note records three gaps.  This module closes
the third: on the **fallback route** with a positive chosen radius there is no
report point right after the mismatching cycle
(`replayStart_report_point_iff_zero`) — the machine sits at a restarted state
`Restarted raw t 0 reset` with `replaying = decide (0 < r)`,
`t.replay = ofNat r`, and the right head moved back onto the centre
(`replayStart_right_position`), `r` cells short of the last letter.  The
report happens only after the replay has walked the right head back up.

The replay is *forced*: at every one of its comparisons the outer symbols
agree, because `MInv` says the centre is the leftmost live centre and the
counter is the distance left to the saved place (`replay_match_of_minv` of
`PalPeg.GalilTickFun2`).  So the segment is completely determined:

* `replay_countdown` — `delay - 1` background ticks (`WatchSegE.countR`) bring
  the clock from `delay` down to `1` without touching anything but the clock
  and the search projection;
* `replay_one` — the matching comparison (`WatchSegE.matchIdleR`) that follows:
  the right head advances one cell (`right_position`), the counter drops by one
  (`minv_matchR`), the scan invariant grows by one (`matched_invariant'`), and
  the output is **refreshed**;
* `replay_run` — `r` iterations of the above: the counter is exhausted, the
  `replaying` flag goes down, and the right head is back on `2·|raw| - 1`;
* `report_after_replay` / `scaffoldRun_report_after_replay` — the packaging:
  the state the replay lands in is a refreshed `ReportPoint` of the same run.

Every state of the segment is also carried as a `SoundScanNR` run
(`StepsAll`), which is what `ScaffoldRun` of
`PalPeg.GalilStructuredSkeleton` wants: the intermediate states are all
*replaying*, so `SoundScanNR` is vacuous there
(`soundScanNR_of_replaying`), and at the terminal state it is the refreshed
output's own soundness (`outputRel_of_refresh'`).

## Geometry: why the right head can always move

During the replay nothing arrives any more, so `canRight` has to come from the
material already on the right stack.  `canRight_of_lt` supplies it: with an
empty incoming FIFO a head that has not yet reached `2·|raw| - 1` is either on
a gap cell (`gap = false`, movable outright) or has a nonempty right stack.
`right_incoming_nil` records that a right move never refills the FIFO.

## What is assumed

* `hnfR` — **the search does not report `found` while the replay counter is
  positive.**  `WatchSegE.matchIdleR` carries `vq.search.mode ≠ .found` (a
  `found` would start a chain instead of continuing the scan), and `hbg` of
  `PalPeg.GalilSegmentConstruct` only covers background events.  That the
  co-running search stays quiet along a replay is a property of the search
  layer and is *not* proved here.
* `hsearch` / `hpres` / `hbg` / `hex` / `hd` — the same co-process hypotheses as
  `watchSegE_construct`.
* `hhead` / `hlast` — the *last letter was the one just consumed before the
  fallback*: `Represents t.right.head raw` with an empty incoming FIFO (there
  is nothing left to arrive), and the right head is exactly `r` cells short of
  the last letter cell.  Establishing these at the fallback exit belongs to the
  fallback layer.
* `Frontier t` and `ReplayRest t` are recorded in the statement of
  `report_after_replay` because they are the invariants that make the situation
  meaningful, but the proof does not need them: `hlast` already pins the
  distance exactly, and `ReplayRest`'s premise is false while replaying.
-/

set_option autoImplicit false

namespace PalPeg.GalilReportReplay

open PalPeg PalPeg.GalilSegmentConstruct PalPeg.GalilTickFun2 PalPeg.GalilBranchInvariants2
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier GalilScaffoldChainInputSupply GalilStructuredSkeleton
open PalPeg.GalilEndOfInput (layout_left_length layout_right layout_incoming)

/-! ## Geometry of the right head while the input has stopped arriving -/

/-- A right move does not refill an empty incoming FIFO. -/
theorem right_incoming_nil {p : PlaceHead} (h : p.head.incoming = []) :
    (right p).head.incoming = [] := by
  cases hg : p.gap with
  | false => simpa [right, hg] using h
  | true =>
    simp only [right, hg, if_true]
    show (GalilScaffoldInputTrace.moveRight p.head).incoming = []
    cases hr : p.head.right with
    | cons a rs => simp [GalilScaffoldInputTrace.moveRight, hr, h]
    | nil => simp [GalilScaffoldInputTrace.moveRight, hr, h]

/-- With nothing left to arrive, the right head can still move as long as it
has not reached the last letter cell `2·|w| - 1`. -/
theorem canRight_of_lt {p : PlaceHead} {w : List (Fin 2)}
    (hrep : GalilScaffoldInputTrace.Represents p.head w)
    (hinc : p.head.incoming = []) (hlt : position p < 2 * w.length - 1) : canRight p := by
  cases hg : p.gap with
  | false => exact Or.inl hg
  | true =>
    refine Or.inr (Or.inl ?_)
    obtain ⟨xs, rs, qq, hh, hw⟩ := hrep
    have hq : qq = [] := by rw [hh, layout_incoming] at hinc; exact hinc
    have hlen : p.head.left.length = xs.length := by rw [hh]; exact layout_left_length _ _ _
    have hrr : p.head.right = (rs.map some) := by rw [hh]; exact layout_right _ _ _
    have hwlen : w.length = xs.length + rs.length := by rw [hw, hq]; simp
    have hpos : position p = 2 * xs.length := by
      simp only [position, hg, if_true, hlen]
    rw [hpos, hwlen] at hlt
    have hrs : rs ≠ [] := by
      intro h0
      rw [h0] at hlt; simp at hlt; omega
    rw [hrr]
    simpa using hrs

/-! ## Counting the clock down to the next comparison -/

/-- A replaying state satisfies `SoundScanNR` vacuously. -/
theorem soundScanNR_of_replaying (raw : List (Fin 2)) {c : Control} {s : GalilVM}
    (hrp : c.replaying = true) : SoundScanNR raw ⟨c, s⟩ := by
  intro _ hnr
  rw [hrp] at hnr
  exact absurd hnr (by simp)

/-- While replaying with an idle chain, the controller spends `k` background
ticks (`WatchSegE.countR`) bringing the clock from `k+1` down to `1`.  Nothing
but the clock and the search projection changes, and every state of the run is
`SoundScanNR` (vacuously: they are all replaying). -/
theorem replay_countdown (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (hsearch : ∀ s' : GalilVM, SearchReady (searchLens.get s') → ∀ a : Bool,
      ∃ v, searchEffect P a s' v)
    (hpres : ∀ (s' : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s') → searchEffect P a s' v → SearchReady v)
    (hbg : ∀ (s' : GalilVM) (v : SearchVM), searchEffect P false s' v → v.search.mode ≠ .found) :
    ∀ (k : ℕ) (c : Control) (s : GalilVM), c.mode = Mode.scan → c.replaying = true →
      c.clock = k + 1 → s.chain = ChainVM.idle → SearchReady (searchLens.get s) →
      ∃ (es : List Bool) (n : ℕ) (s' : GalilVM),
        WatchSegE P q first delay es c s {c with clock := 1} s' ∧ es.length = k ∧
        StepsAll (galilFrameS P q first) delay (SoundScanNR raw) n ⟨c, s⟩ ⟨{c with clock := 1}, s'⟩ ∧
        s'.chain = ChainVM.idle ∧ SearchReady (searchLens.get s') ∧
        s'.left = s.left ∧ s'.right = s.right ∧ s'.center = s.center ∧ s'.replay = s.replay := by
  intro k
  induction k with
  | zero =>
    intro c s hm hrp hclk hidle hsr
    have hc1 : c.clock = 1 := by omega
    have hc : ({c with clock := 1} : Control) = c := by rw [← hc1]
    refine ⟨[], 0, s, ?_, rfl, ?_, hidle, hsr, rfl, rfl, rfl, rfl⟩
    · rw [hc]; exact .stop _ _
    · rw [hc]; exact .zero _ (soundScanNR_of_replaying raw hrp)
  | succ k ih =>
    intro c s hm hrp hclk hidle hsr
    obtain ⟨v, hv⟩ := hsearch s hsr false
    obtain ⟨s1, hb, hch1, hl1, hr1, hC1, hrep1, hget1⟩ :=
      idle_background_exists P q first s hidle hv (hbg s v hv)
    have hsr1 : SearchReady (searchLens.get s1) := by
      rw [hget1]; exact hpres s false v hsr hv
    obtain ⟨es, n, s2, hseg, hlen, hall, hch2, hsr2, hl2, hr2, hC2, hrep2⟩ :=
      ih {c with clock := c.clock - 1} s1 hm hrp (by simp; omega) hch1 hsr1
    refine ⟨false :: es, n + 1, s2, ?_, by simp [hlen], ?_, hch2, hsr2, by rw [hl2, hl1],
      by rw [hr2, hr1], by rw [hC2, hC1], by rw [hrep2, hrep1]⟩
    · exact .countR c s s1 hm hrp (by omega) hidle hb hseg
    · exact .succ (soundScanNR_of_replaying raw hrp)
        (.scan_count c s s1 hm (Or.inl hrp) (by omega) hb) hall

/-! ## One replay comparison -/

/-- **One step of the replay.**  From a scan state that is replaying with the
counter at `m+1` and the right head still short of the last letter, the
controller counts the clock down and performs the forced matching comparison
(`replay_match_of_minv`): the segment ends one cell further right, with the
counter at `m`, the `replaying` flag recomputed from it, and the output
*refreshed*.  The whole segment is a `SoundScanNR` run. -/
theorem replay_one (raw : List (Fin 2)) (P : Shared) (hP : P.onLetter = onLetterVM raw)
    (hP' : P.leftFirst = leftFirstVM)
    (hex : ∀ s, P.replayExhausted s = zero s.replay)
    (q : ℕ) (first : Fin 9) (delay : ℕ) (hd : 1 ≤ delay)
    (hsearch : ∀ s' : GalilVM, SearchReady (searchLens.get s') → ∀ a : Bool,
      ∃ v, searchEffect P a s' v)
    (hpres : ∀ (s' : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s') → searchEffect P a s' v → SearchReady v)
    (hbg : ∀ (s' : GalilVM) (v : SearchVM), searchEffect P false s' v → v.search.mode ≠ .found)
    (hnfR : ∀ (s' : GalilVM) (v : SearchVM) (m : ℕ), 0 < m → s'.replay = ofNat m →
      searchEffect P true s' v → v.search.mode ≠ .found)
    {c : Control} {s : GalilVM} {rad m : ℕ}
    (hm : c.mode = Mode.scan) (hclk : 1 ≤ c.clock) (hrp : c.replaying = true)
    (hrepl : s.replay = ofNat (m + 1))
    (hidle : s.chain = ChainVM.idle) (hsr : SearchReady (searchLens.get s))
    (hM : MInv raw c s)
    (hi : ScanInvariant raw (position s.center) rad s.left s.right)
    (hinc : s.right.head.incoming = [])
    (hlast : position s.right + (m + 1) = 2 * raw.length - 1) :
    ∃ (es : List Bool) (n : ℕ) (c' : Control) (t : GalilVM),
      WatchSegE P q first delay es c s c' t ∧
      StepsAll (galilFrameS P q first) delay (SoundScanNR raw) n ⟨c, s⟩ ⟨c', t⟩ ∧
      c'.mode = Mode.scan ∧ 1 ≤ c'.clock ∧ c'.replaying = decide (0 < m) ∧
      t.replay = ofNat m ∧ t.chain = ChainVM.idle ∧ SearchReady (searchLens.get t) ∧
      position t.right = position s.right + 1 ∧ t.right.head.incoming = [] ∧
      MInv raw c' t ∧ ScanInvariant raw (position t.center) (rad + 1) t.left t.right ∧
      Refreshed P q first ⟨c', t⟩ := by
  classical
  -- count the clock down to one
  obtain ⟨k, hk⟩ : ∃ k, c.clock = k + 1 := ⟨c.clock - 1, by omega⟩
  obtain ⟨es0, n0, s1, hseg0, -, hall0, hidle1, hsr1, hl1, hr1, hC1, hrepl1⟩ :=
    replay_countdown raw P q first delay hsearch hpres hbg k c s hm hrp hk hidle hsr
  set c1 : Control := {c with clock := 1} with hc1def
  have hm1 : c1.mode = Mode.scan := hm
  have hrp1 : c1.replaying = true := hrp
  have hclk1 : c1.clock = 1 := rfl
  have hM1 : MInv raw c1 s1 := minv_same rfl hr1 hC1 hrepl1 hM
  have hi1 : ScanInvariant raw (position s1.center) rad s1.left s1.right := by
    rw [hl1, hr1, hC1]; exact hi
  have hrepl1' : s1.replay = ofNat (m + 1) := by rw [hrepl1]; exact hrepl
  have hinc1 : s1.right.head.incoming = [] := by rw [hr1]; exact hinc
  -- the head can still move
  have hav : canRight s1.right :=
    canRight_of_lt hi1.rightRep hinc1 (by rw [hr1]; omega)
  have hpos1 : position (right s1.right) = position s1.right + 1 :=
    right_position s1.right hav (represented_position _ raw hi1.rightRep hi1.rightPresent).1
  -- the comparison is forced to match
  have hmatch : read (left s1.left) = read (right s1.right) :=
    replay_match_of_minv hM1 hrp1 hav hi1
  obtain ⟨vq, hq⟩ := hsearch s1 hsr1 true
  have hf : vq.search.mode ≠ .found := hnfR s1 vq (m + 1) (by omega) hrepl1' hq
  set vs : ScanVM := ⟨left s1.left, right s1.right, ChainVM.idle⟩ with hvsdef
  have hmt : (galilFrame P q first).matched (scanLens.set s1 vs) := hmatch
  set u : GalilVM := replayDec true (afterCompare s1 vs vq) with hudef
  set o : Bool := if P.onLetter u then decide (P.leftFirst u) else c1.output with hodef
  have ho : refresh (galilFrame P q first) u c1.output o := by
    refine ⟨fun hl => ?_, fun hl => ?_⟩
    · have hl' : P.onLetter u := hl
      show (if P.onLetter u then decide (P.leftFirst u) else c1.output) = true ↔ P.leftFirst u
      rw [if_pos hl']; exact decide_eq_true_iff
    · have hl' : ¬ P.onLetter u := hl
      show (if P.onLetter u then decide (P.leftFirst u) else c1.output) = c1.output
      rw [if_neg hl']
  -- bookkeeping at the target state
  have hreplU : u.replay = ofNat m := by
    rw [hudef, replayDec_true_replay, afterCompare_replay, hrepl1', dec_ofNat_succ]
  have hidleU : u.chain = ChainVM.idle := by
    rw [hudef, replayDec_chain, afterCompare_chain]
  have hgetU : searchLens.get u = vq := by rw [hudef, replayDec_search]; rfl
  have hsrU : SearchReady (searchLens.get u) := by
    rw [hgetU]; exact hpres s1 true vq hsr1 hq
  have hrightU : u.right = right s1.right := by
    rw [hudef, replayDec_right, afterCompare_right]
  have hposU : position u.right = position s.right + 1 := by
    rw [hrightU, hpos1, hr1]
  have hincU : u.right.head.incoming = [] := by
    rw [hrightU]; exact right_incoming_nil hinc1
  set c2 : Control :=
    { c1 with clock := delay, output := o, replaying := !P.replayExhausted u } with hc2def
  have hMU : MInv raw c2 u := minv_matchR P hex o delay hrp1 rfl hav hi1 hM1
  have hiU : ScanInvariant raw (position u.center) (rad + 1) u.left u.right := by
    have h0 := matched_invariant' raw vq (vs := vs) rfl rfl hmatch hav hi1
    rw [hudef, replayDec_left, replayDec_right, replayDec_center, afterCompare_center]
    exact h0
  have hzU : P.replayExhausted u = decide (m = 0) := by
    rw [hex, hreplU]
    cases m with
    | zero => simpa using (zero_ofNat_iff 0).2 rfl
    | succ j => simpa using zero_ofNat_succ j
  -- the tick performing the comparison
  have htick : Tick (galilFrameS P q first) delay ⟨c1, s1⟩ ⟨c2, u⟩ := by
    have ht := scan_match_idle_S' P q first delay c1 s1 vs vq o hm1 (Or.inl hrp1) hclk1 hidle1
      rfl rfl rfl hmt hq hf (by rw [hrp1]; exact ho)
    rw [hrp1] at ht
    simpa using ht
  have hQU : SoundScanNR raw ⟨c2, u⟩ := by
    intro _ _
    exact outputRel_of_refresh' raw P hP hP' q first u c1.output o hiU ho c2 rfl
  refine ⟨es0 ++ [true], n0 + 1, c2, u, ?_, ?_, hm1, ?_, ?_, hreplU, hidleU, hsrU, hposU,
    hincU, hMU, hiU, ⟨c1.output, ho⟩⟩
  · refine watchSegE_trans P q first delay hseg0 ?_
    exact .matchIdleR c1 s1 vs vq o hm1 hrp1 hclk1 hav hidle1 rfl rfl rfl hmt hq hf ho (.stop _ _)
  · have h2 : StepsAll (galilFrameS P q first) delay (SoundScanNR raw) 1 ⟨c1, s1⟩ ⟨c2, u⟩ :=
      .succ (soundScanNR_of_replaying raw hrp1) htick (.zero _ hQU)
    simpa using stepsAll_trans hall0 h2
  · show 1 ≤ delay; exact hd
  · show (!P.replayExhausted u) = decide (0 < m)
    rw [hzU]; cases m <;> simp

/-! ## The whole replay -/

/-- **The replay runs to its end.**  Iterating `replay_one` `m+1` times: the
counter is exhausted, the `replaying` flag goes down, and the right head has
walked back up to the last letter cell `2·|raw| - 1`. -/
theorem replay_run (raw : List (Fin 2)) (P : Shared) (hP : P.onLetter = onLetterVM raw)
    (hP' : P.leftFirst = leftFirstVM)
    (hex : ∀ s, P.replayExhausted s = zero s.replay)
    (q : ℕ) (first : Fin 9) (delay : ℕ) (hd : 1 ≤ delay)
    (hsearch : ∀ s' : GalilVM, SearchReady (searchLens.get s') → ∀ a : Bool,
      ∃ v, searchEffect P a s' v)
    (hpres : ∀ (s' : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s') → searchEffect P a s' v → SearchReady v)
    (hbg : ∀ (s' : GalilVM) (v : SearchVM), searchEffect P false s' v → v.search.mode ≠ .found)
    (hnfR : ∀ (s' : GalilVM) (v : SearchVM) (m : ℕ), 0 < m → s'.replay = ofNat m →
      searchEffect P true s' v → v.search.mode ≠ .found) :
    ∀ (m : ℕ) (c : Control) (s : GalilVM) (rad : ℕ),
      c.mode = Mode.scan → 1 ≤ c.clock → c.replaying = true →
      s.replay = ofNat (m + 1) → s.chain = ChainVM.idle → SearchReady (searchLens.get s) →
      MInv raw c s → ScanInvariant raw (position s.center) rad s.left s.right →
      s.right.head.incoming = [] → position s.right + (m + 1) = 2 * raw.length - 1 →
      ∃ (es : List Bool) (n : ℕ) (c' : Control) (t : GalilVM),
        WatchSegE P q first delay es c s c' t ∧
        StepsAll (galilFrameS P q first) delay (SoundScanNR raw) n ⟨c, s⟩ ⟨c', t⟩ ∧
        c'.mode = Mode.scan ∧ c'.replaying = false ∧
        position t.right = 2 * raw.length - 1 ∧ t.right.head.incoming = [] ∧
        t.chain = ChainVM.idle ∧ MInv raw c' t ∧
        (∃ rad', ScanInvariant raw (position t.center) rad' t.left t.right) ∧
        Refreshed P q first ⟨c', t⟩ := by
  intro m
  induction m with
  | zero =>
    intro c s rad hm hclk hrp hrepl hidle hsr hM hi hinc hlast
    obtain ⟨es, n, c', t, hseg, hall, hm', -, hrp', -, hidle', -, hposR, hincR, hMt, hit, hfr⟩ :=
      replay_one raw P hP hP' hex q first delay hd hsearch hpres hbg hnfR hm hclk hrp hrepl
        hidle hsr hM hi hinc hlast
    refine ⟨es, n, c', t, hseg, hall, hm', by simpa using hrp', by omega, hincR, hidle', hMt,
      ⟨rad + 1, hit⟩, hfr⟩
  | succ j ih =>
    intro c s rad hm hclk hrp hrepl hidle hsr hM hi hinc hlast
    obtain ⟨es1, n1, c1, t1, hseg1, hall1, hm1, hclk1, hrp1, hrepl1, hidle1, hsr1, hposR,
      hincR, hMt, hit, -⟩ :=
      replay_one raw P hP hP' hex q first delay hd hsearch hpres hbg hnfR hm hclk hrp hrepl
        hidle hsr hM hi hinc hlast
    have hrp1' : c1.replaying = true := by simpa using hrp1
    obtain ⟨es2, n2, c2, t2, hseg2, hall2, hm2, hrp2, hpos2, hinc2, hidle2, hM2, hi2, hfr2⟩ :=
      ih c1 t1 (rad + 1) hm1 hclk1 hrp1' hrepl1 hidle1 hsr1 hMt hit hincR (by omega)
    exact ⟨es1 ++ es2, n1 + n2, c2, t2, watchSegE_trans P q first delay hseg1 hseg2,
      stepsAll_trans hall1 hall2, hm2, hrp2, hpos2, hinc2, hidle2, hM2, hi2, hfr2⟩

/-! ## The report point reached after the replay -/

/-- **The report point on the fallback route.**

The machine has just taken the fallback on the comparison that consumed the
last letter of `raw`, so it sits at a restarted state `⟨c, t⟩`:
`Restarted raw t 0 reset`, the replay counter holds the chosen radius `r > 0`
(`hrepl`), the `replaying` flag was set from it (`hrp`, the `replayStart`
branch), and the right head has been moved back onto the centre, `r` cells
short of the last letter (`hlast`) — with nothing left to arrive (`hhead`,
which is `Represents t.right.head raw` with an empty incoming FIFO).

Then the `r` forced replay comparisons of `replay_run` carry the machine back
to the last letter cell, the last one refreshing the output, and the state it
lands in is a refreshed **report point** of the same run. -/
theorem report_after_replay (raw : List (Fin 2)) (P : Shared)
    (hP : P.onLetter = onLetterVM raw) (hP' : P.leftFirst = leftFirstVM)
    (hex : ∀ s, P.replayExhausted s = zero s.replay)
    (q : ℕ) (first : Fin 9) (delay : ℕ) (hd : 1 ≤ delay)
    (hsearch : ∀ s' : GalilVM, SearchReady (searchLens.get s') → ∀ a : Bool,
      ∃ v, searchEffect P a s' v)
    (hpres : ∀ (s' : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s') → searchEffect P a s' v → SearchReady v)
    (hbg : ∀ (s' : GalilVM) (v : SearchVM), searchEffect P false s' v → v.search.mode ≠ .found)
    (hnfR : ∀ (s' : GalilVM) (v : SearchVM) (m : ℕ), 0 < m → s'.replay = ofNat m →
      searchEffect P true s' v → v.search.mode ≠ .found)
    {n : ℕ} {x : State GalilVM} {c : Control} {t : GalilVM} {r : ℕ}
    (hx : x.ctl = GalilScaffoldController.initial delay)
    (hrun : StepsAll (galilFrameS P q first) delay (SoundScanNR raw) n x ⟨c, t⟩)
    (hm : c.mode = Mode.scan) (hclk : 1 ≤ c.clock)
    (hR : Restarted raw t 0 reset)
    (hM : MInv raw c t) (_hfr : Frontier t) (_hrest : ReplayRest c t)
    (hsr : SearchReady (searchLens.get t))
    (hrepl : t.replay = ofNat r) (hrp : c.replaying = decide (0 < r)) (hr0 : 0 < r)
    (hhead : ∃ xs rs : List (Fin 2),
      t.right.head = layout xs (rs.map some) [] ∧ raw = xs.reverse ++ rs)
    (hlast : position t.right + r = 2 * raw.length - 1) :
    ∃ (es : List Bool) (c' : Control) (y : GalilVM),
      WatchSegE P q first delay es c t c' y ∧
      (∃ (k : ℕ) (x' : State GalilVM), x'.ctl = GalilScaffoldController.initial delay ∧
        StepsAll (galilFrameS P q first) delay (SoundScanNR raw) k x' ⟨c', y⟩) ∧
      ReportPoint raw ⟨c', y⟩ ∧ Refreshed P q first ⟨c', y⟩ := by
  obtain ⟨j, rfl⟩ : ∃ j, r = j + 1 := ⟨r - 1, by omega⟩
  have hrp' : c.replaying = true := by rw [hrp]; simp
  have hidle : t.chain = ChainVM.idle := hR.1
  have hi : ScanInvariant raw (position t.center) 0 t.left t.right := hR.2.2.2.1
  have hinc : t.right.head.incoming = [] := by
    obtain ⟨xs, rs, hh, -⟩ := hhead
    rw [hh, layout_incoming]
  have hne : 0 < raw.length := by omega
  obtain ⟨es, k, c', y, hseg, hall, -, hrpF, hposF, -, -, hMF, ⟨radF, hiF⟩, hfrF⟩ :=
    replay_run raw P hP hP' hex q first delay hd hsearch hpres hbg hnfR j c t 0 hm hclk hrp'
      hrepl hidle hsr hM hi hinc hlast
  exact ⟨es, c', y, hseg, ⟨n + k, x, hx, stepsAll_trans hrun hall⟩,
    ⟨hrpF, ⟨radF, hiF⟩, hMF, hposF, hne⟩, hfrF⟩

/-- `report_after_replay` in the `ScaffoldRun` packaging of
`PalPeg.GalilStructuredSkeleton`, i.e. the shape `H_run` of
`pal_in_peg_of_galil'` consumes. -/
theorem scaffoldRun_report_after_replay (w : List (Fin 2)) (Pof : List (Fin 2) → Shared)
    (qof : List (Fin 2) → ℕ) (firstOf : List (Fin 2) → Fin 9) (delay : ℕ) (hd : 1 ≤ delay)
    (hP : (Pof w).onLetter = onLetterVM w) (hP' : (Pof w).leftFirst = leftFirstVM)
    (hex : ∀ s, (Pof w).replayExhausted s = zero s.replay)
    (hsearch : ∀ s' : GalilVM, SearchReady (searchLens.get s') → ∀ a : Bool,
      ∃ v, searchEffect (Pof w) a s' v)
    (hpres : ∀ (s' : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s') → searchEffect (Pof w) a s' v → SearchReady v)
    (hbg : ∀ (s' : GalilVM) (v : SearchVM), searchEffect (Pof w) false s' v →
      v.search.mode ≠ .found)
    (hnfR : ∀ (s' : GalilVM) (v : SearchVM) (m : ℕ), 0 < m → s'.replay = ofNat m →
      searchEffect (Pof w) true s' v → v.search.mode ≠ .found)
    {n : ℕ} {x : State GalilVM} {c : Control} {t : GalilVM} {r : ℕ}
    (hx : x.ctl = GalilScaffoldController.initial delay)
    (hrun : StepsAll (galilFrameS (Pof w) (qof w) (firstOf w)) delay (SoundScanNR w) n x ⟨c, t⟩)
    (hm : c.mode = Mode.scan) (hclk : 1 ≤ c.clock)
    (hR : Restarted w t 0 reset)
    (hM : MInv w c t) (hfr : Frontier t) (hrest : ReplayRest c t)
    (hsr : SearchReady (searchLens.get t))
    (hrepl : t.replay = ofNat r) (hrp : c.replaying = decide (0 < r)) (hr0 : 0 < r)
    (hhead : ∃ xs rs : List (Fin 2),
      t.right.head = layout xs (rs.map some) [] ∧ w = xs.reverse ++ rs)
    (hlast : position t.right + r = 2 * w.length - 1) :
    ∃ y : State GalilVM,
      ScaffoldRun Pof qof firstOf delay w y ∧ ReportPoint w y ∧
        Refreshed (Pof w) (qof w) (firstOf w) y := by
  obtain ⟨es, c', y, -, ⟨k, x', hx', hall⟩, hrpt, hfrsh⟩ :=
    report_after_replay w (Pof w) hP hP' hex (qof w) (firstOf w) delay hd hsearch hpres hbg hnfR
      hx hrun hm hclk hR hM hfr hrest hsr hrepl hrp hr0 hhead hlast
  exact ⟨⟨c', y⟩, ⟨k, x', hx', stepsAll_mono (fun _ _ => trivial) hall⟩, hrpt, hfrsh⟩

#print axioms right_incoming_nil
#print axioms canRight_of_lt
#print axioms replay_countdown
#print axioms replay_one
#print axioms replay_run
#print axioms report_after_replay
#print axioms scaffoldRun_report_after_replay

end PalPeg.GalilReportReplay
