import PalPeg.GalilOracleLocal
import PalPeg.GalilReportComplete
import PalPeg.GalilReportReplay
import PalPeg.GalilReplayFound

/-!
# Report points at every prefix

`ReportPoint raw` pins the right head on the *last* letter of `raw`.  The
real-time ledger needs a checkpoint after every letter, so here the report
point is generalised to a prefix length `m`: the machine still reads the full
word `raw` (all heads `Represents … raw`), but the right head stands on the
`m`-th letter cell `2m - 1`.

* `refresh_exact_prefix` — at such a point a refreshed output is exactly
  `IsPal (raw.take m)` (packaging of `refresh_exact`);
* `reportAt_of_match` — a non-replaying matched comparison moving the right
  head from `2m - 2` onto `2m - 1` lands at a refreshed prefix report point;
* `reportAt_after_replay` — the replay whose counter ends on `2m - 1` lands at
  a refreshed prefix report point (the replay is generalised from the last
  letter to any target `m ≤ |raw|`: the right head can move because the full
  word still has material beyond it, `canRight_of_lt_word`);
* `latch_prefix` — at `m = |raw|` this is exactly `ReportPoint raw`.
-/

set_option autoImplicit false

namespace PalPeg.GalilReportPrefix

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.GalilSegmentConstruct PalPeg.GalilTickFun2 PalPeg.GalilBranchInvariants2
open PalPeg.GalilReportReplay
open PalPeg.GalilEndOfInput (layout_left_length layout_right layout_incoming)
open Manacher

/-! ## The prefix report point -/

/-- A report point for the prefix of length `m`, with the machine reading the whole
word `raw`. -/
structure ReportPointAt (raw : List (Fin 2)) (m : ℕ) (st : State GalilVM) : Prop where
  notReplaying : st.ctl.replaying = false
  scanInv : ∃ r : ℕ, ScanInvariant raw (position st.vm.center) r st.vm.left st.vm.right
  centre : MInv raw st.ctl st.vm
  atPlace : position st.vm.right = 2 * m - 1
  pos : 1 ≤ m
  le : m ≤ raw.length

/-- **(1)** At a prefix report point a refreshed output is the prefix palindrome flag. -/
theorem refresh_exact_prefix (raw : List (Fin 2)) (P : Shared) (hP : P.onLetter = onLetterVM raw)
    (hP' : P.leftFirst = leftFirstVM) (q : ℕ) (first : Fin 9) {m : ℕ} {st : State GalilVM}
    (hrp : ReportPointAt raw m st) (hfr : Refreshed P q first st) :
    st.ctl.output = true ↔ IsPal (raw.take m) := by
  obtain ⟨old, ho⟩ := hfr
  obtain ⟨r, hi⟩ := hrp.scanInv
  exact refresh_exact raw P hP hP' q first hi hrp.centre hrp.notReplaying
    (by have := hrp.pos; omega) hrp.le hrp.atPlace old st.ctl.output ho

/-- **(4)** The full-word prefix report point is the report point. -/
theorem latch_prefix (raw : List (Fin 2)) (st : State GalilVM) :
    ReportPointAt raw raw.length st ↔ ReportPoint raw st := by
  constructor
  · intro h
    exact ⟨h.notReplaying, h.scanInv, h.centre, h.atPlace, by have := h.pos; omega⟩
  · intro h
    exact ⟨h.notReplaying, h.scanInv, h.centre, h.atLast, by have := h.nonempty; omega, le_rfl⟩

/-- At `m = |raw|` the prefix flag is the whole-word flag. -/
theorem refresh_exact_full (raw : List (Fin 2)) (P : Shared) (hP : P.onLetter = onLetterVM raw)
    (hP' : P.leftFirst = leftFirstVM) (q : ℕ) (first : Fin 9) {st : State GalilVM}
    (hrp : ReportPoint raw st) (hfr : Refreshed P q first st) :
    st.ctl.output = true ↔ IsPal raw := by
  have h := refresh_exact_prefix raw P hP hP' q first ((latch_prefix raw st).2 hrp) hfr
  rwa [List.take_length] at h

/-! ## (2) The matched comparison onto `2m - 1` -/

/-- **(2)** A non-replaying matched comparison that moves the right head from `2m-2`
onto `2m-1` lands at a refreshed prefix report point. -/
theorem reportAt_of_match
    (w : List (Fin 2)) (P : Shared) (hP : P.onLetter = onLetterVM w)
    (hP' : P.leftFirst = leftFirstVM) (q : ℕ) (first : Fin 9) (delay : ℕ)
    {c : Control} {s : GalilVM} {m : ℕ}
    (hsrc : SoundScanNR w ⟨c, s⟩)
    (hm : c.mode = Mode.scan) (hclk : c.clock = 1) (hnr : c.replaying = false)
    (hav : canRight s.right) (hM : MInv w c s)
    {r : ℕ} (hi : ScanInvariant w (position s.center) r s.left s.right)
    (hpos : position s.right = 2 * m - 2) (hm1 : 1 ≤ m) (hmle : m ≤ w.length)
    (vs : ScanVM) (vq : SearchVM) (o : Bool) (bb : Bool)
    (hl : vs.left = GalilScaffoldInputHead.left s.left)
    (hrr : vs.right = right s.right)
    (hcmp : (galilFrameS P q first).compare s (afterBirth bb (afterCompare s vs vq)))
    (hmt : (galilFrameS P q first).matched (afterBirth bb (afterCompare s vs vq)))
    (ho : refresh (galilFrameS P q first) (afterBirth bb (afterCompare s vs vq)) c.output o) :
    (∃ k : ℕ, StepsAll (galilFrameS P q first) delay (SoundScanNR w) k ⟨c, s⟩
        ⟨{c with clock := delay, output := o, replaying := false}, afterBirth bb (afterCompare s vs vq)⟩) ∧
      ReportPointAt w m
        ⟨{c with clock := delay, output := o, replaying := false}, afterBirth bb (afterCompare s vs vq)⟩ ∧
      Refreshed P q first
        ⟨{c with clock := delay, output := o, replaying := false}, afterBirth bb (afterCompare s vs vq)⟩ := by
  have hmt0 : (galilFrame P q first).matched (scanLens.set s vs) := by
    have h0 : GalilScaffoldInputHead.read (afterBirth bb (afterCompare s vs vq)).left
      = GalilScaffoldInputHead.read (afterBirth bb (afterCompare s vs vq)).right := hmt
    rw [afterBirth_left, afterBirth_right] at h0
    exact h0
  have hmatch : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left s.left) =
      GalilScaffoldInputHead.read (right s.right) := by
    have h0 := matched_parts P q first hmt0
    rw [hl, hrr] at h0; exact h0
  have hi' : ScanInvariant w (position s.center) (r + 1)
      (afterBirth bb (afterCompare s vs vq)).left (afterBirth bb (afterCompare s vs vq)).right := by
    rw [afterBirth_left, afterBirth_right]
    exact matched_invariant' w vq hl hrr hmatch hav hi
  have hpl : (galilFrameS P q first).matchedPlace c.replaying (afterBirth bb (afterCompare s vs vq))
      (afterBirth bb (afterCompare s vs vq)) := by
    show afterBirth bb (afterCompare s vs vq) = (if c.replaying then _ else afterBirth bb (afterCompare s vs vq))
    rw [hnr]; simp
  have htick : Tick (galilFrameS P q first) delay ⟨c, s⟩
      ⟨{c with clock := delay, output := o, replaying := false}, afterBirth bb (afterCompare s vs vq)⟩ := by
    have h := Tick.scan_match (F := galilFrameS P q first) (delay := delay) c s
      (afterBirth bb (afterCompare s vs vq)) (afterBirth bb (afterCompare s vs vq)) o hm (Or.inr hav) hclk hcmp hmt hpl ho
    rw [hnr] at h
    simpa using h
  have hsound : SoundScanNR w
      ⟨{c with clock := delay, output := o, replaying := false}, afterBirth bb (afterCompare s vs vq)⟩ := by
    intro _ _
    exact outputRel_of_refreshS' w P hP hP' q first (afterBirth bb (afterCompare s vs vq)) c.output o hi' ho _ rfl
  have hp1 : position (right s.right) = position s.right + 1 :=
    right_position s.right hav (represented_position _ w hi.rightRep hi.rightPresent).1
  have hlast' : position (afterBirth bb (afterCompare s vs vq)).right = 2 * m - 1 := by
    rw [afterBirth_right, afterCompare_right, hrr, hp1, hpos]; omega
  refine ⟨⟨1, .succ hsrc htick (.zero _ hsound)⟩, ?_, ?_⟩
  · refine ⟨rfl, ⟨r + 1, ?_⟩, ?_, hlast', hm1, hmle⟩
    · rw [afterBirth_center, afterCompare_center]; exact hi'
    · exact minv_afterBirth bb (minv_match o delay hnr hl hrr hav hmatch hi hM)
  · exact ⟨c.output, (refreshS_iff P q first _ _ _).1 ho⟩

/-! ## (3) The replay ending on `2m - 1` -/

/-- A head reading the whole word can move right while short of its last letter cell,
whatever is still queued. -/
theorem canRight_of_lt_word {p : PlaceHead} {w : List (Fin 2)}
    (hrep : GalilScaffoldInputTrace.Represents p.head w)
    (hlt : position p < 2 * w.length - 1) : canRight p := by
  cases hg : p.gap with
  | false => exact Or.inl hg
  | true =>
    obtain ⟨xs, rs, qq, hh, hw⟩ := hrep
    have hlen : p.head.left.length = xs.length := by rw [hh]; exact layout_left_length _ _ _
    have hrr : p.head.right = (rs.map some) := by rw [hh]; exact layout_right _ _ _
    have hq : p.head.incoming = qq := by rw [hh]; exact layout_incoming _ _ _
    have hwlen : w.length = xs.length + rs.length + qq.length := by rw [hw]; simp; omega
    have hpos : position p = 2 * xs.length := by
      simp only [position, hg, if_true, hlen]
    rw [hpos, hwlen] at hlt
    by_cases hrs : rs = []
    · refine Or.inr (Or.inr ?_)
      rw [hq]
      intro h0
      rw [hrs, h0] at hlt; simp at hlt; omega
    · refine Or.inr (Or.inl ?_)
      rw [hrr]; simpa using hrs

/-- `replay_one` with the saved place at an arbitrary letter cell `2m-1`, `m ≤ |raw|`. -/
theorem replay_oneAt (raw : List (Fin 2)) (P : Shared) (hP : P.onLetter = onLetterVM raw)
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
    {c : Control} {s : GalilVM} {rad j m : ℕ}
    (hm : c.mode = Mode.scan) (hclk : 1 ≤ c.clock) (hrp : c.replaying = true)
    (hrepl : s.replay = ofNat (j + 1))
    (hidle : s.chain = ChainVM.idle) (hsr : SearchReady (searchLens.get s))
    (hM : MInv raw c s)
    (hi : ScanInvariant raw (position s.center) rad s.left s.right)
    (hmle : m ≤ raw.length)
    (hlast : position s.right + (j + 1) = 2 * m - 1) :
    ∃ (es : List Bool) (n : ℕ) (c' : Control) (t : GalilVM),
      WatchSegE P q first delay es c s c' t ∧
      StepsAll (galilFrameS P q first) delay (SoundScanNR raw) n ⟨c, s⟩ ⟨c', t⟩ ∧
      c'.mode = Mode.scan ∧ 1 ≤ c'.clock ∧ c'.replaying = decide (0 < j) ∧
      t.replay = ofNat j ∧ t.chain = ChainVM.idle ∧ SearchReady (searchLens.get t) ∧
      position t.right = position s.right + 1 ∧
      MInv raw c' t ∧ ScanInvariant raw (position t.center) (rad + 1) t.left t.right ∧
      Refreshed P q first ⟨c', t⟩ := by
  classical
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
  have hrepl1' : s1.replay = ofNat (j + 1) := by rw [hrepl1]; exact hrepl
  have hav : canRight s1.right :=
    canRight_of_lt_word hi1.rightRep (by rw [hr1]; omega)
  have hpos1 : position (right s1.right) = position s1.right + 1 :=
    right_position s1.right hav (represented_position _ raw hi1.rightRep hi1.rightPresent).1
  have hmatch : read (left s1.left) = read (right s1.right) :=
    replay_match_of_minv hM1 hrp1 hav hi1
  obtain ⟨vq, hq⟩ := hsearch s1 hsr1 true
  have hf : vq.search.mode ≠ .found := hnfR s1 vq (j + 1) (by omega) hrepl1' hq
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
  have hreplU : u.replay = ofNat j := by
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
  set c2 : Control :=
    { c1 with clock := delay, output := o, replaying := !P.replayExhausted u } with hc2def
  have hMU : MInv raw c2 u := minv_matchR P hex o delay hrp1 rfl hav hi1 hM1
  have hiU : ScanInvariant raw (position u.center) (rad + 1) u.left u.right := by
    have h0 := matched_invariant' raw vq (vs := vs) rfl rfl hmatch hav hi1
    rw [hudef, replayDec_left, replayDec_right, replayDec_center, afterCompare_center]
    exact h0
  have hzU : P.replayExhausted u = decide (j = 0) := by
    rw [hex, hreplU]
    cases j with
    | zero => simpa using (zero_ofNat_iff 0).2 rfl
    | succ i => simpa using zero_ofNat_succ i
  have htick : Tick (galilFrameS P q first) delay ⟨c1, s1⟩ ⟨c2, u⟩ := by
    have ht := scan_match_idle_S' P q first delay c1 s1 vs vq o hm1 (Or.inl hrp1) hclk1 hidle1
      rfl rfl rfl hmt hq hf (by rw [hrp1]; exact ho)
    rw [hrp1] at ht
    simpa using ht
  have hQU : SoundScanNR raw ⟨c2, u⟩ := by
    intro _ _
    exact outputRel_of_refresh' raw P hP hP' q first u c1.output o hiU ho c2 rfl
  refine ⟨es0 ++ [true], n0 + 1, c2, u, ?_, ?_, hm1, ?_, ?_, hreplU, hidleU, hsrU, hposU,
    hMU, hiU, ⟨c1.output, ho⟩⟩
  · refine watchSegE_trans P q first delay hseg0 ?_
    exact .matchIdleR c1 s1 vs vq o hm1 hrp1 hclk1 hav hidle1 rfl rfl rfl hmt hq hf ho (.stop _ _)
  · have h2 : StepsAll (galilFrameS P q first) delay (SoundScanNR raw) 1 ⟨c1, s1⟩ ⟨c2, u⟩ :=
      .succ (soundScanNR_of_replaying raw hrp1) htick (.zero _ hQU)
    simpa using stepsAll_trans hall0 h2
  · show 1 ≤ delay; exact hd
  · show (!P.replayExhausted u) = decide (0 < j)
    rw [hzU]; cases j <;> simp

/-- `replay_run` with the saved place at an arbitrary letter cell `2m-1`, `m ≤ |raw|`. -/
theorem replay_runAt (raw : List (Fin 2)) (P : Shared) (hP : P.onLetter = onLetterVM raw)
    (hP' : P.leftFirst = leftFirstVM)
    (hex : ∀ s, P.replayExhausted s = zero s.replay)
    (q : ℕ) (first : Fin 9) (delay : ℕ) (hd : 1 ≤ delay)
    (hsearch : ∀ s' : GalilVM, SearchReady (searchLens.get s') → ∀ a : Bool,
      ∃ v, searchEffect P a s' v)
    (hpres : ∀ (s' : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s') → searchEffect P a s' v → SearchReady v)
    (hbg : ∀ (s' : GalilVM) (v : SearchVM), searchEffect P false s' v → v.search.mode ≠ .found)
    (hnfR : ∀ (s' : GalilVM) (v : SearchVM) (m : ℕ), 0 < m → s'.replay = ofNat m →
      searchEffect P true s' v → v.search.mode ≠ .found) (m : ℕ) (hmle : m ≤ raw.length) :
    ∀ (j : ℕ) (c : Control) (s : GalilVM) (rad : ℕ),
      c.mode = Mode.scan → 1 ≤ c.clock → c.replaying = true →
      s.replay = ofNat (j + 1) → s.chain = ChainVM.idle → SearchReady (searchLens.get s) →
      MInv raw c s → ScanInvariant raw (position s.center) rad s.left s.right →
      position s.right + (j + 1) = 2 * m - 1 →
      ∃ (es : List Bool) (n : ℕ) (c' : Control) (t : GalilVM),
        WatchSegE P q first delay es c s c' t ∧
        StepsAll (galilFrameS P q first) delay (SoundScanNR raw) n ⟨c, s⟩ ⟨c', t⟩ ∧
        c'.mode = Mode.scan ∧ c'.replaying = false ∧
        position t.right = 2 * m - 1 ∧
        t.chain = ChainVM.idle ∧ MInv raw c' t ∧
        (∃ rad', ScanInvariant raw (position t.center) rad' t.left t.right) ∧
        Refreshed P q first ⟨c', t⟩ := by
  intro j
  induction j with
  | zero =>
    intro c s rad hm hclk hrp hrepl hidle hsr hM hi hlast
    obtain ⟨es, n, c', t, hseg, hall, hm', -, hrp', -, hidle', -, hposR, hMt, hit, hfr⟩ :=
      replay_oneAt raw P hP hP' hex q first delay hd hsearch hpres hbg hnfR hm hclk hrp hrepl
        hidle hsr hM hi hmle hlast
    exact ⟨es, n, c', t, hseg, hall, hm', by simpa using hrp', by omega, hidle', hMt,
      ⟨rad + 1, hit⟩, hfr⟩
  | succ i ih =>
    intro c s rad hm hclk hrp hrepl hidle hsr hM hi hlast
    obtain ⟨es1, n1, c1, t1, hseg1, hall1, hm1, hclk1, hrp1, hrepl1, hidle1, hsr1, hposR,
      hMt, hit, -⟩ :=
      replay_oneAt raw P hP hP' hex q first delay hd hsearch hpres hbg hnfR hm hclk hrp hrepl
        hidle hsr hM hi hmle hlast
    have hrp1' : c1.replaying = true := by simpa using hrp1
    obtain ⟨es2, n2, c2, t2, hseg2, hall2, hm2, hrp2, hpos2, hidle2, hM2, hi2, hfr2⟩ :=
      ih c1 t1 (rad + 1) hm1 hclk1 hrp1' hrepl1 hidle1 hsr1 hMt hit (by omega)
    exact ⟨es1 ++ es2, n1 + n2, c2, t2, watchSegE_trans P q first delay hseg1 hseg2,
      stepsAll_trans hall1 hall2, hm2, hrp2, hpos2, hidle2, hM2, hi2, hfr2⟩

/-- **(3)** The replay whose saved place is the letter cell `2m-1` lands at a refreshed
prefix report point (generalises `report_after_replay_of_halted_local`). -/
theorem reportAt_after_replay (raw : List (Fin 2)) (P : Shared)
    (hP : P.onLetter = onLetterVM raw) (hP' : P.leftFirst = leftFirstVM)
    (hex : ∀ s, P.replayExhausted s = zero s.replay)
    (q : ℕ) (first : Fin 9) (delay : ℕ) (hd : 1 ≤ delay)
    (hsearch : ∀ s' : GalilVM, SearchReady (searchLens.get s') → ∀ a : Bool,
      ∃ v, searchEffect P a s' v)
    (hpres : ∀ (s' : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s') → searchEffect P a s' v → SearchReady v)
    (hbg : ∀ (s' : GalilVM) (v : SearchVM), searchEffect P false s' v → v.search.mode ≠ .found)
    (hhalt : ∀ (s' : GalilVM) (m : ℕ), 0 < m → s'.replay = ofNat m →
      PalPeg.GalilReplayFound.SearchHalted s')
    {c : Control} {t : GalilVM} {r m rad : ℕ}
    (hm : c.mode = Mode.scan) (hclk : 1 ≤ c.clock)
    (hidle : t.chain = ChainVM.idle)
    (hi : ScanInvariant raw (position t.center) rad t.left t.right)
    (hM : MInv raw c t)
    (hsr : SearchReady (searchLens.get t))
    (hrepl : t.replay = ofNat r) (hrp : c.replaying = decide (0 < r)) (hr0 : 0 < r)
    (hm1 : 1 ≤ m) (hmle : m ≤ raw.length)
    (hlast : position t.right + r = 2 * m - 1) :
    ∃ (es : List Bool) (c' : Control) (y : GalilVM),
      WatchSegE P q first delay es c t c' y ∧
      (∃ k : ℕ, StepsAll (galilFrameS P q first) delay (SoundScanNR raw) k ⟨c, t⟩ ⟨c', y⟩) ∧
      ReportPointAt raw m ⟨c', y⟩ ∧ Refreshed P q first ⟨c', y⟩ := by
  obtain ⟨j, rfl⟩ : ∃ j, r = j + 1 := ⟨r - 1, by omega⟩
  have hrp' : c.replaying = true := by rw [hrp]; simp
  obtain ⟨es, k, c', y, hseg, hall, -, hrpF, hposF, -, hMF, hiF, hfrF⟩ :=
    replay_runAt raw P hP hP' hex q first delay hd hsearch hpres hbg
      (PalPeg.GalilReplayFound.not_found_during_replay P hhalt) m hmle j c t rad hm hclk hrp'
      hrepl hidle hsr hM hi hlast
  exact ⟨es, c', y, hseg, ⟨k, hall⟩, ⟨hrpF, hiF, hMF, hposF, hm1, hmle⟩, hfrF⟩

#print axioms refresh_exact_prefix
#print axioms latch_prefix
#print axioms refresh_exact_full
#print axioms reportAt_of_match
#print axioms canRight_of_lt_word
#print axioms replay_oneAt
#print axioms replay_runAt
#print axioms reportAt_after_replay

end PalPeg.GalilReportPrefix
