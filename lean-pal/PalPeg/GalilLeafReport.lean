import PalPeg.GalilOracleLeaves2
import PalPeg.GalilOracleMC3

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.GalilLeafReport

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton PalPeg.GalilOracleDischarge PalPeg.GalilOracleLocal
open PalPeg.GalilCheckpoints PalPeg.GalilTraceCost PalPeg.GalilLexMeasure
open PalPeg.GalilInvPlus PalPeg.GalilInvPlus2 PalPeg.GalilOracleMC
open PalPeg.GalilGlueBLeaves PalPeg.GalilBranchInvariants2 PalPeg.GalilSegmentConstruct
open PalPeg.GalilOracleM PalPeg.GalilOracleMC2 PalPeg.GalilOracleLeaves2
open PalPeg.GalilOneFallback PalPeg.GalilCostedFallback
open PalPeg.GalilOracleMC3

/-! ## 0. Three elementary facts about `WatchSegE` -/

/-- A list with at least `k+1` `true`s splits at its `(k+1)`-st `true`. -/
theorem split_nth_true : ∀ (es : List Bool) (k : ℕ), k + 1 ≤ es.count true →
    ∃ es1 es2 : List Bool, es = es1 ++ true :: es2 ∧ es1.count true = k := by
  intro es
  induction es with
  | nil => intro k h; simp at h
  | cons a es ih =>
    intro k h
    cases a with
    | false =>
      obtain ⟨es1, es2, h1, h2⟩ := ih k (by simpa using h)
      exact ⟨false :: es1, es2, by rw [h1]; rfl, by simpa using h2⟩
    | true =>
      cases k with
      | zero => exact ⟨[], es, rfl, by simp⟩
      | succ k =>
        obtain ⟨es1, es2, h1, h2⟩ := ih k (by simp at h; omega)
        exact ⟨true :: es1, es2, by rw [h1]; rfl, by simp [h2]⟩

/-- A segment entered without a replay in progress stays out of a replay. -/
theorem watchSegE_notReplaying (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) {es : List Bool}
    {c c' : Control} {s t : GalilVM} (h : WatchSegE P q first delay es c s c' t) :
    c.replaying = false → c'.replaying = false := by
  induction h with
  | stop c s => exact id
  | wait c s s' _ hr _ _ _ ih => exact fun _ => ih hr
  | count c s s' _ hr _ _ _ _ ih => exact fun _ => ih hr
  | «match» c s vs vq o _ _ _ _ _ _ _ _ _ _ ih => exact fun _ => ih rfl
  | matchIdle c s vs vq o _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact fun _ => ih rfl
  | countR c s s' _ hr _ _ _ _ _ => exact fun h0 => by rw [h0] at hr; exact absurd hr (by simp)
  | matchIdleR c s vs vq o _ hr _ _ _ _ _ _ _ _ _ _ _ _ =>
      exact fun h0 => by rw [h0] at hr; exact absurd hr (by simp)

/-- `SearchReady` is carried along a segment by the preservation leaf. -/
theorem watchSegE_searchReady (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s) → searchEffect P a s v → SearchReady v)
    {es : List Bool} {c c' : Control} {s t : GalilVM}
    (h : WatchSegE P q first delay es c s c' t) :
    SearchReady (searchLens.get s) → SearchReady (searchLens.get t) := by
  induction h with
  | stop c s => exact id
  | wait c s s' _ _ _ hb _ ih =>
      intro hsr
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hse⟩ := backgroundS_fields P q first hb
      exact ih (hpres s false _ hsr hse)
  | count c s s' _ _ _ _ hb _ ih =>
      intro hsr
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hse⟩ := backgroundS_fields P q first hb
      exact ih (hpres s false _ hsr hse)
  | countR c s s' _ _ _ _ hb _ ih =>
      intro hsr
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hse⟩ := backgroundS_fields P q first hb
      exact ih (hpres s false _ hsr hse)
  | «match» c s vs vq o _ _ _ _ _ _ _ hq _ _ ih => exact fun hsr => ih (hpres s true vq hsr hq)
  | matchIdle c s vs vq o _ _ _ _ _ _ _ _ _ hq _ _ _ ih =>
      exact fun hsr => ih (hpres s true vq hsr hq)
  | matchIdleR c s vs vq o _ _ _ _ _ _ _ _ _ hq _ _ _ ih =>
      exact fun hsr => ih (hpres s true vq hsr hq)

#print axioms split_nth_true
#print axioms watchSegE_notReplaying
#print axioms watchSegE_searchReady

/-! ## 1. Splitting a segment at the target letter cell -/

/-- The scan-mode data of an `InvS` entry (the opening of `segment_of_invLPC`). -/
theorem invS_entry_data {raw : List (Fin 2)} {c : Control} {r : GalilVM} (hI : InvS raw c r) :
    c.mode = Mode.scan ∧ 1 ≤ c.clock ∧ r.chain = ChainVM.idle ∧
      SearchReady (searchLens.get r) ∧ MInv raw c r ∧
      ∃ R : ℕ, ScanInvariant raw (position r.center) R r.left r.right ∧ Frontier r ∧
        ReplayRest c r ∧ ShiftIdle r := by
  rcases hI with h | ⟨k, h⟩
  · obtain ⟨Rad, last, hR⟩ := h.rest
    exact ⟨h.mode.1, by rw [h.mode.2.2]; omega, hR.1, h.search, h.minv, Rad,
      hR.2.2.2.1, h.frontier, h.rest_replay, h.shiftIdle⟩
  · exact ⟨h.mode.1, by rw [h.mode.2.2]; omega, h.chainIdle, h.search, h.minv, k,
      h.scan, h.frontier, h.rest_replay, h.shiftIdle⟩

/-- **The crossing lemma.**  A segment that enters strictly below the letter cell
`2m-1` and reaches at least that cell passes through a state that is
`SegReachedW` *and* `AtTarget m`, and whose next tick is the matching comparison
onto `2m-1`; `reachAtC2_of_target_match` then applies at that state. -/
theorem reachAtC2_of_cross (centre : GalilVM -> Fin 3)
    (place : GalilVM -> GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2))
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s) →
      searchEffect (PofC centre place entry raw) a s v → SearchReady v)
    (m : ℕ) (hm1 : 1 ≤ m) (hmle : m ≤ raw.length)
    {c c' : Control} {r t : GalilVM} (hIC : InvLPC raw c r)
    (hsW : SegReachedW centre place entry q first raw c r c' t)
    (hlt : position r.right < 2 * m - 1) (hge : 2 * m - 1 ≤ position t.right) :
    ReachAtC2 (PofC centre place entry raw) q first raw m c r := by
  classical
  have hI : InvL raw c r := invLPC_invL hIC
  obtain ⟨hs, es, hw⟩ := hsW
  obtain ⟨hmC, hclkC, hidleC, hsrC, hMC, R0, hi0, hfrC, hrrC, hsiC⟩ := invS_entry_data hI.1
  have hnrC : c.replaying = false := (invS_mode hI.1).2
  have hposT : position t.right = position r.right + es.count true :=
    (watchSegE_right_position raw (PofC centre place entry raw) q first 2048 hw hi0).2
  obtain ⟨es1, es2, hsplit, hcnt1⟩ :=
    split_nth_true es (2 * m - 2 - position r.right) (by omega)
  obtain ⟨c1, s1, hw1, hw2⟩ :=
    watchSegE_append (PofC centre place entry raw) q first 2048 es1 (by rw [← hsplit]; exact hw)
  have hi1 : ScanInvariant raw (position r.center) (R0 + es1.count true) s1.left s1.right :=
    scanInvariant_watchSegE (PofC centre place entry raw) q first 2048 hw1 hi0
  have hpos1 : position s1.right = position r.right + es1.count true :=
    (watchSegE_right_position raw (PofC centre place entry raw) q first 2048 hw1 hi0).2
  have hpos1' : position s1.right = 2 * m - 2 := by rw [hpos1, hcnt1]; omega
  have hcen1 : s1.center = r.center :=
    watchSegE_center (PofC centre place entry raw) q first 2048 hw1
  have hnr1 : c1.replaying = false :=
    watchSegE_notReplaying (PofC centre place entry raw) q first 2048 hw1 hnrC
  have hidle1 : s1.chain = ChainVM.idle :=
    watchSegE_idle_start (PofC centre place entry raw) q first 2048 hw2 hs.idle
  have hmode1 : c1.mode = Mode.scan := by
    obtain ⟨av, -, -, -, hmo⟩ := watchSegE_clock (PofC centre place entry raw) q first 2048 hw1
    rw [hmo, hmC]
  have hsr1 : SearchReady (searchLens.get s1) :=
    watchSegE_searchReady (PofC centre place entry raw) q first 2048 hpres hw1 hsrC
  have hM1 : MInv raw c1 s1 :=
    minv_watchSegE raw (PofC centre place entry raw) (fun s => hex_C centre place entry raw s)
      q first 2048 hw1 R0 hi0 hMC
  have hsteps1 : Steps (galilFrameS (PofC centre place entry raw) q first) 2048 es1.length
      ⟨c, r⟩ ⟨c1, s1⟩ := watchSegE_steps_length _ q first 2048 hw1
  have hfr1 : Frontier s1 ∧ ReplayRest c1 s1 :=
    frontier_replayRest_of_scan (onLetterVM raw) leftFirstVM centre place entry q first 2048
      hsteps1 hmC (hlive_of_invLPC centre place entry q first hIC) hfrC hrrC
  have hsi1 : ShiftIdle s1 := by
    rw [shiftIdle_iff, watchSegE_remaining _ q first 2048 hw1]
    exact (shiftIdle_iff r).1 hsiC
  have hrep1 : s1.replay = reset := hfr1.2 (Or.inl hnr1)
  have hrun1 : ∃ k, StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048
      (SoundScanNR raw) k ⟨c, r⟩ ⟨c1, s1⟩ :=
    ⟨es1.length, seg_run centre place entry q first raw hI hw1⟩
  cases hw2 with
  | «match» _ _ vs vq o _ _ _ _ hne2 _ _ _ _ _ => exact absurd hidle1 hne2
  | matchIdleR _ _ vs vq o _ hr2 _ _ _ _ _ _ _ _ _ _ _ => rw [hnr1] at hr2; exact absurd hr2 (by simp)
  | matchIdle _ _ vs vq o hm2 hr2 ha2 hc2 hidle2 hl2 hrr2 hvs2 hmt2 hq2 hnf2 ho2 rest =>
      have hmtread : read (left s1.left) = read (right s1.right) := by
        have h0 := matched_parts (PofC centre place entry raw) q first hmt2
        rw [hl2, hrr2] at h0; exact h0
      have hsW1 : SegReachedW centre place entry q first raw c r c1 s1 :=
        ⟨{ run := hrun1
           center := hcen1
           mode := hmode1
           clock := by omega
           idle := hidle1
           minv := hM1
           search := hsr1
           input := hi1.rightRep
           frontier := hfr1.1
           shiftIdle := hsi1
           scan := ⟨R0 + es1.count true, by rw [hcen1]; exact hi1⟩ }, es1, hw1⟩
      exact reachAtC2_of_target_match centre place entry q first raw m hm1 hmle hpres
        c r c1 s1 hIC hsW1 ⟨hnr1, hc2, ha2, hpos1', hrep1⟩ hmtread vq hq2 hnf2

#print axioms invS_entry_data
#print axioms reachAtC2_of_cross

/-! ## 2. The two named residues -/

/-- **Named residue (1): `EntryRefreshed`.**  A cycle whose entering right head
*already* stands on the target letter cell `2m-1` reports there and then, so the
entering state must be a refreshed one.  `InvLPC` carries `MInv`, the scan
invariant and `replaying = false`, i.e. every field of `ReportPointAt` but the
refreshed output, which no invariant of the recursion records. -/
def EntryRefreshed (centre : GalilVM -> Fin 3) (place : GalilVM -> GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9) : Prop :=
  ∀ (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM), 1 ≤ m → m ≤ w.length →
    InvLPC w c r → position r.right = 2 * m - 1 →
    Refreshed (PofC centre place entry w) q first ⟨c, r⟩

/-- **Named residue (2): `LastMismatchReport`.**  The segment stops on the final
letter with a *mismatch* and the target is the whole word (`m = |w|`): no
comparison of the segment ever lands on `2|w|-1`, and the report point is the one
produced by the fallback and its replay
(`GalilOracleLocal.report_after_replay_of_halted_local` /
`GalilReportPrefix.reportAt_after_replay`), at the costed strength. -/
def LastMismatchReport (centre : GalilVM -> Fin 3) (place : GalilVM -> GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9) : Prop :=
  ∀ (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
    1 ≤ m → m = w.length → InvLPC w c r → position r.right ≤ 2 * m - 1 →
    SegReachedW centre place entry q first w c r c' t →
    c'.clock = 1 → canRight t.right → PopsIncoming t.right →
    (∃ a : Fin 2, t.right.head.incoming = [a]) →
    read (left t.left) ≠ read (right t.right) →
    ReachAtC2 (PofC centre place entry w) q first w m c r

/-! ## 3. The entering state is already the report point -/

theorem reachAtC2_of_entry (centre : GalilVM -> Fin 3)
    (place : GalilVM -> GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m : ℕ) (hm1 : 1 ≤ m) (hmle : m ≤ raw.length)
    {c : Control} {r : GalilVM} (hIC : InvLPC raw c r)
    (hre : Refreshed (PofC centre place entry raw) q first ⟨c, r⟩)
    (hpos : position r.right = 2 * m - 1) :
    ReachAtC2 (PofC centre place entry raw) q first raw m c r := by
  have hI : InvL raw c r := invLPC_invL hIC
  obtain ⟨hmC, hclkC, hidleC, hsrC, hMC, R0, hi0, hfrC, hrrC, hsiC⟩ := invS_entry_data hI.1
  have hnrC : c.replaying = false := (invS_mode hI.1).2
  have hsound : SoundScanNR raw (⟨c, r⟩ : State GalilVM) := fun _ _ => hI.2
  exact ⟨⟨c, r⟩, 0, [], .zero _ hsound, costedRun_nil r,
    ⟨hnrC, ⟨R0, hi0⟩, hMC, hpos, hm1, hmle⟩, hre,
    fun _ => ⟨c, r, 0, [], .zero _ hsound, costedRun_nil r, hIC, by omega⟩⟩

/-! ## 4. `hended` -/

/-- **`hended`, closed** (modulo `EntryRefreshed`).  `GalilEndOfInput` puts a
blocked right head on the final gap `2|w|`, strictly past every target cell
`2m-1`, so the report point lies strictly inside the segment. -/
theorem hended_C (centre : GalilVM -> Fin 3) (place : GalilVM -> GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9)
    (hpres : ∀ (w : List (Fin 2)) (s : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s) →
      searchEffect (PofC centre place entry w) a s v → SearchReady v)
    (hentry : EntryRefreshed centre place entry q first)
    (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM)
    (hm1 : 1 ≤ m) (hmle : m ≤ w.length) (hIC : InvLPC w c r)
    (hp : position r.right ≤ 2 * m - 1)
    (hsW : SegReachedW centre place entry q first w c r c' t) (hn : ¬ canRight t.right) :
    ReachAtC2 (PofC centre place entry w) q first w m c r := by
  obtain ⟨R, hiT⟩ := hsW.1.scan
  have hend : position t.right = 2 * w.length :=
    (PalPeg.GalilEndOfInput.not_canRight_iff t.right w hsW.1.input hiT.rightPresent).1 hn
  rcases Nat.lt_or_ge (position r.right) (2 * m - 1) with hlt | hge
  · exact reachAtC2_of_cross centre place entry q first w (hpres w) m hm1 hmle hIC hsW hlt
      (by omega)
  · exact reachAtC2_of_entry centre place entry q first w m hm1 hmle hIC
      (hentry w m c r hm1 hmle hIC (by omega)) (by omega)

/-! ## 4b. The target comparison when the search reports `found` -/

/-- `CostedRun` only looks at the end state's centre and right head. -/
theorem costedRun_congr_end {a b b' : GalilVM} {k : ℕ} {L : List Piece}
    (h : CostedRun a b k L) (hc : b'.center = b.center) (hr : b'.right = b.right) :
    CostedRun a b' k L :=
  ⟨h.ticks, by rw [hc]; exact h.centre, by rw [hr]; exact h.right_mono,
    by intro p hp; rw [hr]; exact h.places p hp, h.sep⟩

/-- **`reachAtC2_of_target_match` without `hnf`, for the whole-word target.**
`GalilLeafQuiet` refutes `SearchQuiet`, so the comparison onto `2m-1` may well be
the tick on which the search reports `found` and the chain starts.  The report
point is the comparison itself (`reportAt_of_match` does not look at the chain),
and at `m = |raw|` the `InvLPC` continuation of `ReachAtC2` is vacuous, which is
exactly the part the chain start would break. -/
theorem reachAtC2_of_target_match_found (centre : GalilVM -> Fin 3)
    (place : GalilVM -> GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m : ℕ) (hm1 : 1 ≤ m) (hmle : m ≤ raw.length)
    (hfull : raw.length ≤ m)
    (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM) (hIC : InvLPC raw c r)
    (hsW : SegReachedW centre place entry q first raw c r c' t)
    (hT : AtTarget m c' t)
    (hmt : read (left t.left) = read (right t.right))
    (vq : SearchVM) (hq : searchEffect (PofC centre place entry raw) true t vq)
    (hf : vq.search.mode = .found) :
    ReachAtC2 (PofC centre place entry raw) q first raw m c r := by
  classical
  set P : Shared := PofC centre place entry raw with hP
  have hI : InvL raw c r := invLPC_invL hIC
  obtain ⟨hs, es, hw⟩ := hsW
  obtain ⟨hnr, hc1, hav, hpos, hrep⟩ := hT
  obtain ⟨⟨R0, hi0⟩, hc0, -⟩ := invL_entry hI
  have hrun0 := seg_run centre place entry q first raw hI hw
  obtain ⟨R, hi⟩ := hs.scan
  obtain ⟨ch, hchm⟩ : ∃ ch : ChainVM, ChainMatched
      (chainStart (vq.dp.config.tapes 11) (P.centre t) (P.place t) t.center t.radius) ch :=
    ⟨_, ChainMatched.copy _ _ _ _ _ _ _⟩
  set vs : ScanVM := ⟨left t.left, right t.right, ch⟩ with hvs
  have hmt0 : (galilFrame P q first).matched (scanLens.set t vs) := hmt
  have hcmp : (galilFrameS P q first).compare t (afterBirth true (afterCompare t vs vq)) :=
    ⟨vs, vq, true, rfl, rfl, ⟨fun _ => hmt0, fun _ => rfl⟩, hq,
      Or.inr (Or.inr ⟨hs.idle, by simp [hf], by simpa using hchm⟩),
      by rw [hs.idle, chainBorn, ChainVM.isIdle, hf]; rfl⟩
  have hmt1 : (galilFrameS P q first).matched (afterBirth true (afterCompare t vs vq)) := by
    show GalilScaffoldInputHead.read (afterBirth true (afterCompare t vs vq)).left
      = GalilScaffoldInputHead.read (afterBirth true (afterCompare t vs vq)).right
    rw [afterBirth_left, afterBirth_right]
    exact hmt
  set u : GalilVM := afterBirth true (afterCompare t vs vq) with hu
  set o : Bool := if P.onLetter u then decide (P.leftFirst u) else c'.output with ho'
  have ho : refresh (galilFrameS P q first) u c'.output o := by
    refine ⟨fun hl => ?_, fun hl => ?_⟩
    · have hl' : P.onLetter u := hl
      show (if P.onLetter u then decide (P.leftFirst u) else c'.output) = true ↔ P.leftFirst u
      rw [if_pos hl']; exact decide_eq_true_iff
    · have hl' : ¬ P.onLetter u := hl
      show (if P.onLetter u then decide (P.leftFirst u) else c'.output) = c'.output
      rw [if_neg hl']
  have hsrc : SoundScanNR raw ⟨c', t⟩ := stepsAll_last hrun0
  obtain ⟨⟨k1, hrun1⟩, hrp, hfr⟩ :=
    PalPeg.GalilReportPrefix.reportAt_of_match raw P rfl rfl q first 2048 hsrc hs.mode hc1 hnr
      hav hs.minv hi hpos hm1 hmle vs vq o true rfl rfl hcmp hmt1 ho
  have hsound := stepsAll_last hrun1
  have hpl : (galilFrameS P q first).matchedPlace c'.replaying u u := by
    show u = (if c'.replaying then _ else u)
    rw [hnr]; simp
  have htick : Tick (galilFrameS P q first) 2048 ⟨c', t⟩
      ⟨{c' with clock := 2048, output := o, replaying := false}, u⟩ := by
    have h := Tick.scan_match (F := galilFrameS P q first) (delay := 2048) c' t u u o hs.mode
      (Or.inr hav) hc1 hcmp hmt1 hpl ho
    rw [hnr] at h
    simpa using h
  have hall := stepsAll_trans hrun0 (.succ hsrc htick (.zero _ hsound))
  obtain ⟨L, wt, hwt, hcr, -, -⟩ :=
    GalilCostedFallback.costedRun_target_match raw P q first hw hi0 hc0 hc1 hav m hm1 hpos vq
  exact ⟨_, es.length + (0 + 1), L ++ [GalilCostedFallback.cmpPiece (2 * m - 1) wt hwt], hall,
    costedRun_congr_end hcr rfl rfl, hrp, hfr, fun hlt => absurd hlt (by omega)⟩

/-! ## 5. The last-letter exits -/

/-- At the `lastLetter` exit the right head stands on `2|w|-2`. -/
theorem lastLetter_position (centre : GalilVM -> Fin 3)
    (place : GalilVM -> GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    {w : List (Fin 2)} {c c' : Control} {r t : GalilVM}
    (hsW : SegReachedW centre place entry q first w c r c' t)
    (hav : canRight t.right) (hpop : PopsIncoming t.right) {a : Fin 2}
    (hinc : t.right.head.incoming = [a]) :
    position t.right = 2 * w.length - 2 ∧ 0 < w.length := by
  obtain ⟨R, hiT⟩ := hsW.1.scan
  obtain ⟨-, hlast, hne⟩ :=
    PalPeg.GalilReportReach.last_consume_geometry hsW.1.input hpop hinc
  have hstep : position (right t.right) = position t.right + 1 :=
    right_position t.right hav (represented_position _ w hiT.rightRep hiT.rightPresent).1
  exact ⟨by omega, hne⟩

/-- **`hlastMatch`, closed** (modulo `EntryRefreshed`).  Either the target cell is
crossed strictly inside the segment, or `m = |w|` and the last comparison itself
lands on `2m-1`. -/
theorem hlastMatch_C (centre : GalilVM -> Fin 3) (place : GalilVM -> GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9)
    (hsearch : ∀ (w : List (Fin 2)) (s : GalilVM), SearchReady (searchLens.get s) →
      ∀ a : Bool, ∃ v, searchEffect (PofC centre place entry w) a s v)
    (hpres : ∀ (w : List (Fin 2)) (s : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s) →
      searchEffect (PofC centre place entry w) a s v → SearchReady v)
    (hentry : EntryRefreshed centre place entry q first)
    (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM)
    (hm1 : 1 ≤ m) (hmle : m ≤ w.length) (hIC : InvLPC w c r)
    (hp : position r.right ≤ 2 * m - 1)
    (hsW : SegReachedW centre place entry q first w c r c' t)
    (hc : c'.clock = 1) (hav : canRight t.right) (hpop : PopsIncoming t.right)
    (hinc : ∃ a : Fin 2, t.right.head.incoming = [a])
    (hmt : read (left t.left) = read (right t.right)) :
    ReachAtC2 (PofC centre place entry w) q first w m c r := by
  obtain ⟨a, hinc⟩ := hinc
  obtain ⟨hposT, hwne⟩ := lastLetter_position centre place entry q first hsW hav hpop hinc
  rcases Nat.lt_or_ge (position r.right) (2 * m - 1) with hlt | hge
  · rcases Nat.lt_or_ge (position t.right) (2 * m - 1) with h2 | h2
    · -- `2m-1 > 2|w|-2` forces `m = |w|`, so `t` itself is `AtTarget m`
      have hI : InvL w c r := invLPC_invL hIC
      obtain ⟨hmC, hclkC, hidleC, hsrC, hMC, R0, hi0, hfrC, hrrC, hsiC⟩ := invS_entry_data hI.1
      have hnrC : c.replaying = false := (invS_mode hI.1).2
      obtain ⟨es, hw⟩ := hsW.2
      have hnrT : c'.replaying = false :=
        watchSegE_notReplaying (PofC centre place entry w) q first 2048 hw hnrC
      have hstepsT : Steps (galilFrameS (PofC centre place entry w) q first) 2048 es.length
          ⟨c, r⟩ ⟨c', t⟩ := watchSegE_steps_length _ q first 2048 hw
      have hfrT : Frontier t ∧ ReplayRest c' t :=
        frontier_replayRest_of_scan (onLetterVM w) leftFirstVM centre place entry q first 2048
          hstepsT hmC (hlive_of_invLPC centre place entry q first hIC) hfrC hrrC
      obtain ⟨vq, hq⟩ := hsearch w t hsW.1.search true
      have hT : AtTarget m c' t := ⟨hnrT, hc, hav, by omega, hfrT.2 (Or.inl hnrT)⟩
      by_cases hf : vq.search.mode = .found
      · exact reachAtC2_of_target_match_found centre place entry q first w m hm1 hmle
          (by omega) c r c' t hIC hsW hT hmt vq hq hf
      · exact reachAtC2_of_target_match centre place entry q first w m hm1 hmle (hpres w)
          c r c' t hIC hsW hT hmt vq hq hf
    · exact reachAtC2_of_cross centre place entry q first w (hpres w) m hm1 hmle hIC hsW hlt h2
  · exact reachAtC2_of_entry centre place entry q first w m hm1 hmle hIC
      (hentry w m c r hm1 hmle hIC (by omega)) (by omega)

/-- **`hlastMismatch`, closed** (modulo `EntryRefreshed` and `LastMismatchReport`).
The mismatching last comparison never lands on `2|w|-1`, so only the crossing
case and the entering case are discharged here. -/
theorem hlastMismatch_C (centre : GalilVM -> Fin 3) (place : GalilVM -> GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9)
    (hpres : ∀ (w : List (Fin 2)) (s : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s) →
      searchEffect (PofC centre place entry w) a s v → SearchReady v)
    (hentry : EntryRefreshed centre place entry q first)
    (hlast : LastMismatchReport centre place entry q first)
    (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM)
    (hm1 : 1 ≤ m) (hmle : m ≤ w.length) (hIC : InvLPC w c r)
    (hp : position r.right ≤ 2 * m - 1)
    (hsW : SegReachedW centre place entry q first w c r c' t)
    (hc : c'.clock = 1) (hav : canRight t.right) (hpop : PopsIncoming t.right)
    (hinc : ∃ a : Fin 2, t.right.head.incoming = [a])
    (hmt : read (left t.left) ≠ read (right t.right)) :
    ReachAtC2 (PofC centre place entry w) q first w m c r := by
  obtain ⟨a, hinc'⟩ := hinc
  obtain ⟨hposT, hwne⟩ := lastLetter_position centre place entry q first hsW hav hpop hinc'
  rcases Nat.lt_or_ge (position r.right) (2 * m - 1) with hlt | hge
  · rcases Nat.lt_or_ge (position t.right) (2 * m - 1) with h2 | h2
    · exact hlast w m c r c' t hm1 (by omega) hIC hp hsW hc hav hpop ⟨a, hinc'⟩ hmt
    · exact reachAtC2_of_cross centre place entry q first w (hpres w) m hm1 hmle hIC hsW hlt h2
  · exact reachAtC2_of_entry centre place entry q first w m hm1 hmle hIC
      (hentry w m c r hm1 hmle hIC (by omega)) (by omega)

#print axioms reachAtC2_of_entry
#print axioms hended_C
#print axioms lastLetter_position
#print axioms reachAtC2_of_target_match_found
#print axioms hlastMatch_C
#print axioms hlastMismatch_C

/-! ## 6. `H_oracle` with the three report leaves discharged -/

open PalPeg.GalilFinalAssembly PalPeg.GalilFinalAssembly2 in
/-- **`GalilOracleMC3.h_oracle_of_leaves''` with `hended`, `hlastMatch` and
`hlastMismatch` discharged**, at the cost of the two named residues
`EntryRefreshed` and `LastMismatchReport`.  `hquiet` is gone (it is false, see
`GalilLeafQuiet`): the target comparison is split on the search's own verdict. -/
theorem h_oracle_of_leaves_R (entry q : ℕ) (first : Fin 9)
    (hpres : ∀ (w : List (Fin 2)) (s : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s) →
      searchEffect (PofC centreC placeC entry w) a s v → SearchReady v)
    (hshape : ∀ w : List (Fin 2),
      PalPeg.GalilWatchOkInst.StartShape (PofC centreC placeC entry w))
    (hbudget : ∀ w : List (Fin 2),
      PalPeg.GalilFoundStage.ReplayBudgetR w (PofC centreC placeC entry w) q first 2048)
    (hstage : ∀ w : List (Fin 2),
      PalPeg.GalilFoundStage.ReplayStageInv w (PofC centreC placeC entry w) q first)
    (hrs : ∀ w : List (Fin 2),
      PalPeg.GalilReplaySpan.RestartShape (PofC centreC placeC entry w))
    (hends : ∀ (w : List (Fin 2)) (c : Control) (r : GalilVM), InvLPC w c r →
      ∃ n : ℕ, ∀ (es : List Bool) (c' : Control) (t : GalilVM),
        WatchSegE (PofC centreC placeC entry w) q first 2048 es c r c' t →
        es.length = n → SegEnd (PofC centreC placeC entry w) c' t)
    (hentry : EntryRefreshed centreC placeC entry q first)
    (hlastMis : LastMismatchReport centreC placeC entry q first)
    (hmismatch : ∀ (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) (c' : Control)
      (t : GalilVM), 1 ≤ m → m ≤ w.length → InvLPC w c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centreC placeC entry q first w c r c' t →
      c'.replaying = false → c'.clock = 1 → canRight t.right →
      read (left t.left) ≠ read (right t.right) →
      FallbackRouteMC2 (PofC centreC placeC entry w) q first w m c r c' t)
    (hfound : ∀ (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) (c' : Control)
      (t : GalilVM), 1 ≤ m → m ≤ w.length → InvLPC w c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centreC placeC entry q first w c r c' t →
      c'.clock = 1 → canRight t.right →
      read (left t.left) = read (right t.right) →
      (∃ vq, searchEffect (PofC centreC placeC entry w) true t vq ∧ vq.search.mode = .found) →
      FoundRouteMC2 (PofC centreC placeC entry w) q first w m c r c' t)
    (hfoundBg : ∀ (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) (c' : Control)
      (t : GalilVM), 1 ≤ m → m ≤ w.length → InvLPC w c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centreC placeC entry q first w c r c' t → 1 ≤ c'.clock →
      (∃ vq, searchEffect (PofC centreC placeC entry w) false t vq ∧ vq.search.mode = .found) →
      FoundRouteMC2 (PofC centreC placeC entry w) q first w m c r c r)
    (hfoundReplay : ∀ (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) (cT : Control)
      (sT : GalilVM) (R k : ℕ), 1 ≤ m → m ≤ w.length → InvLPC w c r →
      StepsAll (galilFrameS (PofC centreC placeC entry w) q first) 2048 (SoundScanNR w) k
        ⟨c, r⟩ ⟨cT, sT⟩ →
      ReplayLanding w cT sT R → SpanRep sT →
      position r.center < position sT.center → position sT.right ≤ 2 * m - 1 →
      (PalPeg.GalilReplaySpan.ChainEnd w (PofC centreC placeC entry w) q first 2048
          (position sT.right + R) cT sT 0 R ∨
        PalPeg.GalilReplaySpan.BrokeAndRestarted w (PofC centreC placeC entry w) q first 2048
          cT sT) →
      FoundInReplayRouteMC2 (PofC centreC placeC entry w) q first w m c r)
    (hstr : ∀ (w : List (Fin 2)) (c : Control) (r : GalilVM), InvL w c r → InvLPC w c r) :
    PalPeg.GalilFinalAssembly.H_oracle centreC placeC entry q first :=
  PalPeg.GalilOracleMC3.h_oracle_of_leaves'' entry q first hpres hshape hbudget hstage hrs hends
    (hended_C centreC placeC entry q first hpres hentry)
    (hlastMatch_C centreC placeC entry q first
      (fun w s hs a => hsearch_C centreC placeC entry w s hs a) hpres hentry)
    (hlastMismatch_C centreC placeC entry q first hpres hentry hlastMis)
    hmismatch hfound hfoundBg hfoundReplay hstr

#print axioms h_oracle_of_leaves_R

end PalPeg.GalilLeafReport
