import PalPeg.GalilOracleM
import PalPeg.GalilTraceCost
import PalPeg.GalilCostedFallback
import PalPeg.GalilCostedFound
import PalPeg.GalilInvPlus

/-!
# The costed per-target cycle oracle, assembled from pieces

`cycleOracleMC_of_pieces` upgrades `GalilOracleM.cycleOracleM_of_pieces` to
`GalilTraceCost.CycleOracleMC`: every exit returns a `CostedRun` whose tick count
is the tick count of its sound run.

* The idle segment comes as `SegReachedW` (with its `WatchSegE`); its sound run
  of exactly `|es|` ticks is `watchSegE_stepsAll_len`.
* **Target match** (proved here): `costedRun_target_match` — the pending ticks of
  the segment are absorbed into the report comparison piece; the resume
  continuation is the empty costed run.
* **Mismatch** (atTarget or segment exit): the leaf `hmismatch` returns a
  `FallbackRouteMC` — the fallback phase from the segment end (`1 + fb` ticks)
  plus the FPP data `FppData`; `costedRun_fallback_zero` (`R = 0`) and
  `costedRun_fallback_replay` with `replay_after_fallback` (`R > 0`) produce the
  costed run, the segment's pending ticks going into the fallback piece's wait.
* **Found** (atTarget or segment exit): the leaf `hfound` returns a
  `FoundRouteMC` started at the segment end, whose costed run takes the pending
  ticks `p0` (the shape of `costedRun_found_noshift` / `costedRun_found_shift`,
  see `foundCost_of_noshift` / `foundCost_of_shift`); the pending `w1` of
  `costedRun_watchSegE` is threaded in and the two runs composed with
  `costedRun_trans`.
* **Background found**: the leaf `hfoundBg` returns a `FoundRouteMC` started at
  the cycle start (`p0 = 0`), since the segment end need not be able to move right.
* **Report exits** (`ended`, `lastLetter`) and route `report` constructors are
  `ReachAtC` leaves.
-/

set_option autoImplicit false

namespace PalPeg.GalilOracleMC

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier
open GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton
open PalPeg.GalilOracleDischarge
open PalPeg.GalilOracleLocal
open PalPeg.GalilCheckpoints
open PalPeg.GalilSegmentConstruct PalPeg.GalilTickFun2 PalPeg.GalilBranchInvariants2
open PalPeg.GalilOracleM PalPeg.GalilTraceCost PalPeg.GalilInvPlus
open Manacher

/-! ## Segments run exactly one tick per event -/

/-- `watchSegE_stepsAll` with the tick count `|es|`. -/
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
    have hs := ih r (by rw [hl, hr']; exact hi) (outputRel_background raw P q first hb rfl ho)
    exact .succ ho (.scan_wait c s s' hm ⟨hr, hn⟩ hb) hs
  | count c s s' hm hr ha hc hb _ ih =>
    intro r hi ho
    obtain ⟨hl, hr', _, _⟩ := background_frame P q first hb
    have hs := ih r (by rw [hl, hr']; exact hi) (outputRel_background raw P q first hb rfl ho)
    exact .succ ho (.scan_count c s s' hm (Or.inr ha) hc hb) hs
  | countR c s s' hm hr hc hidle hb _ ih =>
    intro r hi ho
    obtain ⟨hl, hr', _, _⟩ := background_frame P q first hb
    have hs := ih r (by rw [hl, hr']; exact hi) (outputRel_background raw P q first hb rfl ho)
    exact .succ ho (.scan_count c s s' hm (Or.inl hr) hc hb) hs
  | «match» c s vs vq o hm hr ha hc hne hcmp hmt hq ho' _ ih =>
    intro r hi ho
    have hi' := matched_invariant raw P q first vq hcmp hmt ha hi
    have hs := ih (r+1) hi' (outputRel_of_refresh' raw P hP hP' q first _ c.output o hi' ho' _ rfl)
    exact .succ ho (scan_match_S P q first delay c s vs vq o hm hr ha hc hne hcmp hmt hq ho') hs
  | matchIdle c s vs vq o hm hr ha hc hidle hl hrr hvs hmt hq hnf ho' _ ih =>
    intro r hi ho
    have hmatch : read (left s.left) = read (right s.right) := by
      have := matched_parts P q first hmt
      rw [hl, hrr] at this; exact this
    have hi' := matched_invariant' raw vq hl hrr hmatch ha hi
    have hs := ih (r+1) hi' (outputRel_of_refresh' raw P hP hP' q first _ c.output o hi' ho' _ rfl)
    exact .succ ho (scan_match_idle_S P q first delay c s vs vq o hm hr ha hc hidle hl hrr hvs hmt hq
      hnf ho') hs
  | matchIdleR c s vs vq o hm hr hc ha hidle hl hrr hvs hmt hq hnf ho' _ ih =>
    intro r hi ho
    have hmatch : read (left s.left) = read (right s.right) := by
      have := matched_parts P q first hmt
      rw [hl, hrr] at this; exact this
    have hi' : ScanInvariant raw cen (r+1) (replayDec true (afterCompare s vs vq)).left
        (replayDec true (afterCompare s vs vq)).right := by
      rw [replayDec_left, replayDec_right, afterCompare_left, afterCompare_right, hl, hrr]
      exact scanInvariant_matched hi ha hmatch
    have hs := ih (r+1) hi' (outputRel_of_refresh' raw P hP hP' q first _ c.output o hi' ho' _ rfl)
    have ht := scan_match_idle_S' P q first delay c s vs vq o hm (Or.inl hr) hc hidle hl hrr hvs hmt
      hq hnf (by rw [hr]; exact ho')
    rw [hr] at ht
    exact .succ ho (by simpa using ht) hs

/-- What `InvL` gives the segment's costed run: a scan invariant, a clock within
the delay and a sound output. -/
theorem invL_entry {raw : List (Fin 2)} {c : Control} {r : GalilVM} (hI : InvL raw c r) :
    (∃ R : ℕ, ScanInvariant raw (position r.center) R r.left r.right) ∧ c.clock ≤ 2048 ∧
      OutputRel raw c r := by
  refine ⟨?_, ?_, hI.2⟩
  · rcases hI.1 with h | ⟨k, h⟩
    · obtain ⟨Rad, last, hR⟩ := h.rest
      exact ⟨Rad, hR.2.2.2.1⟩
    · exact ⟨k, h.scan⟩
  · rcases hI.1 with h | ⟨k, h⟩
    · rw [h.mode.2.2]
    · rw [h.mode.2.2]

/-- The segment of `SegReachedW` as a sound run of exactly `|es|` ticks. -/
theorem seg_run (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9) (raw : List (Fin 2)) {es : List Bool}
    {c c' : Control} {r t : GalilVM} (hI : InvL raw c r)
    (hw : WatchSegE (PofC centre place entry raw) q first 2048 es c r c' t) :
    StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048 (SoundScanNR raw)
      es.length ⟨c, r⟩ ⟨c', t⟩ := by
  obtain ⟨⟨R, hi⟩, _, ho⟩ := invL_entry hI
  exact stepsAll_mono (fun st h0 _ _ => h0)
    (watchSegE_stepsAll_len raw (PofC centre place entry raw) rfl rfl q first 2048 hw _ R hi ho)

/-! ## Costed routes -/

/-- The FPP facts at the mismatching state `s` that `costedRun_fallback_replay`
consumes: a fallback phase of `fb` ticks choosing radius `R`. -/
def FppData (raw : List (Fin 2)) (s : GalilVM) (fb R : ℕ) : Prop :=
  ∃ (Rad ℓ : ℕ) (a : Fin 2) (xs rs' q' : List (Fin 2)) (a₀ : Fin 2) (ls₀ rs₀ q₀ : List (Fin 2))
    (gap₀ : Bool) (lower span : ℕ) (y : GalilFppWide.Config 12),
    ScanInvariant raw (position s.center) Rad s.left s.right ∧
    RadiusRep s.radius Rad ∧ SpanRep s ∧ value s.length = ℓ ∧ Rad < position s.center ∧
    right s.right = represent ⟨a :: xs,(right s.right).gap⟩ (rs'.map some) q' ∧
    raw = (a :: xs).reverse ++ rs' ++ q' ∧
    raw = (a₀ :: ls₀).reverse ++ rs₀ ++ q₀ ∧
    position s.center = position (represent ⟨a₀ :: ls₀,gap₀⟩ (rs₀.map some) q₀) ∧
    Rad ≤ span ∧
    GalilDpCorrect.Result ((GalilScaffoldPlace.stream ⟨a₀ :: ls₀,gap₀⟩).take (span+1)) lower 0 y ∧
    y.pc = 347 ∧
    (∀ δ, 0 < δ → δ ≤ lower → ¬ HasPeriod (Span raw (position s.center) Rad) (2*δ)) ∧
    R = chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)) ∧
    fb ≤ 1588*(ℓ+1) + 836

/-- The mismatch route, costed: a report, or the fallback phase from the segment
end `⟨c', t⟩` (`1 + fb` ticks) with its FPP data, landing at radius `0` or on a
replay of `R > 0` rounds. -/
inductive FallbackRouteMC (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ)
    (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM) : Prop
  | report (h : ReachAtC P q first raw m c r)
  | landed (fb : ℕ) (cT : Control) (sT : GalilVM)
      (hst : StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) (1 + fb) ⟨c', t⟩ ⟨cT, sT⟩)
      (hD : FppData raw t fb 0)
      (hland : position sT.center = position (right t.right) - 0) (hCR : sT.center = sT.right)
      (hI : Inv raw cT sT) (hprog : position t.center < position sT.center)
      (hpos : position (right t.right) ≤ 2 * m - 1)
  | replaying (fb R : ℕ) (cT : Control) (sT : GalilVM)
      (hst : StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) (1 + fb) ⟨c', t⟩ ⟨cT, sT⟩)
      (hD : FppData raw t fb R) (hL : ReplayLanding raw cT sT R)
      (hland : position sT.center = position (right t.right) - R) (hCR : sT.center = sT.right)
      (hprog : position t.center < position sT.center)
      (hpos : position (right t.right) ≤ 2 * m - 1)

/-- The costed run of a found cycle started at `⟨c0, s0⟩` with `p0` pending ticks. -/
def FoundCost (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (c0 : Control) (s0 : GalilVM) (cT : Control) (sT : GalilVM) : Prop :=
  ∀ p0 : ℕ, p0 + c0.clock ≤ 2048 → ∃ (k : ℕ) (L : List Piece),
    StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c0, s0⟩ ⟨cT, sT⟩ ∧
    CostedRun s0 sT (k + p0) L

/-- The found route, costed, started at `⟨c0, s0⟩`. -/
inductive FoundRouteMC (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ)
    (c : Control) (r : GalilVM) (c0 : Control) (s0 : GalilVM) : Prop
  | report (h : ReachAtC P q first raw m c r)
  | shift (cT : Control) (sT : GalilVM) (hcost : FoundCost P q first raw c0 s0 cT sT)
      (hM : MInv raw cT sT) (hR : ∃ (Rad : ℕ) (last : Counter), Restarted raw sT Rad last)
      (hres : FoundResidual raw cT sT) (hprog : position s0.center < position sT.center)
      (hpos : position sT.right ≤ 2 * m - 1)
  | noShift (cT : Control) (sT : GalilVM) (hcost : FoundCost P q first raw c0 s0 cT sT)
      (hM : MInv raw cT sT) (hR : ∃ (Rad : ℕ) (last : Counter), Restarted raw sT Rad last)
      (hres : FoundResidual raw cT sT) (hprog : position s0.center < position sT.center)
      (hpos : position sT.right ≤ 2 * m - 1)

/-! ## Exits -/

/-- A found route started at the segment end, composed with the segment. -/
theorem cycleOutMC_of_found (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m : ℕ) {c c' : Control} {r t : GalilVM} {es : List Bool}
    (hI : InvL raw c r)
    (hw : WatchSegE (PofC centre place entry raw) q first 2048 es c r c' t)
    (hcen : t.center = r.center) (hav : canRight t.right)
    (h : FoundRouteMC (PofC centre place entry raw) q first raw m c r c' t) :
    CycleOutMC (PofC centre place entry raw) q first raw m c r := by
  obtain ⟨⟨R, hi⟩, hc0, _⟩ := invL_entry hI
  have hrun0 := seg_run centre place entry q first raw hI hw
  obtain ⟨Ls, k', w1, hcrS, he, hw1, -, -, -, -⟩ :=
    GalilCostedFallback.costedRun_watchSegE raw (PofC centre place entry raw) q first hw hi hc0 hav
  have fin : ∀ (cT : Control) (sT : GalilVM),
      FoundCost (PofC centre place entry raw) q first raw c' t cT sT →
      InvS raw cT sT → position t.center < position sT.center →
      position sT.right ≤ 2 * m - 1 → CycleOutMC (PofC centre place entry raw) q first raw m c r := by
    intro cT sT hcost hIT hprog hpos
    obtain ⟨k, L, hst, hcr⟩ := hcost w1 hw1
    have hall := stepsAll_trans hrun0 hst
    have hcr' := costedRun_trans hcrS hcr
    rw [show k' + (k + w1) = es.length + k by omega] at hcr'
    exact Or.inr ⟨cT, sT, _, _, hall, hcr', invL_of_run hall hIT, by rw [← hcen]; exact hprog, hpos⟩
  cases h with
  | report h => exact Or.inl h
  | shift cT sT hcost hM hR hres hprog hpos =>
      exact fin cT sT hcost (Or.inl (inv_of_residual hM hR hres)) hprog hpos
  | noShift cT sT hcost hM hR hres hprog hpos =>
      exact fin cT sT hcost (Or.inl (inv_of_residual hM hR hres)) hprog hpos

/-- A found route started at the cycle start (background found). -/
theorem cycleOutMC_of_foundBg {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)} {m : ℕ}
    {c : Control} {r : GalilVM} (hI : InvL raw c r) (h : FoundRouteMC P q first raw m c r c r) :
    CycleOutMC P q first raw m c r := by
  obtain ⟨_, hc0, _⟩ := invL_entry hI
  have fin : ∀ (cT : Control) (sT : GalilVM), FoundCost P q first raw c r cT sT →
      InvS raw cT sT → position r.center < position sT.center →
      position sT.right ≤ 2 * m - 1 → CycleOutMC P q first raw m c r := by
    intro cT sT hcost hIT hprog hpos
    obtain ⟨k, L, hst, hcr⟩ := hcost 0 (by omega)
    exact Or.inr ⟨cT, sT, k, L, hst, hcr, invL_of_run hst hIT, hprog, hpos⟩
  cases h with
  | report h => exact Or.inl h
  | shift cT sT hcost hM hR hres hprog hpos =>
      exact fin cT sT hcost (Or.inl (inv_of_residual hM hR hres)) hprog hpos
  | noShift cT sT hcost hM hR hres hprog hpos =>
      exact fin cT sT hcost (Or.inl (inv_of_residual hM hR hres)) hprog hpos

/-- A mismatch route composed with the segment. -/
theorem cycleOutMC_of_fallback (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m : ℕ)
    (hex : ∀ s, (PofC centre place entry raw).replayExhausted s = zero s.replay)
    (hsearch : ∀ s : GalilVM, SearchReady (searchLens.get s) →
      ∀ a : Bool, ∃ v, searchEffect (PofC centre place entry raw) a s v)
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s) →
      searchEffect (PofC centre place entry raw) a s v → SearchReady v)
    (hquiet : PalPeg.GalilReplaySegment.SearchQuiet (PofC centre place entry raw))
    (hout : ∀ (c' : Control) (t' : GalilVM) (k : ℕ),
      PalPeg.GalilReplaySegment.InvScan 2048 raw c' t' k → SoundScanNR raw ⟨c', t'⟩)
    {c c' : Control} {r t : GalilVM} {es : List Bool}
    (hI : InvL raw c r)
    (hw : WatchSegE (PofC centre place entry raw) q first 2048 es c r c' t)
    (hcen : t.center = r.center) (hc1 : c'.clock = 1) (hav : canRight t.right)
    (h : FallbackRouteMC (PofC centre place entry raw) q first raw m c r c' t) :
    CycleOutMC (PofC centre place entry raw) q first raw m c r := by
  obtain ⟨⟨R0, hi0⟩, hc0, _⟩ := invL_entry hI
  have hrun0 := seg_run centre place entry q first raw hI hw
  cases h with
  | report h => exact Or.inl h
  | landed fb cT sT hst hD hland hCR hIT hprog hpos =>
      obtain ⟨Rad, ℓ, a, xs, rs', q', a₀, ls₀, rs₀, q₀, gap₀, lower, span, y, hi, hRR, hS, hv, hkC,
        hdec, hraw, hraw₀, hC₀, hspan, hres, hidle, hlow, hR, hfb⟩ := hD
      obtain ⟨L, w, hw', e, hcr, -, -, -, -, -, hr'⟩ :=
        GalilCostedFallback.costedRun_fallback_zero raw (PofC centre place entry raw) q first hw hi0
          hc0 hc1 (t := sT) hi hav hRR hS ℓ hv hkC a xs rs' q' hdec hraw a₀ ls₀ rs₀ q₀ gap₀ hraw₀
          hC₀ hspan hres hidle hlow fb hR hfb hland hCR
      have hall := stepsAll_trans hrun0 hst
      rw [show es.length + (1 + fb) = es.length + 1 + fb by omega] at hall
      exact Or.inr ⟨cT, sT, _, _, hall, hcr, invL_of_run hall (Or.inl hIT),
        by rw [← hcen]; exact hprog, by rw [hr']; exact hpos⟩
  | replaying fb R cT sT hst hD hL hland hCR hprog hpos =>
      obtain ⟨Rad, ℓ, a, xs, rs', q', a₀, ls₀, rs₀, q₀, gap₀, lower, span, y, hi, hRR, hS, hv, hkC,
        hdec, hraw, hraw₀, hC₀, hspan, hres, hidle, hlow, hR, hfb⟩ := hD
      obtain ⟨esR, c'', t'', _hseg, hstR, hlen, _hcnt, hrr, hcc, hIS⟩ :=
        PalPeg.GalilReplaySegment.replay_after_fallback raw (PofC centre place entry raw) q first
          2048 hex (by norm_num) hsearch hpres hquiet R hL.pos cT sT hL.mode hL.clock hL.replaying
          hL.rest hL.replay hL.minv hL.frontier hL.shiftIdle
      obtain ⟨L, w, hw', e, hcr, -, -, -, -, -, hr'⟩ :=
        GalilCostedFallback.costedRun_fallback_replay raw (PofC centre place entry raw) q first hw
          hi0 hc0 hc1 (t := sT) (t' := t'') hi hav hRR hS ℓ hv hkC a xs rs' q' hdec hraw a₀ ls₀
          rs₀ q₀ gap₀ hraw₀ hC₀ hspan hres hidle hlow fb esR R hR hfb hlen hland hCR hrr hcc
      have hall := stepsAll_trans (stepsAll_trans hrun0 hst) (hstR (hout c'' t'' R hIS))
      rw [show es.length + (1 + fb) + esR.length = es.length + 1 + fb + esR.length by omega] at hall
      exact Or.inr ⟨c'', t'', _, _, hall, hcr, invL_of_run hall (Or.inr ⟨R, hIS⟩),
        by rw [hcc, ← hcen]; exact hprog, by rw [hr']; exact hpos⟩

/-- **The matched, not-found comparison onto `2m-1`, costed.**  The segment and
the report comparison form one costed run of `|es| + 1` ticks (the pending
ticks are the report piece's wait); the resume continuation is empty. -/
theorem reachAtC_of_target_match (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m : ℕ) (hm1 : 1 ≤ m) (hmle : m ≤ raw.length)
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s) →
      searchEffect (PofC centre place entry raw) a s v → SearchReady v)
    (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM) (hI : InvL raw c r)
    (hsW : SegReachedW centre place entry q first raw c r c' t)
    (hT : AtTarget m c' t)
    (hmt : read (left t.left) = read (right t.right))
    (vq : SearchVM) (hq : searchEffect (PofC centre place entry raw) true t vq)
    (hnf : vq.search.mode ≠ .found) :
    ReachAtC (PofC centre place entry raw) q first raw m c r := by
  classical
  set P : Shared := PofC centre place entry raw with hP
  obtain ⟨hs, es, hw⟩ := hsW
  obtain ⟨hnr, hc1, hav, hpos, hrep⟩ := hT
  obtain ⟨⟨R0, hi0⟩, hc0, _⟩ := invL_entry hI
  have hrun0 := seg_run centre place entry q first raw hI hw
  obtain ⟨R, hi⟩ := hs.scan
  set vs : ScanVM := ⟨left t.left, right t.right, ChainVM.idle⟩ with hvs
  have hmt0 : (galilFrame P q first).matched (scanLens.set t vs) := hmt
  have hborn : chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) t.chain
      = false := by
    have hd : decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found) = false := by
      simp [hnf]
    unfold chainBorn
    rw [hd]
    exact Bool.and_false _
  have hcmp : (galilFrameS P q first).compare t (afterCompare t vs vq) :=
    ⟨vs, vq, true, rfl, rfl, ⟨fun _ => hmt0, fun _ => rfl⟩, hq,
      Or.inr (Or.inl ⟨hs.idle, by simp [hnf], rfl⟩), by rw [hborn]; rfl⟩
  have hmt1 : (galilFrameS P q first).matched (afterCompare t vs vq) := hmt
  set u : GalilVM := afterCompare t vs vq with hu
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
      hav hs.minv hi hpos hm1 hmle vs vq o false rfl rfl hcmp hmt1 ho
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
  obtain ⟨L, w, hw', hcr, -, -⟩ :=
    GalilCostedFallback.costedRun_target_match raw P q first hw hi0 hc0 hc1 hav m hm1 hpos vq
  refine ⟨_, es.length + (0 + 1), L ++ [GalilCostedFallback.cmpPiece (2 * m - 1) w hw'], hall,
    hcr, hrp, hfr, fun _ => ⟨_, u, 0, [], .zero _ (stepsAll_last hall), costedRun_nil u, ?_, ?_⟩⟩
  · have hIS : PalPeg.GalilReplaySegment.InvScan 2048 raw
        {c' with clock := 2048, output := o, replaying := false} u (R + 1) := by
      refine PalPeg.GalilReplaySegment.inv_after_replay 2048 raw _ u (R + 1) hs.mode rfl rfl
        (by rw [hu, afterCompare_chain]) ?_ hrp.centre ?_ ?_ ?_
      · exact matched_invariant' raw vq (vs := vs) rfl rfl hmt hav hi
      · exact hpres t true vq hs.search hq
      · rw [hu, afterCompare_replay]; exact hrep
      · exact PalPeg.GalilReplaySegment.shiftIdle_congr
          (PalPeg.GalilReplaySegment.afterCompare_remaining t vs vq) hs.shiftIdle
    exact invL_of_run hall (Or.inr ⟨R + 1, hIS⟩)
  · have h1 : position u.right = 2 * m - 1 := hrp.atPlace
    omega

/-! ## The found lemmas deliver `FoundCost` -/

section FoundAdapters
open PalPeg.GalilCostedFound

/-- `costedRun_found_noshift` delivers the costed-route shape `FoundCost` (delay `2048`). -/
theorem foundCost_of_noshift (raw : List (Fin 2)) (P : Shared) (hP : P.onLetter = onLetterVM raw)
    (hP' : P.leftFirst = leftFirstVM) (qq : ℕ) (first : Fin 9)
    {cF : Control} {sF : GalilVM} (hmF : cF.mode = .scan) (hrF : cF.replaying = false)
    (hcF : cF.clock = 1) (havF : canRight sF.right) (hidle : sF.chain = .idle)
    {cen R : ℕ} (hscan : ScanInvariant raw cen R sF.left sF.right) (houtF : OutputRel raw cF sF)
    (vq : SearchVM) (hq : searchEffect P true sF vq) (hfound : vq.search.mode = .found)
    (hmt : read (left sF.left) = read (right sF.right))
    (ch : ChainVM)
    (hch : ChainMatched (chainStart (vq.dp.config.tapes 11) (P.centre sF) (P.place sF) sF.center sF.radius) ch)
    (hchne : ch ≠ .idle) (oF : Bool)
    (hoF : refresh (galilFrame P qq first)
      (afterBirth true (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq)) cF.output oF)
    {es : List Bool} {c2 : Control} {s2 : GalilVM}
    (hprepSeg : WatchSegE P qq first 2048 es {cF with clock := 2048, output := oF, replaying := false}
      (afterBirth true (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq)) c2 s2)
    {c3 : Control} {s3 : GalilVM} (hseg : WatchSeg P qq first 2048 c2 s2 c3 s3)
    (hm3 : c3.mode = .scan) (hr3 : c3.replaying = false) (hc3 : c3.clock = 1)
    (w3 : GalilScaffoldChainWatch.State) (hs3 : s3.chain = .watch w3) (hav3 : canRight s3.right)
    (vs3 : ScanVM) (vq3 : SearchVM)
    (hcmp3 : (galilFrame P qq first).compare s3 (scanLens.set s3 vs3))
    (hmt3 : (galilFrame P qq first).matched (scanLens.set s3 vs3))
    (hq3 : searchEffect P true s3 vq3)
    (o3 : Bool) (ho3 : refresh (galilFrame P qq first) (afterCompare s3 vs3 vq3) c3.output o3)
    (w3' : GalilScaffoldChainWatch.State) (hbroken : (afterCompare s3 vs3 vq3).chain = .broken w3')
    (hmargin : negative w3'.margin = false) (hlast : positive w3'.machine.control.last = true)
    (hlag : zero w3'.lag = true) (entry : ℕ) (hres : ∀ s t, restartVM entry s t → P.restart s t) :
    FoundCost P qq first raw cF sF {c3 with clock := 2048, output := o3, replaying := false}
      {(afterCompare s3 vs3 vq3) with chain := .idle, lower := w3'.machine.control.last, search := GalilScaffoldSearchFinish.begin w3'.machine.control.last (afterCompare s3 vs3 vq3).radius, dp := GalilScaffoldControl.reset entry (afterCompare s3 vs3 vq3).dp} := by
  intro p0 hp0
  obtain ⟨k, L, h1, h2, -⟩ := costedRun_found_noshift (delay := 2048) (hd := le_rfl)
    raw P hP hP' qq first hmF hrF hcF havF hidle hscan houtF vq hq hfound hmt ch hch hchne oF hoF hprepSeg hseg hm3 hr3 hc3 w3 hs3 hav3 vs3 vq3 hcmp3 hmt3 hq3 o3 ho3 w3' hbroken hmargin hlast hlag entry hres p0 hp0
  exact ⟨k, L, h1, h2⟩
/-- `costedRun_found_shift` delivers the costed-route shape `FoundCost` (delay `2048`). -/
theorem foundCost_of_shift (raw : List (Fin 2)) (P : Shared) (hP : P.onLetter = onLetterVM raw)
    (hP' : P.leftFirst = leftFirstVM) (qq : ℕ) (first : Fin 9)
    {cF : Control} {sF : GalilVM} (hmF : cF.mode = .scan) (hrF : cF.replaying = false)
    (hcF : cF.clock = 1) (havF : canRight sF.right) (hidle : sF.chain = .idle)
    {cen R : ℕ} (hscan : ScanInvariant raw cen R sF.left sF.right) (houtF : OutputRel raw cF sF)
    (vq : SearchVM) (hq : searchEffect P true sF vq) (hfound : vq.search.mode = .found)
    (hmt : read (left sF.left) = read (right sF.right))
    (ch : ChainVM)
    (hch : ChainMatched (chainStart (vq.dp.config.tapes 11) (P.centre sF) (P.place sF) sF.center sF.radius) ch)
    (hchne : ch ≠ .idle) (oF : Bool)
    (hoF : refresh (galilFrame P qq first)
      (afterBirth true (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq)) cF.output oF)
    {es : List Bool} {c2 : Control} {s2 : GalilVM}
    (hprepSeg : WatchSegE P qq first 2048 es {cF with clock := 2048, output := oF, replaying := false}
      (afterBirth true (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq)) c2 s2)
    {c1 : Control} {s1 : GalilVM} (hseg : WatchSeg P qq first 2048 c2 s2 c1 s1)
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
    (hoc : org.center = position sF.center)
    {m : ℕ} {c' : Control} {s' : GalilVM}
    (hrounds : Rounds P qq first 2048 h m {c1 with mode := .scan, clock := 2048, output := o}
      (shiftLens.set s2' ⟨t', .watch v, cycle⟩) c' s')
    {n : ℕ} {c3 : Control} {s3 : GalilVM} (hseg3 : ScanSeg P qq first 2048 n c' s' c3 s3)
    (hm3 : c3.mode = .scan) (hr3 : c3.replaying = false) (hc3 : c3.clock = 1)
    (w3 : GalilScaffoldChainWatch.State) (hs3 : s3.chain = .watch w3) (hav3 : canRight s3.right)
    (vs3 : ScanVM) (vq3 : SearchVM)
    (hcmp3 : (galilFrame P qq first).compare s3 (scanLens.set s3 vs3))
    (hmt3 : (galilFrame P qq first).matched (scanLens.set s3 vs3))
    (hq3 : searchEffect P true s3 vq3)
    (o3 : Bool) (ho3 : refresh (galilFrame P qq first) (afterCompare s3 vs3 vq3) c3.output o3)
    (w3' : GalilScaffoldChainWatch.State) (hbroken : (afterCompare s3 vs3 vq3).chain = .broken w3')
    (hmargin : negative w3'.margin = false) (hlast : positive w3'.machine.control.last = true)
    (hlag : zero w3'.lag = true) (entry : ℕ) (hres : ∀ s t, restartVM entry s t → P.restart s t) :
    FoundCost P qq first raw cF sF {c3 with clock := 2048, output := o3, replaying := false}
      {(afterCompare s3 vs3 vq3) with chain := .idle, lower := w3'.machine.control.last, search := GalilScaffoldSearchFinish.begin w3'.machine.control.last (afterCompare s3 vs3 vq3).radius, dp := GalilScaffoldControl.reset entry (afterCompare s3 vs3 vq3).dp} := by
  intro p0 hp0
  obtain ⟨k, L, h1, h2, -⟩ := costedRun_found_shift (delay := 2048) (hd := le_rfl)
    raw P hP hP' qq first hmF hrF hcF havF hidle hscan houtF vq hq hfound hmt ch hch hchne oF hoF hprepSeg hseg h hm1 hr1 hc1 w hs1 hz hav vs vq' hcmp hmis hq' hg s2' hb hs2' hi2 hchain o ho org hint he hoc hrounds hseg3 hm3 hr3 hc3 w3 hs3 hav3 vs3 vq3 hcmp3 hmt3 hq3 o3 ho3 w3' hbroken hmargin hlast hlag entry hres p0 hp0
  exact ⟨k, L, h1, h2⟩

end FoundAdapters

/-! ## The costed oracle -/

/-- **The costed per-target cycle oracle, assembled.** -/
theorem cycleOracleMC_of_pieces (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2))
    (hex : ∀ s, (PofC centre place entry raw).replayExhausted s = zero s.replay)
    (hsearch : ∀ s : GalilVM, SearchReady (searchLens.get s) →
      ∀ a : Bool, ∃ v, searchEffect (PofC centre place entry raw) a s v)
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s) →
      searchEffect (PofC centre place entry raw) a s v → SearchReady v)
    (hquiet : PalPeg.GalilReplaySegment.SearchQuiet (PofC centre place entry raw))
    (houtReplay : ∀ (c' : Control) (t' : GalilVM) (k : ℕ),
      PalPeg.GalilReplaySegment.InvScan 2048 raw c' t' k → SoundScanNR raw ⟨c', t'⟩)
    (hsegmentM : ∀ (m : ℕ) (c : Control) (r : GalilVM), 1 ≤ m → m ≤ raw.length →
      InvL raw c r → position r.right ≤ 2 * m - 1 →
      ∃ (c' : Control) (t : GalilVM),
        SegReachedW centre place entry q first raw c r c' t ∧
        (AtTarget m c' t ∨ SegEnd (PofC centre place entry raw) c' t))
    (hended : ∀ (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ raw.length → InvL raw c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centre place entry q first raw c r c' t → ¬ canRight t.right →
      ReachAtC (PofC centre place entry raw) q first raw m c r)
    (hlastMatch : ∀ (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ raw.length → InvL raw c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centre place entry q first raw c r c' t →
      c'.clock = 1 → canRight t.right → PopsIncoming t.right →
      (∃ a : Fin 2, t.right.head.incoming = [a]) →
      read (left t.left) = read (right t.right) →
      ReachAtC (PofC centre place entry raw) q first raw m c r)
    (hlastMismatch : ∀ (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ raw.length → InvL raw c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centre place entry q first raw c r c' t →
      c'.clock = 1 → canRight t.right → PopsIncoming t.right →
      (∃ a : Fin 2, t.right.head.incoming = [a]) →
      read (left t.left) ≠ read (right t.right) →
      ReachAtC (PofC centre place entry raw) q first raw m c r)
    (hmismatch : ∀ (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ raw.length → InvL raw c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centre place entry q first raw c r c' t →
      c'.replaying = false → c'.clock = 1 → canRight t.right →
      read (left t.left) ≠ read (right t.right) →
      FallbackRouteMC (PofC centre place entry raw) q first raw m c r c' t)
    (hfound : ∀ (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ raw.length → InvL raw c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centre place entry q first raw c r c' t →
      c'.clock = 1 → canRight t.right →
      read (left t.left) = read (right t.right) →
      (∃ vq, searchEffect (PofC centre place entry raw) true t vq ∧ vq.search.mode = .found) →
      FoundRouteMC (PofC centre place entry raw) q first raw m c r c' t)
    (hfoundBg : ∀ (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ raw.length → InvL raw c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centre place entry q first raw c r c' t → 1 ≤ c'.clock →
      (∃ vq, searchEffect (PofC centre place entry raw) false t vq ∧ vq.search.mode = .found) →
      FoundRouteMC (PofC centre place entry raw) q first raw m c r c r) :
    CycleOracleMC (PofC centre place entry raw) q first raw := by
  intro m c r hm1 hmle hI hp
  obtain ⟨c', t, hsW, hend⟩ := hsegmentM m c r hm1 hmle hI hp
  obtain ⟨hs, es, hw⟩ := id hsW
  rcases hend with hT | hend
  · obtain ⟨hnr, hc1, hav, _, _⟩ := id hT
    by_cases hmt : read (left t.left) = read (right t.right)
    · obtain ⟨vq, hq⟩ := hsearch t hs.search true
      by_cases hf : vq.search.mode = .found
      · exact cycleOutMC_of_found centre place entry q first raw m hI hw hs.center hav
          (hfound m c r c' t hm1 hmle hI hp hsW hc1 hav hmt ⟨vq, hq, hf⟩)
      · exact Or.inl (reachAtC_of_target_match centre place entry q first raw m hm1 hmle hpres
          c r c' t hI hsW hT hmt vq hq hf)
    · exact cycleOutMC_of_fallback centre place entry q first raw m hex hsearch hpres hquiet
        houtReplay hI hw hs.center hc1 hav (hmismatch m c r c' t hm1 hmle hI hp hsW hnr hc1 hav hmt)
  · cases hend with
    | ended hn => exact Or.inl (hended m c r c' t hm1 hmle hI hp hsW hn)
    | mismatch hr hc hav hne =>
        exact cycleOutMC_of_fallback centre place entry q first raw m hex hsearch hpres hquiet
          houtReplay hI hw hs.center hc hav (hmismatch m c r c' t hm1 hmle hI hp hsW hr hc hav hne)
    | found hc hav hmt hq =>
        exact cycleOutMC_of_found centre place entry q first raw m hI hw hs.center hav
          (hfound m c r c' t hm1 hmle hI hp hsW hc hav hmt hq)
    | foundBackground hc hq =>
        exact cycleOutMC_of_foundBg hI (hfoundBg m c r c' t hm1 hmle hI hp hsW hc hq)
    | lastLetter hc hav hpop hinc =>
        by_cases hmt : read (left t.left) = read (right t.right)
        · exact Or.inl (hlastMatch m c r c' t hm1 hmle hI hp hsW hc hav hpop hinc hmt)
        · exact Or.inl (hlastMismatch m c r c' t hm1 hmle hI hp hsW hc hav hpop hinc hmt)

#print axioms watchSegE_stepsAll_len
#print axioms invL_entry
#print axioms seg_run
#print axioms foundCost_of_noshift
#print axioms foundCost_of_shift
#print axioms cycleOutMC_of_found
#print axioms cycleOutMC_of_foundBg
#print axioms cycleOutMC_of_fallback
#print axioms reachAtC_of_target_match
#print axioms cycleOracleMC_of_pieces

end PalPeg.GalilOracleMC
