import PalPeg.CloseoutPreload40
import PalPeg.GalilOracleMC3
import PalPeg.GalilSegmentConstructB

/-!
# `CloseoutOracle5`: the target-match use of `hpres` moved onto `HpresAt`

`GalilSegmentConstructB.h_oracle_of_leaves3` (the triple-primed one) records
that after the segment site is repaired, the refuted universal leaf

```
hpres : ∀ s a v, SearchReady (searchLens.get s) → searchEffect P a s v → SearchReady v
```

(refuted by `GalilLeafPres.hpres_false_at`) is still consumed at exactly two
sites of `GalilOracleMC3.cycleOracleMC2C_of_pieces'`:

* `GalilOracleMC2.reachAtC2_of_target_match` (`:544`), once, as
  `hpres t true vq hs.search hq`, at the landing `t` of a target comparison —
  a **scan** state with `t.chain = ChainVM.idle` and `c'.clock = 1`;
* `GalilOracleMC3.invScanO_of_replay_generalR`, threaded through
  `GalilFoundStage.replay_after_fallback_general'''` and
  `GalilReplaySpan.replay_construct3` for the whole fallback **replay**.

The first site is exactly the shape of `CloseoutPreload40.HpresAt`: chain idle,
and `a = true → clock ≤ 1`.  `reachAtC2_of_target_matchP` below re-proves
`reachAtC2_of_target_match` on `HpresAt` at that one landing, and
`cycleOracleMC2C_of_piecesP` propagates the split, so the universal `hpres`
survives in the assembly **only** as `hpresRep`, the fallback-replay
hypothesis.

Note what this does *not* do.  `CloseoutPreload40.hpresAt_along_run` delivers
`HpresAt` at states with `y.ctl.mode = Mode.scan` (`ReadyFieldP3.paced` is
conditioned on `Mode.scan`, `CloseoutPreload39:62`); the replay site lives at
`Mode.replay` states, which the readiness field does not speak about at all.
So `hOP` of `CloseoutPreload40` is *not* discharged here: what is discharged is
its scan half.

`hpresT` is stated *reachability-restricted* (`InvLPC` entry + `SegReachedW`
landing + `clock = 1`), so `GalilLeafPres.hpres_false_at` — which builds a bare
chain-idle `.run` state with exhausted debt, with no run attached — does not
refute it, whereas it does refute both `hpres` and any merely clock-guarded
universal form.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutOracle5

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton PalPeg.GalilOracleDischarge PalPeg.GalilOracleLocal
open PalPeg.GalilCheckpoints PalPeg.GalilTraceCost PalPeg.GalilLexMeasure
open PalPeg.GalilInvPlus PalPeg.GalilInvPlus2 PalPeg.GalilOracleMC
open PalPeg.GalilGlueBLeaves PalPeg.GalilBranchInvariants2 PalPeg.GalilSegmentConstruct
open PalPeg.GalilOracleM PalPeg.GalilOracleMC2 PalPeg.GalilFinalAssembly2
open PalPeg.GalilLeafOutReplay PalPeg.GalilOracleLeaves2 PalPeg.GalilOracleMC3
open PalPeg.GalilLeafPres PalPeg.GalilLeafEnds PalPeg.GalilSegmentConstructB

/-! ## 1. The target-match landing, off the universal leaf -/

theorem reachAtC2_of_target_matchP (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m : ℕ) (hm1 : 1 ≤ m) (hmle : m ≤ raw.length)
    (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM)
    (hpresAt : PalPeg.CloseoutPreload40.HpresAt (PofC centre place entry raw) c' t)
    (hIC : InvLPC raw c r)
    (hsW : SegReachedW centre place entry q first raw c r c' t)
    (hT : AtTarget m c' t)
    (hmt : read (left t.left) = read (right t.right))
    (vq : SearchVM) (hq : searchEffect (PofC centre place entry raw) true t vq)
    (hnf : vq.search.mode ≠ .found) :
    ReachAtC2 (PofC centre place entry raw) q first raw m c r := by
  classical
  set P : Shared := PofC centre place entry raw with hP
  have hI : InvL raw c r := invLPC_invL hIC
  obtain ⟨hs, es, hw⟩ := hsW
  obtain ⟨hnr, hc1, hav, hpos, hrep⟩ := hT
  obtain ⟨⟨R0, hi0⟩, hc0, -⟩ := invL_entry hI
  have hrun0 := seg_run centre place entry q first raw hI hw
  obtain ⟨R, hi⟩ := hs.scan
  -- the entering counters, transported along the idle segment
  obtain ⟨RadE, hiE, hRRE, hSE, hLE⟩ := hIC.1.1.2
  have hiT : ScanInvariant raw (position r.center) (RadE + es.count true) t.left t.right :=
    scanInvariant_watchSegE P q first 2048 hw hiE
  have hRRT : RadiusRep t.radius (RadE + es.count true) :=
    radiusRep_watchSegE P q first 2048 hw hRRE
  have hST : SpanRep t := spanRep_watchSegE P q first 2048 hw hSE
  have hLT : Canonical t.length := canonical_length_watchSegE P q first 2048 hw hLE
  set vs : ScanVM := ⟨left t.left, right t.right, ChainVM.idle⟩ with hvs
  have hmt0 : (galilFrame P q first).matched (scanLens.set t vs) := hmt
  have hcmp : (galilFrameS P q first).compare t (afterCompare t vs vq) :=
    ⟨vs, vq, true, rfl, rfl, ⟨fun _ => hmt0, fun _ => rfl⟩, hq,
      Or.inr (Or.inl ⟨hs.idle, by simp [hnf], rfl⟩), rfl⟩
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
      hav hs.minv hi hpos hm1 hmle vs vq o rfl rfl hcmp hmt1 ho
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
  -- the counters and the centre head at the landing of the comparison
  have hcu : u.center = r.center := by rw [hu, afterCompare_center, hs.center]
  have hEu : EntryCounters raw u := by
    refine ⟨RadE + es.count true + 1, ?_, ?_, ?_, ?_⟩
    · rw [hcu]; exact matched_invariant' raw vq (vs := vs) rfl rfl hmt hav hiT
    · rw [hu, afterCompare_radius]; exact radius_rep_inc hRRT
    · rw [hu]; exact spanRep_afterCompare hST
    · rw [hu, afterCompare_length]; exact inc_canonical _ (inc_canonical _ hLT)
  refine ⟨_, es.length + (0 + 1), L ++ [GalilCostedFallback.cmpPiece (2 * m - 1) w hw'], hall,
    hcr, hrp, hfr, fun _ => ⟨_, u, 0, [], .zero _ (stepsAll_last hall), costedRun_nil u, ?_, ?_⟩⟩
  · have hIS : PalPeg.GalilReplaySegment.InvScan 2048 raw
        {c' with clock := 2048, output := o, replaying := false} u (R + 1) := by
      refine PalPeg.GalilReplaySegment.inv_after_replay 2048 raw _ u (R + 1) hs.mode rfl rfl
        (by rw [hu, afterCompare_chain]) ?_ hrp.centre ?_ ?_ ?_
      · exact matched_invariant' raw vq (vs := vs) rfl rfl hmt hav hi
      · exact hpresAt true vq hs.idle (fun _ => by omega) hq
      · rw [hu, afterCompare_replay]; exact hrep
      · exact PalPeg.GalilReplaySegment.shiftIdle_congr
          (PalPeg.GalilReplaySegment.afterCompare_remaining t vs vq) hs.shiftIdle
    have hIL : InvLP raw {c' with clock := 2048, output := o, replaying := false} u :=
      ⟨invL_of_run hall (Or.inr ⟨R + 1, hIS⟩), hEu⟩
    exact ⟨invLP2_of_stepsAll centre place entry q first hIC.1.2 hall hIL,
      centreRep_congr hcu hIC.2⟩
  · have h1 : position u.right = 2 * m - 1 := hrp.atPlace
    omega


/-! ## 5. The general replay, over `ReplayBudgetR` -/

#print axioms reachAtC2_of_target_matchP

/-! ## 2. The cycle oracle with the two uses separated -/

theorem cycleOracleMC2C_of_piecesP (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2))
    (hex : ∀ s, (PofC centre place entry raw).replayExhausted s = zero s.replay)
    (hsearch : ∀ s : GalilVM, SearchReady (searchLens.get s) →
      ∀ a : Bool, ∃ v, searchEffect (PofC centre place entry raw) a s v)
    (hpresRep : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s) →
      searchEffect (PofC centre place entry raw) a s v → SearchReady v)
    (hpresT : ∀ (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM), InvLPC raw c r →
      SegReachedW centre place entry q first raw c r c' t → c'.clock = 1 →
      PalPeg.CloseoutPreload40.HpresAt (PofC centre place entry raw) c' t)
    (hshape : PalPeg.GalilWatchOkInst.StartShape (PofC centre place entry raw))
    (hbudget : PalPeg.GalilFoundStage.ReplayBudgetR raw (PofC centre place entry raw) q first 2048)
    (hstage : PalPeg.GalilFoundStage.ReplayStageInv raw (PofC centre place entry raw) q first)
    (hrs : PalPeg.GalilReplaySpan.RestartShape (PofC centre place entry raw))
    (hsegmentM : ∀ (m : ℕ) (c : Control) (r : GalilVM), 1 ≤ m → m ≤ raw.length →
      InvLPC raw c r → position r.right ≤ 2 * m - 1 →
      ∃ (c' : Control) (t : GalilVM),
        SegReachedW centre place entry q first raw c r c' t ∧
        (AtTarget m c' t ∨ SegEnd (PofC centre place entry raw) c' t))
    (hended : ∀ (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ raw.length → InvLPC raw c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centre place entry q first raw c r c' t → ¬ canRight t.right →
      ReachAtC2 (PofC centre place entry raw) q first raw m c r)
    (hlastMatch : ∀ (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ raw.length → InvLPC raw c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centre place entry q first raw c r c' t →
      c'.clock = 1 → canRight t.right → PopsIncoming t.right →
      (∃ a : Fin 2, t.right.head.incoming = [a]) →
      read (left t.left) = read (right t.right) →
      ReachAtC2 (PofC centre place entry raw) q first raw m c r)
    (hlastMismatch : ∀ (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ raw.length → InvLPC raw c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centre place entry q first raw c r c' t →
      c'.clock = 1 → canRight t.right → PopsIncoming t.right →
      (∃ a : Fin 2, t.right.head.incoming = [a]) →
      read (left t.left) ≠ read (right t.right) →
      ReachAtC2 (PofC centre place entry raw) q first raw m c r)
    (hmismatch : ∀ (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ raw.length → InvLPC raw c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centre place entry q first raw c r c' t →
      c'.replaying = false → c'.clock = 1 → canRight t.right →
      read (left t.left) ≠ read (right t.right) →
      FallbackRouteMC2 (PofC centre place entry raw) q first raw m c r c' t)
    (hfound : ∀ (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ raw.length → InvLPC raw c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centre place entry q first raw c r c' t →
      c'.clock = 1 → canRight t.right →
      read (left t.left) = read (right t.right) →
      (∃ vq, searchEffect (PofC centre place entry raw) true t vq ∧ vq.search.mode = .found) →
      FoundRouteMC2 (PofC centre place entry raw) q first raw m c r c' t)
    (hfoundBg : ∀ (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ raw.length → InvLPC raw c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centre place entry q first raw c r c' t → 1 ≤ c'.clock →
      (∃ vq, searchEffect (PofC centre place entry raw) false t vq ∧ vq.search.mode = .found) →
      FoundRouteMC2 (PofC centre place entry raw) q first raw m c r c r)
    (hfoundReplay : ∀ (m : ℕ) (c : Control) (r : GalilVM) (cT : Control) (sT : GalilVM) (R k : ℕ),
      1 ≤ m → m ≤ raw.length → InvLPC raw c r →
      StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048 (SoundScanNR raw) k
        ⟨c, r⟩ ⟨cT, sT⟩ →
      ReplayLanding raw cT sT R → SpanRep sT →
      position r.center < position sT.center → position sT.right ≤ 2 * m - 1 →
      (PalPeg.GalilReplaySpan.ChainEnd raw (PofC centre place entry raw) q first 2048
          (position sT.right + R) cT sT 0 R ∨
        PalPeg.GalilReplaySpan.BrokeAndRestarted raw (PofC centre place entry raw) q first 2048
          cT sT) →
      FoundInReplayRouteMC2 (PofC centre place entry raw) q first raw m c r) :
    CycleOracleMC2C (PofC centre place entry raw) q first raw := by
  intro m c r hm1 hmle hIC hp
  obtain ⟨c', t, hsW, hend⟩ := hsegmentM m c r hm1 hmle hIC hp
  obtain ⟨hs, es, hw⟩ := id hsW
  rcases hend with hT | hend
  · obtain ⟨hnr, hc1, hav, -, -⟩ := id hT
    by_cases hmt : read (left t.left) = read (right t.right)
    · obtain ⟨vq, hq⟩ := hsearch t hs.search true
      by_cases hf : vq.search.mode = .found
      · exact cycleOutMC2C_of_found centre place entry q first raw m hIC hw hs.center hav
          (hfound m c r c' t hm1 hmle hIC hp hsW hc1 hav hmt ⟨vq, hq, hf⟩)
      · exact Or.inl (reachAtC2_of_target_matchP centre place entry q first raw m hm1 hmle
          c r c' t (hpresT c r c' t hIC hsW hc1) hIC hsW hT hmt vq hq hf)
    · exact cycleOutMC2C_of_fallback' centre place entry q first raw m hm1 hmle hex hsearch hpresRep
        hshape hbudget hstage hrs (hfoundReplay m) hIC hw hs.center hc1 hav
        (hmismatch m c r c' t hm1 hmle hIC hp hsW hnr hc1 hav hmt)
  · cases hend with
    | ended hn => exact Or.inl (hended m c r c' t hm1 hmle hIC hp hsW hn)
    | mismatch hr hc hav hne =>
        exact cycleOutMC2C_of_fallback' centre place entry q first raw m hm1 hmle hex hsearch hpresRep
          hshape hbudget hstage hrs (hfoundReplay m) hIC hw hs.center hc hav
          (hmismatch m c r c' t hm1 hmle hIC hp hsW hr hc hav hne)
    | found hc hav hmt hq =>
        exact cycleOutMC2C_of_found centre place entry q first raw m hIC hw hs.center hav
          (hfound m c r c' t hm1 hmle hIC hp hsW hc hav hmt hq)
    | foundBackground hc hq =>
        exact cycleOutMC2C_of_foundBg centre place entry q first raw m hIC
          (hfoundBg m c r c' t hm1 hmle hIC hp hsW hc hq)
    | lastLetter hc hav hpop hinc =>
        by_cases hmt : read (left t.left) = read (right t.right)
        · exact Or.inl (hlastMatch m c r c' t hm1 hmle hIC hp hsW hc hav hpop hinc hmt)
        · exact Or.inl (hlastMismatch m c r c' t hm1 hmle hIC hp hsW hc hav hpop hinc hmt)


#print axioms cycleOracleMC2C_of_piecesP

/-! ## 3. `H_oracle` with the segment site and the target-match site off `hpres` -/

/-- **`GalilSegmentConstructB.h_oracle_of_leaves'''` with the target-match use of
`hpres` moved to the pointwise `HpresAt`.**  The universal (refuted) leaf now
enters only as `hpresRep`, consumed solely by `invScanO_of_replay_generalR`
(the fallback replay); `hpresT` is the pointwise form the readiness layer can
speak about, and `hreadyB` is `GalilSegmentConstructB`'s segment residual. -/
theorem h_oracle_of_leaves4 (entry q : ℕ) (first : Fin 9)
    (hreadyB : ∀ (w : List (Fin 2)) (c : Control) (r : GalilVM), InvLPC w c r →
      ReadyFuel (searchLens.get r) (headRank r.right * 2048 + c.clock) (headRank r.right))
    (hpresRep : ∀ (w : List (Fin 2)) (s : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s) →
      searchEffect (PofC centreC placeC entry w) a s v → SearchReady v)
    (hpresT : ∀ (w : List (Fin 2)) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      InvLPC w c r → SegReachedW centreC placeC entry q first w c r c' t → c'.clock = 1 →
      PalPeg.CloseoutPreload40.HpresAt (PofC centreC placeC entry w) c' t)
    (hshape : ∀ w : List (Fin 2),
      PalPeg.GalilWatchOkInst.StartShape (PofC centreC placeC entry w))
    (hbudget : ∀ w : List (Fin 2),
      PalPeg.GalilFoundStage.ReplayBudgetR w (PofC centreC placeC entry w) q first 2048)
    (hstage : ∀ w : List (Fin 2),
      PalPeg.GalilFoundStage.ReplayStageInv w (PofC centreC placeC entry w) q first)
    (hrs : ∀ w : List (Fin 2),
      PalPeg.GalilReplaySpan.RestartShape (PofC centreC placeC entry w))
    (hended : ∀ (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ w.length → InvLPC w c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centreC placeC entry q first w c r c' t → ¬ canRight t.right →
      ReachAtC2 (PofC centreC placeC entry w) q first w m c r)
    (hlastMatch : ∀ (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) (c' : Control)
      (t : GalilVM), 1 ≤ m → m ≤ w.length → InvLPC w c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centreC placeC entry q first w c r c' t →
      c'.clock = 1 → canRight t.right → PopsIncoming t.right →
      (∃ a : Fin 2, t.right.head.incoming = [a]) →
      read (left t.left) = read (right t.right) →
      ReachAtC2 (PofC centreC placeC entry w) q first w m c r)
    (hlastMismatch : ∀ (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) (c' : Control)
      (t : GalilVM), 1 ≤ m → m ≤ w.length → InvLPC w c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centreC placeC entry q first w c r c' t →
      c'.clock = 1 → canRight t.right → PopsIncoming t.right →
      (∃ a : Fin 2, t.right.head.incoming = [a]) →
      read (left t.left) ≠ read (right t.right) →
      ReachAtC2 (PofC centreC placeC entry w) q first w m c r)
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
  fun w _ => cycleOracleMC_of_MC2C
    (cycleOracleMC2C_of_piecesP centreC placeC entry q first w
      (fun s => hex_C centreC placeC entry w s)
      (fun s hs a => hsearch_C centreC placeC entry w s hs a)
      (hpresRep w) (hpresT w) (hshape w) (hbudget w) (hstage w) (hrs w)
      (fun m c r _ _ hIC _ => by
        obtain ⟨c', t, hsW, hEnd⟩ :=
          segment_of_invLPCB centreC placeC entry q first w
            (fun s => hex_C centreC placeC entry w s)
            (fun s hs a => hsearch_C centreC placeC entry w s hs a) c r hIC
            (hreadyB w c r hIC)
        exact ⟨c', t, hsW, Or.inr hEnd⟩)
      (hended w) (hlastMatch w) (hlastMismatch w) (hmismatch w) (hfound w) (hfoundBg w)
      (hfoundReplay w)) (hstr w)

#print axioms h_oracle_of_leaves4

end PalPeg.CloseoutOracle5
