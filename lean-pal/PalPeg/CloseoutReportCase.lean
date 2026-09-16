import PalPeg.GalilOracleMC4
import PalPeg.GalilReadyFuelUses
import PalPeg.GalilInvPlus3

/-!
# The crossing case, on `ReadyFuel`

`GalilOracleMC4.cycleOracleMC2C_of_pieces''` splits the cycle at the checkpoint
cell `2m-1`.  The middle branch — the segment *crosses* the cell — is
`GalilLeafReport.reachAtC2_of_cross`, and it is one of the three sites at which
the refuted preservation leaf

```
hpres : ∀ s a v, SearchReady (searchLens.get s) → searchEffect P a s v → SearchReady v
```

still enters the assembly.  It enters there twice: once as
`GalilLeafReport.watchSegE_searchReady` (readiness carried along the prefix of
the segment that stops on `2m-2`), and once as the `hpres` argument of
`GalilOracleMC2.reachAtC2_of_target_match` (readiness at the landing of the
report comparison itself).

`GalilReadyFuelUses.reachAtC2_of_target_matchF` already removed the second use in
favour of `ReadyFuel (searchLens.get t) 1 1`.  This file removes the first as
well, and answers the accounting question: **the `ReadyFuel … 1 1` at the
crossing state is derivable from the *entry* budget** — the very
`hreadyB`-shaped premise of `GalilSegmentConstructB.h_oracle_of_leaves'''` —
and needs no new leaf, provided the report comparison's fuel premise is stated
with a *residue*: `ReadyFuel (searchLens.get t) (n+1) (K+1)` for arbitrary `n K`,
not the tight `ReadyFuel … 1 1` of `GalilReadyFuelUses`.  The tight form is not
derivable — `readyFuel_mono` only ever weakens (raises `n`, lowers `K`), so a
short prefix cannot burn the entry index `headRank r.right * 2048 + c.clock`
down to `1`.  The residual form is, and `readyFuel_effect_true` needs nothing
more.  Two facts do it:

* `readyFuel_watchSegE`: fuel is transported along a segment that ends with the
  chain idle.  The `readyFuel_effect_*` lemmas demand `chain = idle` at the
  event, and `GalilScaffoldTopSearchRun.watchSegE_idle_start` propagates
  idleness *backwards* from the end, so every event of such a segment is served.
  A background event spends one unit, a comparison one unit and one match.
* `rank_count`: along any segment `headRank t.right + es.count true =
  headRank s.right`, so the match half of the entry budget, `headRank r.right`,
  covers the segment's comparisons *plus* the report comparison as soon as the
  crossing state can still move right (`canRight`, i.e. `1 ≤ headRank s₁.right`).
  The length half is covered by `GalilLeafEnds.exhausted_of_long` read
  contrapositively at the same `canRight`.

Nothing is taken from the *exit* budget: the exit `t` of the crossing cycle is
not the report state, it lies beyond it.

The main theorem is stated over the stage-carrying landing type
`GalilInvPlus3.InvLPS` and returns `ReachAtC3`, so it drops straight into
`GalilInvPlus3.cycleOracleMC3_of_pieces`'s crossing branch.
`reachAtC3_of_target_matchF` is `GalilInvPlus3.reachAtC3_of_target_match` with
its single `hpres t true vq hs.search hq` replaced by
`readyFuel_ready (readyFuel_effect_true P hs.idle hready hq)`, exactly as
`GalilReadyFuelUses` did at the `MC2` level.

No not-found hypothesis is added at the last letter: the crossing branch is
entered on `2 * m - 1 ≤ position t.right` alone.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutReportCase

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton PalPeg.GalilOracleDischarge PalPeg.GalilOracleLocal
open PalPeg.GalilCheckpoints PalPeg.GalilTraceCost PalPeg.GalilLexMeasure
open PalPeg.GalilInvPlus PalPeg.GalilInvPlus2 PalPeg.GalilOracleMC
open PalPeg.GalilGlueBLeaves PalPeg.GalilBranchInvariants2 PalPeg.GalilSegmentConstruct
open PalPeg.GalilOracleM PalPeg.GalilOracleMC2 PalPeg.GalilFinalAssembly2
open PalPeg.GalilOracleLeaves2 PalPeg.GalilOracleMC3
open PalPeg.GalilLeafPos PalPeg.GalilLeafReport PalPeg.GalilLeafEnds
open PalPeg.GalilSegmentConstructB PalPeg.GalilReadyFuelUses PalPeg.GalilOneFallback
open PalPeg.GalilFoundStage PalPeg.GalilFoundStageInv PalPeg.GalilInvPlus3

/-! ## 1. Fuel along a segment that ends idle -/

/-- **`ReadyFuel` is carried along a segment whose end has an idle chain.**
The `readyFuel_effect_*` lemmas need `chain = idle` at each event;
`watchSegE_idle_start` supplies it for every suffix, hence for every event.  A
background event spends one unit of fuel, a comparison one unit and one match. -/
theorem readyFuel_watchSegE (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    {es : List Bool} {c c' : Control} {s t : GalilVM}
    (h : WatchSegE P q first delay es c s c' t) (ht : t.chain = ChainVM.idle) :
    ∀ n K : ℕ, ReadyFuel (searchLens.get s) (n + es.length) (K + es.count true) →
      ReadyFuel (searchLens.get t) n K := by
  induction h with
  | stop c s => intro n K h0; simpa using h0
  | wait c s s' hm hr hn hb rest ih =>
      intro n K h0
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hse⟩ := backgroundS_fields P q first hb
      have hs' : s'.chain = ChainVM.idle := watchSegE_idle_start P q first delay rest ht
      have hs : s.chain = ChainVM.idle := by
        by_contra hne
        exact chainTick_ne_idle (backgroundS_chainTick P q first hb hne) hne hs'
      refine ih ht n K (readyFuel_effect_false P hs ?_ hse)
      refine readyFuel_mono (by simp; omega) (by simp) h0
  | count c s s' hm hr ha hc hb rest ih =>
      intro n K h0
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hse⟩ := backgroundS_fields P q first hb
      have hs' : s'.chain = ChainVM.idle := watchSegE_idle_start P q first delay rest ht
      have hs : s.chain = ChainVM.idle := by
        by_contra hne
        exact chainTick_ne_idle (backgroundS_chainTick P q first hb hne) hne hs'
      refine ih ht n K (readyFuel_effect_false P hs ?_ hse)
      refine readyFuel_mono (by simp; omega) (by simp) h0
  | countR c s s' hm hr hc hidle hb rest ih =>
      intro n K h0
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hse⟩ := backgroundS_fields P q first hb
      refine ih ht n K (readyFuel_effect_false P hidle ?_ hse)
      refine readyFuel_mono (by simp; omega) (by simp) h0
  | «match» c s vs vq o hm hr ha hc hne hcmp hmt hq ho rest ih =>
      intro n K h0
      have hs' : (afterCompare s vs vq).chain = ChainVM.idle :=
        watchSegE_idle_start P q first delay rest ht
      have hmatch : read (left s.left) = read (right s.right) := by
        obtain ⟨⟨hl0, hr0, -⟩, -⟩ := hcmp
        rw [scanLens.get_set] at hl0 hr0
        have hmp := matched_parts P q first hmt
        rw [hl0, hr0] at hmp; exact hmp
      obtain ⟨-, -, htk⟩ := compare_parts P q first hcmp hmatch
      have hs : s.chain = ChainVM.idle := by
        by_contra hne0
        rw [afterCompare_chain] at hs'
        exact chainTick_ne_idle htk hne0 hs'
      exact absurd hs hne
  | matchIdle c s vs vq o hm hr ha hc hidle hl hrr hvs hmt hq hnf ho rest ih =>
      intro n K h0
      refine ih ht n K (readyFuel_effect_true P hidle ?_ hq)
      refine readyFuel_mono (by simp; omega) (by simp) h0
  | matchIdleR c s vs vq o hm hr hc ha hidle hl hrr hvs hmt hq hnf ho rest ih =>
      intro n K h0
      refine ih ht n K (readyFuel_effect_true P hidle ?_ hq)
      refine readyFuel_mono (by simp; omega) (by simp) h0

#print axioms readyFuel_watchSegE

/-! ## 2. The rank spent by a segment is its comparison count -/

/-- **The right head's rank descends by exactly the comparisons.**  Background
events leave the right head alone; each comparison moves it one half step
(`GalilLeafEnds.rank_right`). -/
theorem rank_count (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    {es : List Bool} {c c' : Control} {s t : GalilVM}
    (h : WatchSegE P q first delay es c s c' t) :
    headRank t.right + es.count true = headRank s.right := by
  induction h with
  | stop c s => simp
  | wait c s s' hm hr hn hb rest ih =>
      have hrr : s'.right = s.right := (background_frame P q first hb).2.1
      rw [List.count_cons]; simp only [beq_iff_eq]; rw [hrr] at ih; simpa using ih
  | count c s s' hm hr ha hc hb rest ih =>
      have hrr : s'.right = s.right := (background_frame P q first hb).2.1
      rw [List.count_cons]; simp only [beq_iff_eq]; rw [hrr] at ih; simpa using ih
  | countR c s s' hm hr hc hidle hb rest ih =>
      have hrr : s'.right = s.right := (background_frame P q first hb).2.1
      rw [List.count_cons]; simp only [beq_iff_eq]; rw [hrr] at ih; simpa using ih
  | «match» c s vs vq o hm hr ha hc hne hcmp hmt hq ho rest ih =>
      have hmatch : read (left s.left) = read (right s.right) := by
        obtain ⟨⟨hl0, hr0, -⟩, -⟩ := hcmp
        rw [scanLens.get_set] at hl0 hr0
        have hmp := matched_parts P q first hmt
        rw [hl0, hr0] at hmp; exact hmp
      have hvr : vs.right = right s.right := (compare_parts P q first hcmp hmatch).2.1
      have hrank : headRank (afterCompare s vs vq).right + 1 = headRank s.right := by
        rw [afterCompare_right, hvr]; exact rank_right s.right ha
      rw [List.count_cons]
      simp only [beq_self_eq_true, if_true]
      omega
  | matchIdle c s vs vq o hm hr ha hc hidle hl hrr hvs hmt hq hnf ho rest ih =>
      have hrank : headRank (afterCompare s vs vq).right + 1 = headRank s.right := by
        rw [afterCompare_right, hrr]; exact rank_right s.right ha
      rw [List.count_cons]
      simp only [beq_self_eq_true, if_true]
      omega
  | matchIdleR c s vs vq o hm hr hc ha hidle hl hrr hvs hmt hq hnf ho rest ih =>
      have hrank : headRank (replayDec true (afterCompare s vs vq)).right + 1
          = headRank s.right := by
        rw [replayDec_right, afterCompare_right, hrr]; exact rank_right s.right ha
      rw [List.count_cons]
      simp only [beq_self_eq_true, if_true]
      omega

#print axioms rank_count

/-! ## 3. The report comparison over `InvLPS`, on `ReadyFuel` -/

/-- **`GalilInvPlus3.reachAtC3_of_target_match` without `hpres`.**  Identical
proof; the single readiness site is served by one comparison unit of fuel at the
segment exit, as in `GalilReadyFuelUses.reachAtC2_of_target_matchF`. -/
theorem reachAtC3_of_target_matchF (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m : ℕ) (hm1 : 1 ≤ m) (hmle : m ≤ raw.length)
    (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM)
    (hIN : InvLPS (PofC centre place entry raw) q first raw c r)
    (n K : ℕ) (hready : ReadyFuel (searchLens.get t) (n + 1) (K + 1))
    (hsW : SegReachedW centre place entry q first raw c r c' t)
    (hT : AtTarget m c' t)
    (hmt : read (left t.left) = read (right t.right))
    (vq : SearchVM) (hq : searchEffect (PofC centre place entry raw) true t vq)
    (hnf : vq.search.mode ≠ .found) :
    ReachAtC3 (PofC centre place entry raw) q first raw m c r := by
  classical
  set P : Shared := PofC centre place entry raw with hP
  have hIC : InvLPC raw c r := hIN.1
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
  -- the stage data: the report comparison is a `matchIdle` step of the segment
  have hmid : WatchSegE P q first 2048 [true] c' t
      {c' with clock := 2048, output := o, replaying := false} u :=
    .matchIdle c' t vs vq o hs.mode hnr hav hc1 hs.idle rfl rfl rfl hmt0 hq hnf ho (.stop _ _)
  have hstage : ReplayStage raw P q first
      {c' with clock := 2048, output := o, replaying := false} u :=
    replayStage_trans (replayStage_trans hIN.2 hw) hmid
  refine ⟨_, es.length + (0 + 1), L ++ [GalilCostedFallback.cmpPiece (2 * m - 1) w hw'], hall,
    hcr, hrp, hfr, fun _ => ⟨_, u, 0, [], .zero _ (stepsAll_last hall), costedRun_nil u, ?_, ?_⟩⟩
  · have hIS : PalPeg.GalilReplaySegment.InvScan 2048 raw
        {c' with clock := 2048, output := o, replaying := false} u (R + 1) := by
      refine PalPeg.GalilReplaySegment.inv_after_replay 2048 raw _ u (R + 1) hs.mode rfl rfl
        (by rw [hu, afterCompare_chain]) ?_ hrp.centre ?_ ?_ ?_
      · exact matched_invariant' raw vq (vs := vs) rfl rfl hmt hav hi
      · exact readyFuel_ready (readyFuel_effect_true P hs.idle hready hq)
      · rw [hu, afterCompare_replay]; exact hrep
      · exact PalPeg.GalilReplaySegment.shiftIdle_congr
          (PalPeg.GalilReplaySegment.afterCompare_remaining t vs vq) hs.shiftIdle
    have hIL : InvLP raw {c' with clock := 2048, output := o, replaying := false} u :=
      ⟨invL_of_run hall (Or.inr ⟨R + 1, hIS⟩), hEu⟩
    exact ⟨⟨invLP2_of_stepsAll centre place entry q first hIC.1.2 hall hIL,
      centreRep_congr hcu hIC.2⟩, hstage⟩
  · have h1 : position u.right = 2 * m - 1 := hrp.atPlace
    omega

#print axioms reachAtC3_of_target_matchF

/-! ## 4. The crossing case, over `InvLPS`, off `hpres` -/

/-- **`GalilLeafReport.reachAtC2_of_cross` over `InvLPS` and off `hpres`.**  A
segment entering strictly below the checkpoint cell `2m-1` and reaching it
passes through the state `s₁` on `2m-2` whose next tick is the report
comparison.  Both former `hpres` sites are served by the entry budget: the fuel
is carried to `s₁` by `readyFuel_watchSegE` (the prefix ends idle), and what is
left there —
`ReadyFuel … (headRank r.right * 2048 + c.clock - es₁.length - 1 + 1)
(headRank r.right - es₁.count true - 1 + 1)` — still has the one comparison unit
the report tick spends.

The two side conditions of the transport are read off `canRight s₁.right`, which
the crossing tick supplies: `rank_count` turns the match budget
`headRank r.right` into `headRank s₁.right + es₁.count true ≥ es₁.count true + 1`,
and `GalilLeafEnds.exhausted_of_long`, read contrapositively, bounds the prefix
length by `headRank r.right * 2048 + c.clock - 1`. -/
theorem reachAtC3_of_crossF (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m : ℕ) (hm1 : 1 ≤ m) (hmle : m ≤ raw.length)
    {c c' : Control} {r t : GalilVM}
    (hIN : InvLPS (PofC centre place entry raw) q first raw c r)
    (hready : ReadyFuel (searchLens.get r) (headRank r.right * 2048 + c.clock)
      (headRank r.right))
    (hsW : SegReachedW centre place entry q first raw c r c' t)
    (hlt : position r.right < 2 * m - 1) (hge : 2 * m - 1 ≤ position t.right) :
    ReachAtC3 (PofC centre place entry raw) q first raw m c r := by
  classical
  have hIC : InvLPC raw c r := hIN.1
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
  have hrank1 : headRank s1.right + es1.count true = headRank r.right :=
    rank_count (PofC centre place entry raw) q first 2048 hw1
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
      -- the crossing state can still move right: both halves of the budget
      have hrk : 1 ≤ headRank s1.right := by
        have := rank_right s1.right ha2; omega
      have hlen1 : es1.length + 1 ≤ headRank r.right * 2048 + c.clock := by
        by_contra hcon
        exact (exhausted_of_long (PofC centre place entry raw) q first 2048 (by norm_num)
          hw1 hclkC (by omega)) ha2
      have hfuel1 : ReadyFuel (searchLens.get s1)
          ((headRank r.right * 2048 + c.clock - es1.length - 1) + 1)
          ((headRank r.right - es1.count true - 1) + 1) :=
        readyFuel_watchSegE (PofC centre place entry raw) q first 2048 hw1 hidle1 _ _
          (readyFuel_mono (by omega) (by omega) hready)
      have hsr1 : SearchReady (searchLens.get s1) := readyFuel_ready hfuel1
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
      exact reachAtC3_of_target_matchF centre place entry q first raw m hm1 hmle
        c r c1 s1 hIN _ _ hfuel1 hsW1 ⟨hnr1, hc2, ha2, hpos1', hrep1⟩ hmtread vq hq2 hnf2

#print axioms reachAtC3_of_crossF
