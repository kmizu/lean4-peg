import PalPeg.CloseoutWatchRound49
import PalPeg.CloseoutOracle6
import PalPeg.GalilFoundLandingL

/-!
# Closeout found route 1 — the entry of the found cycle

`hfound` (of `GalilOracleMC3.h_oracle_of_leaves''` and its successor
`CloseoutOracle6.h_oracle_of_leaves5`) reads

```
∀ w m c r c' t, 1 ≤ m → m ≤ w.length → InvLPC w c r → position r.right ≤ 2*m-1 →
  SegReachedW centreC placeC entry q first w c r c' t →
  c'.clock = 1 → canRight t.right → read (left t.left) = read (right t.right) →
  (∃ vq, searchEffect (PofC …) true t vq ∧ vq.search.mode = .found) →
  FoundRouteMC2 (PofC …) q first w m c r c' t
```

Its route half starts at the **found tick**: the matched comparison at `t`
whose search quantum reports `found`, so `chainAt true true` fires
`chain.start()`.  `CloseoutWatchRound2.FoundCompareCtxC` is exactly the record
of that tick, and it is the entry pack of the whole `foundExit_compare_final*`
chain (`CloseoutWatchRound49`), which turns it into `FoundExitLPS`.  Until now
`FoundCompareCtxC` was carried as a *hypothesis*.

This file **discharges it**: from `hfound`'s own hypotheses,
`FoundCompareCtxC` is free.  The facts it needs beyond what `SegReachedW`
already records are proved here:

* `invLPC_not_replaying` — the cycle entry is not replaying (both branches of
  `InvS` pin `c.replaying = false`);
* `watchSegE_replaying_false` — a watch segment entered with the flag down
  exits with the flag down (the two `…R` constructors need it up);
* `exists_chainMatched_chainStart` — `chain.start()` always produces a
  non-idle chain (`chainStart` is a `.copy`, and `ChainMatched.copy` matches
  it);
* `exists_refresh` — the output refresh is total;
* `centre_split` — `CentreRep` *is* the `represent ⟨a :: ls, gap⟩` shape.

`found_first_tick` then executes the tick: the segment run extended by the
found comparison, with the landing control `{c' with clock := 2048,
output := oF, replaying := false}`, its `OutputRel`, its `ScanInvariant` at
radius `+1`, and a running chain.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

namespace PalPeg.CloseoutFoundRoute1

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton PalPeg.GalilInvPlus PalPeg.GalilInvPlus2
open PalPeg.GalilOracleDischarge PalPeg.GalilOracleLocal
open PalPeg.GalilFoundLandingL PalPeg.GalilCostedFound
open PalPeg.CloseoutContracts
open PalPeg.GalilFoundStage
open PalPeg.CloseoutWatchRound2 (FoundCompareCtxC)
open PalPeg.CloseoutWatchRound3 (DistanceNonnegC)
open PalPeg.CloseoutWatchRound4 (ZeroLagAtMatchC)
open PalPeg.CloseoutWatchRound6 (RightCanC RightSaneC StartLeC LedgerOriginC PeriodMatchC)
open PalPeg.CloseoutWatchRound7 (PrepLandingWatchC ShiftReachC ShiftRoundAtC BreakTermData)
open PalPeg.CloseoutWatchRound10 (FoundDpAtC)
open PalPeg.CloseoutPrepInputs2 (MismatchExitG)
open PalPeg.CloseoutPrepInputs3 (PrepInputsG3)
open PalPeg.CloseoutWatchRound30 (ShiftCopyIdleC MismatchClassifierTieC)
open PalPeg.CloseoutWatchRound31 (FoundExitLPS FallbackReachS)
open PalPeg.CloseoutWatchRound33 (ShiftRunCL)
open PalPeg.CloseoutWatchRound34 (ShiftBreakOracleC ShiftBreakFitC)
open PalPeg.CloseoutWatchRound37 (ShiftRoundInvCL ShiftOriginRestCL)
open PalPeg.CloseoutWatchRound44 (LandingFreshC')
open PalPeg.CloseoutWatchRound45 (PrepBirthLagC')
open PalPeg.CloseoutWatchRound49 (WatchFreshC foundExit_compare_final19)
open PalPeg.CloseoutWatchRun (LiveScanWatch roundFuel)

/-! ## 1. The entry flag -/

/-- **(P1) CLOSED.**  A cycle entry state is not replaying: both branches of
`InvS` (`GalilRunInv.Inv.mode`, `GalilReplaySegment.InvScan.mode`) pin it. -/
theorem invLPC_not_replaying {raw : List (Fin 2)} {c : Control} {r : GalilVM}
    (h : InvLPC raw c r) : c.replaying = false := by
  rcases h.1.1.1.1 with hI | ⟨k, hI⟩
  · exact hI.mode.2.1
  · exact hI.mode.2.1

/-- **(P2) CLOSED.**  A watch segment entered with the replay flag down exits
with it down: `countR` / `matchIdleR` are the only constructors that keep the
flag up, and both require it up at their entry. -/
theorem watchSegE_replaying_false (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    {es : List Bool} {c c' : Control} {s t : GalilVM}
    (h : WatchSegE P q first delay es c s c' t) :
    c.replaying = false → c'.replaying = false := by
  induction h with
  | stop c s => intro h0; exact h0
  | wait c s s' hm hrc hn hb _ ih => intro h0; exact ih h0
  | count c s s' hm hrc ha hc hb _ ih => intro h0; exact ih h0
  | «match» c s vs vq o hm hrc ha hc hne hcmp hmt hq ho _ ih => intro h0; exact ih rfl
  | matchIdle c s vs vq o hm hrc ha hc hidle hl hrr hvs hmt hq hnf ho _ ih =>
      intro h0; exact ih rfl
  | countR c s s' hm hrc hc hidle hb _ ih =>
      intro h0; rw [h0] at hrc; exact absurd hrc (by simp)
  | matchIdleR c s vs vq o hm hrc hc ha hidle hl hrr hvs hmt hq hnf ho _ ih =>
      intro h0; rw [h0] at hrc; exact absurd hrc (by simp)

/-- **(P1)+(P2) CLOSED.**  The found tick's control is not replaying. -/
theorem segReachedW_not_replaying (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) {c c' : Control} {r t : GalilVM}
    (hIC : InvLPC raw c r)
    (hsW : SegReachedW centre place entry q first raw c r c' t) :
    c'.replaying = false := by
  obtain ⟨es0, hseg0⟩ := hsW.2
  exact watchSegE_replaying_false _ _ _ _ hseg0 (invLPC_not_replaying hIC)

/-! ## 2. `chain.start()` and the refresh are total -/

/-- **(P3) CLOSED.**  `chainStart` is a `.copy`, so `ChainMatched` has a
witness and it is not idle. -/
theorem exists_chainMatched_chainStart (answer : GalilScaffoldTape.Tape) (cen : Fin 3)
    (walker : GalilScaffoldPlace.Place) (ver : PlaceHead) (radius : Counter) :
    ∃ ch : ChainVM,
      ChainMatched (chainStart answer cen walker ver radius) ch ∧ ch ≠ ChainVM.idle :=
  ⟨_, ChainMatched.copy answer reset walker (GalilScaffoldChainPeriod.start cen) radius radius ver,
    fun h => ChainVM.noConfusion h⟩

/-- **(P4) CLOSED.**  The output refresh is total. -/
theorem exists_refresh {σ : Type} (F : Frame σ) (s : σ) (old : Bool) :
    ∃ o : Bool, refresh F s old o := by
  by_cases hL : F.onLetter s
  · by_cases hF : F.leftFirst s
    · exact ⟨true, fun _ => ⟨fun _ => hF, fun _ => rfl⟩, fun hn => absurd hL hn⟩
    · exact ⟨false, fun _ => ⟨fun h => absurd h (by simp), fun h => absurd h hF⟩,
        fun hn => absurd hL hn⟩
  · exact ⟨old, fun h => absurd h hL, fun _ => rfl⟩

/-! ## 3. The centre shape -/

/-- **(P5) CLOSED.**  `CentreRep` unfolds to the `represent ⟨a :: ls, gap⟩`
shape asked for by `FoundCompareCtxC`. -/
theorem centre_split {raw : List (Fin 2)} {s : GalilVM} (h : CentreRep raw s) :
    ∃ (a : Fin 2) (ls rs qw : List (Fin 2)) (gap : Bool),
      raw = (a :: ls).reverse ++ rs ++ qw ∧
      s.center = represent ⟨a :: ls, gap⟩ (rs.map some) qw := by
  obtain ⟨⟨xs, rs, qw, hlay, hraw⟩, hfoc⟩ := h
  cases xs with
  | nil => exact absurd (by rw [hlay]; rfl) hfoc
  | cons a ls =>
      refine ⟨a, ls, rs, qw, s.center.gap, hraw, ?_⟩
      show s.center = (⟨layout (a :: ls) (rs.map some) qw, s.center.gap⟩ : PlaceHead)
      rw [← hlay]

/-! ## 4. The found compare context is free -/

/-- **CLOSED — the first genuine step of the found route.**  From exactly the
hypotheses of `hfound`, the found-tick record `FoundCompareCtxC` (the input
pack of `CloseoutWatchRound49.foundExit_compare_final19`) holds. -/
theorem foundCompareCtxC_of_found (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) {c c' : Control} {r t : GalilVM}
    (hIC : InvLPC raw c r)
    (hsW : SegReachedW centre place entry q first raw c r c' t)
    (hc1 : c'.clock = 1) (hav : canRight t.right)
    (hmt : read (left t.left) = read (right t.right))
    (hq : ∃ vq, searchEffect (PofC centre place entry raw) true t vq ∧
      vq.search.mode = .found) :
    ∃ (cP : Control) (sP : GalilVM),
      FoundCompareCtxC centre place entry q first raw c r cP sP := by
  obtain ⟨es0, hseg0⟩ := hsW.2
  obtain ⟨vq, hqe, hfound⟩ := hq
  obtain ⟨a, ls, rs, qw, gap, hraw, hcen⟩ := centre_split hIC.2
  obtain ⟨ch, hch, hchne⟩ := exists_chainMatched_chainStart (vq.dp.config.tapes 11)
    ((PofC centre place entry raw).centre t) ((PofC centre place entry raw).place t)
    t.center t.radius
  obtain ⟨oF, hoF⟩ := exists_refresh (galilFrame (PofC centre place entry raw) q first)
    (afterCompare t ⟨left t.left, right t.right, ch⟩ vq) c'.output
  exact ⟨_, _, es0, c', t, vq, ch, oF, a, ls, rs, qw, gap, hraw, hseg0, hsW.1.mode,
    segReachedW_not_replaying centre place entry q first raw hIC hsW, hc1, hav, hsW.1.idle,
    by rw [hsW.1.center]; exact hcen, hqe, hfound, hmt, hch, hchne, hoF, rfl, rfl⟩

/-! ## 5. The tick itself, with its accounting -/

/-- **CLOSED — the found tick executed.**  The idle segment extended by the
found comparison: `es0.length + 1` sound ticks from the cycle entry to the
preparation entry, whose control is fresh, whose output relation holds, whose
scan invariant is one radius up, and whose chain is running. -/
theorem found_first_tick (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) {c c' : Control} {r t : GalilVM}
    (hIC : InvLPC raw c r)
    (hsW : SegReachedW centre place entry q first raw c r c' t)
    (hc1 : c'.clock = 1) (hav : canRight t.right)
    (hmt : read (left t.left) = read (right t.right))
    (hq : ∃ vq, searchEffect (PofC centre place entry raw) true t vq ∧
      vq.search.mode = .found) :
    ∃ (cP : Control) (sP : GalilVM) (k R : ℕ),
      FoundCompareCtxC centre place entry q first raw c r cP sP ∧
      StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048 (SoundOut raw)
        (k + 1) ⟨c, r⟩ ⟨cP, sP⟩ ∧
      cP.mode = Mode.scan ∧ cP.replaying = false ∧ cP.clock = 2048 ∧
      OutputRel raw cP sP ∧
      ScanInvariant raw (position r.center) R sP.left sP.right ∧
      sP.chain ≠ ChainVM.idle := by
  obtain ⟨es0, hseg0⟩ := hsW.2
  obtain ⟨vq, hqe, hfound⟩ := hq
  obtain ⟨a, ls, rs, qw, gap, hraw, hcenR⟩ := centre_split hIC.2
  obtain ⟨ch, hch, hchne⟩ := exists_chainMatched_chainStart (vq.dp.config.tapes 11)
    ((PofC centre place entry raw).centre t) ((PofC centre place entry raw).place t)
    t.center t.radius
  obtain ⟨oF, hoF⟩ := exists_refresh (galilFrame (PofC centre place entry raw) q first)
    (afterCompare t ⟨left t.left, right t.right, ch⟩ vq) c'.output
  have hnr : c'.replaying = false :=
    segReachedW_not_replaying centre place entry q first raw hIC hsW
  have hI : InvLP raw c r := PalPeg.GalilOracleMC2.invLPC_invLP hIC
  obtain ⟨R0, hstep, hscan0, hRR, hcanon, hSpan, hscanT, houtF, hcenT⟩ :=
    at_found centre place entry q first raw hI hseg0
  have hrun : StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048 (SoundOut raw)
      es0.length ⟨c, r⟩ ⟨c', t⟩ :=
    watchSegE_stepsAll_len raw (PofC centre place entry raw) rfl rfl q first 2048 hseg0
      (position r.center) R0 hscan0 hI.1.2
  have htick := found_start_match (PofC centre place entry raw) q first 2048 c' t
    hsW.1.mode hnr hc1 hav hsW.1.idle vq hqe hfound hmt ch hch oF hoF
  have hscanT' : ScanInvariant raw (position r.center) (R0 + es0.count true) t.left t.right := by
    rw [← hcenT]; exact hscanT
  obtain ⟨hinv1, hout1⟩ :=
    outputRel_matched_refresh' raw (PofC centre place entry raw) rfl rfl q first vq
      (vs := ⟨left t.left, right t.right, ch⟩) rfl rfl hmt hav hscanT' c'.output oF hoF
      {c' with clock := 2048, output := oF, replaying := false} rfl
  refine ⟨{c' with clock := 2048, output := oF, replaying := false},
    afterCompare t ⟨left t.left, right t.right, ch⟩ vq, es0.length,
    R0 + es0.count true + 1,
    ⟨es0, c', t, vq, ch, oF, a, ls, rs, qw, gap, hraw, hseg0, hsW.1.mode, hnr, hc1, hav,
      hsW.1.idle, by rw [hsW.1.center]; exact hcenR, hqe, hfound, hmt, hch, hchne, hoF, rfl, rfl⟩,
    stepsAll_trans hrun (.succ houtF htick (.zero _ hout1)),
    hsW.1.mode, rfl, rfl, hout1, hinv1, ?_⟩
  rw [afterCompare_chain]; exact hchne

/-! ## 6. The found-route consumer with the context discharged -/

/-- **CLOSED.**  The preparation entry of a found tick is a *fresh* scan
control: mode, flag and clock are all fixed by `FoundCompareCtxC` itself. -/
theorem foundCompareCtxC_control {centre : GalilVM → Fin 3}
    {place : GalilVM → GalilScaffoldPlace.Place} {entry q : ℕ} {first : Fin 9}
    {raw : List (Fin 2)} {c cP : Control} {r sP : GalilVM}
    (h : FoundCompareCtxC centre place entry q first raw c r cP sP) :
    cP.mode = Mode.scan ∧ cP.replaying = false ∧ cP.clock = 2048 := by
  obtain ⟨es0, cF, sF, vq, ch, oF, a, ls, rs, qw, gap, hraw, hseg, hmF, hrF, hcF, havF, hidle,
    hcen, hqe, hf, hmt, hch, hchne, hoF, hcP, hsP⟩ := h
  subst hcP
  exact ⟨hmF, rfl, rfl⟩

/-- **`CloseoutWatchRound49.foundExit_compare_final19` with the found-compare
context, the fresh-control triple and the stage data discharged.**

Where `final19` *assumed* `FoundCompareCtxC … cP sP`, `cP.mode = .scan`,
`cP.replaying = false`, `1 ≤ cP.clock` and `ReplayStage`, `final20` takes the
data `hfound` actually hands over — the segment, the full clock, the available
right head, the match and the found quantum — and builds the preparation entry
`⟨cP, sP⟩` itself (`foundCompareCtxC_of_found`).  The remaining packs, which
all speak about that entry, are quantified over it. -/
theorem foundExit_compare_final20 (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (m h lower span : ℕ) (μ : ℕ → Control → GalilVM → ℕ)
    (hP : Decodes (PofC centre place entry w))
    (hex : ∀ s, (PofC centre place entry w).replayExhausted s = zero s.replay)
    (hready : PalPeg.GalilReplayChainSeg.ChainTickable)
    (hcan : RightCanC) (hsane : RightSaneC) (hstart : StartLeC)
    (hor : LedgerOriginC centre place entry q first 2048 w)
    (hzl : ZeroLagAtMatchC) (hnn : DistanceNonnegC) (hpm : PeriodMatchC)
    {c c' : Control} {r t : GalilVM}
    (hE : StageEntryC (PofC centre place entry w) q first w c r)
    (hsW : SegReachedW centre place entry q first w c r c' t)
    (hc1 : c'.clock = 1) (hav : canRight t.right)
    (hmt : read (left t.left) = read (right t.right))
    (hq : ∃ vq, searchEffect (PofC centre place entry w) true t vq ∧
      vq.search.mode = .found)
    (hat : FoundDpAtC centre place entry q first w lower span h c r)
    (hreach : ShiftReachC centre place entry q first w h)
    (hround : ShiftRoundAtC centre place entry q first w m h lower)
    (h3 : ShiftCopyIdleC) (h4 : ShiftRunCL)
    (hinv : ShiftRoundInvCL w)
    (horacle : ∀ h', ShiftBreakOracleC centre place entry q first w h' (μ h'))
    (hfit : ∀ h', ShiftBreakFitC centre place entry q first w m h')
    (hrest : ShiftOriginRestCL centre place entry q first w lower)
    (htie : MismatchClassifierTieC (PofC centre place entry w) q first)
    (hfreshClk : WatchFreshC (PofC centre place entry w) q first)
    (hstepBreak : ∀ (c0 : Control) (s0 : GalilVM), LiveScanWatch c0 s0 →
      PalPeg.CloseoutWatchRun.RoundStepC (PofC centre place entry w) q first (roundFuel h)
        (BreakTermData centre place entry q first w m h) c0 s0)
    (hpack : ∀ (cP : Control) (sP : GalilVM) (a : Fin 2) (ls rs qw : List (Fin 2)) (gap : Bool),
      FoundCompareCtxC centre place entry q first w c r cP sP →
      w = (a :: ls).reverse ++ rs ++ qw →
      PrepInputsG3 (PofC centre place entry w) q first ⟨a :: ls, gap⟩ lower span cP sP ∧
      MismatchExitG (PofC centre place entry w) q first w m c r cP sP ∧
      FallbackReachS (PofC centre place entry w) q first w m c r cP sP ∧
      PrepLandingWatchC (PofC centre place entry w) q first cP sP ∧
      PrepBirthLagC' (PofC centre place entry w) q first c r cP sP ∧
      LandingFreshC' (PofC centre place entry w) q first cP sP ∧
      (∀ sF : GalilVM,
        PalPeg.CloseoutWatchRound5.BreakLandingC centre place entry q first w h sF cP sP)) :
    FoundExitLPS (PofC centre place entry w) q first w m c r := by
  obtain ⟨cP, sP, hctx⟩ :=
    foundCompareCtxC_of_found centre place entry q first w hE.invLPC hsW hc1 hav hmt hq
  obtain ⟨es0, cF, sF, vq, ch, oF, a, ls, rs, qw, gap, hraw, hseg, hmF, hrF, hcF, havF, hidle,
    hcen, hqe, hf, hmtF, hch, hchne, hoF, hcPe, hsPe⟩ := id hctx
  obtain ⟨hprep, hmis, hfbS, hwatch, hbirth, hfresh, hland⟩ :=
    hpack cP sP a ls rs qw gap hctx hraw
  obtain ⟨hmP, hrP, hcP⟩ := foundCompareCtxC_control hctx
  exact foundExit_compare_final19 centre place entry q first w m h lower span μ hP hex hready
    hcan hsane hstart hor hzl hnn hpm hE hsW a ls rs qw gap hprep hmis hctx hfbS hE.stage
    hmP hrP (by rw [hcP]; omega) hwatch hat hreach hround h3 h4 hinv horacle hfit hrest htie
    hbirth hfreshClk hfresh hland hstepBreak


#print axioms invLPC_not_replaying
#print axioms watchSegE_replaying_false
#print axioms segReachedW_not_replaying
#print axioms exists_chainMatched_chainStart
#print axioms exists_refresh
#print axioms centre_split
#print axioms foundCompareCtxC_of_found
#print axioms found_first_tick
#print axioms foundCompareCtxC_control
#print axioms foundExit_compare_final20

end PalPeg.CloseoutFoundRoute1
