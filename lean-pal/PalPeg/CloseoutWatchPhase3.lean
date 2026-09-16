import PalPeg.CloseoutWatchPhase2
import PalPeg.GalilCandidatePeriod

/-!
# The watch phase, third pass: the break tail's palindromes are already paid for

`CloseoutWatchPhase2` named two per-instance tails, `ShiftTailC` and
`NoShiftTailC`, and proved the two raw routes from them.  Both were named open
*as a whole*, with the honest reason that a preparation landing determines
neither where the terminal mismatch falls nor whether the shift guard passes.
That reason is sound for the run-shaped conjuncts; it is **not** sound for all
of them, and this file removes the ones it does not cover.

## Derived here

1. **The two `PalAt` conjuncts of `NoShiftTailC` are consequences of the found
   tick.**  The found comparison's DP result is a `GalilDpCorrect.Candidate` at
   the half-period `h`, and `GalilScaffoldChainInputSupply.candidate_palAt`
   turns a candidate into exactly the two centred palindromes
   `PalAt (encoded raw) (C - h) h` and `PalAt (encoded raw) (C - 2h) (2h)`
   sharing their right end at the head position `C`.  `palAt_pair_of_candidate`
   states this in the shape `NoShiftTailC` asks for (`ys.length + 1` for `h`,
   `position r.center` for `C`).  So these two conjuncts are *word
   combinatorics already established by the search*, not unknown run data: they
   never belonged in an open tail.
2. **`NoShiftTailC0`, the tail with them removed.**  It carries instead the
   found tick's own candidate data — the decomposition
   `raw = (a::ls).reverse ++ rs ++ qw`, the centre representation, the DP
   candidate at `h` — and, per landing, only `ys.length + 1 = h`.
   `noShiftTailC_of_0` rebuilds `NoShiftTailC`, and `breakRouteLPraw_of_tail0`
   gives the raw break route directly.  The cost is one equation,
   `position r.center = position sF.center` (`hpr`): the preparation segment of
   a *no-shift* cycle does not move the centre, which is why
   `foundRouteMC_noshift''` phrases its palindromes at the entry head while the
   search establishes them at the found head.
3. **The branch is a disjunction, not a choice.**  `WatchRouteLPraw` and
   `watchRouteLPraw_of_tails`: whichever of the two tails holds, the cycle has a
   raw route, and `watchRouteLP_of_tails` lifts it past `LandingRestartReach`.
   The two tails are mutually exclusive by the terminal comparison (`matched` or
   not), so the closeout never has to supply both.
4. **`LandingRestartReach` is `Inv` at the landings.**
   `landingRestartReach_of_inv` — if every landing reachable from the cycle
   entry satisfies the full `Inv`, the reach statement is free
   (`CloseoutWatchPhase2.landingRestart_of_inv`).  Equivalently
   (`landingRestartReach_of_restarted`) it suffices that each such landing carry
   one `Restarted` witness with its `StageEntry` budget — the form the main-loop
   theorems (`GalilScaffoldTopLifeRestart.life_restarted`) actually produce.

## The ledger landing (new)

`NoShiftTailC0L` is `NoShiftTailC0` with the preparation landing weakened from
the verbatim `s2.chain = .watch (freshWatch …)` to the ledger datum
`s2.chain = .watch w2` plus a background run `Run (freshWatch …) es' w2`
(`es'.count true = 0`).  That is what the machine produces once the preparation
consumes its period tape.  `foundRouteMC_noshift_L` re-proves
`GalilNoShiftStage.foundRouteMC_noshift'` over it — the two watch runs compose
(`run_appendW`), the extra ticks add no `true`, so `fresh_break_ledger`'s
`distance = radius + 1 + #matched` and `distance = 4h + margin` are unchanged —
and `breakRouteLPraw_of_tail0L` gives the raw break route.  The verbatim tail
is a ledger tail (`noShiftTailC0L_of_0`); nothing needs the converse.

## Still open, NAMED with exact types

* `NoShiftTailC0` (below) and `CloseoutWatchPhase2.ShiftTailC` — the genuinely
  run-shaped residue: the terminal comparison's position and outcome, the shift
  guard, the rounds, and `es.count true = 0` for the no-shift preparation.
  None of these is a function of `cP sP` alone.
* `CloseoutWatchPhase2.LandingRestartReach` — unchanged; §4 only exhibits two
  sufficient forms.
* `hpr : position r.center = position sF.center` is a hypothesis of
  `NoShiftTailC0`, not a new axiom: on the no-shift branch the preparation
  segment performs no `beginShift`, so it is a statement about `WatchSegE`.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutWatchPhase3

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton PalPeg.GalilTraceCost
open PalPeg.GalilInvPlus PalPeg.GalilInvPlus3
open PalPeg.GalilFoundStage PalPeg.GalilFoundStageInv
open PalPeg.GalilInvPlus2 (InvLP2 InvLPC invLP2_invLP)
open PalPeg.CloseoutContracts
open PalPeg.CloseoutWatchPhase (LandingRestart)
open PalPeg.CloseoutWatchPhase2
  (LandingRestartReach RoundsRouteLPraw BreakRouteLPraw ShiftTailC NoShiftTailC
   landingRestart_of_inv landingRestart_of_restarted roundsRouteLP_of_raw breakRouteLP_of_raw
   roundsRouteLPraw_of_tail breakRouteLPraw_of_tail)

/-! ## 1. The break tail's palindromes, from the found tick -/

/-- **Derived.**  A DP candidate at the found head gives exactly the two `PalAt`
facts `NoShiftTailC` asks for, once `h` is named as `ys.length + 1` and the head
position is transported from the found state `sF` to the cycle entry `r`. -/
theorem palAt_pair_of_candidate
    (a : Fin 2) (ls rs q : List (Fin 2)) (gap : Bool) (span lower : ℕ)
    (ys : List (Fin 3)) (raw : List (Fin 2)) (r sF : GalilVM)
    (hraw : raw = (a :: ls).reverse ++ rs ++ q)
    (hcen : sF.center = represent ⟨a :: ls, gap⟩ (rs.map some) q)
    (hpr : position r.center = position sF.center)
    (hc : GalilDpCorrect.Candidate
      ((GalilScaffoldPlace.stream ⟨a :: ls, gap⟩).take (span+1)) lower (ys.length + 1)) :
    Manacher.PalAt (encoded raw) (position r.center - (ys.length + 1)) (ys.length + 1) ∧
    Manacher.PalAt (encoded raw)
      (position r.center - 2 * (ys.length + 1)) (2 * (ys.length + 1)) := by
  have h2 := PalPeg.GalilScaffoldChainInputSupply.candidate_palAt a ls rs q gap span lower
    (ys.length + 1) hc
  simp only at h2
  have hC : position r.center = position (represent ⟨a :: ls, gap⟩ (rs.map some) q) := by
    rw [hpr, hcen]
  rw [hraw, hC]
  exact h2

/-! ## 2. The break tail without them -/

/-- **NAMED (open), per instance.**  `CloseoutWatchPhase2.NoShiftTailC` with the
two `PalAt` conjuncts replaced by the found tick's DP candidate at `h`.  Every
remaining conjunct is genuinely run data: where the terminal comparison falls,
that it matches, and that the preparation credited no comparison. -/
def NoShiftTailC0 (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry qq : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ)
    (c0 : Control) (r : GalilVM) (cP : Control) (sP : GalilVM) : Prop :=
  ∃ (es0 : List Bool) (cF : Control) (sF : GalilVM) (vq : SearchVM) (ch : ChainVM) (oF : Bool)
    (a : Fin 2) (ls rs qw : List (Fin 2)) (gap : Bool) (span lower h : ℕ),
    raw = (a :: ls).reverse ++ rs ++ qw ∧
    sF.center = represent ⟨a :: ls, gap⟩ (rs.map some) qw ∧
    position r.center = position sF.center ∧
    GalilDpCorrect.Candidate
      ((GalilScaffoldPlace.stream ⟨a :: ls, gap⟩).take (span+1)) lower h ∧
    WatchSegE (PofC centre place entry raw) qq first 2048 es0 c0 r cF sF ∧
    cF.mode = .scan ∧ cF.replaying = false ∧ cF.clock = 1 ∧ canRight sF.right ∧
    sF.chain = ChainVM.idle ∧
    searchEffect (PofC centre place entry raw) true sF vq ∧ vq.search.mode = .found ∧
    read (left sF.left) = read (right sF.right) ∧
    ChainMatched (chainStart (vq.dp.config.tapes 11)
      ((PofC centre place entry raw).centre sF) ((PofC centre place entry raw).place sF)
      sF.center sF.radius) ch ∧
    ch ≠ ChainVM.idle ∧
    refresh (galilFrame (PofC centre place entry raw) qq first)
      (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq) cF.output oF ∧
    cP = {cF with clock := 2048, output := oF, replaying := false} ∧
    sP = afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq ∧
    (∀ (es : List Bool) (c2 : Control) (s2 : GalilVM),
      WatchSegE (PofC centre place entry raw) qq first 2048 es cP sP c2 s2 →
      ∃ (cen : Fin 3) (ys : List (Fin 3)) (b : Fin 3) (c3 : Control) (s3 : GalilVM)
        (w3 : GalilScaffoldChainWatch.State) (vs3 : ScanVM) (vq3 : SearchVM) (o3 : Bool)
        (w3' : GalilScaffoldChainWatch.State),
        ys.length + 1 = h ∧
        s2.chain = ChainVM.watch
          (PalPeg.GalilNoShiftStage.freshWatch sF.center cen ys b sF.radius) ∧
        es.count true = 0 ∧
        WatchSeg (PofC centre place entry raw) qq first 2048 c2 s2 c3 s3 ∧
        c3.mode = .scan ∧ c3.replaying = false ∧ c3.clock = 1 ∧
        s3.chain = ChainVM.watch w3 ∧ canRight s3.right ∧
        (galilFrame (PofC centre place entry raw) qq first).compare s3 (scanLens.set s3 vs3) ∧
        (galilFrame (PofC centre place entry raw) qq first).matched (scanLens.set s3 vs3) ∧
        searchEffect (PofC centre place entry raw) true s3 vq3 ∧
        refresh (galilFrame (PofC centre place entry raw) qq first)
          (afterCompare s3 vs3 vq3) c3.output o3 ∧
        (afterCompare s3 vs3 vq3).chain = ChainVM.broken w3' ∧
        negative w3'.margin = false ∧
        position (afterCompare s3 vs3 vq3).right ≤ 2 * m - 1)

/-- **Derived.**  `NoShiftTailC0` is `NoShiftTailC`: the palindromes come from
the candidate by `palAt_pair_of_candidate`. -/
theorem noShiftTailC_of_0 (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m : ℕ) {c0 cP : Control} {r sP : GalilVM}
    (h0 : NoShiftTailC0 centre place entry qq first raw m c0 r cP sP) :
    NoShiftTailC centre place entry qq first raw m c0 r cP sP := by
  obtain ⟨es0, cF, sF, vq, ch, oF, a, ls, rs, qw, gap, span, lower, h, hraw, hcenF, hpr, hcand,
    hseg0, hmF, hrF, hcF, havF, hidle, hq, hfound, hmt, hch, hchne, hoF, hcPeq, hsPeq, htl⟩ := h0
  refine ⟨es0, cF, sF, vq, ch, oF, hseg0, hmF, hrF, hcF, havF, hidle, hq, hfound, hmt, hch,
    hchne, hoF, hcPeq, hsPeq, ?_⟩
  intro es c2 s2 hprepSeg
  obtain ⟨cen, ys, b, c3, s3, w3, vs3, vq3, o3, w3', hys, hwatch2, hes0, hseg, hm3, hr3,
    hc3, hs3, hav3, hcmp3, hmt3, hq3, ho3, hbroken, hmargin, hbound⟩ := htl es c2 s2 hprepSeg
  obtain ⟨hpal1, hpal2⟩ :=
    palAt_pair_of_candidate a ls rs qw gap span lower ys raw r sF hraw hcenF hpr
      (by rw [hys]; exact hcand)
  exact ⟨cen, ys, b, c3, s3, w3, vs3, vq3, o3, w3', hwatch2, hes0, hpal1, hpal2, hseg, hm3, hr3,
    hc3, hs3, hav3, hcmp3, hmt3, hq3, ho3, hbroken, hmargin, hbound⟩

/-- **Derived.**  The raw break route from the reduced tail. -/
theorem breakRouteLPraw_of_tail0 (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m : ℕ)
    (hex : ∀ s, (PofC centre place entry raw).replayExhausted s = zero s.replay)
    {c0 cP : Control} {r sP : GalilVM}
    (hE : StageEntryC (PofC centre place entry raw) qq first raw c0 r)
    (h0 : NoShiftTailC0 centre place entry qq first raw m c0 r cP sP) :
    BreakRouteLPraw (PofC centre place entry raw) qq first raw m c0 r cP sP :=
  breakRouteLPraw_of_tail centre place entry qq first raw m hex hE
    (noShiftTailC_of_0 centre place entry qq first raw m h0)


/-! ## 2b. The ledger landing: `freshWatch` reachable instead of verbatim -/

/-- Watch runs compose. -/
theorem run_appendW {w m t : GalilScaffoldChainWatch.State} {es es' : List Bool}
    (h1 : GalilScaffoldChainWatch.Run w es m)
    (h2 : GalilScaffoldChainWatch.Run m es' t) :
    GalilScaffoldChainWatch.Run w (es ++ es') t := by
  induction h1 with
  | stop s => simpa using h2
  | next ht _ ih => exact .next ht (ih h2)

/-- **`GalilNoShiftStage.foundRouteMC_noshift'` over the ledger landing.**  The
preparation landing need not be the fresh watch itself: it is enough that it be
*reachable* from the fresh watch by a background run (`hrun0`, with no matched
comparison, `hes'`).  This is what the machine actually produces once the
period tape is consumed during the preparation, and it is all the chain ledgers
(`fresh_break_ledger`, `fresh_break_places`, `fresh_break_stage`) ever use. -/
theorem foundRouteMC_noshift_L (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2))
    (hex : ∀ s, (PofC centre place entry raw).replayExhausted s = zero s.replay)
    {c0 : Control} {r : GalilVM} (hI : InvLP raw c0 r)
    (hlive : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (PofC centre place entry raw) qq first) 2048 m ⟨c0, r⟩ z →
      CentreLive z.ctl z.vm)
    (hcenS : ∀ k : ℕ, PalPeg.GalilReplaySegment.InvScan 2048 raw c0 r k →
      GalilScaffoldInputTrace.Represents r.center.head raw ∧ r.center.head.focus ≠ none)
    {es0 : List Bool} {cF : Control} {sF : GalilVM}
    (hseg0 : WatchSegE (PofC centre place entry raw) qq first 2048 es0 c0 r cF sF)
    (hmF : cF.mode = .scan) (hrF : cF.replaying = false)
    (hcF : cF.clock = 1) (havF : canRight sF.right) (hidle : sF.chain = .idle)
    (vq : SearchVM) (hq : searchEffect (PofC centre place entry raw) true sF vq)
    (hfound : vq.search.mode = .found)
    (hmt : read (left sF.left) = read (right sF.right))
    (ch : ChainVM)
    (hch : ChainMatched (chainStart (vq.dp.config.tapes 11)
      ((PofC centre place entry raw).centre sF)
      ((PofC centre place entry raw).place sF) sF.center sF.radius) ch)
    (hchne : ch ≠ .idle) (oF : Bool)
    (hoF : refresh (galilFrame (PofC centre place entry raw) qq first)
      (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq) cF.output oF)
    {es : List Bool} {c2 : Control} {s2 : GalilVM}
    (hprepSeg : WatchSegE (PofC centre place entry raw) qq first 2048 es
      {cF with clock := 2048, output := oF, replaying := false}
      (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq) c2 s2)
    (cen : Fin 3) (ys : List (Fin 3)) (b : Fin 3)
    (w2 : GalilScaffoldChainWatch.State) (es' : List Bool)
    (hwatch2 : s2.chain = .watch w2)
    (hrun0 : GalilScaffoldChainWatch.Run
      (PalPeg.GalilNoShiftStage.freshWatch sF.center cen ys b sF.radius) es' w2)
    (hes' : es'.count true = 0)
    (hes0 : es.count true = 0)
    (hpal1 : Manacher.PalAt (encoded raw) (position r.center - (ys.length + 1)) (ys.length + 1))
    (hpal2 : Manacher.PalAt (encoded raw)
      (position r.center - 2 * (ys.length + 1)) (2 * (ys.length + 1)))
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
    (hmargin : negative w3'.margin = false) :
    ∃ (cT : Control) (sT : GalilVM) (k : ℕ) (L : List Piece),
      StepsAll (galilFrameS (PofC centre place entry raw) qq first) 2048 (SoundScanNR raw) k
        ⟨c0, r⟩ ⟨cT, sT⟩ ∧
      CostedRun r sT k L ∧ InvLP raw cT sT ∧
      position sT.center = position r.center ∧ position r.right < position sT.right ∧
      sT.right = (afterCompare s3 vs3 vq3).right := by
  set P := PofC centre place entry raw with hPdef
  have hcenR : GalilScaffoldInputTrace.Represents r.center.head raw ∧ r.center.head.focus ≠ none :=
    hI.1.1.elim GalilNoShiftStage.centreRep_of_inv (fun ⟨k, h⟩ => hcenS k h)
  obtain ⟨R, hi0, hRR0, -, -⟩ := hI.2
  obtain ⟨hsc0, _, hrad0, hrc0, _⟩ := watchSegE_heads P qq first 2048 hseg0
  have hcen : sF.center = r.center := watchSegE_center P qq first 2048 hseg0
  have hrcF : Canonical sF.radius := hrc0 hRR0.1
  have hradF : value sF.radius = (R : ℤ) + es0.count true := by rw [hrad0, hRR0.2]
  have hinvF : ScanInvariant raw (position sF.center) (R + es0.count true) sF.left sF.right := by
    rw [hcen]; exact scan_events_invariant (hsc0 raw (position r.center) R) hi0
  have hinv1 := matched_invariant' raw vq (s := sF) (vs := ⟨left sF.left, right sF.right, ch⟩)
    rfl rfl hmt havF hinvF
  obtain ⟨hsc1, _, hrad1, _, _⟩ := watchSegE_heads P qq first 2048 hprepSeg
  have hcen2 : s2.center = sF.center := by
    have h0 := watchSegE_center P qq first 2048 hprepSeg
    rw [afterCompare_center] at h0; exact h0
  have hinv2 := scan_events_invariant (hsc1 raw (position sF.center) _) hinv1
  have hne2 : s2.chain ≠ .idle := by rw [hwatch2]; intro h0; cases h0
  obtain ⟨es2, hticks, hsc2, hcen21, _, hrad2, _, _⟩ := watchSeg_events P qq first 2048 hseg hne2
  have hi3 : ScanInvariant raw (position s3.center)
      (R + es0.count true + 1 + es.count true + es2.count true) s3.left s3.right := by
    rw [hcen21, hcen2]
    exact scan_events_invariant (hsc2 raw (position sF.center) _) hinv2
  have hinv3 := matched_invariant raw P qq first vq3 hcmp3 hmt3 hav3 hi3
  rw [hwatch2, hs3] at hticks
  have hrun3 := chainTicks_watch_run es2 hticks
  have hmatch3 : read (left s3.left) = read (right s3.right) := by
    obtain ⟨⟨hl0, hr0, _⟩, _⟩ := hcmp3
    rw [scanLens.get_set] at hl0 hr0
    have hp0 := matched_parts P qq first hmt3
    rw [hl0, hr0] at hp0; exact hp0
  obtain ⟨-, -, htick⟩ := compare_parts P qq first hcmp3 hmatch3
  have hvs3 : vs3.chain = .broken w3' := by rw [← afterCompare_chain s3 vs3 vq3]; exact hbroken
  rw [hs3, hvs3] at htick
  obtain ⟨y, hy, hym⟩ := htick
  cases hy with
  | watchStep _ m hint =>
  have hym' : ChainMatched (.watch m) (.broken w3') := by simpa using hym
  cases hym' with
  | breaks _ _ hbr =>
  have hrunM := GalilNoShiftStage.run_snoc (run_appendW hrun0 hrun3) (.step hint (.idle m))
  obtain ⟨-, -, -, -, -, hdR, -, -⟩ :=
    GalilNoShiftStage.fresh_break_ledger _ cen ys b _ hrcF hrunM hbr
  have hc2 : ((es' ++ es2) ++ [false]).count true = es2.count true := by
    simp [List.count_append, hes']
  rw [hc2] at hdR
  have hplaces := GalilNoShiftStage.fresh_break_places raw sF.center cen ys b sF.radius hrcF
    (by rw [hcen]; exact hcenR.1) (by rw [hcen]; exact hcenR.2)
    (by rw [hcen]; exact hpal1) (by rw [hcen]; exact hpal2) hrunM hbr hmargin
    (fun R' hR' => by
      have hp := hinv3.palindrome
      have e : R' = R + es0.count true + 1 + es.count true + es2.count true + 1 := by
        have : (R' : ℤ) = (R : ℤ) + es0.count true + 1 + es2.count true + 1 := by
          rw [hR', hdR, hradF]
        rw [hes0]; omega
      rw [e, ← hcen2, ← hcen21]; exact hp)
  obtain ⟨hcanon, hlast, hlag, hst⟩ :=
    GalilNoShiftStage.fresh_break_stage _ cen ys b _ hrcF hrunM hbr hplaces
  refine PalPeg.GalilFoundLandingL.foundRouteMC_noshift centre place entry qq first raw hex hI
    hlive hcenR hseg0 hmF hrF hcF havF hidle vq hq hfound hmt ch hch hchne oF hoF hprepSeg hseg
    hm3 hr3 hc3 w3 hs3 hav3 vs3 vq3 hcmp3 hmt3 hq3 o3 ho3 w3' hbroken hmargin hlast hlag hcanon
    (fun R' hR' => hst R' ?_)
  have hv := hR'.2
  rw [afterCompare_radius, inc_value, hrad2, hrad1, afterCompare_radius, inc_value, hes0] at hv
  rw [hdR]
  push_cast at hv ⊢
  linarith

#print axioms run_appendW
#print axioms foundRouteMC_noshift_L


/-! ## 2c. The ledger tail -/

/-- **NAMED (open), per instance — `NoShiftTailC0` over the ledger landing.**
The only change to `NoShiftTailC0` is the preparation landing: instead of the
verbatim `s2.chain = .watch (freshWatch …)` it asks only that the landing's
watch state be *reachable* from the fresh watch by a background run
(`es'.count true = 0`).  This is strictly weaker, and it is what the machine
supplies: the preparation's own background ticks consume the period tape, so
the landing is a successor of the fresh watch, not the fresh watch itself. -/
def NoShiftTailC0L (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry qq : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ)
    (c0 : Control) (r : GalilVM) (cP : Control) (sP : GalilVM) : Prop :=
  ∃ (es0 : List Bool) (cF : Control) (sF : GalilVM) (vq : SearchVM) (ch : ChainVM) (oF : Bool)
    (a : Fin 2) (ls rs qw : List (Fin 2)) (gap : Bool) (span lower h : ℕ),
    raw = (a :: ls).reverse ++ rs ++ qw ∧
    sF.center = represent ⟨a :: ls, gap⟩ (rs.map some) qw ∧
    position r.center = position sF.center ∧
    GalilDpCorrect.Candidate
      ((GalilScaffoldPlace.stream ⟨a :: ls, gap⟩).take (span+1)) lower h ∧
    WatchSegE (PofC centre place entry raw) qq first 2048 es0 c0 r cF sF ∧
    cF.mode = .scan ∧ cF.replaying = false ∧ cF.clock = 1 ∧ canRight sF.right ∧
    sF.chain = ChainVM.idle ∧
    searchEffect (PofC centre place entry raw) true sF vq ∧ vq.search.mode = .found ∧
    read (left sF.left) = read (right sF.right) ∧
    ChainMatched (chainStart (vq.dp.config.tapes 11)
      ((PofC centre place entry raw).centre sF) ((PofC centre place entry raw).place sF)
      sF.center sF.radius) ch ∧
    ch ≠ ChainVM.idle ∧
    refresh (galilFrame (PofC centre place entry raw) qq first)
      (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq) cF.output oF ∧
    cP = {cF with clock := 2048, output := oF, replaying := false} ∧
    sP = afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq ∧
    (∀ (es : List Bool) (c2 : Control) (s2 : GalilVM),
      WatchSegE (PofC centre place entry raw) qq first 2048 es cP sP c2 s2 →
      ∃ (cen : Fin 3) (ys : List (Fin 3)) (b : Fin 3)
        (w2 : GalilScaffoldChainWatch.State) (es' : List Bool)
        (c3 : Control) (s3 : GalilVM)
        (w3 : GalilScaffoldChainWatch.State) (vs3 : ScanVM) (vq3 : SearchVM) (o3 : Bool)
        (w3' : GalilScaffoldChainWatch.State),
        ys.length + 1 = h ∧
        s2.chain = ChainVM.watch w2 ∧
        GalilScaffoldChainWatch.Run
          (PalPeg.GalilNoShiftStage.freshWatch sF.center cen ys b sF.radius) es' w2 ∧
        es'.count true = 0 ∧
        es.count true = 0 ∧
        WatchSeg (PofC centre place entry raw) qq first 2048 c2 s2 c3 s3 ∧
        c3.mode = .scan ∧ c3.replaying = false ∧ c3.clock = 1 ∧
        s3.chain = ChainVM.watch w3 ∧ canRight s3.right ∧
        (galilFrame (PofC centre place entry raw) qq first).compare s3 (scanLens.set s3 vs3) ∧
        (galilFrame (PofC centre place entry raw) qq first).matched (scanLens.set s3 vs3) ∧
        searchEffect (PofC centre place entry raw) true s3 vq3 ∧
        refresh (galilFrame (PofC centre place entry raw) qq first)
          (afterCompare s3 vs3 vq3) c3.output o3 ∧
        (afterCompare s3 vs3 vq3).chain = ChainVM.broken w3' ∧
        negative w3'.margin = false ∧
        position (afterCompare s3 vs3 vq3).right ≤ 2 * m - 1)

/-- The verbatim tail is a ledger tail (`Run.stop`). -/
theorem noShiftTailC0L_of_0 (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m : ℕ) {c0 cP : Control} {r sP : GalilVM}
    (h0 : NoShiftTailC0 centre place entry qq first raw m c0 r cP sP) :
    NoShiftTailC0L centre place entry qq first raw m c0 r cP sP := by
  obtain ⟨es0, cF, sF, vq, ch, oF, a, ls, rs, qw, gap, span, lower, h, hraw, hcenF, hpr, hcand,
    hseg0, hmF, hrF, hcF, havF, hidle, hq, hfound, hmt, hch, hchne, hoF, hcPeq, hsPeq, htl⟩ := h0
  refine ⟨es0, cF, sF, vq, ch, oF, a, ls, rs, qw, gap, span, lower, h, hraw, hcenF, hpr, hcand,
    hseg0, hmF, hrF, hcF, havF, hidle, hq, hfound, hmt, hch, hchne, hoF, hcPeq, hsPeq, ?_⟩
  intro es c2 s2 hseg
  obtain ⟨cen, ys, b, c3, s3, w3, vs3, vq3, o3, w3', hys, hwatch2, hes0, hseg3, hm3, hr3,
    hc3, hs3, hav3, hcmp3, hmt3, hq3, ho3, hbroken, hmargin, hbound⟩ := htl es c2 s2 hseg
  exact ⟨cen, ys, b, _, [], c3, s3, w3, vs3, vq3, o3, w3', hys, hwatch2, .stop _, by simp, hes0,
    hseg3, hm3, hr3, hc3, hs3, hav3, hcmp3, hmt3, hq3, ho3, hbroken, hmargin, hbound⟩

/-- **Derived.**  The raw break route from the *ledger* tail, through
`foundRouteMC_noshift_L`.  This is the point of the weakening: no step of the
route needs the landing to be the fresh watch verbatim. -/
theorem breakRouteLPraw_of_tail0L (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m : ℕ)
    (hex : ∀ s, (PofC centre place entry raw).replayExhausted s = zero s.replay)
    {c0 cP : Control} {r sP : GalilVM}
    (hE : StageEntryC (PofC centre place entry raw) qq first raw c0 r)
    (h0 : NoShiftTailC0L centre place entry qq first raw m c0 r cP sP) :
    BreakRouteLPraw (PofC centre place entry raw) qq first raw m c0 r cP sP := by
  classical
  obtain ⟨es0, cF, sF, vq, ch, oF, a, ls, rs, qw, gap, span, lower, h, hraw, hcenF, hpr, hcand,
    hseg0, hmF, hrF, hcF, havF, hidle, hq, hfound, hmt, hch, hchne, hoF, hcPeq, hsPeq, htl⟩ := h0
  subst hcPeq
  subst hsPeq
  intro hh es c2 s2 hprepSeg hlen hw
  obtain ⟨cen, ys, b, w2, es', c3, s3, w3, vs3, vq3, o3, w3', hys, hwatch2, hrun0, hes', hes0,
    hseg, hm3, hr3, hc3, hs3, hav3, hcmp3, hmt3, hq3, ho3, hbroken, hmargin, hbound⟩ :=
    htl es c2 s2 hprepSeg
  obtain ⟨hpal1, hpal2⟩ :=
    palAt_pair_of_candidate a ls rs qw gap span lower ys raw r sF hraw hcenF hpr
      (by rw [hys]; exact hcand)
  obtain ⟨cT, sT, k, L, hst, hcr, hIT, hc, hlt, hright⟩ :=
    foundRouteMC_noshift_L centre place entry qq first raw hex hE.invLPC.1.1
      (PalPeg.GalilOracleLeaves2.hlive_of_invLPC centre place entry qq first hE.invLPC)
      (fun _ _ => hE.invLPC.2) hseg0 hmF hrF hcF havF hidle vq hq hfound hmt ch hch hchne oF hoF
      hprepSeg cen ys b w2 es' hwatch2 hrun0 hes' hes0 hpal1 hpal2 hseg hm3 hr3 hc3 w3 hs3 hav3
      vs3 vq3 hcmp3 hmt3 hq3 o3 ho3 w3' hbroken hmargin
  refine ⟨cT, sT, k, L, hst, hcr,
    PalPeg.GalilInvPlus2.invLP2_of_stepsAll centre place entry qq first hE.invLPC.1.2 hst hIT,
    hc, hlt, ?_⟩
  rw [hright]; exact hbound

#print axioms noShiftTailC0L_of_0
#print axioms breakRouteLPraw_of_tail0L

/-! ## 3. The branch as a disjunction -/

/-- A cycle has *a* raw route: rounds (the shift branch) or break (the no-shift
branch).  The terminal comparison decides which, so exactly one holds. -/
def WatchRouteLPraw (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ)
    (c : Control) (r : GalilVM) (cP : Control) (sP : GalilVM) : Prop :=
  RoundsRouteLPraw P q first raw m c r cP sP ∨ BreakRouteLPraw P q first raw m c r cP sP

/-- **Derived.**  Either tail gives the disjunctive raw route. -/
theorem watchRouteLPraw_of_tails (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m : ℕ)
    (hex : ∀ s, (PofC centre place entry raw).replayExhausted s = zero s.replay)
    {c0 cP : Control} {r sP : GalilVM}
    (hE : StageEntryC (PofC centre place entry raw) qq first raw c0 r)
    (htail : ShiftTailC centre place entry qq first raw m c0 r cP sP ∨
      NoShiftTailC centre place entry qq first raw m c0 r cP sP) :
    WatchRouteLPraw (PofC centre place entry raw) qq first raw m c0 r cP sP := by
  rcases htail with hs | hn
  · exact Or.inl (roundsRouteLPraw_of_tail centre place entry qq first raw m hex hE hs)
  · exact Or.inr (breakRouteLPraw_of_tail centre place entry qq first raw m hex hE hn)

/-- **Derived.**  …and past the sharpening: the disjunction of the two landing
records of `CloseoutWatchPhase`. -/
theorem watchRouteLP_of_tails (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m : ℕ)
    (hex : ∀ s, (PofC centre place entry raw).replayExhausted s = zero s.replay)
    {c0 cP : Control} {r sP : GalilVM}
    (hE : StageEntryC (PofC centre place entry raw) qq first raw c0 r)
    (hLR : LandingRestartReach (PofC centre place entry raw) qq first raw c0 r)
    (htail : ShiftTailC centre place entry qq first raw m c0 r cP sP ∨
      NoShiftTailC centre place entry qq first raw m c0 r cP sP) :
    PalPeg.CloseoutWatchPhase.RoundsRouteLP (PofC centre place entry raw) qq first raw m
        c0 r cP sP ∨
    PalPeg.CloseoutWatchPhase.BreakRouteLP (PofC centre place entry raw) qq first raw m
        c0 r cP sP := by
  rcases watchRouteLPraw_of_tails centre place entry qq first raw m hex hE htail with h | h
  · exact Or.inl (roundsRouteLP_of_raw h hLR)
  · exact Or.inr (breakRouteLP_of_raw h hLR)

/-! ## 4. Two sufficient forms of `LandingRestartReach` -/

/-- **Derived.**  If every reachable `InvLP` landing is in fact `Inv`, the reach
statement is free. -/
theorem landingRestartReach_of_inv {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    {c : Control} {r : GalilVM}
    (h : ∀ (k : ℕ) (cT : Control) (sT : GalilVM),
      StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩ →
      InvLP raw cT sT → Inv raw cT sT) :
    LandingRestartReach P q first raw c r :=
  fun k cT sT hst hLP => landingRestart_of_inv (h k cT sT hst hLP)

/-- **Derived.**  It is enough that each reachable landing carry one restart
witness with its stage budget — the shape `life_restarted` produces. -/
theorem landingRestartReach_of_restarted {P : Shared} {q : ℕ} {first : Fin 9}
    {raw : List (Fin 2)} {c : Control} {r : GalilVM}
    (h : ∀ (k : ℕ) (cT : Control) (sT : GalilVM),
      StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩ →
      InvLP raw cT sT →
      ∃ (Rad : ℕ) (last : Counter), Restarted raw sT Rad last ∧ StageEntry Rad last) :
    LandingRestartReach P q first raw c r := by
  intro k cT sT hst hLP
  obtain ⟨Rad, last, hR, hS⟩ := h k cT sT hst hLP
  exact landingRestart_of_restarted hR hS

end PalPeg.CloseoutWatchPhase3

#print axioms PalPeg.CloseoutWatchPhase3.palAt_pair_of_candidate
#print axioms PalPeg.CloseoutWatchPhase3.noShiftTailC_of_0
#print axioms PalPeg.CloseoutWatchPhase3.breakRouteLPraw_of_tail0
#print axioms PalPeg.CloseoutWatchPhase3.watchRouteLPraw_of_tails
#print axioms PalPeg.CloseoutWatchPhase3.watchRouteLP_of_tails
#print axioms PalPeg.CloseoutWatchPhase3.landingRestartReach_of_inv
#print axioms PalPeg.CloseoutWatchPhase3.landingRestartReach_of_restarted
