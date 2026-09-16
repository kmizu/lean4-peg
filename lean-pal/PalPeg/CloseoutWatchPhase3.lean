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
