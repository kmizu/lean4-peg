import PalPeg.CloseoutWatchRound36

/-!
# Closeout watch round 38 — the two branch hypotheses of Round 36, each reduced
to one residue

`CloseoutWatchRound36` left `ChainEndLandingC` (branch (ii)) and
`RestartLandingC` (branch (iii)) open.  This round derives each from ONE named
residue, discharging everything the landing data already supplies.

* **(iii) `restartLandingC_of_landing`.**  The (iii) landing `⟨c', t'⟩` is
  `InvScan R ∧ OutputRel`, centre kept, reached by a `StepsAll` run from the
  fallback landing.  Derived here: `InvL` (`invL_of_run` on the run from the
  preparation landing, `InvS` by the `InvScan` disjunct), the copy pack
  (`copyPack_of_stepsAll` from `CopyPack cP sP`), the centre head
  (`centreRep_congr` + `centreRep_of_restarted` at the `ReplayLanding`), hence
  `InvLPC`.  Residue `RestartLandingDataC`: `RadiusRep t'.radius R`, `SpanRep t'`,
  `Canonical t'.length` (no `WatchSegE` through the break, so
  `radiusRep_watchSegE` / `spanRep_watchSegE` / `canonical_length_watchSegE` do
  not apply — `BrokeAndRestarted` relates `⟨cT, sT⟩` only to the state *before*
  the restart, not to `⟨c', t'⟩`), the `ReplayStage` witness (same reason), the
  cost `CostedRun sT t' n' L` (`costedRun_fallback_replay` needs
  `|es| = R·2048`, which (iii) does not give), and the right-head budget
  (`FallbackCostPieceC` needs the mismatch data `clock = 1` / `canRight` /
  `read ≠ read`, which `RestartLandingC` does not quantify over).
* **(ii) `chainEndLandingC_of_route`.**  `ChainEnd` does NOT say the chain ended
  its round: it says the last chain started in the replay *survives* to the
  span end `B = position sT.right + R` (`t.chain ≠ .idle`, `ChainW … B`).  So
  there is no shift/break case to route here; the residue `ChainRoundRouteC` is
  the chain's own round *from* that landing (`ChainW` at window `B`, clock
  `2048`, replay off) to an `InvLPS` state with the cost of the whole run from
  `sT`.  Derived here: the unpacking of `ChainEnd`, the `StepsAll` composition
  (`stepsAll_trans`), centre monotonicity (`t.center = sT.center`), and the
  scan invariant at radius `R` (`0 + R`).  `roundsRouteLP_of_tail` cannot
  supply the residue: `ShiftTailC` is a contract over a found-tick state with
  a preparation segment (`∀ es c2 s2, WatchSegE … cP sP c2 s2 → …`), not over
  a live-chain landing.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutWatchRound38

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton PalPeg.GalilOracleDischarge PalPeg.GalilOracleLocal
open PalPeg.GalilCheckpoints PalPeg.GalilTraceCost PalPeg.GalilLexMeasure
open PalPeg.GalilInvPlus PalPeg.GalilInvPlus2 PalPeg.GalilOracleMC
open PalPeg.GalilGlueBLeaves PalPeg.GalilBranchInvariants2 PalPeg.GalilSegmentConstruct
open PalPeg.GalilOracleM PalPeg.GalilOracleMC2 PalPeg.GalilOracleGlueB
open PalPeg.GalilFoundStage
open PalPeg.GalilInvPlus3 (InvLPS)
open PalPeg.CloseoutContracts
open PalPeg.CloseoutWatchRound21 (FallbackLanding)
open PalPeg.CloseoutWatchRound24 (stepsAll_watchSeg)
open PalPeg.CloseoutWatchRound36 (ChainEndLandingC RestartLandingC)
open PalPeg.GalilReplaySpan (ChainEnd BrokeAndRestarted)

/-! ## 1. Branch (iii): `RestartLandingC` -/

/-- **NAMED (open) — the residue of branch (iii).**  At the idle landing
`⟨c', t'⟩` after the break-and-restart: the radius counter reads `R`, the span
relation and the canonical length counter hold, the landing ends a chain-idle
segment out of a restarted state (`ReplayStage`), the run from the fallback
landing is costed, and the right head is inside the region.  Suppliers:
counter bookkeeping across `ReplayChainSeg2` + the post-restart idle replay
(the `radiusRep_watchSegE` / `spanRep_watchSegE` / `canonical_length_watchSegE`
pattern, but through the break), `replayStage_entry` at the restarted state
(`RestartShapeL` gives `Restarted` there) + `replayStage_trans`, and a
break-aware `costedRun_fallback_replay`. -/
def RestartLandingDataC (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ)
    (cP : Control) (sP : GalilVM) : Prop :=
  ∀ (es : List Bool) (c1 : Control) (s1 : GalilVM),
    WatchSegE P q first 2048 es cP sP c1 s1 →
    ∀ (n R : ℕ) (cT : Control) (sT : GalilVM), 0 < R →
      FallbackLanding P q first raw c1 s1 n R cT sT →
      BrokeAndRestarted raw P q first 2048 cT sT →
      ∀ (n' : ℕ) (c' : Control) (t' : GalilVM),
        StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) n' ⟨cT, sT⟩ ⟨c', t'⟩ →
        position t'.right = position sT.right + R → t'.center = sT.center →
        PalPeg.GalilReplaySegment.InvScan 2048 raw c' t' R → OutputRel raw c' t' →
        RadiusRep t'.radius R ∧ SpanRep t' ∧ Canonical t'.length ∧
          ReplayStage raw P q first c' t' ∧
          (∃ L : List Piece, CostedRun sT t' n' L) ∧ position t'.right ≤ 2 * m - 1

/-- **`RestartLandingC` from `RestartLandingDataC`.**  `InvL`, the copy pack and
the centre head are derived; the counters, the stage witness, the cost and the
budget are the residue. -/
theorem restartLandingC_of_landing (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m : ℕ) (cP : Control) (sP : GalilVM)
    (hcopyP : PalPeg.GalilChainCoupling.CopyPack cP sP)
    (hEP : EntryCounters raw sP) (houtP : OutputRel raw cP sP)
    (hdata : RestartLandingDataC (PofC centre place entry raw) q first raw m cP sP) :
    RestartLandingC (PofC centre place entry raw) q first raw m cP sP := by
  intro es c1 s1 hseg n R cT sT hR hL hBR n' c' t' hst hpos hcen hIS hO
  obtain ⟨hRR, hSR, hCan, hstage, ⟨L, hcost⟩, hbound⟩ :=
    hdata es c1 s1 hseg n R cT sT hR hL hBR n' c' t' hst hpos hcen hIS hO
  have hRL : ReplayLanding raw cT sT R := hL.2.2.2.1 hR
  -- the run from the preparation landing to `⟨c', t'⟩`
  have hall : StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048 (SoundScanNR raw)
      (es.length + (1 + (n + 1)) + n') ⟨cP, sP⟩ ⟨c', t'⟩ :=
    stepsAll_trans (stepsAll_trans
      (stepsAll_watchSeg centre place entry q first raw hseg hEP houtP) hL.1) hst
  have hInvL : InvL raw c' t' := invL_of_run hall (Or.inr ⟨R, hIS⟩)
  have hEC : EntryCounters raw t' := entryCounters_of_invScan hIS hRR hSR hCan
  have hLP2 : InvLP2 raw c' t' :=
    ⟨⟨hInvL, hEC⟩, copyPack_of_stepsAll centre place entry q first hcopyP hall⟩
  have hCR : CentreRep raw t' := centreRep_congr hcen (centreRep_of_restarted hRL.rest)
  exact ⟨L, hcost, ⟨⟨hLP2, hCR⟩, hstage⟩, hbound⟩

#print axioms restartLandingC_of_landing

/-! ## 2. Branch (ii): `ChainEndLandingC` -/

/-- **NAMED (open) — the residue of branch (ii).**  From the `ChainEnd` landing
`⟨c', t⟩` of the replay out of `⟨cT, sT⟩` (chain live in `ChainW` at window
`B = position sT.right + R`, clock `2048`, replay off, `MInv`, scan invariant at
radius `R`, `Frontier`, `ReplayRest`), the chain's own round reaches an
`InvLPS` state, with the cost of the whole run from `sT` (`k0` replay ticks +
`k` round ticks), centre monotone from `t`, and the right-head budget.
Supplier: the shift/break route of a live chain round *without* a preparation
segment (`ShiftTailC` / `roundsRouteLP_of_tail` are stated over found-tick
states with a preparation `WatchSegE`, not over this landing). -/
def ChainRoundRouteC (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ)
    (cP : Control) (sP : GalilVM) : Prop :=
  ∀ (es : List Bool) (c1 : Control) (s1 : GalilVM),
    WatchSegE P q first 2048 es cP sP c1 s1 →
    ∀ (n R : ℕ) (cT : Control) (sT : GalilVM), 0 < R →
      FallbackLanding P q first raw c1 s1 n R cT sT →
      ∀ (k0 : ℕ) (c' : Control) (t : GalilVM) (cc b : Fin 3) (xs : List (Fin 3)),
        StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k0 ⟨cT, sT⟩ ⟨c', t⟩ →
        c'.mode = .scan → c'.clock = 2048 → c'.replaying = false → t.replay = reset →
        t.chain ≠ .idle →
        PalPeg.GalilReplaySpan.ChainW raw (position t.center) (position sT.right + R)
          (position t.right) (PalPeg.GalilReplaySpan.budOf 2048 (position sT.right + R) c' t)
          false cc b xs t.chain →
        position t.right = position sT.right + R → MInv raw c' t →
        ScanInvariant raw (position t.center) R t.left t.right → t.center = sT.center →
        Frontier t → ReplayRest c' t → t.remaining = sT.remaining →
        ∃ (cT' : Control) (sT' : GalilVM) (k : ℕ) (L : List Piece),
          StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c', t⟩ ⟨cT', sT'⟩ ∧
          CostedRun sT sT' (k0 + k) L ∧ InvLPS P q first raw cT' sT' ∧
          position t.center ≤ position sT'.center ∧ position sT'.right ≤ 2 * m - 1

/-- **`ChainEndLandingC` from `ChainRoundRouteC`.**  `ChainEnd` is unpacked to
its landing, the runs are composed and the centre is carried through
`t.center = sT.center`. -/
theorem chainEndLandingC_of_route (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (m : ℕ) (cP : Control) (sP : GalilVM)
    (hroute : ChainRoundRouteC P q first raw m cP sP) :
    ChainEndLandingC P q first raw m cP sP := by
  intro es c1 s1 hseg n R cT sT hR hL hCE
  obtain ⟨n1, c1', s1', c2, s2, es2, c', t, k0, cc, b, xs, -, -, -, -, -, hst, -, hm, hc, hrp,
    hrep, hne, hW, hB, hM, hi, hpos, hcen, hfr, hrest, hrem⟩ := hCE
  rw [Nat.zero_add] at hi
  obtain ⟨cT', sT', k, L, hk, hcost, hS, hmono, hbound⟩ :=
    hroute es c1 s1 hseg n R cT sT hR hL k0 c' t cc b xs hst hm hc hrp hrep hne hW hB hM hi hcen
      hfr hrest hrem
  refine ⟨cT', sT', k0 + k, L, stepsAll_trans hst hk, hcost, hS, ?_, hbound⟩
  rw [hcen] at hmono
  exact hmono

#print axioms chainEndLandingC_of_route

end PalPeg.CloseoutWatchRound38
