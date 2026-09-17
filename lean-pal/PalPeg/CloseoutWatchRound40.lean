import PalPeg.CloseoutWatchRound38

/-!
# Closeout watch round 40 — `ChainRoundRouteC` from the live-chain round

`CloseoutWatchRound38.ChainRoundRouteC` is the residue of branch (ii): from the
`ChainEnd` landing `⟨c', t⟩` (the chain *survives* the replay span, `ChainW`
at window `B = position sT.right + R`, clock `2048`, replay off) the chain's
own round must reach an `InvLPS` state with the cost of the whole run from the
fallback landing `sT`.

## Why the existing 4-way split and routes do not apply verbatim

* `exitSplit4C_of_tick` (Round 23) needs `LiveScanWatch cP sP`, i.e. a
  **`.watch`** chain.  `ChainW` does not give that: at the span end the
  surviving chain may still be in its `.copy` or `.back` phase
  (`chainW_shape` below is the exact trichotomy `ChainW` yields).
* `roundsRouteLP_of_tail` / `breakRouteLP_of_tail` (Round 15) and
  `fallbackReachS_of_context` (Round 31) are all rooted in a **found tick**
  (`ShiftTailC` / `NoShiftTailC` quantify a preparation `WatchSegE` out of a
  found comparison with its DP record, and the routes are
  `GalilFoundLandingL.foundRouteMC_shift_Inv` /
  `GalilInvPlus2.foundRouteMC_noshift''_Inv` from `InvLPC` at that tick).
  The `ChainEnd` landing has no found tick behind it: its chain was started
  *inside* the replay, and its landing is not `InvScan` (`InvScan.chainIdle`).
* `chain_life` (`GalilScaffoldTopChainLife`) is likewise stated for a chain
  born from a found DP (`watchStart` of a `Candidate`), not for `ChainW` data.

So the ONE hypothesis is the live-chain round itself, `LiveChainRoundC`,
stated exactly at the landing shape.  Everything the landing already supplies
is discharged here and handed to it:

* `LiveScanChain c' t` — the `LiveScanWatch`-like fact: scan mode, replay off,
  positive clock, and the chain in one of `.copy` / `.back` / `.watch`
  (`chainW_shape`, from `ChainW`);
* `OutputRel raw c' t` — from `SoundScanNR` at the last state of the replay
  run (`stepsAll_last`);
* `Leftmost raw (position t.right) (position t.center)` — from `MInv` with
  `replaying = false`;
* `ReplayLanding raw cT sT R`, `SpanRep sT` — from `FallbackLanding`;
* centre monotonicity `position t.center ≤ position sT'.center` — from the
  supplier's `CostedRun sT sT' _ _` (`CostedRun.centre`) and `t.center = sT.center`,
  so the hypothesis need not state it.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutWatchRound40

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
open PalPeg.CloseoutWatchRound38 (ChainRoundRouteC)
open PalPeg.GalilReplaySpan (ChainW)

/-! ## 1. The landing shape a `ChainW` chain provides -/

/-- The `LiveScanWatch`-like fact at a `ChainEnd` landing: scan mode, replay
off, positive clock, and a chain in one of its three live phases.  (Compare
`CloseoutWatchRun.LiveScanWatch`, which fixes the `.watch` phase.) -/
def LiveScanChain (c : Control) (s : GalilVM) : Prop :=
  c.mode = .scan ∧ c.replaying = false ∧ 1 ≤ c.clock ∧
    ((∃ t h p v lag margin ver, s.chain = ChainVM.copy t h p v lag margin ver) ∨
      (∃ p h lag margin ver, s.chain = ChainVM.back p h lag margin ver) ∨
      (∃ w, s.chain = ChainVM.watch w))

/-- **Closed.**  `ChainW` holds only of a `.copy`, `.back` or `.watch` chain. -/
theorem chainW_shape {raw : List (Fin 2)} {C E R bud : ℕ} {lim : Bool} {cc b : Fin 3}
    {xs : List (Fin 3)} {x : ChainVM} (h : ChainW raw C E R bud lim cc b xs x) :
    (∃ t h p v lag margin ver, x = ChainVM.copy t h p v lag margin ver) ∨
      (∃ p h lag margin ver, x = ChainVM.back p h lag margin ver) ∨
      (∃ w, x = ChainVM.watch w) := by
  cases x with
  | idle => exact False.elim h
  | copy t h' p v lag margin ver => exact Or.inl ⟨t, h', p, v, lag, margin, ver, rfl⟩
  | back p h' lag margin ver => exact Or.inr (Or.inl ⟨p, h', lag, margin, ver, rfl⟩)
  | watch w => exact Or.inr (Or.inr ⟨w, rfl⟩)
  | broken _ => exact False.elim h

/-- **Closed.**  The `ChainEnd` landing is a live scan landing with a live chain. -/
theorem liveScanChain_of_landing {raw : List (Fin 2)} {E R bud : ℕ} {cc b : Fin 3}
    {xs : List (Fin 3)} {c : Control} {t : GalilVM}
    (hm : c.mode = .scan) (hr : c.replaying = false) (hc : c.clock = 2048)
    (hW : ChainW raw (position t.center) E R bud false cc b xs t.chain) :
    LiveScanChain c t :=
  ⟨hm, hr, by omega, chainW_shape hW⟩

/-- **Closed.**  `OutputRel` at the last state of a `SoundScanNR` run that is
parked in a non-replaying scan. -/
theorem outputRel_of_stepsAll {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    {k : ℕ} {x : State GalilVM} {c : Control} {t : GalilVM}
    (hst : StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k x ⟨c, t⟩)
    (hm : c.mode = .scan) (hr : c.replaying = false) : OutputRel raw c t :=
  stepsAll_last hst hm hr

/-! ## 2. The hypothesis -/

/-- **NAMED (open) — the live chain's round from its `ChainEnd` landing.**  At a
landing `⟨c', t⟩` reached from the fallback landing `⟨cT, sT⟩` (positive
radius, `ReplayLanding`, `SpanRep`) by `k0` sound ticks — live scan landing
with a live chain, clock `2048`, replay counter reset, `ChainW` at window
`B = position sT.right + R` with the right head at `B`, `MInv` (and its
`Leftmost` consequence), scan invariant at radius `R`, centre unmoved since
`sT`, `Frontier`, `ReplayRest`, `remaining` unmoved, `OutputRel` — the chain's
own round (shift → `beginShiftVM'` → shift run, or break → fallback, or input
end) reaches an `InvLPS` state, with the cost of the whole run from `sT` and
the right-head budget.  Centre monotonicity is *not* asked: it follows from
the cost record.  Supplier: a `chain_life`-style round for a `ChainW` chain
(not a found-DP chain), or `rounds_construct_break` on a `ChainW`-based
invariant, followed by the shift/fallback landings. -/
def LiveChainRoundC (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ) : Prop :=
  ∀ (R : ℕ) (cT : Control) (sT : GalilVM), 0 < R →
    ReplayLanding raw cT sT R → SpanRep sT →
    ∀ (k0 : ℕ) (c' : Control) (t : GalilVM) (cc b : Fin 3) (xs : List (Fin 3)),
      StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k0 ⟨cT, sT⟩ ⟨c', t⟩ →
      LiveScanChain c' t → c'.clock = 2048 → t.replay = reset →
      ChainW raw (position t.center) (position sT.right + R) (position t.right)
        (PalPeg.GalilReplaySpan.budOf 2048 (position sT.right + R) c' t) false cc b xs t.chain →
      position t.right = position sT.right + R → MInv raw c' t →
      Leftmost raw (position t.right) (position t.center) →
      ScanInvariant raw (position t.center) R t.left t.right → t.center = sT.center →
      Frontier t → ReplayRest c' t → t.remaining = sT.remaining → OutputRel raw c' t →
      ∃ (cT' : Control) (sT' : GalilVM) (k : ℕ) (L : List Piece),
        StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c', t⟩ ⟨cT', sT'⟩ ∧
        CostedRun sT sT' (k0 + k) L ∧ InvLPS P q first raw cT' sT' ∧
        position sT'.right ≤ 2 * m - 1

/-! ## 3. The target -/

/-- **`ChainRoundRouteC` from `LiveChainRoundC`.**  The landing shape, the
output relation and the leftmost centre are derived; the replay landing and
span data come from `FallbackLanding`; centre monotonicity from the cost
record. -/
theorem chainRoundRouteC_of_life (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (m : ℕ) (cP : Control) (sP : GalilVM)
    (hlife : LiveChainRoundC P q first raw m) :
    ChainRoundRouteC P q first raw m cP sP := by
  intro es c1 s1 hseg n R cT sT hR hL k0 c' t cc b xs hst hm hc hrp hrep hne hW hB hM hi hcen
    hfr hrest hrem
  have hRL : ReplayLanding raw cT sT R := hL.2.2.2.1 hR
  have hSR : SpanRep sT := hL.2.2.2.2
  have hlive : LiveScanChain c' t := liveScanChain_of_landing hm hrp hc hW
  have hout : OutputRel raw c' t := outputRel_of_stepsAll hst hm hrp
  have hlm : Leftmost raw (position t.right) (position t.center) := hM.2 hrp
  obtain ⟨cT', sT', k, L, hk, hcost, hS, hbound⟩ :=
    hlife R cT sT hR hRL hSR k0 c' t cc b xs hst hlive hc hrep hW hB hM hlm hi hcen hfr hrest
      hrem hout
  refine ⟨cT', sT', k, L, hk, hcost, hS, ?_, hbound⟩
  have hcc := hcost.centre
  rw [hcen]
  omega

end PalPeg.CloseoutWatchRound40

#print axioms PalPeg.CloseoutWatchRound40.chainW_shape
#print axioms PalPeg.CloseoutWatchRound40.chainRoundRouteC_of_life
