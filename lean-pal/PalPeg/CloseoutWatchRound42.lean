import PalPeg.CloseoutWatchRound40

/-!
# Closeout watch round 42 — `LiveChainRoundC` reduced to the replay-born round

`CloseoutWatchRound40.LiveChainRoundC` asks for the round of the chain that
survives the replay span (`ChainW` landing, chain in `.copy` / `.back` /
`.watch`).  This round separates the two things Round 40 lumped together.

## What is reusable without a found tick

* **The four-way exit split.**  `CloseoutWatchRound23.exitSplit4C_of_tick`
  needs only `LiveScanWatch cP sP` and `WatchPrefixC`, and `WatchPrefixC` is
  unconditional (`CloseoutWatchRound20.watchPrefixC_of_unique`).  So at a
  `.watch` landing of the replay-born chain the split is available verbatim
  (`exitSplit4C_of_liveScanWatch` below); no found tick, no `StageEntryC`, no
  DP record enters the split.
* **The `.watch` landing shape.**  `LiveScanChain` in its third phase *is*
  `LiveScanWatch` (`liveScanWatch_of_liveScanChain`).

## What genuinely differs — the ONE hypothesis

The four route consumers behind the split are rooted in a found tick:

* `CloseoutWatchRound15.roundsRouteLP_of_tail` / `breakRouteLP_of_tail`
  consume `ShiftTailC` / `NoShiftTailC` (`CloseoutWatchPhase2`), whose head is
  the found comparison `cF sF vq` with `sF.chain = ChainVM.idle`,
  `cF.replaying = false`, a `WatchSegE … c0 r cF sF` out of the stage entry,
  the birth `ChainMatched (chainStart (vq.dp.config.tapes 11) …) ch`, and the
  DP record `GalilDpCorrect.Result … lower 0 (denote vq.dp.config)` with
  `pc = 346`; the routes themselves are `GalilFoundLandingL.foundRouteMC_shift_Inv`
  and `GalilInvPlus2.foundRouteMC_noshift''_Inv`, run from `InvLPC` at that tick.
* `CloseoutWatchRound31.fallbackReachS_of_context` consumes `EntryCostC` /
  `ReplayRunC` out of the stage entry `⟨c, r⟩`.

The replay-born chain has none of this: its birth is a found quantum *inside*
the replay (`c.replaying = true`), so `cF.replaying = false` and the
`WatchSegE` from a stage entry are false of it, and its `InvLPC` rooting is
replaced by the `ChainW` data (`VerAt` / `BlockOn` / `CoreX` / margin identity,
`GalilReplaySpan.coreX_born`).  The DP candidate *does* exist at that quantum
(`compareFound` with `mode = .found` carries `vq.dp`), so the routes' DP-side
premises (`hdp`, `hpc`, `pos 11 = h`) are re-suppliable; what is not is the
`StageEntryC`/`InvLPC` rooting and the non-replaying `WatchSegE` head.

So the ONE hypothesis is `ReplayBornRoundC`: the round of a **`.watch`** chain
with the `ChainW` landing data, with **no** clock requirement (it is reached
either directly, or after the copy/back phase spent some clock).  Its supplier
is a `ShiftTailC`/`NoShiftTailC` analogue whose head is the replay found
quantum and whose invariant is `ChainW`-rooted rather than `InvLPC`-rooted.

## The mechanical residue (not the differing piece)

From `.copy` / `.back` the chain reaches `.watch` within its window by
background ticks (`GalilReplaySpan.chainW_step`: `copyBit` / `copyEnd` /
`backStep` / `backDone`, cost strictly decreasing, `CoreX` at `backDone` by
`coreX_born`), during the `count` ticks of the landing's clock, with the right
head, centre, `MInv`, scan invariant, `Frontier`, `ReplayRest`, `remaining`
and `OutputRel` unchanged — this is a run construction
(`GalilScaffoldTopProgressS.backgroundS_exists` + `chainW_step`), stated as
`ChainWatchReachC`.  It is *not* the found-tick difference; it is left open
here only because it is a run construction, not a rooting question.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutWatchRound42

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
open PalPeg.CloseoutWatchRun (LiveScanWatch)
open PalPeg.CloseoutWatchRound19 (WatchPrefixC)
open PalPeg.CloseoutWatchRound20 (watchPrefixC_of_unique)
open PalPeg.CloseoutWatchRound23 (ExitSplit4C exitSplit4C_of_tick)
open PalPeg.CloseoutWatchRound40 (LiveScanChain LiveChainRoundC)
open PalPeg.GalilReplaySpan (ChainW budOf)

/-! ## 1. The `.watch` phase of a `ChainW` landing is a live watch landing -/

/-- **Closed.**  In its third phase, `LiveScanChain` is `LiveScanWatch`. -/
theorem liveScanWatch_of_liveScanChain {c : Control} {t : GalilVM}
    (hlive : LiveScanChain c t) {w : GalilScaffoldChainWatch.State}
    (hw : t.chain = ChainVM.watch w) : LiveScanWatch c t :=
  ⟨hlive.1, hlive.2.1, hlive.2.2.1, w, hw⟩

/-! ## 2. The four-way split needs no found tick -/

/-- **Closed.**  At any live watch landing — in particular at the `.watch`
landing of the replay-born chain — Round 23's four-way exit split holds:
`WatchPrefixC` is unconditional (`watchPrefixC_of_unique`), and no found-tick
data enters `exitSplit4C_of_tick`. -/
theorem exitSplit4C_of_liveScanWatch (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (h : ℕ) (cP : Control) (sP : GalilVM)
    (hlive : LiveScanWatch cP sP) :
    ExitSplit4C centre place entry qq first raw h cP sP :=
  exitSplit4C_of_tick centre place entry qq first raw h cP sP hlive
    (watchPrefixC_of_unique (PofC centre place entry raw) qq first cP sP)

/-- **Closed.**  The same, at the `.watch` phase of a `ChainW` landing. -/
theorem exitSplit4C_of_liveScanChain (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (h : ℕ) (cP : Control) (sP : GalilVM)
    (hlive : LiveScanChain cP sP) {w : GalilScaffoldChainWatch.State}
    (hw : sP.chain = ChainVM.watch w) :
    ExitSplit4C centre place entry qq first raw h cP sP :=
  exitSplit4C_of_liveScanWatch centre place entry qq first raw h cP sP
    (liveScanWatch_of_liveScanChain hlive hw)

/-! ## 3. The landing bundle -/

/-- The `ChainW` landing data of `LiveChainRoundC` at a state `⟨c', t⟩`,
relative to the fallback landing `sT` and radius `R`, *without* the clock
requirement and without the control-only facts (`LiveScanChain`/`LiveScanWatch`
are kept separate so the same bundle serves both phases). -/
def LandingData (raw : List (Fin 2)) (R : ℕ) (sT : GalilVM) (cc b : Fin 3)
    (xs : List (Fin 3)) (c' : Control) (t : GalilVM) : Prop :=
  t.replay = reset ∧
  ChainW raw (position t.center) (position sT.right + R) (position t.right)
    (budOf 2048 (position sT.right + R) c' t) false cc b xs t.chain ∧
  position t.right = position sT.right + R ∧ MInv raw c' t ∧
  Leftmost raw (position t.right) (position t.center) ∧
  ScanInvariant raw (position t.center) R t.left t.right ∧ t.center = sT.center ∧
  Frontier t ∧ ReplayRest c' t ∧ t.remaining = sT.remaining ∧ OutputRel raw c' t

/-! ## 4. The ONE hypothesis: the replay-born `.watch` round -/

/-- **NAMED (open) — the round of the replay-born chain from its `.watch`
landing.**  This is the piece that genuinely differs from the found-rooted
routes: the landing carries `ChainW` data (birth at a replay found quantum,
`coreX_born`), not `InvLPC` at a non-replaying found tick with a stage-entry
`WatchSegE` (`ShiftTailC` / `NoShiftTailC`).  The clock is only positive
(`LiveScanWatch`), since the landing may be reached after the copy/back phase.
Supplier: a `ShiftTailC`/`NoShiftTailC` analogue with the replay found quantum
as head and `ChainW` as invariant, fed to the split of §2. -/
def ReplayBornRoundC (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ) : Prop :=
  ∀ (R : ℕ) (cT : Control) (sT : GalilVM), 0 < R →
    ReplayLanding raw cT sT R → SpanRep sT →
    ∀ (k0 : ℕ) (c' : Control) (t : GalilVM) (cc b : Fin 3) (xs : List (Fin 3)),
      StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k0 ⟨cT, sT⟩ ⟨c', t⟩ →
      LiveScanWatch c' t → LandingData raw R sT cc b xs c' t →
      ∃ (cT' : Control) (sT' : GalilVM) (k : ℕ) (L : List Piece),
        StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c', t⟩ ⟨cT', sT'⟩ ∧
        CostedRun sT sT' (k0 + k) L ∧ InvLPS P q first raw cT' sT' ∧
        position sT'.right ≤ 2 * m - 1

/-! ## 5. The mechanical residue: copy/back reach `.watch` -/

/-- **NAMED (open) — run construction, not a rooting difference.**  From a
`.copy` / `.back` `ChainW` landing at clock `2048`, the background ticks of the
landing's own `count` phase carry the chain to `.watch`
(`GalilReplaySpan.chainW_step`, cost strictly decreasing; `coreX_born` at
`backDone`) before the clock reaches `1`, so the right head, centre and the
whole landing bundle are unchanged; the clock is merely positive afterwards.
The ticks are sound (`SoundScanNR`) since mode/replay flags are untouched. -/
def ChainWatchReachC (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) : Prop :=
  ∀ (R : ℕ) (sT : GalilVM) (c' : Control) (t : GalilVM) (cc b : Fin 3) (xs : List (Fin 3)),
    LiveScanChain c' t → c'.clock = 2048 → LandingData raw R sT cc b xs c' t →
    ∃ (k1 : ℕ) (c'' : Control) (t'' : GalilVM),
      StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k1 ⟨c', t⟩ ⟨c'', t''⟩ ∧
      LiveScanWatch c'' t'' ∧ LandingData raw R sT cc b xs c'' t''

/-! ## 6. The target -/

/-- **`LiveChainRoundC` from the replay-born `.watch` round.**  At the `.watch`
phase the round hypothesis applies directly; at the `.copy` / `.back` phases the
reach residue first carries the landing to `.watch`, and the runs and the cost
record compose (`stepsAll_trans`, `k0 + (k1 + k) = (k0 + k1) + k`). -/
theorem liveChainRoundC_of_life (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (m : ℕ)
    (hreach : ChainWatchReachC P q first raw)
    (hround : ReplayBornRoundC P q first raw m) :
    LiveChainRoundC P q first raw m := by
  intro R cT sT hR hRL hSR k0 c' t cc b xs hst hlive hc hrep hW hB hM hlm hi hcen hfr hrest
    hrem hout
  have hdata : LandingData raw R sT cc b xs c' t :=
    ⟨hrep, hW, hB, hM, hlm, hi, hcen, hfr, hrest, hrem, hout⟩
  -- the `.watch` phase: the round applies at the landing itself
  have direct : ∀ (w : GalilScaffoldChainWatch.State), t.chain = ChainVM.watch w →
      ∃ (cT' : Control) (sT' : GalilVM) (k : ℕ) (L : List Piece),
        StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c', t⟩ ⟨cT', sT'⟩ ∧
        CostedRun sT sT' (k0 + k) L ∧ InvLPS P q first raw cT' sT' ∧
        position sT'.right ≤ 2 * m - 1 := by
    intro w hw
    exact hround R cT sT hR hRL hSR k0 c' t cc b xs hst
      (liveScanWatch_of_liveScanChain hlive hw) hdata
  -- the `.copy` / `.back` phases: reach `.watch` first, then the round
  have viaReach : ∃ (cT' : Control) (sT' : GalilVM) (k : ℕ) (L : List Piece),
      StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c', t⟩ ⟨cT', sT'⟩ ∧
      CostedRun sT sT' (k0 + k) L ∧ InvLPS P q first raw cT' sT' ∧
      position sT'.right ≤ 2 * m - 1 := by
    obtain ⟨k1, c'', t'', hst1, hliveW, hdata''⟩ :=
      hreach R sT c' t cc b xs hlive hc hdata
    obtain ⟨cT', sT', k, L, hk, hcost, hS, hbound⟩ :=
      hround R cT sT hR hRL hSR (k0 + k1) c'' t'' cc b xs (stepsAll_trans hst hst1) hliveW hdata''
    refine ⟨cT', sT', k1 + k, L, stepsAll_trans hst1 hk, ?_, hS, hbound⟩
    have e : k0 + (k1 + k) = k0 + k1 + k := by omega
    rw [e]
    exact hcost
  rcases hlive.2.2.2 with _ | _ | ⟨w, hw⟩
  · exact viaReach
  · exact viaReach
  · exact direct w hw

end PalPeg.CloseoutWatchRound42

#print axioms PalPeg.CloseoutWatchRound42.liveScanWatch_of_liveScanChain
#print axioms PalPeg.CloseoutWatchRound42.exitSplit4C_of_liveScanWatch
#print axioms PalPeg.CloseoutWatchRound42.exitSplit4C_of_liveScanChain
#print axioms PalPeg.CloseoutWatchRound42.liveChainRoundC_of_life
