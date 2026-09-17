import PalPeg.CloseoutWatchRound24

/-!
# Closeout watch round 26 — `EntryCostC` from the found-compare context

`CloseoutWatchRound24.EntryCostC` (the costed run from the stage entry `⟨c, r⟩`
to the preparation landing `⟨cP, sP⟩`) is discharged from
`CloseoutWatchRound2.FoundCompareCtxC`: the chain-idle scan segment
`WatchSegE … c r cF sF` (`GalilOracleMC.watchSegE_stepsAll_len`, costed by
`GalilCostedFallback.costedRun_watchSegE` with `w1` pending counting ticks
before the found comparison) followed by the found comparison tick
(`found_start_match`), which is one `cmpPiece` at `position sF.right + 1`
whose wait absorbs the `w1` pending ticks (`w1 + 1 ≤ 2048` since
`cF.clock = 1`).  The landing `⟨cP, sP⟩` is `SoundScanNR` by
`outputRel_matched_refresh'`.

Extra premises beyond the context: `EntryCounters raw r` (the scan invariant at
the entry), `OutputRel raw c r` and `c.clock ≤ 2048` — the same shape of
premises `CloseoutWatchRound22.watchFallbackC_of_context` takes at `sP`.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutWatchRound26

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton PalPeg.GalilTraceCost
open PalPeg.GalilGlueBLeaves (EntryCounters scanInvariant_watchSegE)
open PalPeg.CloseoutWatchRound2 (FoundCompareCtxC)
open PalPeg.CloseoutWatchRound24 (EntryCostC)
open PalPeg.GalilCostedFallback (costedRun_watchSegE)
open PalPeg.GalilCostedFound (cmpPiece cmpPiece_ticks cmpPiece_adv costedRun_single)

/-- **`EntryCostC` from `FoundCompareCtxC`.**  The run is `|es0| + 1` ticks
(the segment and the found comparison); the costed record is the segment's
matched pieces followed by the found comparison piece at `position sF.right + 1`. -/
theorem entryCostC_of_ctx (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) {c cP : Control} {r sP : GalilVM}
    (hctx : FoundCompareCtxC centre place entry q first raw c r cP sP)
    (hE : EntryCounters raw r) (hout : OutputRel raw c r) (hclk : c.clock ≤ 2048) :
    EntryCostC (PofC centre place entry raw) q first raw c r cP sP := by
  obtain ⟨es0, cF, sF, vq, ch, oF, a, ls, rs, qw, gap, -, hseg, hmF, hrF, hcF, havF, hidle, -,
    hq, hfound, hmt, hch, hchne, hoF, rfl, rfl⟩ := hctx
  obtain ⟨Rad, hi, -, -, -⟩ := hE
  -- the segment up to the found comparison
  have hst0 := PalPeg.GalilOracleMC.watchSegE_stepsAll_len raw (PofC centre place entry raw) rfl rfl
    q first 2048 hseg (position r.center) Rad hi hout
  have houtF : OutputRel raw cF sF := stepsAll_last hst0
  have hiF := scanInvariant_watchSegE (PofC centre place entry raw) q first 2048 hseg hi
  -- the found comparison tick and its landing
  have htick := found_start_match (PofC centre place entry raw) q first 2048 cF sF hmF hrF hcF havF
    hidle vq hq hfound hmt ch hch oF hoF
  obtain ⟨hiP, houtP⟩ := outputRel_matched_refresh' raw (PofC centre place entry raw) rfl rfl q first
    vq rfl rfl hmt havF hiF cF.output oF hoF {cF with clock := 2048, output := oF, replaying := false} rfl
  have hst : StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048 (SoundScanNR raw)
      (es0.length + 1) ⟨c, r⟩
      ⟨{cF with clock := 2048, output := oF, replaying := false},
        afterBirth true (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq)⟩ :=
    stepsAll_trans (stepsAll_mono (fun st h _ _ => h) hst0)
      (.succ (fun _ _ => houtF) htick (.zero _ (fun _ _ => houtP)))
  -- the cost: the segment's pieces, then the found comparison piece
  obtain ⟨L, k', w1, hcr, hk, hw1, -, -, -, -⟩ :=
    costedRun_watchSegE raw (PofC centre place entry raw) q first hseg hi hclk havF
  have hw : w1 ≤ 2048 := by omega
  have hpos : position (afterBirth true (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq)).right =
      position sF.right + 1 := by
    rw [afterBirth_right]
    have := hiF.rightPos; have := hiP.rightPos; omega
  have h1 := costedRun_single (a := sF) (b := afterBirth true (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq))
    (cmpPiece (position sF.right + 1) w1 hw) (by simp [cmpPiece])
    (by simp [cmpPiece, hpos])
    (by rw [cmpPiece_adv, afterBirth_center, afterCompare_center]; simp)
  rw [cmpPiece_ticks] at h1
  refine ⟨es0.length + 1, L ++ [cmpPiece (position sF.right + 1) w1 hw], hst, ?_⟩
  have := costedRun_trans hcr h1
  rwa [show k' + (w1 + 1) = es0.length + 1 by omega] at this

end PalPeg.CloseoutWatchRound26

#print axioms PalPeg.CloseoutWatchRound26.entryCostC_of_ctx
