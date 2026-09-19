import PalPeg.CloseoutWatchRound23

/-!
# Closeout watch round 25 — `foundExit_compare_final12` on the four-way split

`CloseoutWatchRound23.ExitSplit4C` splits a watch round's exit into the shift
family, the exhausted family, the guard-failing outer mismatch
(`TerminalRunFallbackGC`, which Round 23 turns into `WatchMismatchNoShiftC`) and
the **mismatch-shift** family `TerminalRunMismatchShiftC`: a reachable clock-`1`
available outer mismatch at which `MismatchGuardFails` fails, i.e. some disabled
chain tick passes `shiftGuardVM` after the mismatch — the machine's real
`beginChainShift` exit (Round 22).

## The shift landing and what it has

The shift family is routed by `CloseoutWatchRound7.ShiftRoundAtC`, which is
keyed on a live landing `s1` with `roundFuel h s1 = 0 ∨ shiftGuardVM s1` and
returns `ShiftRoundData` — the mismatch at `s1`, the guard *after* the mismatch,
`beginShift`, the shift run, the rounds and the breaking match — which
`CloseoutWatchRound5.shiftExitTailC_of_parts` packs into `ShiftTailC` and
`CloseoutWatchRound15.roundsRouteLP_of_tail` feeds to
`GalilFoundLandingL.foundRouteMC_shift_Inv`.  The mismatch-shift landing has
the mismatch, `canRight`, `clock = 1`, liveness, and the guard after the
mismatch tick (`¬ MismatchGuardFails s1`, §1); it does **not** have the
trigger conjunct `roundFuel h s1 = 0 ∨ shiftGuardVM s1` of `ShiftRoundAtC`:
`shiftGuardVM s1` reads the chain and the right head *at the landing*, while the
recorded guard reads them on the scan projection *after* the compare
(`afterMismatch s1 vs vq`: `vs.chain`, `read vs.right`).  So the shift route is
entered through **one** hypothesis:

* `MismatchShiftRouteC` — `ShiftRoundAtC` with its trigger conjunct
  `(roundFuel h s1 = 0 ∨ shiftGuardVM s1)` replaced by the mismatch-shift
  landing's own record (`clock = 1`, `canRight`, outer mismatch,
  `¬ MismatchGuardFails s1`).

What is proved:

1. `mismatchShift_tick` — at such a landing (given a disabled chain tick exists)
   the next tick *is* the chain-shift tick: some disabled chain tick passes the
   guard after the mismatch and `beginShiftVM'` fires from there.
2. `mismatchShift_to_shiftRoute` — `TerminalRunMismatchShiftC` lands in the
   shift route: with `MismatchShiftRouteC` it yields the same `ShiftTailC` as
   `TerminalRunShiftC` does through `shiftExitTailC_of_parts`.
3. **`foundExit_compare_final12`** — `foundExit_compare_final11` with the split
   taken from `exitSplit4C_of_tick`: families 1–3 go through
   `foundExit_compare_final9` (as a constant `ExitSplit3C`), family 4 through
   `mismatchShift_to_shiftRoute` and Round 15's route.  `WatchPrefixC` and
   `WatchMismatchNoShiftC` are discharged; `MismatchShiftRouteC` is the only new
   hypothesis.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

namespace PalPeg.CloseoutWatchRound25

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton PalPeg.GalilInvPlus PalPeg.GalilInvPlus2
open PalPeg.GalilFoundStage PalPeg.GalilTraceCost
open PalPeg.CloseoutContracts
open PalPeg.CloseoutWatchRun (LiveScanWatch roundFuel watchSeg_append)
open PalPeg.CloseoutWatchPhase2 (ShiftTailC NoShiftTailC LandingRestartReach)
open PalPeg.CloseoutWatchRound2 (FoundCompareCtxC TerminalRunC TerminalC' terminalC'_of_align)
open PalPeg.CloseoutWatchRound3 (TerminalRunShiftC DistanceNonnegC)
open PalPeg.CloseoutWatchRound5 (PrepLandingLiveC)
open PalPeg.CloseoutWatchRound7 (PrepLandingWatchC ShiftReachC ShiftRoundAtC BreakTermData
  ShiftRoundData)
open PalPeg.CloseoutWatchRound10 (FoundDpAtC)
open PalPeg.CloseoutWatchRound6 (RightCanC RightSaneC StartLeC LedgerOriginC PeriodMatchC)
open PalPeg.CloseoutWatchRound4 (ZeroLagAtMatchC)
open PalPeg.CloseoutPrepInputs2 (MismatchExitG)
open PalPeg.CloseoutPrepInputs3 (PrepInputsG3 foundExit_of_compare3)
open PalPeg.CloseoutWatchRound17 (FallbackRouteW)
open PalPeg.CloseoutWatchRound18 (ExitSplit3C)
open PalPeg.CloseoutWatchRound23 (MismatchGuardFails BreakEndAvSC TerminalRunMismatchShiftC
  ExitSplit4C exitSplit4C_of_tick terminalRunFallbackC_of_G)
open PalPeg.CloseoutWatchRound20 (watchPrefixC_of_unique)

/-! ## 1. The mismatch-shift tick -/

/-- **Derived.**  At a landing where the classifier fails and a disabled chain
tick exists, some disabled chain tick passes the shift guard after the
mismatch, and from there the chain-shift entry `beginShiftVM'` fires: the next
tick is the shift tick. -/
theorem mismatchShift_tick {s1 : GalilVM}
    (hz : ∃ z, ChainTick false s1.chain z) (hnG : ¬ MismatchGuardFails s1) :
    ∃ (vs : ScanVM) (vq : SearchVM),
      ChainTick false s1.chain vs.chain ∧ shiftGuardVM (afterMismatch s1 vs vq) ∧
        ∃ t, beginShiftVM' (afterMismatch s1 vs vq) t := by
  classical
  by_contra hno
  apply hnG
  refine ⟨hz, ?_⟩
  intro vs vq ht hg
  exact hno ⟨vs, vq, ht, hg, beginShift_exists _ hg⟩

/-! ## 2. The one hypothesis -/

/-- **NAMED (open) — the ONE hypothesis.**  `CloseoutWatchRound7.ShiftRoundAtC`
keyed on the mismatch-shift landing: its trigger conjunct
`roundFuel h s1 = 0 ∨ shiftGuardVM s1` is replaced by what
`TerminalRunMismatchShiftC` records there — clock `1`, an available outer
mismatch, and the classifier failing (a disabled chain tick passes the guard
*after* the mismatch).  The conclusion is `ShiftRoundData`, verbatim. -/
def MismatchShiftRouteC (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m h lower : ℕ) : Prop :=
  ∀ (sF : GalilVM) (vq : SearchVM) (c1 : Control) (s1 : GalilVM),
    LiveScanWatch c1 s1 → c1.clock = 1 → canRight s1.right →
    read (left s1.left) ≠ read (right s1.right) → ¬ MismatchGuardFails s1 →
      ShiftRoundData centre place entry qq first raw m h lower sF vq c1 s1

/-! ## 3. The fourth family lands in the shift route -/

/-- **Derived — `CloseoutWatchRound5.shiftExitTailC_of_parts` for the
mismatch-shift family.**  Same packing: the terminal landing and the recorded
mismatch landing are composed by `watchSeg_append`, and the route data comes
from `MismatchShiftRouteC` at the mismatch landing. -/
theorem mismatchShift_to_shiftRoute (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m h lower span : ℕ) {c0 cP : Control} {r sP : GalilVM}
    (hdp : PalPeg.CloseoutWatchRound5.FoundDpShiftC centre place entry qq first raw lower span
      c0 r)
    (hroute : MismatchShiftRouteC centre place entry qq first raw m h lower)
    (hctx : FoundCompareCtxC centre place entry qq first raw c0 r cP sP)
    (hrun : TerminalRunMismatchShiftC (PofC centre place entry raw) qq first h cP sP) :
    ShiftTailC centre place entry qq first raw m c0 r cP sP := by
  obtain ⟨es0, cF, sF, vq, ch, oF, a, ls, rs, qw, gap, hraw, hseg0, hmF, hrF, hcF, havF,
    hidle, hCen, hq, hfound, hmt, hch, hchne, hoF, hcPeq, hsPeq⟩ := hctx
  obtain ⟨hres, hpc⟩ := hdp a ls rs qw gap es0 cF sF vq hseg0 hCen hq hfound
  refine ⟨a, ls, rs, qw, gap, es0, cF, sF, vq, ch, oF, lower, span, hraw, hseg0, hmF, hrF, hcF,
    havF, hidle, hCen, hq, hfound, hmt, hch, hchne, hoF, hcPeq, hsPeq, hres, hpc, ?_⟩
  intro es c2 s2 hseg hwLanding
  obtain ⟨hmL, hrL, hcL⟩ := watchSegE_live_control (delay := 2048) (by omega) hseg
    (by rw [hcPeq]; exact hmF) (by rw [hcPeq]) (by simp [hcPeq])
  obtain ⟨cT, sT, hsegT, hLT, c1, s1, hseg1, hclk, hlive1, hav1, hne1, hnG⟩ :=
    hrun es c2 s2 hseg ⟨hmL, hrL, hcL, hwLanding⟩
  obtain ⟨w, vs, vq', s2', t', v, cycle, o, org, mm, c', s', n, c3, s3, w3, vs3, vq3, o3, w3',
    hm1, hr1, hc1, hs1, hz, hav, hcmp, hmis, hq', hg, hb, hs2', hi2, hchain, ho, hint, he,
    hoc, ha, hpos11, hlow, hrounds, hseg3, hm3, hr3, hc3, hs3, hav3, hcmp3, hmt3, hq3, ho3,
    hbroken, hmargin, hlast, hlag, hbound⟩ := hroute sF vq c1 s1 hlive1 hclk hav1 hne1 hnG
  exact ⟨c1, s1, h, w, vs, vq', s2', t', v, cycle, o, org, mm, c', s', n, c3, s3, w3, vs3, vq3,
    o3, w3', watchSeg_append hsegT hseg1, hm1, hr1, hc1, hs1, hz, hav, hcmp, hmis, hq', hg, hb,
    hs2', hi2, hchain, ho, hint, he, hoc, ha, hpos11, hlow, hrounds, hseg3, hm3, hr3, hc3, hs3,
    hav3, hcmp3, hmt3, hq3, ho3, hbroken, hmargin, hlast, hlag, hbound⟩

/-! ## 4. The consumer -/

/-- **Derived — `CloseoutWatchRound20.foundExit_compare_final11` on
`ExitSplit4C`.**  Families 1–3 are handed to `foundExit_compare_final9` as a
constant three-way split; family 4 goes through `mismatchShift_to_shiftRoute`
and Round 15's shift route.  New hypothesis: `MismatchShiftRouteC`. -/
theorem foundExit_compare_final12 (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (m h lower span : ℕ)
    (hP : Decodes (PofC centre place entry w))
    (hex : ∀ s, (PofC centre place entry w).replayExhausted s = zero s.replay)
    (hready : PalPeg.GalilReplayChainSeg.ChainTickable)
    (hcan : RightCanC) (hsane : RightSaneC) (hstart : StartLeC)
    (hor : LedgerOriginC centre place entry q first 2048 w)
    (hzl : ZeroLagAtMatchC) (hnn : DistanceNonnegC) (hpm : PeriodMatchC)
    {c c' cP : Control} {r t sP : GalilVM}
    (hE : StageEntryC (PofC centre place entry w) q first w c r)
    (hsW : SegReachedW centre place entry q first w c r c' t)
    (a : Fin 2) (ls rs qw : List (Fin 2)) (gap : Bool)
    (hprep : PrepInputsG3 (PofC centre place entry w) q first ⟨a :: ls, gap⟩ lower span cP sP)
    (hmis : MismatchExitG (PofC centre place entry w) q first w m c r cP sP)
    (hctx : FoundCompareCtxC centre place entry q first w c r cP sP)
    (hfb : FallbackRouteW (PofC centre place entry w) q first w m c r cP sP)
    (hLR : LandingRestartReach (PofC centre place entry w) q first w c r)
    (hstage : ReplayStage w (PofC centre place entry w) q first c r)
    (hmP : cP.mode = .scan) (hrP : cP.replaying = false) (hcP : 1 ≤ cP.clock)
    (hreachWatch : ∃ (es : List Bool) (c2 : Control) (s2 : GalilVM),
      WatchSegE (PofC centre place entry w) q first 2048 es cP sP c2 s2 ∧
        PalPeg.CloseoutWatchRun.LiveScanWatch c2 s2)
    (hat : FoundDpAtC centre place entry q first w lower span h c r)
    (hreach : ShiftReachC centre place entry q first w h)
    (hround : ShiftRoundAtC centre place entry q first w m h lower)
    (hmsr : MismatchShiftRouteC centre place entry q first w m h lower)
    (hland : ∀ sF : GalilVM,
      PalPeg.CloseoutWatchRound5.BreakLandingC centre place entry q first w h sF cP sP)
    (hstepBreak : ∀ (c0 : Control) (s0 : GalilVM), LiveScanWatch c0 s0 →
      PalPeg.CloseoutWatchRun.RoundStepC (PofC centre place entry w) q first (roundFuel h)
        (BreakTermData centre place entry q first w m h) c0 s0) :
    FoundExit (PofC centre place entry w) q first w m c r := by
  classical
  have hsplit4 : ExitSplit4C centre place entry q first w h cP sP :=
    exitSplit4C_of_tick centre place entry q first w h cP sP
      (PalPeg.CloseoutWatchRound2.chain_ne_idle_of_foundCompareCtx hctx)
      (watchPrefixC_of_unique _ _ _ _ _)
  -- the terminal record, exactly as in Round 18
  have hstp := PalPeg.CloseoutWatchRound6.lagStepC_of_parts hcan hsane hstart
  have hre := PalPeg.CloseoutWatchRound6.ledgerReachC_of_origin centre place entry q first 2048 w
    hstp hor
  have hled := PalPeg.CloseoutWatchRound4.watchLedgerC_of_reach hstp hre
  have hcaught := PalPeg.CloseoutWatchRound4.caughtAtMatchC_of_zeroLag hled hzl
  have hpred := PalPeg.CloseoutWatchRound6.predictC_of_match hled hzl hpm
  have havail := PalPeg.CloseoutWatchRound6.landingCanRightC_of_reach hstp hre
  have hT : TerminalC' centre place entry q first w h c r cP sP :=
    terminalC'_of_align centre place entry q first w h hready
      (PalPeg.CloseoutWatchRound3.matchTickC_of_parts hled hcaught hpred)
      (PalPeg.CloseoutWatchRound3.landingReadyC_of_parts hled havail hnn) hctx
  -- families 1–3: a constant three-way split into Round 18
  have via3 : ∀ (hs3 : ExitSplit3C centre place entry q first w h cP sP),
      FoundExit (PofC centre place entry w) q first w m c r := fun hs3 =>
    PalPeg.CloseoutWatchRound18.foundExit_compare_final9 centre place entry q first w m h
      lower span hP hex hready hcan hsane hstart hor hzl hnn hpm hE hsW a ls rs qw gap hprep hmis
      hctx hs3 hfb hLR hstage hmP hrP hcP hreachWatch hat hreach hround hland hstepBreak
  rcases hsplit4 hT.2 with hs | hb | hf | hm
  · exact via3 (fun _ => Or.inl hs)
  · exact via3 (fun _ => Or.inr (Or.inl hb))
  · exact via3 (fun _ => Or.inr (Or.inr (terminalRunFallbackC_of_G hf)))
  · -- family 4: the mismatch-shift landing, through the shift route
    have htail : ShiftTailC centre place entry q first w m c r cP sP :=
      mismatchShift_to_shiftRoute centre place entry q first w m h lower span
        (PalPeg.CloseoutWatchRound10.foundDpShiftC_of_at centre place entry q first w hP
          lower span h hstage hat)
        hmsr hctx hm
    have hroute := PalPeg.CloseoutWatchRound15.roundsRouteLP_of_tail centre place entry q first
      w m hex hE htail
    exact foundExit_of_compare3 centre place entry q first w m hP hE hsW a ls rs qw gap
      hprep hmis (Or.inl (PalPeg.CloseoutWatchPhase.roundsExit_of_LP hroute))

end PalPeg.CloseoutWatchRound25

#print axioms PalPeg.CloseoutWatchRound25.mismatchShift_tick
#print axioms PalPeg.CloseoutWatchRound25.mismatchShift_to_shiftRoute
#print axioms PalPeg.CloseoutWatchRound25.foundExit_compare_final12
