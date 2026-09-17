import PalPeg.CloseoutWatchRound15
import PalPeg.CloseoutWatchRound17

/-!
# Round 18: the `WatchSeg → WatchSegE` bridge and the three-way exit split

Round 17 named one missing fact and one missing construction:

> **Missing fact (one sentence):** that a `WatchSeg P q first 2048 c s c1 s1`
> carries an event list, i.e. `∃ es, WatchSegE P q first 2048 es c s c1 s1`,
> which no lemma in the tree states (`watchSeg_append` and `watchSegE_append`
> are proved separately, never related).

and

> **`ExitSplit3C` / `foundExit_compare_final9` are NOT constructed.**

Both are supplied here.

## What is proved here (unconditionally, no `sorry` of its own)

1. `watchSegE_of_watchSeg` — **the bridge.**  `WatchSeg` and `WatchSegE` have
   the same first four constructors up to the event emitted (`false` for
   `wait`/`count`, `true` for `match`), so a straight induction on the
   `WatchSeg` derivation reads off the list.  `WatchSegE`'s three extra
   constructors (`matchIdle`, `countR`, `matchIdleR`) are exactly the idle /
   replaying cases `WatchSeg` does not have, so the bridge is one-directional
   by construction; the converse `watchSeg_of_E` is already in
   `GalilScaffoldTopWatchSegE` (under `s.chain ≠ .idle`), and
   `watchSeg_of_watchSegE` is re-exported here as `watchSeg_of_watchSegE'` for
   symmetry — it is **not** unconditional, and cannot be: `countR` runs with
   `c.replaying = true`, which `WatchSeg` forbids outright.
2. `BreakEndAvC`, `breakEndC_of_av` — `CloseoutWatchRound.BreakEndC` with the
   landing's `canRight`, which `BreakEndC` omits and
   `CloseoutWatchRound17.foundExitW_of_breakEndE` requires.
3. `TerminalRunBreak0C`, `TerminalRunFallbackC`, `ExitSplit3C` — the classifier
   `CloseoutWatchRound3.ExitSplitC` split in three: shift guard, input
   exhausted (chain break with no further input), outer mismatch.
   `terminalRunBreakC_of_break0` shows the middle branch still implies
   Round 3's two-way `TerminalRunBreakC`, so 1 and 2 of the three fold back
   onto the old split with no loss.
4. `foundExit_of_split3` — the third branch discharged: `TerminalRunFallbackC`
   at the preparation landing, `watchSeg_append`, the bridge (1), and
   `CloseoutWatchRound17.foundExitW_of_breakEndE` give `FoundExit` outright.
5. `foundExit_compare_final9'` — **the abstract lifting.**
   `foundExit_compare_final8`'s conclusion from `ExitSplit3C`, taking the
   two-way result as an opaque hypothesis `hTwo`.  Sorry-free and independent
   of the state of the `_Inv` routes.
6. `foundExit_compare_final9` — 5 instantiated at
   `CloseoutWatchRound15.foundExit_compare_final8`: Round 15's hypothesis list
   with `ExitSplitC` replaced by `ExitSplit3C`, plus
   `CloseoutWatchRound17.FallbackRouteW` and
   `CloseoutWatchPhase2.LandingRestartReach`.

## Remaining contracts (unchanged or newly named by this round)

* `CloseoutWatchRound17.FallbackRouteW` — **NAMED (open).**  Round 17 showed it
  is not derivable from `FallbackRouteLP` (disjoint premises,
  `not_prepChain_of_liveScanWatch`); it remains the one genuinely new
  assumption the third branch costs.
* `ExitSplit3C` — **NAMED (open).**  Strictly stronger than
  `CloseoutWatchRound3.ExitSplitC` (it must separate `¬ canRight` from
  `BreakEndAvC`, and strengthen `BreakEndC` to `BreakEndAvC`).
* `CloseoutWatchPhase2.LandingRestartReach` — still consumed, now only by the
  fallback branch (Round 15 removed it from the other two).
* `CloseoutPrepInputs2.MismatchExitG` — unchanged input of `final8`.
* Everything Round 15 lists: `RoundsExit`/`BreakExit` existential-landing
  restatement, run determinism for `StepsAll … (SoundScanNR raw)`.

**Build note.**  Verified with `lean` against the project's oleans; every
theorem above uses only `propext` / `Classical.choice` / `Quot.sound`.  One
workaround was needed and is *not* in this file: the uncommitted
`PalPeg/GalilInvPlus2.lean` uses `foundRouteMC_noshift_Inv` from
`PalPeg.GalilFoundLandingL` without importing it, so it does not compile as it
stands (and `CloseoutWatchRound15` then fails at line 168 with
`Unknown identifier … foundRouteMC_noshift''_Inv`).  Adding
`import PalPeg.GalilFoundLandingL` to `GalilInvPlus2.lean` fixes both — there
is no import cycle — and with that one line added everything here, including
`foundExit_compare_final9` through `final8`, is sorry-free.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

namespace PalPeg.CloseoutWatchRound18

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton PalPeg.GalilInvPlus PalPeg.GalilInvPlus2
open PalPeg.GalilFoundStage PalPeg.GalilTraceCost
open PalPeg.CloseoutContracts
open PalPeg.CloseoutWatchRun (LiveScanWatch roundFuel watchSeg_append)
open PalPeg.CloseoutWatchRound (BreakEndC)
open PalPeg.CloseoutWatchPhase2 (ShiftTailC NoShiftTailC LandingRestartReach)
open PalPeg.CloseoutWatchRound2 (FoundCompareCtxC TerminalRunC TerminalC' terminalC'_of_align)
open PalPeg.CloseoutWatchRound3 (TerminalRunShiftC TerminalRunBreakC ExitSplitC
  DistanceNonnegC CompareKeepsWatchC)
open PalPeg.CloseoutWatchRound5 (PrepLandingLiveC)
open PalPeg.CloseoutWatchRound7 (PrepLandingWatchC ShiftReachC ShiftRoundAtC BreakTermData)
open PalPeg.CloseoutWatchRound10 (FoundDpAtC)
open PalPeg.CloseoutWatchRound6 (RightCanC RightSaneC StartLeC LedgerOriginC PeriodMatchC)
open PalPeg.CloseoutWatchRound4 (ZeroLagAtMatchC)
open PalPeg.CloseoutPrepInputs2 (MismatchExitG)
open PalPeg.CloseoutPrepInputs3 (PrepInputsG3)
open PalPeg.CloseoutWatchRound17 (FallbackRouteW)

/-! ## 1. The bridge -/

/-- **Derived — the missing fact named in Round 17's header.**  Every `WatchSeg`
derivation carries an event list: its four constructors map one-for-one onto
`WatchSegE`'s first four, emitting `false` at a waiting or counting tick and
`true` at a matched comparison. -/
theorem watchSegE_of_watchSeg {P : Shared} {q : ℕ} {first : Fin 9} {delay : ℕ}
    {c c' : Control} {s t : GalilVM} (h : WatchSeg P q first delay c s c' t) :
    ∃ es : List Bool, WatchSegE P q first delay es c s c' t := by
  induction h with
  | stop c s => exact ⟨[], .stop _ _⟩
  | wait c s s' hm hr hn hb _ ih =>
    obtain ⟨es, he⟩ := ih
    exact ⟨false :: es, .wait c s s' hm hr hn hb he⟩
  | count c s s' hm hr ha hc hb _ ih =>
    obtain ⟨es, he⟩ := ih
    exact ⟨false :: es, .count c s s' hm hr ha hc hb he⟩
  | «match» c s vs vq o hm hr ha hc hne hcmp hmt hq ho _ ih =>
    obtain ⟨es, he⟩ := ih
    exact ⟨true :: es, .match c s vs vq o hm hr ha hc hne hcmp hmt hq ho he⟩

/-- **Re-export.**  The converse, from `GalilScaffoldTopWatchSegE`: it needs
`s.chain ≠ .idle`, and cannot be made unconditional — `WatchSegE.countR` runs
with `c.replaying = true`, which every `WatchSeg` constructor forbids. -/
theorem watchSeg_of_watchSegE' {P : Shared} {q : ℕ} {first : Fin 9} {delay : ℕ}
    {es : List Bool} {c c' : Control} {s t : GalilVM}
    (h : WatchSegE P q first delay es c s c' t) (hne : s.chain ≠ ChainVM.idle) :
    WatchSeg P q first delay c s c' t :=
  watchSeg_of_E P q first delay h hne

/-! ## 2. `BreakEndC` with the landing's availability -/

/-- `CloseoutWatchRound.BreakEndC` together with `canRight` at the landing, the
one extra field `CloseoutWatchRound17.foundExitW_of_breakEndE` asks for. -/
def BreakEndAvC (P : Shared) (q : ℕ) (first : Fin 9) (c : Control) (s : GalilVM) : Prop :=
  ∃ (c1 : Control) (s1 : GalilVM),
    WatchSeg P q first 2048 c s c1 s1 ∧ c1.clock = 1 ∧ LiveScanWatch c1 s1 ∧
      canRight s1.right ∧ read (left s1.left) ≠ read (right s1.right)

theorem breakEndC_of_av {P : Shared} {q : ℕ} {first : Fin 9} {c : Control} {s : GalilVM}
    (h : BreakEndAvC P q first c s) : BreakEndC P q first c s := by
  obtain ⟨c1, s1, hseg, hclk, hlive, -, hne⟩ := h
  exact ⟨c1, s1, hseg, hclk, hlive, hne⟩

/-! ## 3. The three-way classifier -/

/-- The input-exhausted family: the break side of `TerminalRunBreakC` with the
outer-mismatch alternative removed. -/
def TerminalRunBreak0C (P : Shared) (q : ℕ) (first : Fin 9) (h : ℕ)
    (cP : Control) (sP : GalilVM) : Prop :=
  ∀ (es : List Bool) (c2 : Control) (s2 : GalilVM),
    WatchSegE P q first 2048 es cP sP c2 s2 → LiveScanWatch c2 s2 →
      ∃ (cT : Control) (sT : GalilVM),
        WatchSeg P q first 2048 c2 s2 cT sT ∧ LiveScanWatch cT sT ∧ ¬ canRight sT.right

/-- The outer-mismatch family: the round ends at a clock-one landing whose outer
symbols disagree while the chain is still watching — the `FallbackRouteW`
shape. -/
def TerminalRunFallbackC (P : Shared) (q : ℕ) (first : Fin 9) (h : ℕ)
    (cP : Control) (sP : GalilVM) : Prop :=
  ∀ (es : List Bool) (c2 : Control) (s2 : GalilVM),
    WatchSegE P q first 2048 es cP sP c2 s2 → LiveScanWatch c2 s2 →
      ∃ (cT : Control) (sT : GalilVM),
        WatchSeg P q first 2048 c2 s2 cT sT ∧ LiveScanWatch cT sT ∧
          BreakEndAvC P q first cT sT

/-- **NAMED (open) — `CloseoutWatchRound3.ExitSplitC` in three.** -/
def ExitSplit3C (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (h : ℕ) (cP : Control) (sP : GalilVM) : Prop :=
  TerminalRunC (PofC centre place entry raw) qq first h cP sP →
    TerminalRunShiftC (PofC centre place entry raw) qq first h cP sP ∨
      TerminalRunBreak0C (PofC centre place entry raw) qq first h cP sP ∨
        TerminalRunFallbackC (PofC centre place entry raw) qq first h cP sP

/-- **Derived.**  The middle branch still gives Round 3's two-way break family. -/
theorem terminalRunBreakC_of_break0 {P : Shared} {q : ℕ} {first : Fin 9} {h : ℕ}
    {cP : Control} {sP : GalilVM} (hb : TerminalRunBreak0C P q first h cP sP) :
    TerminalRunBreakC P q first h cP sP := by
  intro es c2 s2 hseg hlive
  obtain ⟨cT, sT, hrun, hliveT, hav⟩ := hb es c2 s2 hseg hlive
  exact ⟨cT, sT, hrun, hliveT, Or.inl hav⟩

/-! ## 4. The third branch -/

/-- **Derived — the fallback branch of the split, discharged.**  The fallback
family fires at the preparation landing itself (the empty segment); its landing
is composed with the `BreakEndAvC` tail by `watchSeg_append`, put in event form
by `watchSegE_of_watchSeg`, and fed to Round 17. -/
theorem foundExit_of_split3 {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    {m h : ℕ} {c cP : Control} {r sP : GalilVM}
    (hfb : FallbackRouteW P q first raw m c r cP sP)
    (hLR : LandingRestartReach P q first raw c r)
    (hlive : PrepLandingLiveC P q first cP sP)
    (hf : TerminalRunFallbackC P q first h cP sP) :
    FoundExit P q first raw m c r := by
  have hliveP : LiveScanWatch cP sP := hlive [] cP sP (.stop _ _)
  obtain ⟨cT, sT, hseg1, hliveT, hbe⟩ := hf [] cP sP (.stop _ _) hliveP
  obtain ⟨c1, s1, hseg2, hclk, hlive1, hav, hne⟩ := hbe
  obtain ⟨es, hsegE⟩ := watchSegE_of_watchSeg (watchSeg_append hseg1 hseg2)
  exact PalPeg.CloseoutWatchRound17.foundExitW_of_breakEndE hfb hLR
    ⟨es, c1, s1, hsegE, hclk, hlive1, hav, hne⟩

/-! ## 5. The lifting -/

/-- **Derived — the abstract form.**  Given the two-way result as a hypothesis,
`ExitSplit3C` suffices: branches 1 and 2 rebuild an `ExitSplitC` (branch 2
through `terminalRunBreakC_of_break0`), branch 3 goes through
`foundExit_of_split3`.  Sorry-free. -/
theorem foundExit_compare_final9' {centre : GalilVM → Fin 3}
    {place : GalilVM → GalilScaffoldPlace.Place} {entry q : ℕ} {first : Fin 9}
    {w : List (Fin 2)} {m h : ℕ} {c cP : Control} {r sP : GalilVM}
    (hTwo : ExitSplitC centre place entry q first w h cP sP →
      FoundExit (PofC centre place entry w) q first w m c r)
    (hrun : TerminalRunC (PofC centre place entry w) q first h cP sP)
    (hsplit3 : ExitSplit3C centre place entry q first w h cP sP)
    (hfb : FallbackRouteW (PofC centre place entry w) q first w m c r cP sP)
    (hLR : LandingRestartReach (PofC centre place entry w) q first w c r)
    (hlive : PrepLandingLiveC (PofC centre place entry w) q first cP sP) :
    FoundExit (PofC centre place entry w) q first w m c r := by
  rcases hsplit3 hrun with hs | hb | hf
  · exact hTwo (fun _ => Or.inl hs)
  · exact hTwo (fun _ => Or.inr (terminalRunBreakC_of_break0 hb))
  · exact foundExit_of_split3 hfb hLR hlive hf

/-- **Derived — `CloseoutWatchRound15.foundExit_compare_final8` with the
three-way split.**  Round 15's hypothesis list with `ExitSplitC` replaced by
`ExitSplit3C`, plus `CloseoutWatchRound17.FallbackRouteW` and
`CloseoutWatchPhase2.LandingRestartReach` for the new third branch. -/
theorem foundExit_compare_final9 (centre : GalilVM → Fin 3)
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
    (hsplit3 : ExitSplit3C centre place entry q first w h cP sP)
    (hfb : FallbackRouteW (PofC centre place entry w) q first w m c r cP sP)
    (hLR : LandingRestartReach (PofC centre place entry w) q first w c r)
    (hstage : ReplayStage w (PofC centre place entry w) q first c r)
    (hmP : cP.mode = .scan) (hrP : cP.replaying = false) (hcP : 1 ≤ cP.clock)
    (hwatch : PrepLandingWatchC (PofC centre place entry w) q first cP sP)
    (hat : FoundDpAtC centre place entry q first w lower span h c r)
    (hreach : ShiftReachC centre place entry q first w h)
    (hround : ShiftRoundAtC centre place entry q first w m h lower)
    (hland : ∀ sF : GalilVM,
      PalPeg.CloseoutWatchRound5.BreakLandingC centre place entry q first w h sF cP sP)
    (hstepBreak : ∀ (c0 : Control) (s0 : GalilVM), LiveScanWatch c0 s0 →
      PalPeg.CloseoutWatchRun.RoundStepC (PofC centre place entry w) q first (roundFuel h)
        (BreakTermData centre place entry q first w m h) c0 s0) :
    FoundExit (PofC centre place entry w) q first w m c r := by
  have hlive : PrepLandingLiveC (PofC centre place entry w) q first cP sP :=
    PalPeg.CloseoutWatchRound7.prepLandingLiveC_of_watch (PofC centre place entry w) q first
      hmP hrP hcP hwatch
  have hT : TerminalC' centre place entry q first w h c r cP sP :=
    terminalC'_of_align centre place entry q first w h hready
      (PalPeg.CloseoutWatchRound3.matchTickC_of_parts
        (PalPeg.CloseoutWatchRound4.watchLedgerC_of_reach
          (PalPeg.CloseoutWatchRound6.lagStepC_of_parts hcan hsane hstart)
          (PalPeg.CloseoutWatchRound6.ledgerReachC_of_origin centre place entry q first 2048 w
            (PalPeg.CloseoutWatchRound6.lagStepC_of_parts hcan hsane hstart) hor))
        (PalPeg.CloseoutWatchRound4.caughtAtMatchC_of_zeroLag
          (PalPeg.CloseoutWatchRound4.watchLedgerC_of_reach
            (PalPeg.CloseoutWatchRound6.lagStepC_of_parts hcan hsane hstart)
            (PalPeg.CloseoutWatchRound6.ledgerReachC_of_origin centre place entry q first 2048 w
              (PalPeg.CloseoutWatchRound6.lagStepC_of_parts hcan hsane hstart) hor)) hzl)
        (PalPeg.CloseoutWatchRound6.predictC_of_match
          (PalPeg.CloseoutWatchRound4.watchLedgerC_of_reach
            (PalPeg.CloseoutWatchRound6.lagStepC_of_parts hcan hsane hstart)
            (PalPeg.CloseoutWatchRound6.ledgerReachC_of_origin centre place entry q first 2048 w
              (PalPeg.CloseoutWatchRound6.lagStepC_of_parts hcan hsane hstart) hor)) hzl hpm))
      (PalPeg.CloseoutWatchRound3.landingReadyC_of_parts
        (PalPeg.CloseoutWatchRound4.watchLedgerC_of_reach
          (PalPeg.CloseoutWatchRound6.lagStepC_of_parts hcan hsane hstart)
          (PalPeg.CloseoutWatchRound6.ledgerReachC_of_origin centre place entry q first 2048 w
            (PalPeg.CloseoutWatchRound6.lagStepC_of_parts hcan hsane hstart) hor))
        (PalPeg.CloseoutWatchRound6.landingCanRightC_of_reach
          (PalPeg.CloseoutWatchRound6.lagStepC_of_parts hcan hsane hstart)
          (PalPeg.CloseoutWatchRound6.ledgerReachC_of_origin centre place entry q first 2048 w
            (PalPeg.CloseoutWatchRound6.lagStepC_of_parts hcan hsane hstart) hor)) hnn) hctx
  refine foundExit_compare_final9' (h := h) ?_ hT.2 hsplit3 hfb hLR hlive
  intro hsplit
  exact PalPeg.CloseoutWatchRound15.foundExit_compare_final8 centre place entry q first w m h
    lower span hP hex hready hcan hsane hstart hor hzl hnn hpm hE hsW a ls rs qw gap hprep hmis
    hctx hsplit hstage hmP hrP hcP hwatch hat hreach hround hland hstepBreak

end PalPeg.CloseoutWatchRound18

#print axioms PalPeg.CloseoutWatchRound18.watchSegE_of_watchSeg
#print axioms PalPeg.CloseoutWatchRound18.watchSeg_of_watchSegE'
#print axioms PalPeg.CloseoutWatchRound18.breakEndC_of_av
#print axioms PalPeg.CloseoutWatchRound18.terminalRunBreakC_of_break0
#print axioms PalPeg.CloseoutWatchRound18.foundExit_of_split3
#print axioms PalPeg.CloseoutWatchRound18.foundExit_compare_final9'
#print axioms PalPeg.CloseoutWatchRound18.foundExit_compare_final9
