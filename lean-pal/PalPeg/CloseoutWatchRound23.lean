import PalPeg.CloseoutWatchRound22

/-!
# Closeout watch round 23 — `WatchMismatchNoShiftC` from a guard-recording split

`CloseoutWatchRound22.WatchMismatchNoShiftC` is the shift/fallback classifier at
a watch-mode clock-`1` outer mismatch: a disabled chain tick exists and every
disabled chain tick fails `shiftGuardVM` after the mismatch.

## Route taken: the families of `ExitSplit3C` are NOT exclusive

`CloseoutWatchRound19.split3_of_prefix` puts a run in the outer-mismatch family
(`TerminalRunFallbackC`) as soon as *some* available clock-`1` mismatch is
reachable, whatever the guard does there; and the shift family
(`TerminalRunShiftC`) records `shiftGuardVM sT` at a *landing* `sT`, not
`shiftGuardVM (afterMismatch s1 vs vq)` after the mismatch tick.  So "in the
outer-mismatch family ⇒ the guard fails" is not a consequence of the split:
a watching mismatch whose chain predicts the right symbol is exactly the
machine's `beginChainShift` exit (Round 22's finding) and is put in the third
family by Round 19.  The `WatchMismatchNoShiftC` shape is therefore a genuine
fourth outcome, not a bookkeeping gap.

What is done here:

1. `MismatchGuardFails s1` — the per-landing classifier body.
2. `BreakEndAvGC`, `TerminalRunFallbackGC` — `BreakEndAvC` /
   `TerminalRunFallbackC` with the guard failure recorded at the mismatch;
   `TerminalRunMismatchShiftC` — the complementary family (a reachable mismatch
   at which the classifier fails: the mismatch-shift exit).
3. `split4_of_prefix` — the four-way split from Round 19's pieces
   (`watchSeg_stuck_of_mismatch`, comparability); `exitSplit4C_of_tick` — the
   `ExitSplit4C` producer.
4. **`watchMismatchNoShiftC_of_split`** — `TerminalRunFallbackGC` gives
   `WatchMismatchNoShiftC`.  Only `watchSeg_stuck_of_mismatch` is needed: the
   family is applied at the mismatch landing itself, where the only segment is
   empty, so the recorded landing *is* the landing.

Left open: the fourth family `TerminalRunMismatchShiftC` (the outer mismatch
that shifts) has no consumer; it is the branch Round 22 identified as absent
from the exit classifier and it cannot be folded into `TerminalRunShiftC`.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutWatchRound23

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton
open PalPeg.CloseoutContracts
open PalPeg.CloseoutWatchRun (LiveScanWatch roundFuel watchSeg_append)
open PalPeg.CloseoutWatchRound (BreakEndC TerminalC)
open PalPeg.CloseoutWatchRound2 (TerminalRunC)
open PalPeg.CloseoutWatchRound3 (TerminalRunShiftC)
open PalPeg.CloseoutWatchRound18 (BreakEndAvC TerminalRunBreak0C TerminalRunFallbackC
  watchSeg_of_watchSegE')
open PalPeg.CloseoutWatchRound19 (WatchPrefixC watchSeg_stuck_of_mismatch watchSeg_not_canRight)
open PalPeg.CloseoutWatchRound22 (WatchMismatchNoShiftC)

/-! ## 1. The per-landing classifier -/

/-- The body of `WatchMismatchNoShiftC` at one landing: a disabled chain tick
exists and every disabled chain tick fails the shift guard after the mismatch. -/
def MismatchGuardFails (s1 : GalilVM) : Prop :=
  (∃ z, ChainTick false s1.chain z) ∧
    (∀ (vs : ScanVM) (vq : SearchVM), ChainTick false s1.chain vs.chain →
      ¬ shiftGuardVM (afterMismatch s1 vs vq))

/-- `BreakEndAvC` with the classifier recorded at the mismatch landing. -/
def BreakEndAvGC (P : Shared) (q : ℕ) (first : Fin 9) (c : Control) (s : GalilVM) : Prop :=
  ∃ (c1 : Control) (s1 : GalilVM),
    WatchSeg P q first 2048 c s c1 s1 ∧ c1.clock = 1 ∧ LiveScanWatch c1 s1 ∧
      canRight s1.right ∧ read (left s1.left) ≠ read (right s1.right) ∧
      MismatchGuardFails s1

/-- `BreakEndAvC` with the classifier *failing* at the mismatch landing: the
mismatch-shift exit. -/
def BreakEndAvSC (P : Shared) (q : ℕ) (first : Fin 9) (c : Control) (s : GalilVM) : Prop :=
  ∃ (c1 : Control) (s1 : GalilVM),
    WatchSeg P q first 2048 c s c1 s1 ∧ c1.clock = 1 ∧ LiveScanWatch c1 s1 ∧
      canRight s1.right ∧ read (left s1.left) ≠ read (right s1.right) ∧
      ¬ MismatchGuardFails s1

theorem breakEndAvC_of_G {P : Shared} {q : ℕ} {first : Fin 9} {c : Control} {s : GalilVM}
    (h : BreakEndAvGC P q first c s) : BreakEndAvC P q first c s := by
  obtain ⟨c1, s1, hseg, hclk, hlive, hav, hne, -⟩ := h
  exact ⟨c1, s1, hseg, hclk, hlive, hav, hne⟩

/-- The outer-mismatch family with the guard failure recorded. -/
def TerminalRunFallbackGC (P : Shared) (q : ℕ) (first : Fin 9) (h : ℕ)
    (cP : Control) (sP : GalilVM) : Prop :=
  ∀ (es : List Bool) (c2 : Control) (s2 : GalilVM),
    WatchSegE P q first 2048 es cP sP c2 s2 → LiveScanWatch c2 s2 →
      ∃ (cT : Control) (sT : GalilVM),
        WatchSeg P q first 2048 c2 s2 cT sT ∧ LiveScanWatch cT sT ∧
          BreakEndAvGC P q first cT sT

/-- The fourth family: the outer mismatch at which the chain may shift. -/
def TerminalRunMismatchShiftC (P : Shared) (q : ℕ) (first : Fin 9) (h : ℕ)
    (cP : Control) (sP : GalilVM) : Prop :=
  ∀ (es : List Bool) (c2 : Control) (s2 : GalilVM),
    WatchSegE P q first 2048 es cP sP c2 s2 → LiveScanWatch c2 s2 →
      ∃ (cT : Control) (sT : GalilVM),
        WatchSeg P q first 2048 c2 s2 cT sT ∧ LiveScanWatch cT sT ∧
          BreakEndAvSC P q first cT sT

theorem terminalRunFallbackC_of_G {P : Shared} {q : ℕ} {first : Fin 9} {h : ℕ}
    {cP : Control} {sP : GalilVM} (hf : TerminalRunFallbackGC P q first h cP sP) :
    TerminalRunFallbackC P q first h cP sP := by
  intro es c2 s2 hseg hlive
  obtain ⟨cT, sT, hrun, hliveT, hbe⟩ := hf es c2 s2 hseg hlive
  exact ⟨cT, sT, hrun, hliveT, breakEndAvC_of_G hbe⟩

/-- `ExitSplit3C` with the outer-mismatch family split by the classifier. -/
def ExitSplit4C (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (h : ℕ) (cP : Control) (sP : GalilVM) : Prop :=
  TerminalRunC (PofC centre place entry raw) qq first h cP sP →
    TerminalRunShiftC (PofC centre place entry raw) qq first h cP sP ∨
      TerminalRunBreak0C (PofC centre place entry raw) qq first h cP sP ∨
        TerminalRunFallbackGC (PofC centre place entry raw) qq first h cP sP ∨
          TerminalRunMismatchShiftC (PofC centre place entry raw) qq first h cP sP

/-! ## 2. The target -/

/-- **The target.**  In the guard-recording outer-mismatch family, the
classifier holds at every reachable available clock-`1` mismatch: apply the
family at that landing; every `WatchSeg` out of it is empty
(`watchSeg_stuck_of_mismatch`), so the recorded landing is the landing itself. -/
theorem watchMismatchNoShiftC_of_split {P : Shared} {q : ℕ} {first : Fin 9} {h : ℕ}
    {cP : Control} {sP : GalilVM}
    (hf : TerminalRunFallbackGC P q first h cP sP) :
    WatchMismatchNoShiftC P q first cP sP := by
  intro es c1 s1 hseg hlive hclk hav hne
  rcases hlive.2.2.2 with ⟨hPhase, hLag⟩ | ⟨wLive, hwLive⟩
  · -- copy/back 相: watch ラウンドの機械を経由せず直接出る
    exact PalPeg.CopyPhaseNoShift.watchMismatchNoShift_parts_of_copyOrBack hPhase hLag
  obtain ⟨cT, sT, hrun, -, hbe⟩ :=
    hf es c1 s1 hseg ⟨hlive.1, hlive.2.1, hlive.2.2.1, wLive, hwLive⟩
  obtain ⟨hcT, hsT⟩ := watchSeg_stuck_of_mismatch hrun hclk hav hne
  subst hcT; subst hsT
  obtain ⟨c1', s1', hseg', -, -, -, -, hG⟩ := hbe
  obtain ⟨hc', hs'⟩ := watchSeg_stuck_of_mismatch hseg' hclk hav hne
  subst hc'; subst hs'
  exact hG

/-! ## 3. The four-way split from Round 19's pieces -/

/-- **`split3_of_prefix` with the outer-mismatch family split by the
classifier.**  Same case analysis; the mismatch case is tried first with the
classifier, then without. -/
theorem split4_of_prefix (P : Shared) (q : ℕ) (first : Fin 9) (h : ℕ)
    (cP : Control) (sP : GalilVM)
    (hneP : sP.chain ≠ ChainVM.idle) (hpre : WatchPrefixC P q first cP sP)
    (hrun : TerminalRunC P q first h cP sP) :
    TerminalRunShiftC P q first h cP sP ∨ TerminalRunBreak0C P q first h cP sP ∨
      TerminalRunFallbackGC P q first h cP sP ∨ TerminalRunMismatchShiftC P q first h cP sP := by
  classical
  have toSeg : ∀ {es : List Bool} {c2 : Control} {s2 : GalilVM},
      WatchSegE P q first 2048 es cP sP c2 s2 → WatchSeg P q first 2048 cP sP c2 s2 :=
    fun hE => watchSeg_of_watchSegE' hE hneP
  by_cases hEx : ∃ (cW : Control) (sW : GalilVM),
      WatchSeg P q first 2048 cP sP cW sW ∧ LiveScanWatch cW sW ∧ ¬ canRight sW.right
  · obtain ⟨cW, sW, hW, hliveW, hnW⟩ := hEx
    refine Or.inr (Or.inl ?_)
    intro es c2 s2 hE hlive2
    rcases hpre c2 cW s2 sW (toSeg hE) hW with hfw | hbw
    · exact ⟨cW, sW, hfw, hliveW, hnW⟩
    · exact ⟨c2, s2, .stop _ _, hlive2, watchSeg_not_canRight hbw hnW⟩
  · by_cases hMisG : ∃ (c1 : Control) (s1 : GalilVM),
        WatchSeg P q first 2048 cP sP c1 s1 ∧ c1.clock = 1 ∧ LiveScanWatch c1 s1 ∧
          canRight s1.right ∧ read (left s1.left) ≠ read (right s1.right) ∧
          MismatchGuardFails s1
    · obtain ⟨c1, s1, h1, hclk, hlive1, hav1, hne1, hG⟩ := hMisG
      refine Or.inr (Or.inr (Or.inl ?_))
      intro es c2 s2 hE hlive2
      rcases hpre c2 c1 s2 s1 (toSeg hE) h1 with hfw | hbw
      · exact ⟨c2, s2, .stop _ _, hlive2, c1, s1, hfw, hclk, hlive1, hav1, hne1, hG⟩
      · obtain ⟨hc, hs⟩ := watchSeg_stuck_of_mismatch hbw hclk hav1 hne1
        subst hc; subst hs
        exact ⟨_, _, .stop _ _, hlive2, _, _, .stop _ _, hclk, hlive1, hav1, hne1, hG⟩
    · by_cases hMis : ∃ (c1 : Control) (s1 : GalilVM),
          WatchSeg P q first 2048 cP sP c1 s1 ∧ c1.clock = 1 ∧ LiveScanWatch c1 s1 ∧
            canRight s1.right ∧ read (left s1.left) ≠ read (right s1.right)
      · obtain ⟨c1, s1, h1, hclk, hlive1, hav1, hne1⟩ := hMis
        have hnG : ¬ MismatchGuardFails s1 := fun hG =>
          hMisG ⟨c1, s1, h1, hclk, hlive1, hav1, hne1, hG⟩
        refine Or.inr (Or.inr (Or.inr ?_))
        intro es c2 s2 hE hlive2
        rcases hpre c2 c1 s2 s1 (toSeg hE) h1 with hfw | hbw
        · exact ⟨c2, s2, .stop _ _, hlive2, c1, s1, hfw, hclk, hlive1, hav1, hne1, hnG⟩
        · obtain ⟨hc, hs⟩ := watchSeg_stuck_of_mismatch hbw hclk hav1 hne1
          subst hc; subst hs
          exact ⟨_, _, .stop _ _, hlive2, _, _, .stop _ _, hclk, hlive1, hav1, hne1, hnG⟩
      · refine Or.inl ?_
        intro es c2 s2 hE hlive2
        obtain ⟨cT, sT, hseg, hliveT, hT⟩ := hrun es c2 s2 hE hlive2
        obtain ⟨-, -, hT⟩ := hT
        have hreachT : WatchSeg P q first 2048 cP sP cT sT := watchSeg_append (toSeg hE) hseg
        refine ⟨cT, sT, hseg, hliveT, ?_⟩
        rcases hT with h0 | hsg | hnc | hbe
        · exact Or.inl h0
        · exact Or.inr hsg
        · exact absurd ⟨cT, sT, hreachT, hliveT, hnc⟩ hEx
        · obtain ⟨c1, s1, hseg1, hclk, hlive1, hne1⟩ := hbe
          have hreach1 : WatchSeg P q first 2048 cP sP c1 s1 := watchSeg_append hreachT hseg1
          by_cases hav1 : canRight s1.right
          · exact absurd ⟨c1, s1, hreach1, hclk, hlive1, hav1, hne1⟩ hMis
          · exact absurd ⟨c1, s1, hreach1, hlive1, hav1⟩ hEx

/-- **`ExitSplit4C` discharged** under `WatchPrefixC` and a live preparation
landing. -/
theorem exitSplit4C_of_tick (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (h : ℕ) (cP : Control) (sP : GalilVM)
    (hneP : sP.chain ≠ ChainVM.idle)
    (hpre : WatchPrefixC (PofC centre place entry raw) qq first cP sP) :
    ExitSplit4C centre place entry qq first raw h cP sP :=
  fun hrun => split4_of_prefix (PofC centre place entry raw) qq first h cP sP hneP hpre hrun

/-- **Derived.**  The four-way split folds back to Round 18's three-way split
(the fourth family lands in `TerminalRunFallbackC` too, forgetting the guard). -/
theorem exitSplit3C_of_4 {centre : GalilVM → Fin 3}
    {place : GalilVM → GalilScaffoldPlace.Place} {entry qq : ℕ} {first : Fin 9}
    {raw : List (Fin 2)} {h : ℕ} {cP : Control} {sP : GalilVM}
    (h4 : ExitSplit4C centre place entry qq first raw h cP sP) :
    PalPeg.CloseoutWatchRound18.ExitSplit3C centre place entry qq first raw h cP sP := by
  intro hrun
  rcases h4 hrun with hs | hb | hf | hm
  · exact Or.inl hs
  · exact Or.inr (Or.inl hb)
  · exact Or.inr (Or.inr (terminalRunFallbackC_of_G hf))
  · refine Or.inr (Or.inr ?_)
    intro es c2 s2 hseg hlive
    obtain ⟨cT, sT, hrunT, hliveT, c1, s1, hseg1, hclk, hlive1, hav, hne, -⟩ :=
      hm es c2 s2 hseg hlive
    exact ⟨cT, sT, hrunT, hliveT, c1, s1, hseg1, hclk, hlive1, hav, hne⟩

end PalPeg.CloseoutWatchRound23

#print axioms PalPeg.CloseoutWatchRound23.watchMismatchNoShiftC_of_split
#print axioms PalPeg.CloseoutWatchRound23.split4_of_prefix
#print axioms PalPeg.CloseoutWatchRound23.exitSplit4C_of_tick
#print axioms PalPeg.CloseoutWatchRound23.exitSplit3C_of_4
