import PalPeg.CloseoutWatchRound12
import PalPeg.CloseoutContracts

/-!
# Round 13: removing `hland` from the watch-phase crossing route

`CloseoutWatchRound12.reachAtC3_of_crossW` closes the crossing case of the
watch phase, but only modulo one NAMED fact, `hland`: that the landing of the
crossing comparison is *itself* a cycle-entry state (`InvLPS`).  That fact is
false-shaped for the idle machinery (`GalilReplaySegment.inv_after_replay`
produces `ChainVM.idle`, while a watch landing has `ChainVM.watch w'`), and
Round 12's continuation was the *empty* run at the crossing state, which is why
it needed `InvLPS` right there.

This file supplies the continuation from the **watch remainder** instead.
`ReachAtC3`'s continuation clause only asks for *some* costed run out of the
report point `y` reaching an `InvLPS` state below `2(m+1)-1`; it does not ask
for `y` itself to be a cycle entry.  So the crossing state is handed to the
watch phase's own exit — `CloseoutWatchRun.watchRun_of_distance` drives the
rounds to a terminal tail, `CloseoutWatchRound3/4/5` turn a tail into
`CloseoutContracts.FoundExit`, and *both* of `FoundExit`'s constructors already
deliver an `InvLPS` landing:

* `landed` — `GalilInvPlus3.invLPS_of_landed` at the *entry* copy pack
  `hIN.1.1.2` and the run `⟨c, r⟩ ⟶ ⟨c1, s1⟩ ⟶ ⟨cT, sT⟩` (`stepsAll_trans`);
  the crossing state never has to carry a pack of its own.
* `broke` — the `InvLP2`/`CentreRep`/`ReplayStage` triple *is* `InvLPS`
  definitionally, exactly as in `GalilInvPlus3.cycleOutMC3_of_foundInReplay`.

Taking the `FoundExit` at index `m+1` gives the position bound
`position sT.right ≤ 2*(m+1)-1` that `ReachAtC3` demands, verbatim.

## What is proved here (unconditionally, no `sorry`)

1. `invLPS_tail_of_foundExit` — a `FoundExit` out of any state reached from an
   `InvLPS` entry yields the `ReachAtC3` continuation payload (run, cost,
   `InvLPS`, position bound).
2. `reachAtC3_of_crossW'` — **`reachAtC3_of_crossW` with `hland` removed.**
   The `hland` hypothesis is replaced by `WatchTailC`, the watch remainder at
   the crossing landing, which is the conclusion of
   `CloseoutWatchRound6.foundExit_compare_final6` (§3 records the exact
   instantiation).

## Still open, NAMED with exact type

* `WatchTailC` (below): at the landing `(c1, s1)` of the crossing comparison,

  ```
  FoundExit (PofC centre place entry raw) q first raw (m+1) c1 s1
  ```

  i.e. the watch phase run out of that landing terminates in a tail.  This is
  the *same* contract group `foundExit_compare_final6` already receives
  (`RightCanC`, `RightSaneC`, `StartLeC`, `LedgerOriginC`, `ZeroLagAtMatchC`,
  `DistanceNonnegC`, `PeriodMatchC`, plus the per-state entry data
  `StageEntryC` / `SegReachedW` / `LandingRestartReach` / `PrepInputsG3` /
  `MismatchExitG` / `FoundCompareCtxC` / `ExitSplitC` and the two tails), now
  quantified over the crossing landing rather than over a stage entry.  Nothing
  in the tree currently instantiates that group at a *mid-segment* landing, so
  the quantified form is left NAMED.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

namespace PalPeg.CloseoutWatchRound13

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton PalPeg.GalilOracleDischarge PalPeg.GalilOracleLocal
open PalPeg.GalilCheckpoints PalPeg.GalilInvPlus PalPeg.GalilInvPlus2
open PalPeg.GalilOracleMC PalPeg.GalilOracleMC2 PalPeg.GalilOracleMC3
open PalPeg.GalilLeafPos PalPeg.GalilLeafReport PalPeg.GalilOneFallback
open PalPeg.GalilInvPlus3 PalPeg.GalilTraceCost PalPeg.GalilCostedFound
open PalPeg.CloseoutContracts (FoundExit)
open PalPeg.CloseoutWatchRound11
open PalPeg.CloseoutWatchRound12 (scanSeg_split reportPointAt_of_scanSeg)

/-! ## 1. A `FoundExit` tail is a `ReachAtC3` continuation -/

/-- **Derived.**  `FoundExit` out of a state `(c1, s1)` that is itself reached
from an `InvLPS` entry `(c, r)` gives exactly the payload the continuation
clause of `ReachAtC3` asks for.  The `landed` branch uses the *entry* copy pack
and the composed run, so `(c1, s1)` need not be a cycle entry. -/
theorem invLPS_tail_of_foundExit (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m : ℕ) {c c1 : Control} {r s1 : GalilVM} {k0 : ℕ}
    (hIN : InvLPS (PofC centre place entry raw) q first raw c r)
    (hst0 : StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048
      (SoundScanNR raw) k0 ⟨c, r⟩ ⟨c1, s1⟩)
    (h : FoundExit (PofC centre place entry raw) q first raw m c1 s1) :
    ∃ (c' : Control) (r' : GalilVM) (k' : ℕ) (L' : List Piece),
      StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048 (SoundScanNR raw) k'
        ⟨c1, s1⟩ ⟨c', r'⟩ ∧
      CostedRun s1 r' k' L' ∧
      InvLPS (PofC centre place entry raw) q first raw c' r' ∧
      position r'.right ≤ 2 * m - 1 := by
  cases h with
  | landed cT sT k L hst hcr hM hR hres hSpan hprog hpos =>
      exact ⟨cT, sT, k, L, hst, hcr,
        invLPS_of_landed centre place entry q first hIN.1.1.2 (stepsAll_trans hst0 hst)
          (inv_of_residual hM hR hres) hSpan, hpos⟩
  | broke cT sT k L hst hcr hIT hcenT hstage hc hlt hpos =>
      exact ⟨cT, sT, k, L, hst, hcr, ⟨⟨hIT, hcenT⟩, hstage⟩, hpos⟩

/-! ## 2. The crossing route without `hland` -/

/-- **NAMED (open) — the watch remainder at the crossing landing.**  The landing
of the crossing comparison runs on to a terminal tail of the watch phase.  This
is `CloseoutWatchRound6.foundExit_compare_final6`'s conclusion, quantified over
the landing. -/
def WatchTailC (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m j : ℕ)
    (c : Control) (r : GalilVM) : Prop :=
  ∀ (c1 : Control) (s1 : GalilVM),
    ScanSeg (PofC centre place entry raw) q first 2048 j c r c1 s1 →
    position s1.right = 2 * m - 1 → c1.replaying = false → c1.clock = 2048 →
    FoundExit (PofC centre place entry raw) q first raw (m + 1) c1 s1

/-- **Derived — `CloseoutWatchRound12.reachAtC3_of_crossW` with `hland`
removed.**  The continuation is the watch remainder, not the empty run. -/
theorem reachAtC3_of_crossW' (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m n : ℕ) (hm1 : 1 ≤ m) (hmle : m ≤ raw.length)
    {c c' : Control} {r t : GalilVM}
    (hIN : InvLPS (PofC centre place entry raw) q first raw c r)
    (hseg : ScanSeg (PofC centre place entry raw) q first 2048 n c r c' t)
    (hlt : position r.right < 2 * m - 1) (hge : 2 * m - 1 ≤ position t.right)
    (htail : WatchTailC centre place entry q first raw m (2 * m - 1 - position r.right) c r) :
    ReachAtC3 (PofC centre place entry raw) q first raw m c r := by
  classical
  set P : Shared := PofC centre place entry raw with hP
  have hI : InvL raw c r := invLPS_invL hIN
  obtain ⟨-, -, -, -, hMC, R0, hi0, -, -, -⟩ := invS_entry_data hI.1
  obtain ⟨-, hc0, ho0⟩ := invL_entry hI
  set j : ℕ := 2 * m - 1 - position r.right with hj
  have hposT : position t.right = position r.right + n :=
    (scanSeg_right_position raw P q first 2048 hseg hi0).2
  have hjn : j ≤ n := by omega
  have hj1 : 1 ≤ j := by omega
  obtain ⟨c1, s1, h1, -, href⟩ := scanSeg_split P q first 2048 hseg j hjn
  obtain ⟨hfr, hnr1, hclk1⟩ := href hj1
  obtain ⟨hi1, hp1⟩ := scanSeg_right_position raw P q first 2048 h1 hi0
  have hpos1 : position s1.right = 2 * m - 1 := by rw [hp1]; omega
  have hrp : PalPeg.GalilReportPrefix.ReportPointAt raw m ⟨c1, s1⟩ :=
    reportPointAt_of_scanSeg raw P q first m j hm1 hmle h1 hi0 hMC hnr1 (by omega)
  obtain ⟨k, kc, p', r', L, hstOut, hk, hp', hcr, -, -, -⟩ :=
    watchSeg_costed raw P rfl rfl q first 2048 le_rfl
      (watchSeg_of_scanSeg P q first 2048 h1) (position r.center) R0 0 hi0 ho0 (by omega)
      (by omega)
  have hkc : kc = k := by omega
  have hst : StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨c1, s1⟩ :=
    stepsAll_mono (fun st h0 _ _ => h0) hstOut
  have hcont := invLPS_tail_of_foundExit centre place entry q first raw (m + 1) hIN hst
    (htail c1 s1 h1 hpos1 hnr1 hclk1)
  refine ⟨⟨c1, s1⟩, k, L, hst, by rw [← hkc] at *; exact hcr, hrp, hfr, fun _ => ?_⟩
  obtain ⟨cT, sT, k', L', hst', hcr', hIS, hposT'⟩ := hcont
  exact ⟨cT, sT, k', L', hst', hcr', hIS, hposT'⟩

#print axioms invLPS_tail_of_foundExit
#print axioms reachAtC3_of_crossW'

end PalPeg.CloseoutWatchRound13
