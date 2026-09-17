import PalPeg.CloseoutWatchRound25

/-!
# Closeout watch round 27 — tying the mismatch-shift guard to the frame's compare

Round 25 diagnosed why `MismatchShiftRouteC` (Round 25 §2) is not an instance of
`CloseoutWatchRound7.ShiftRoundAtC`: the trigger `shiftGuardVM s1` reads the
chain and the right head *at the landing*, while the recorded guard reads them
on the post-compare scan projection.  Two facts sharpen the diagnosis.

1. `ShiftRoundAtC` is itself a **named open hypothesis** (a `def`, no producer
   anywhere in `PalPeg/`).  There is no proof "that only uses the trigger to get
   the post-compare guard" to re-run with the trigger replaced; the only way to
   derive `MismatchShiftRouteC` from `ShiftRoundAtC` is to *produce* the trigger
   at `s1`, and that is exactly the pre/post-compare mismatch.  So the honest
   statement is `mismatchShiftRouteC_of_unique` below: `ShiftRoundAtC` plus the
   trigger-at-landing hypothesis `MismatchTriggerC`.

2. The witness `vs` of `¬ MismatchGuardFails s1` is **not pinned** by
   `compare_scan_unique`: `MismatchGuardFails` quantifies over `vs` with only
   `ChainTick false s1.chain vs.chain`, so `vs.left`/`vs.right` are free and the
   recorded guard `symbol focus = read vs.right` says nothing about the frame's
   real right head `right s1.right`.  `compare_scan_unique` needs a *compare*
   for `vs`, which the classifier does not give.  The tied classifier
   `MismatchGuardFailsC` (quantifying over the compares of the frame) fixes
   this: `guard_of_mismatchShift` then yields the guard on the frame's actual
   post-compare state for *every* search quantum, i.e. at the state where
   `beginShiftVM'` fires.  `mismatchGuardFailsC_of` shows the tied classifier
   is implied by the original one — so `¬ MismatchGuardFailsC` is the *stronger*
   record; Round 23's producers would have to record it (they classify by the
   frame's compare, so this is a bookkeeping change, not a new proof obligation).

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

namespace PalPeg.CloseoutWatchRound27

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton PalPeg.GalilInvPlus PalPeg.GalilInvPlus2
open PalPeg.CloseoutContracts
open PalPeg.CloseoutWatchRun (LiveScanWatch roundFuel)
open PalPeg.CloseoutWatchRound7 (ShiftRoundAtC ShiftRoundData)
open PalPeg.CloseoutWatchRound23 (MismatchGuardFails)
open PalPeg.CloseoutWatchRound25 (MismatchShiftRouteC mismatchShift_tick)
open PalPeg.CloseoutWatchRound20 (compare_scan_unique)

/-! ## 1. The compare's chain tick at an outer mismatch is the disabled tick -/

theorem chainTick_false_of_compare {P : Shared} {q : ℕ} {first : Fin 9} {s : GalilVM}
    {vs : ScanVM} (hcmp : (galilFrame P q first).compare s (scanLens.set s vs))
    (hne : read (left s.left) ≠ read (right s.right)) :
    ChainTick false s.chain vs.chain := by
  obtain ⟨⟨-, -, ht⟩, -⟩ := hcmp
  rw [scanLens.get_set] at ht
  have hd : decide (read (left s.left) = read (right s.right)) = false := by
    simpa using hne
  have ht' : ChainTick (decide (read (left s.left) = read (right s.right))) s.chain vs.chain := ht
  rw [hd] at ht'
  exact ht'

/-! ## 2. The post-mismatch guard depends only on `vs.chain` and `vs.right` -/

theorem shiftGuard_afterMismatch_transfer {s : GalilVM} {vs vs' : ScanVM} {vq vq' : SearchVM}
    (hc : vs.chain = vs'.chain) (hr : vs.right = vs'.right)
    (hg : shiftGuardVM (afterMismatch s vs vq)) : shiftGuardVM (afterMismatch s vs' vq') := by
  obtain ⟨w, hw, hlag, hph, hbr, hmar, hsym⟩ := hg
  refine ⟨w, ?_, hlag, hph, hbr, ?_, ?_⟩
  · show vs'.chain = .watch w
    exact hc ▸ hw
  · show (if s.periodOnly then singlePositive s.cycle = true else negative w.margin = false)
    exact hmar
  · show GalilScaffoldChainConsume.symbol w.machine.control.period.focus = read vs'.right
    exact hr ▸ hsym

/-! ## 3. The tied classifier -/

/-- `MismatchGuardFails` with the scan projection tied to the frame's compare:
every scan projection the frame can choose fails the guard after the mismatch. -/
def MismatchGuardFailsC (P : Shared) (q : ℕ) (first : Fin 9) (s1 : GalilVM) : Prop :=
  (∃ z, ChainTick false s1.chain z) ∧
    (∀ (vs : ScanVM) (vq : SearchVM), (galilFrame P q first).compare s1 (scanLens.set s1 vs) →
      ¬ shiftGuardVM (afterMismatch s1 vs vq))

/-- The original classifier implies the tied one (at an outer mismatch), so
`¬ MismatchGuardFailsC` is the stronger record. -/
theorem mismatchGuardFailsC_of {P : Shared} {q : ℕ} {first : Fin 9} {s1 : GalilVM}
    (hne : read (left s1.left) ≠ read (right s1.right)) (h : MismatchGuardFails s1) :
    MismatchGuardFailsC P q first s1 :=
  ⟨h.1, fun vs vq hcmp => h.2 vs vq (chainTick_false_of_compare hcmp hne)⟩

/-- **The guard at the frame's actual post-compare state.**  With the tied
classifier failing, the frame's compare at `s1` (pinned by `compare_scan_unique`)
lands in a state where `shiftGuardVM` holds for every search quantum — the
state from which `beginShiftVM'` fires. -/
theorem guard_of_mismatchShift {P : Shared} {q : ℕ} {first : Fin 9} {s1 : GalilVM} {vs : ScanVM}
    (hnG : ¬ MismatchGuardFailsC P q first s1)
    (hcmp : (galilFrame P q first).compare s1 (scanLens.set s1 vs))
    (hne : read (left s1.left) ≠ read (right s1.right)) :
    ∀ vq : SearchVM, shiftGuardVM (afterMismatch s1 vs vq) ∧
      ∃ t, beginShiftVM' (afterMismatch s1 vs vq) t := by
  classical
  intro vq
  have hz : ∃ z, ChainTick false s1.chain z := ⟨_, chainTick_false_of_compare hcmp hne⟩
  by_contra hno
  apply hnG
  refine ⟨hz, ?_⟩
  intro vs' vq' hcmp' hg'
  have hvs : vs' = vs := compare_scan_unique hcmp' hcmp
  subst hvs
  have hg : shiftGuardVM (afterMismatch s1 vs' vq) :=
    shiftGuard_afterMismatch_transfer rfl rfl hg'
  exact hno ⟨hg, beginShift_exists _ hg⟩

/-! ## 4. `MismatchShiftRouteC` from `ShiftRoundAtC` — the minimal reformulation -/

/-- **NAMED (open) — the trigger at the mismatch-shift landing.**  What
`ShiftRoundAtC` needs and the mismatch-shift record lacks: the pre-compare
trigger `roundFuel h s1 = 0 ∨ shiftGuardVM s1` at the landing itself. -/
def MismatchTriggerC (h : ℕ) : Prop :=
  ∀ (c1 : Control) (s1 : GalilVM), LiveScanWatch c1 s1 → c1.clock = 1 → canRight s1.right →
    read (left s1.left) ≠ read (right s1.right) → ¬ MismatchGuardFails s1 →
      (roundFuel h s1 = 0 ∨ shiftGuardVM s1)

/-- `MismatchShiftRouteC` is `ShiftRoundAtC` once the trigger is available at the
landing.  `ShiftRoundAtC` has no producer, so nothing weaker is derivable from it. -/
theorem mismatchShiftRouteC_of_unique (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m h lower : ℕ)
    (hat : ShiftRoundAtC centre place entry qq first raw m h lower)
    (htrig : MismatchTriggerC h) :
    MismatchShiftRouteC centre place entry qq first raw m h lower := by
  intro sF vq c1 s1 hlive hclk hav hne hnG
  exact hat sF vq c1 s1 hlive (htrig c1 s1 hlive hclk hav hne hnG)

end PalPeg.CloseoutWatchRound27

#print axioms PalPeg.CloseoutWatchRound27.chainTick_false_of_compare
#print axioms PalPeg.CloseoutWatchRound27.guard_of_mismatchShift
#print axioms PalPeg.CloseoutWatchRound27.mismatchGuardFailsC_of
#print axioms PalPeg.CloseoutWatchRound27.mismatchShiftRouteC_of_unique
