import PalPeg.PhysicalMatchCounters

/-! # Grow and matched-search counters in one bounded physical row

This is the nonhead part of the comparison. It keeps the source heads and
output control; the final comparison still needs their twelve-slot assembly.
-/
set_option autoImplicit false
namespace PalPeg.PhysicalGrowMatch
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract
open PalPeg.PhysicalDebtMirror (RebuildingCore Rebuilding)
open PalPeg.PhysicalLoanInvariant (Balanced)
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilScaffoldCounter (positive dec)
open PalPeg.Program PalPeg.Local PalPeg.CloseoutCoreEnc12 PalPeg.LocalStepFusion

def prepared (x : State GalilVM) : State GalilVM :=
  PalPeg.PhysicalMatchCounters.prepared x.vm.periodOnly x.ctl.replaying (PalPeg.PhysicalGrowCount.grown x)

noncomputable def body : ActRule (Fin 2) CoreControl Γm tapeCountM microRadius :=
  seqRule PalPeg.PhysicalGrowCount.body PalPeg.PhysicalMatchCounters.currentRule

theorem balanced (x : State GalilVM) (hb : Balanced x) : Balanced (prepared x) :=
  PalPeg.PhysicalMatchCounters.balanced x.vm.periodOnly x.ctl.replaying _
    (PalPeg.PhysicalGrowCount.balanced_grown x hb)

/-- Grow's span/work row and its two payments use 32+32+32; the matched
counter row uses 32. Intermediate windows supply every debt sign decision. -/
theorem body_ideal (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : Rebuilding w x p) (hb : Balanced x) :
    Rebuilding w (prepared x) (idealStep body blankM p none) := by
  have hg := PalPeg.PhysicalGrowCount.body_ideal w x p he hb
  have hm := PalPeg.PhysicalMatchCounters.running_current w (PalPeg.PhysicalGrowCount.grown x) _ hg hb.1
  change Rebuilding w (prepared x)
    (idealStep (K := 96 + 32)
      (seqRule PalPeg.PhysicalGrowCount.body PalPeg.PhysicalMatchCounters.currentRule) blankM p none)
  rw [seqRule_ideal blankM _ _ p none (fun j =>
    (show 96 + 32 ≤ margin by decide).trans (PalPeg.PhysicalDebtRebuild.sweep_margin w x p he j))]
  exact hm

/-- The complete counter/search row is executable by one real sweep, with no
extra abstract tick between growth and its matched advance. -/
theorem running (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : Rebuilding w x p) (hb : Balanced x) :
    Rebuilding w (prepared x) ((compStep body).apply blankM p none) := by
  have hi := body_ideal w x p he hb
  have hm : ∀ j, microRadius ≤ pos (p.2 j) := fun j =>
    (show microRadius ≤ margin by decide).trans (PalPeg.PhysicalDebtRebuild.sweep_margin w x p he j)
  obtain ⟨hc, ht⟩ := compStep_apply body blankM p none hm
  exact PalPeg.MachineStep.sweepClosed_sweepClosure blankM (RebuildingCore w) _ _ _ hi hc.symm ht

/-- The two cursor changes are exactly what remains of the matched VM update.
The control/output change is also left to the final tick assembler. -/
def moved (x : State GalilVM) : GalilVM :=
  {(prepared x).vm with left := PalPeg.GalilScaffoldInputHead.left x.vm.left, right := PalPeg.GalilScaffoldChainVerifier.right x.vm.right}

theorem matched_grow (P : Shared) (x : State GalilVM)
    (hi : x.vm.chain = .idle) (hm : x.vm.search.mode = .grow)
    (hw : positive x.vm.search.work = true)
    (ha : PalPeg.GalilScaffoldInputHead.read (PalPeg.GalilScaffoldInputHead.left x.vm.left) =
      PalPeg.GalilScaffoldInputHead.read (PalPeg.GalilScaffoldChainVerifier.right x.vm.right)) :
    (if x.ctl.replaying then {compareFun P x.vm with replay := dec (compareFun P x.vm).replay}
      else compareFun P x.vm) = moved x := by
  simp only [compareFun, ha, decide_true, searchEffectFun, hi, searchLens, searchStepFun,
    hm, hw, if_true, SearchVM.toPrep, SearchVM.ofPrep, PalPeg.GalilScaffoldStagePrepare.growStep,
    PalPeg.GalilScaffoldStagePrepare.runState, PalPeg.GalilScaffoldPreparePaced.afterAdvance,
    chainBorn, ChainVM.isIdle, Bool.true_and, chainAtFun]
  cases hc : x.vm.periodOnly <;> cases hr : x.ctl.replaying <;>
    simp [moved, prepared, PalPeg.PhysicalMatchCounters.prepared, PalPeg.PhysicalGrowCount.grown,
      PalPeg.PhysicalGrowStorage.prepared, PalPeg.PhysicalDebtRebuild.paid,
      PalPeg.ChainBoundaryCache.advanceCounter, PalPeg.GalilScaffoldGrow.add,
      afterCompare, cycleAfter, radiusAfter, scanLens, searchLens, afterBirth, hc, hr, hm, hi] <;> exact ⟨rfl, rfl⟩

/-- info: 'PalPeg.PhysicalGrowMatch.running' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms running

/-- info: 'PalPeg.PhysicalGrowMatch.matched_grow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms matched_grow

end PalPeg.PhysicalGrowMatch
