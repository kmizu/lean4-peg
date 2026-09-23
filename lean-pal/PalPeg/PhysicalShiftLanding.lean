import PalPeg.PhysicalShiftTick
import PalPeg.PhysicalCompareGuard

/-! # Identifying the complete physical entry with the abstract shift tick -/
set_option autoImplicit false
namespace PalPeg.PhysicalShiftLanding
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract PalPeg.PhysicalShiftTick
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilScaffoldInputHead (left read)
open PalPeg.GalilScaffoldChainVerifier (right)
open PalPeg.GalilScaffoldCounter (positive inc)
open PalPeg.PhysicalWatchStep (afterInternal)

/-- The two successful watch quanta preserve the period length used by
beginShift. The physical row lends that same length to remaining. -/
theorem moved_eq_entry (P : Shared) (q : ℕ) (first : Fin 9) (x : State GalilVM)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm)
    (t u : GalilVM) (hcmp : compareFound P q first x.vm t)
    (hmis : ¬ (galilFrameS P q first).matched t)
    (hmid : t.chain = .watch (afterInternal (positive wm.lag) wm))
    (hblock : PalPeg.GalilBranchInvariants.OnBlock
      (afterInternal (positive wm.lag) wm).machine.control.period)
    (hentry : beginShiftVM' t u) :
    moved (positive wm.lag) x wm = ⟨{x.ctl with mode := .shift, clock := 2048}, u⟩ := by
  have hfun := compare_eq_compareFun hcmp
  have hne : read (left x.vm.left) ≠ read (right x.vm.right) := by
    intro heq
    apply hmis
    change read t.left = read t.right
    rw [hfun, (compareFun_cursors P x.vm).1, (compareFun_cursors P x.vm).2]
    exact heq
  have ht := hfun.trans (PalPeg.PhysicalCompareGuard.compare_mismatch P x.vm wm hchain hne)
  obtain ⟨other, hother, hu⟩ := hentry
  have heq : other = afterInternal (positive wm.lag) wm := ChainVM.watch.inj (hother.symm.trans hmid)
  subst other
  let mid := afterInternal (positive wm.lag) wm
  have hlen : periodLength (PalPeg.GalilScaffoldChainWatch.immediate mid) = periodLength mid :=
    PalPeg.GalilChainCoupling.periodLength_consume mid.machine mid.lag mid.margin
      mid.lag (inc mid.margin) hblock
  rw [hu, ht]
  simp only [moved, PalPeg.PhysicalShiftStart.entryState, PalPeg.PhysicalShiftEntry.lent,
    PalPeg.PhysicalShiftStart.prepared, PalPeg.PhysicalShiftStart.pairedState,
    stepState, chainVerifierBack, afterMismatch, scanLens, searchLens, radiusAfter]
  rw [hlen]

/-- The physical step reaches the actual abstract beginShift successor. Its
two successful quanta are supplied by the comparison and source window; the
only period premise is the existing source block invariant. -/
theorem running_from_window (w arrived : List (Fin 2)) (x : State GalilVM)
    (p : PalPeg.LocalRoleRouting.Config CoreControl Γm tapeCountM)
    (he : PalPeg.PhysicalCacheInvariant.Running w x (PalPeg.LocalRoleRouting.decode p))
    (hmode : x.ctl.mode = .scan) (P : Shared) (q : ℕ) (first : Fin 9) (t u : GalilVM)
    (hcmp : compareFound P q first x.vm t)
    (hmis : ¬ (galilFrameS P q first).matched t) (hg : shiftGuardVM t)
    (hentry : beginShiftVM' t u)
    (hx : PalPeg.WindowRun.ChainWindowRun arrived x.ctl x.vm)
    (hblock : PalPeg.GalilBranchInvariants.BlockInv x.vm.chain)
    (hr : PalPeg.GalilScaffoldInputTrace.Represents x.vm.right.head arrived)
    (hp : x.vm.right.head.focus ≠ none) (hcan : PalPeg.GalilScaffoldChainVerifier.canRight x.vm.right)
    (hlen : arrived.length ≤ w.length) :
    ∃ wm : PalPeg.GalilScaffoldChainWatch.State, x.vm.chain = .watch wm ∧
      PalPeg.PhysicalCacheInvariant.Running w ⟨{x.ctl with mode := .shift, clock := 2048}, u⟩
        (PalPeg.LocalRoleRouting.decode ((step (positive wm.lag)).apply blankM p none)) := by
  obtain ⟨wm, hw, hfirst, hmid⟩ := PalPeg.PhysicalShiftStart.source_of_guard hcmp hmis hg
  have hgood := PalPeg.PhysicalShiftStart.immediate_good_of_window arrived hx hr hp hcan
    hcmp hmis hg _ hmid
  obtain ⟨old, hold, hinternal⟩ := PalPeg.WindowPack.source_watch_of_guard hcmp hmis hg
  have holdEq : old = wm := ChainVM.watch.inj (hold.symm.trans hw)
  subst old
  have hb := PalPeg.GalilBranchInvariants.blockInv_step
    (ChainStep.watchStep wm _ (hinternal _ hmid)) (hw ▸ hblock)
  have hout := running (positive wm.lag) w arrived x p he hmode wm hw hfirst hgood hcan hr hlen
  rw [moved_eq_entry P q first x wm hw t u hcmp hmis hmid hb hentry] at hout
  exact ⟨wm, hw, hout⟩

/-- The comparison/entry relations select exactly the shift arm of tickFun. -/
theorem tick_eq_entry (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (x : State GalilVM) (t u : GalilVM)
    (hmode : x.ctl.mode = .scan) (hclock : x.ctl.clock = 1)
    (hwatch : ∃ wm, x.vm.chain = .watch wm)
    (hcan : PalPeg.GalilScaffoldChainVerifier.canRight x.vm.right)
    (hcmp : compareFound (PalPeg.GalilRunSkeleton.PofC centre place entry w) q first x.vm t)
    (hmis : ¬ (galilFrameS (PalPeg.GalilRunSkeleton.PofC centre place entry w) q first).matched t)
    (hg : shiftGuardVM t) (hentry : beginShiftVM' t u) :
    tickFun (PalPeg.FrameFunction.galilFrameFun centre place entry q first w)
      (galilFrameS (PalPeg.GalilRunSkeleton.PofC centre place entry w) q first) 2048 x =
      ⟨{x.ctl with mode := .shift, clock := 2048}, u⟩ := by
  obtain ⟨wm, hw⟩ := hwatch
  have hrestart : restartGuardTest x.vm = false := by simp [restartGuardTest, hw]
  have hav := (canRightTest_iff x.vm.right).mp hcan
  have hmatch : PalPeg.FrameFunction.matchedTest (scanLens.get t) = false := decide_eq_false hmis
  have hguard := (shiftGuardTest_iff t).mp hg
  have hvalue := compare_eq_compareFun hcmp
  have hentryValue := beginShiftFun_eq hg hentry
  simp only [tickFun, hmode, PalPeg.FrameFunction.galilFrameFun, hrestart,
    Bool.false_eq_true, if_false, hav, Bool.not_true, Bool.and_false, hclock,
    Nat.lt_irrefl, ← hvalue, hmatch, hguard, if_true, ← hentryValue]

/-- The complete one-sweep physical entry simulates the abstract tickFun arm.
Transport of the source window and word facts from OnRun, and selection in the
shared dispatcher, are the remaining entry obligations. -/
theorem running_tick (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (w arrived : List (Fin 2)) (x : State GalilVM)
    (p : PalPeg.LocalRoleRouting.Config CoreControl Γm tapeCountM)
    (he : PalPeg.PhysicalCacheInvariant.Running w x (PalPeg.LocalRoleRouting.decode p))
    (hmode : x.ctl.mode = .scan) (hclock : x.ctl.clock = 1) (t : GalilVM)
    (hcmp : compareFound (PalPeg.GalilRunSkeleton.PofC centre place entry w) q first x.vm t)
    (hmis : ¬ (galilFrameS (PalPeg.GalilRunSkeleton.PofC centre place entry w) q first).matched t)
    (hg : shiftGuardVM t)
    (hx : PalPeg.WindowRun.ChainWindowRun arrived x.ctl x.vm)
    (hblock : PalPeg.GalilBranchInvariants.BlockInv x.vm.chain)
    (hr : PalPeg.GalilScaffoldInputTrace.Represents x.vm.right.head arrived)
    (hp : x.vm.right.head.focus ≠ none) (hcan : PalPeg.GalilScaffoldChainVerifier.canRight x.vm.right)
    (hlen : arrived.length ≤ w.length) :
    ∃ wm : PalPeg.GalilScaffoldChainWatch.State, x.vm.chain = .watch wm ∧
      PalPeg.PhysicalCacheInvariant.Running w
        (tickFun (PalPeg.FrameFunction.galilFrameFun centre place entry q first w)
          (galilFrameS (PalPeg.GalilRunSkeleton.PofC centre place entry w) q first) 2048 x)
        (PalPeg.LocalRoleRouting.decode ((step (positive wm.lag)).apply blankM p none)) := by
  obtain ⟨u, hu⟩ := beginShift_exists t hg
  obtain ⟨wm, hw, hout⟩ := running_from_window w arrived x p he hmode
    (PalPeg.GalilRunSkeleton.PofC centre place entry w) q first t u hcmp hmis hg hu
    hx hblock hr hp hcan hlen
  rw [← tick_eq_entry centre place entry q first w x t u hmode hclock ⟨wm, hw⟩ hcan hcmp hmis hg hu] at hout
  exact ⟨wm, hw, hout⟩

/-- info: 'PalPeg.PhysicalShiftLanding.running_tick' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms running_tick

end PalPeg.PhysicalShiftLanding
