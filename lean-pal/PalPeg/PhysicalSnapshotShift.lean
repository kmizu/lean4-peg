import PalPeg.PhysicalSnapshotInvariant

/-! # Shift with the independent restart snapshots

All six reclaimed carriers decrement in the same sweep as the existing shift
row. The legal canonical tick supplies head availability for its storage
representative; no run hypothesis is imposed on that representative.
-/
set_option autoImplicit false
namespace PalPeg.PhysicalSnapshotShift
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract
open PalPeg.PhysicalRestartStorage
open PalPeg.PhysicalSearchSnapshots (saved)
open PalPeg.PhysicalScanCount (RestCommands workStep)
open PalPeg.PhysicalCacheInvariant (Running)
open PalPeg.PhysicalCacheMachine (successor)
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilScaffoldCounter (Counter positive dec)
open PalPeg.GalilFinalAssembly2 (centreC placeC)
open PalPeg.PhysicalShift (shifted)

/-- Rebuild the legal moving tick after changing only dormant storage. -/
theorem saved_tick (w : List (Fin 2)) (x : State GalilVM)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm)
    (hmode : x.ctl.mode = .shift) (hremaining : positive x.vm.remaining = true)
    {y : State GalilVM}
    (htick : Tick (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x y)
    (boundary last spare : Counter) :
    Tick (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048
      (saved x boundary last spare) (shifted (saved x boundary last spare) wm) := by
  obtain ⟨_, _, hcenterReady, hleftReady, hleftNextReady⟩ := PalPeg.PhysicalShift.ready_of_tick w htick hmode hremaining
  apply Tick.shift_one _ _ _ hmode (Or.inl hremaining)
  exact ⟨⟨hcenterReady, hleftReady, hleftNextReady, wm, hchain, rfl⟩, rfl⟩

noncomputable def moving (rest : RestCommands) : PalPeg.PhysicalBootFeed.CoreStep :=
  PalPeg.PhysicalSearchSnapshots.overlayWith PalPeg.PhysicalSearchSnapshots.decrement (workStep rest)

/-- The existing shift and all snapshot updates are proved on the same source
windows and same physical sweep. -/
theorem running (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : CoreState) (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm)
    (spare : Counter) (h age : ℕ) (hInv : PalPeg.ChainBoundaryCache.Inv h age wm.machine.control spare)
    (henc : Running w (saved x wm.machine.control.boundary wm.machine.control.last spare) p)
    (hmode : x.ctl.mode = .shift) (hremaining : positive x.vm.remaining = true)
    (hbound : PalPeg.PhysicalShift.RemainingBound x) {y : State GalilVM}
    (htick : Tick (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x y) :
    Running w (saved (successor w x) (chainShiftOne wm).machine.control.boundary
      (chainShiftOne wm).machine.control.last (dec spare)) ((moving rest).apply blankM p none) ∧
      PalPeg.ChainBoundaryCache.Inv h age (chainShiftOne wm).machine.control (dec spare) := by
  let sx := saved x wm.machine.control.boundary wm.machine.control.last spare
  have hrepresentativeTick := saved_tick w x wm hchain hmode hremaining htick wm.machine.control.boundary wm.machine.control.last spare
  have hrepresentativeBound : PalPeg.PhysicalShift.RemainingBound sx := hbound
  have hbase := PalPeg.PhysicalShift.running rest w sx p henc hmode hremaining hrepresentativeBound hrepresentativeTick
  obtain ⟨hout, hinv⟩ := PalPeg.PhysicalSearchSnapshots.shift_running (workStep rest)
    w x (successor w sx) p wm spare h age hInv henc hbase
  have hs : saved (successor w sx) (chainShiftOne wm).machine.control.boundary
      (chainShiftOne wm).machine.control.last (dec spare) =
      saved (successor w x) (chainShiftOne wm).machine.control.boundary
        (chainShiftOne wm).machine.control.last (dec spare) :=
    PalPeg.PhysicalSnapshotInvariant.saved_related (related_tick w
      (PalPeg.PhysicalSnapshotInvariant.related_saved x _ _ _ (Or.inl (by simp [hchain])))) _ _ _
  rw [hs] at hout
  exact ⟨hout, hinv⟩

theorem done_related (w : List (Fin 2)) {x y : State GalilVM} (hrelated : StateRelated x y) :
    (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w).remainingPos y.vm =
      (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w).remainingPos x.vm := by
  have hs := hrelated.2.1
  unfold Same at hs
  rw [hs]
  rfl

theorem successor_saved_exit (w : List (Fin 2)) (x : State GalilVM)
    (boundary last spare : Counter) (hmode : x.ctl.mode = .shift)
    (hdone : (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w).remainingPos x.vm = false) :
    successor w (saved x boundary last spare) = saved (successor w x) boundary last spare := by
  rw [successor, PalPeg.PhysicalShift.tickFun_exit w (saved x boundary last spare) hmode hdone,
    successor, PalPeg.PhysicalShift.tickFun_exit w x hmode hdone]
  rfl

noncomputable def step (rest : RestCommands) : PalPeg.PhysicalBootFeed.CoreStep :=
  PalPeg.PhysicalTickDispatch.branchStep (fun q ws => remainsTest q.polarity ws)
    (moving rest) (workStep rest)

theorem remaining_read (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (henc : Running w x p) :
    remainsTest p.1.polarity (fun j => PalPeg.Local.readWin blankM macroRadius (p.2 j)) =
      (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w).remainingPos x.vm := by
  apply PalPeg.PhysicalTickDispatch.read_from_running (fun q ws => remainsTest q.polarity ws)
    (fun x => (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w).remainingPos x.vm)
    w x p (PalPeg.PhysicalCacheInvariant.running_core henc)
  intro T hT
  simpa only [tapesOf, Equiv.apply_symm_apply] using
    remainsTest_eq hT.1.2 (by decide : 1 ≤ macroRadius) (le_refl margin) centreC placeC 0 1 0 w

theorem step_moving (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : CoreState) (henc : Running w x p) (hremaining : positive x.vm.remaining = true) :
    (step rest).apply blankM p none = (moving rest).apply blankM p none := by
  rw [step, PalPeg.PhysicalTickDispatch.branch_apply, remaining_read w x p henc]
  have htest : (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w).remainingPos x.vm = true := by
    change (positive x.vm.remaining || _) = true
    rw [hremaining, Bool.true_or]
  rw [htest, if_pos rfl]

theorem step_exit (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : CoreState) (henc : Running w x p)
    (hdone : (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w).remainingPos x.vm = false) :
    (step rest).apply blankM p none = (workStep rest).apply blankM p none := by
  rw [step, PalPeg.PhysicalTickDispatch.branch_apply, remaining_read w x p henc,
    hdone, if_neg Bool.false_ne_true]

/-- The new encoding also survives exhaustion, including a broken chain.
All six snapshot carriers stay in place on this branch. -/
theorem exit_enc (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : PalPeg.PhysicalShiftDispatch.RoutedCore)
    (henc : PalPeg.PhysicalSnapshotInvariant.Enc w x (PalPeg.PhysicalShiftDispatch.liftConfig p))
    (hmode : x.ctl.mode = .shift)
    (hdone : (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w).remainingPos x.vm = false) :
    PalPeg.PhysicalSnapshotInvariant.Enc w (successor w x)
      (PalPeg.PhysicalShiftDispatch.liftConfig
        ((PalPeg.LocalRoleRouting.hold (step rest)).apply blankM p none)) := by
  obtain ⟨⟨y, hrelated, hrepresentativeEnc⟩, hcopies⟩ := henc
  have hrepresentativeMode : y.ctl.mode = .shift := (congrArg _ hrelated.1).symm.trans hmode
  have hrepresentativeDone := (done_related w hrelated).trans hdone
  have hdecode := PalPeg.LocalRoleRouting.decode_hold (step rest) blankM p none
  rw [step_exit rest w y (PalPeg.LocalRoleRouting.decode p) hrepresentativeEnc hrepresentativeDone] at hdecode
  have hstep : ∀ z, Running w z (PalPeg.LocalRoleRouting.decode p) →
      z.ctl.mode = .shift →
      (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w).remainingPos z.vm = false →
      PalPeg.PhysicalSnapshotInvariant.OldEnc w (successor w z)
        (PalPeg.PhysicalShiftDispatch.liftConfig
          ((PalPeg.LocalRoleRouting.hold (step rest)).apply blankM p none)) := by
    intro z hsourceEnc hmode hdone
    change Running w (successor w z) (PalPeg.LocalRoleRouting.decode _)
    rw [hdecode]
    exact PalPeg.PhysicalShift.running_exit rest w z _ hsourceEnc hmode hdone
  refine ⟨⟨successor w y, related_tick w hrelated, hstep y hrepresentativeEnc hrepresentativeMode hrepresentativeDone⟩, ?_⟩
  intro wm hchain
  have hchainKept : (successor w x).vm.chain = x.vm.chain := by
    rw [successor, PalPeg.PhysicalShift.tickFun_exit w x hmode hdone]
    rfl
  rw [hchainKept] at hchain
  obtain ⟨h, age, spare, hInv, hsavedEnc⟩ := hcopies wm hchain
  refine ⟨h, age, spare, hInv, ?_⟩
  rw [← successor_saved_exit w x _ _ _ hmode hdone]
  exact hstep _ hsavedEnc hmode hdone

/-- info: 'PalPeg.PhysicalSnapshotShift.running' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms running

/-- info: 'PalPeg.PhysicalSnapshotShift.exit_enc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exit_enc

end PalPeg.PhysicalSnapshotShift
