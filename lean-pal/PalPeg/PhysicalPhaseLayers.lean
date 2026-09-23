import PalPeg.PhysicalPhaseStill
import PalPeg.PhysicalCacheMachine
import PalPeg.PhysicalBoundaryCount
import PalPeg.PhysicalShiftDispatch
import PalPeg.PhysicalSnapshotMachine
import PalPeg.PhysicalDpCleanupDispatch

/-!
# Non-scan ticks pass through the dispatcher layers

Every branch test of the dispatcher layers reads `countRead` (or another scan-only test), so
outside scan each layer runs the layer below it. This file carries a non-scan tick from the
fused work step up the layers.
-/
set_option autoImplicit false
namespace PalPeg.PhysicalPhaseLayers
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract PalPeg.PhysicalScanCount
open PalPeg.Program (STape)
open PalPeg.Local (readWin pos)
open PalPeg.CloseoutCoreEnc12 PalPeg.LocalStepFusion
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilFinalAssembly2 (centreC placeC)

/-- Outside scan every branch test of the cache machine is off: it runs the work step. -/
theorem selected_nonscan (rest : RestCommands) (p : CoreState)
    (hmode : p.1.ctl.mode ≠ .scan) :
    (PalPeg.PhysicalCacheMachine.activeStep rest).apply blankM p none =
      (workStep rest).apply blankM p none := by
  have hcount : countRead p.1 (fun tape => readWin blankM macroRadius (p.2 tape)) = false := by
    simp [countRead, hmode]
  simp [PalPeg.PhysicalCacheMachine.activeStep, PalPeg.PhysicalWatchEntry.withWatchEntry,
    PalPeg.PhysicalTickDispatch.branch_apply, PalPeg.PhysicalWatchEntry.entryRead,
    PalPeg.PhysicalCacheMachine.prepareRead, counted_apply, hcount]
  rfl

/-- **A non-scan tick through the cache machine**, from its fused `Running` step. -/
theorem forward_nonscan (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : PalPeg.PhysicalContract.PhysicalState) (he : PalPeg.PhysicalCacheMachine.Enc w x p)
    (hmode : x.ctl.mode ≠ .scan) (hstarved : PalPeg.FrameFunction.starvedTest x = false)
    (hrun : ∀ q : CoreControl, p.1 = Sum.inr q → PalPeg.PhysicalCacheInvariant.Running w x (q, p.2) →
      PalPeg.PhysicalCacheInvariant.Running w (PalPeg.PhysicalCacheMachine.successor w x)
        ((workStep rest).apply blankM (q, p.2) none)) :
    PalPeg.PhysicalCacheMachine.Enc w (PalPeg.PhysicalCacheMachine.successor w x)
      ((PalPeg.PhysicalCacheMachine.machine rest).apply blankM p none) := by
  rcases p with ⟨q, T⟩
  cases q with
  | inl tag =>
    rw [he.1, PalPeg.PhysicalBootFeed.initial_starved] at hstarved
    cases hstarved
  | inr q =>
    have hr : PalPeg.PhysicalCacheInvariant.Running w x (q, T) := he
    rw [PalPeg.PhysicalCacheMachine.machine,
      PalPeg.PhysicalTickDispatch.apply_active (PalPeg.PhysicalCacheMachine.activeStep rest) w x
        (q, T) (PalPeg.PhysicalCacheInvariant.running_core hr) hstarved]
    have hqmode : q.ctl.mode ≠ .scan := by
      obtain ⟨T', hT', _⟩ := PalPeg.PhysicalCacheInvariant.running_core hr
      have hc : q.ctl.mode = x.ctl.mode :=
        congrArg PalPeg.GalilScaffoldController.Control.mode hT'.1.1.ctl
      rw [hc]; exact hmode
    rw [selected_nonscan rest (q, T) hqmode]
    have h := hrun q rfl hr
    generalize (workStep rest).apply blankM (q, T) none = r at h ⊢
    exact h

/-- The fused step of a non-scan tick keeps the running invariant (the per-mode lemmas). -/
def RunsNonscan (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM) : Prop :=
  ∀ p : CoreState, PalPeg.PhysicalCacheInvariant.Running w x p →
    PalPeg.PhysicalCacheInvariant.Running w (PalPeg.PhysicalCacheMachine.successor w x)
      ((workStep rest).apply blankM p none)

/-- **A non-scan tick through the role-routing layer**: no role change outside scan. -/
theorem forward_nonscan_routed (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : PalPeg.PhysicalRoles.PhysicalState) (he : PalPeg.PhysicalBoundaryCount.Enc w x p)
    (hmode : x.ctl.mode ≠ .scan) (hs : PalPeg.FrameFunction.starvedTest x = false)
    (hrun : RunsNonscan rest w x) :
    PalPeg.PhysicalBoundaryCount.Enc w (PalPeg.PhysicalCacheMachine.successor w x)
      ((PalPeg.PhysicalBoundaryCount.machine rest).apply blankM p none) := by
  change PalPeg.PhysicalCacheInvariant.Enc w _ (PalPeg.LocalRoleRouting.decode _)
  rw [PalPeg.PhysicalBoundaryCount.decode_machine]
  rcases p with ⟨⟨roles, q⟩, T⟩
  cases q with
  | inl tag => rw [he.1, PalPeg.PhysicalBootFeed.initial_starved] at hs; cases hs
  | inr q =>
    let U := fun j => T (roles j)
    have hr : PalPeg.PhysicalCacheInvariant.Running w x (q, U) := he
    have hcore := PalPeg.PhysicalCacheInvariant.running_core hr
    have hm : q.ctl.mode ≠ .scan := by
      obtain ⟨ideal, hi, _⟩ := hcore
      have hc : q.ctl.mode = x.ctl.mode :=
        congrArg PalPeg.GalilScaffoldController.Control.mode hi.1.1.ctl
      rw [hc]; exact hmode
    have hchange : PalPeg.PhysicalBoundaryCount.boundaryRead q
        (fun j => readWin blankM macroRadius (U j)) = false := by
      simp only [PalPeg.PhysicalBoundaryCount.boundaryRead, PalPeg.PhysicalCacheMachine.prepareRead,
        countRead, hm, decide_false, Bool.false_and, Bool.and_false]
    change PalPeg.PhysicalCacheInvariant.Enc w _
      (PalPeg.PhysicalBoundaryCount.completedOuter
        (PalPeg.PhysicalBoundaryCount.boundaryRead q (fun j => readWin blankM macroRadius (U j)))
        ((PalPeg.PhysicalCacheMachine.machine rest).apply blankM (.inr q, U) none))
    rw [hchange, PalPeg.PhysicalBoundaryCount.completedOuter, if_neg Bool.false_ne_true]
    exact forward_nonscan rest w x (.inr q, U) hr hmode hs (fun q' hq hr' => by
      cases hq; exact hrun _ hr')

/-- **A non-scan tick through the shift-entry layer**: the entry test reads scan. -/
theorem forward_nonscan_shiftDispatch (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : PalPeg.PhysicalShiftDispatch.RoutedState) (he : PalPeg.PhysicalShiftDispatch.Enc w x p)
    (hmode : x.ctl.mode ≠ .scan) (hs : PalPeg.FrameFunction.starvedTest x = false)
    (hrun : RunsNonscan rest w x) :
    PalPeg.PhysicalShiftDispatch.Enc w (PalPeg.PhysicalCacheMachine.successor w x)
      ((PalPeg.PhysicalShiftDispatch.machine rest).apply blankM p none) := by
  have hentry : PalPeg.PhysicalShiftDispatch.entryTest p.1 none
      (fun j => readWin blankM macroRadius (p.2 j)) = false := by
    rcases p with ⟨⟨roles, q⟩, T⟩
    cases q with
    | inl tag => rfl
    | inr c =>
      have hr : PalPeg.PhysicalCacheInvariant.Running w x (c, fun j => T (roles j)) := he
      obtain ⟨ideal, hi, _⟩ := PalPeg.PhysicalCacheInvariant.running_core hr
      have hc : c.ctl.mode = x.ctl.mode :=
        congrArg PalPeg.GalilScaffoldController.Control.mode hi.1.1.ctl
      simp [PalPeg.PhysicalShiftDispatch.entryTest, PalPeg.PhysicalShiftDispatch.entryRead, hc, hmode]
  rw [PalPeg.PhysicalShiftDispatch.apply_previous rest p none hentry]
  exact forward_nonscan_routed rest w x p he hmode hs hrun

/-- **A non-scan tick through the snapshot layer.** The representative steps with the source,
and with an idle chain there are no saved copies to carry. -/
theorem forward_nonscan_snapshot (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : PalPeg.PhysicalShiftDispatch.RoutedState) (he : PalPeg.PhysicalSnapshotInvariant.Enc w x p)
    (hmode : x.ctl.mode ≠ .scan) (hs : PalPeg.FrameFunction.starvedTest x = false)
    (hidle : (PalPeg.PhysicalCacheMachine.successor w x).vm.chain = .idle)
    (hrun : ∀ y, PalPeg.PhysicalRestartStorage.StateRelated x y → RunsNonscan rest w y) :
    PalPeg.PhysicalSnapshotInvariant.Enc w (PalPeg.PhysicalCacheMachine.successor w x)
      ((PalPeg.PhysicalSnapshotMachine.machine rest).apply blankM p none) := by
  obtain ⟨⟨y, hr, hold⟩, _⟩ := he
  have hctl : y.ctl = x.ctl := hr.1.symm
  have hmodey : y.ctl.mode ≠ .scan := by rw [hctl]; exact hmode
  have hsy : PalPeg.FrameFunction.starvedTest y = false := by
    rw [PalPeg.PhysicalRestartStorage.related_starved hr]; exact hs
  have htests : PalPeg.PhysicalSnapshotMachine.entryTest p.1 none
        (fun j => readWin blankM macroRadius (p.2 j)) = false ∧
      PalPeg.PhysicalSnapshotMachine.matchTest p.1 none
        (fun j => readWin blankM macroRadius (p.2 j)) = false := by
    rcases p with ⟨⟨roles, q⟩, T⟩
    cases q with
    | inl tag => exact ⟨rfl, rfl⟩
    | inr c =>
      have hrun' : PalPeg.PhysicalCacheInvariant.Running w y (c, fun j => T (roles j)) := hold
      obtain ⟨ideal, hi, _⟩ := PalPeg.PhysicalCacheInvariant.running_core hrun'
      have hc : c.ctl.mode = y.ctl.mode :=
        congrArg PalPeg.GalilScaffoldController.Control.mode hi.1.1.ctl
      have hcount : countRead c (fun j => readWin blankM macroRadius (T (roles j))) = false := by
        simp [countRead, hc, hmodey]
      constructor
      · simp [PalPeg.PhysicalSnapshotMachine.entryTest, PalPeg.PhysicalWatchEntry.entryRead, hcount]
      · simp [PalPeg.PhysicalSnapshotMachine.matchTest, PalPeg.PhysicalCacheMachine.prepareRead,
          hcount]
  rw [PalPeg.PhysicalSnapshotMachine.apply_previous rest p none htests.1 htests.2]
  refine ⟨⟨PalPeg.PhysicalCacheMachine.successor w y,
    PalPeg.PhysicalRestartStorage.related_tick w hr,
    forward_nonscan_shiftDispatch rest w y p hold hmodey hsy (hrun y hr)⟩, ?_⟩
  intro wm hwm
  rw [hidle] at hwm
  rcases hwm with h | h <;> cases h

/-- **A non-scan, non-shift tick through the whole common machine.** Each dispatcher above the
snapshot layer tests scan (or shift), so it runs the layer below; the cleanup layer carries its
finite state. The target must not borrow the radius carrier (it is a plain snapshot state). -/
theorem forward_nonscan_machine (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : PalPeg.PhysicalDpCleanup.Config) (he : PalPeg.PhysicalDpCleanup.Enc w x p)
    (hmode : x.ctl.mode ≠ .scan) (hshift : x.ctl.mode ≠ .shift)
    (hs : PalPeg.FrameFunction.starvedTest x = false)
    (hidle : (PalPeg.PhysicalCacheMachine.successor w x).vm.chain = .idle)
    (hloan : ¬ PalPeg.PhysicalLoanInvariant.NeedsLoan (PalPeg.PhysicalCacheMachine.successor w x))
    (hrun : ∀ y, PalPeg.PhysicalRestartStorage.StateRelated x y → RunsNonscan rest w y) :
    PalPeg.PhysicalDpCleanup.Enc w (PalPeg.PhysicalCacheMachine.successor w x)
      ((PalPeg.PhysicalDpCleanup.machine rest).apply blankM p none) := by
  apply PalPeg.PhysicalDpCleanupDispatch.forward_of_previous rest w x _ p none he
  have hx : ¬ PalPeg.PhysicalLoanInvariant.NeedsLoan x := fun h => hmode h.1
  apply PalPeg.PhysicalLoanDispatch.active_of_previous rest w x _ he.1 hs hx hloan
  intro hsnap
  rw [PalPeg.PhysicalSnapshotEntryDispatch.previous_when rest w x _ hsnap (.inl hmode),
    PalPeg.PhysicalSnapshotShiftDispatch.previous_nonshift rest w x _ hsnap hshift]
  exact forward_nonscan_snapshot rest w x _ hsnap hmode hs hidle hrun

end PalPeg.PhysicalPhaseLayers
