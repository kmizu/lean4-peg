import PalPeg.PhysicalSnapshotMachine
import PalPeg.PhysicalSnapshotShift

/-! # The snapshot dispatcher, including the whole shift mode

This extends the watch-count dispatcher in place: the alphabet, tape slots,
finite role register, radius and canonical encoding are unchanged.
-/
set_option autoImplicit false
namespace PalPeg.PhysicalSnapshotShiftDispatch
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract
open PalPeg.PhysicalRestartStorage
open PalPeg.PhysicalSearchSnapshots (saved)
open PalPeg.PhysicalSnapshotInvariant (Enc OldEnc)
open PalPeg.PhysicalScanCount (RestCommands)
open PalPeg.PhysicalShiftDispatch (RoutedState RoutedStep RoutedControl RoutedCore liftConfig liftStep select select_apply)
open PalPeg.PhysicalCacheInvariant (Running running_core)
open PalPeg.PhysicalCacheMachine (successor)
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilScaffoldCounter (positive)
open PalPeg.Local (readWin)
open PalPeg.LocalRoleRouting (decode)
open PalPeg.GalilFinalAssembly2 (centreC placeC)

noncomputable def shiftTest (q : RoutedControl) (input : Option (Fin 2))
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm macroRadius) : Bool :=
  match q.2, input with
  | .inr c, none => decide (c.ctl.mode = .shift) &&
      !PalPeg.PhysicalTickDispatch.starvedRead c (fun j => ws (q.1 j))
  | _, _ => false

noncomputable def machine (rest : RestCommands) : RoutedStep :=
  let old := PalPeg.PhysicalSnapshotMachine.machine rest
  select shiftTest
    (liftStep (PalPeg.LocalRoleRouting.hold (PalPeg.PhysicalSnapshotShift.step rest)) old) old

theorem apply_previous (rest : RestCommands) (p : RoutedState) (input : Option (Fin 2))
    (h : shiftTest p.1 input (fun j => readWin blankM macroRadius (p.2 j)) = false) :
    (machine rest).apply blankM p input = (PalPeg.PhysicalSnapshotMachine.machine rest).apply blankM p input := by
  rw [machine, select_apply, h, if_neg Bool.false_ne_true]

theorem shiftTest_running (w : List (Fin 2)) (x : State GalilVM) (p : RoutedCore)
    (henc : Running w x (decode p)) :
    shiftTest (liftConfig p).1 none (fun j => readWin blankM macroRadius (p.2 j)) =
      (decide (x.ctl.mode = .shift) && !PalPeg.FrameFunction.starvedTest x) := by
  have hrelated := PalPeg.PhysicalTickDispatch.starvedRead_running (p := decode p) (running_core henc)
  obtain ⟨T, hT, _⟩ := running_core henc
  have hmode := congrArg PalPeg.GalilScaffoldController.Control.mode hT.1.1.ctl
  change (decode p).1.ctl.mode = x.ctl.mode at hmode
  change (decide ((decode p).1.ctl.mode = .shift) &&
    !PalPeg.PhysicalTickDispatch.starvedRead (decode p).1
      (fun j => readWin blankM macroRadius ((decode p).2 j))) = _
  rw [hmode, hrelated]

theorem previous_nonshift (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : RoutedState) (henc : Enc w x p) (hmode : x.ctl.mode ≠ .shift) :
    (machine rest).apply blankM p none = (PalPeg.PhysicalSnapshotMachine.machine rest).apply blankM p none := by
  obtain ⟨y, hrelated, hrepresentativeEnc⟩ := henc.1
  apply apply_previous
  rcases p with ⟨⟨roles, q⟩, T⟩
  cases q with
  | inl tag => rfl
  | inr q =>
    have hread := shiftTest_running w y ((roles, q), T) hrepresentativeEnc
    have hrepresentativeMode : y.ctl.mode ≠ .shift := by rw [← hrelated.1]; exact hmode
    simpa only [hrepresentativeMode, decide_false, Bool.false_and, liftConfig] using hread

theorem forward_feed (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : RoutedState) (a : Fin 2) (henc : Enc w x p) :
    Enc w (PalPeg.GalilArriveChain.arriveState' a x) ((machine rest).apply blankM p (some a)) := by
  rw [apply_previous rest p (some a) (by cases hq : p.1.2 <;> simp [shiftTest, hq])]
  exact PalPeg.PhysicalSnapshotMachine.forward_feed rest w x p a henc

theorem forward_starved (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : RoutedState) (henc : Enc w x p) (hstarved : PalPeg.FrameFunction.starvedTest x = true) :
    Enc w x ((machine rest).apply blankM p none) := by
  obtain ⟨y, hrelated, hrepresentativeEnc⟩ := henc.1
  have hrepresentativeStarved := (related_starved hrelated).trans hstarved
  have htest : shiftTest p.1 none (fun j => readWin blankM macroRadius (p.2 j)) = false := by
    rcases p with ⟨⟨roles, q⟩, T⟩
    cases q with
    | inl tag => rfl
    | inr q =>
      have hread := shiftTest_running w y ((roles, q), T) hrepresentativeEnc
      simpa only [hrepresentativeStarved, Bool.not_true, Bool.and_false, liftConfig] using hread
  rw [apply_previous rest p none htest]
  exact PalPeg.PhysicalSnapshotMachine.forward_starved rest w x p henc hstarved

/-- Both moving and exhausted shift preserve the complete snapshot encoding.
The original legal tick and run-side copy/budget facts suffice. -/
theorem forward_shift (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : RoutedState) (henc : Enc w x p) (hmode : x.ctl.mode = .shift)
    (hstarved : PalPeg.FrameFunction.starvedTest x = false)
    (hcopy : CopyIdle x.vm) (hbound : PalPeg.PhysicalShift.RemainingBound x) {y : State GalilVM}
    (htick : Tick (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x y) :
    Enc w (successor w x) ((machine rest).apply blankM p none) := by
  obtain ⟨z, hrelated, hrepresentativeEnc⟩ := henc.1
  rcases p with ⟨⟨roles, q⟩, T⟩
  cases q with
  | inl tag =>
    have hrepresentativeStarved := (related_starved hrelated).trans hstarved
    rw [hrepresentativeEnc.1, PalPeg.PhysicalBootFeed.initial_starved] at hrepresentativeStarved
    cases hrepresentativeStarved
  | inr q =>
    let p : RoutedCore := ((roles, q), T)
    have hrepresentativeMode : z.ctl.mode = .shift := (congrArg _ hrelated.1).symm.trans hmode
    have htest := shiftTest_running w z p hrepresentativeEnc
    rw [hrepresentativeMode, related_starved hrelated, hstarved] at htest
    change shiftTest (liftConfig p).1 none
      (fun j => readWin blankM macroRadius ((liftConfig p).2 j)) = true at htest
    change Enc w (successor w x) ((machine rest).apply blankM (liftConfig p) none)
    rw [machine, select_apply, htest, if_pos rfl, PalPeg.PhysicalShiftDispatch.lift_apply]
    by_cases hrem : positive x.vm.remaining = true
    · obtain ⟨wm, hchain, _, _, _⟩ := PalPeg.PhysicalShift.ready_of_tick w htick hmode hrem
      obtain ⟨h, age, spare, hInv, hsavedEnc⟩ := henc.2 wm (Or.inl hchain)
      have hnext : (successor w x).vm.chain = .watch (chainShiftOne wm) := by
        rw [successor, PalPeg.PhysicalShift.tickFun_shift w x wm hchain hmode hrem]
        rfl
      obtain ⟨hout, hinv⟩ := PalPeg.PhysicalSnapshotShift.running rest w x (decode p)
        wm hchain spare h age hInv hsavedEnc hmode hrem hbound htick
      apply PalPeg.PhysicalSnapshotInvariant.of_watching w (successor w x) _
        (chainShiftOne wm) (Or.inl hnext) h age _ hinv
      change Running w _ (decode _)
      rw [PalPeg.LocalRoleRouting.decode_hold,
        PalPeg.PhysicalSnapshotShift.step_moving rest w
          (saved x wm.machine.control.boundary wm.machine.control.last spare) (decode p) hsavedEnc hrem]
      exact hout
    · have hcopyStopped : PalPeg.FrameFunction.copyRemainingTest x.vm.fpp = false := by
        rcases (copyIdle_iff _).mp hcopy with hcopyStopped | hcopyStopped <;>
          simp [PalPeg.FrameFunction.copyRemainingTest, hcopyStopped]
      have hdone : (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w).remainingPos x.vm = false := by
        change (positive x.vm.remaining || _) = false
        exact Bool.or_eq_false_iff.mpr ⟨Bool.eq_false_iff.mpr hrem, hcopyStopped⟩
      exact PalPeg.PhysicalSnapshotShift.exit_enc rest w x p henc hmode hdone

theorem enc_initial (w : List (Fin 2)) :
    Enc w initialState (PalPeg.PhysicalRoles.initialControl, fun _ => PalPeg.Program.STape.blankTape blankM) :=
  PalPeg.PhysicalSnapshotInvariant.enc_initial w

open PalPeg.CloseoutCheckW (PreTraceIMW CanonTrace)
open PalPeg.LocalSysConcrete (absSC)
open PalPeg.LocalReplayParked (Mirrored1)
open PalPeg.LocalBlankState (tapeCount)
open PalPeg.ShadowedLocalFinal (localGood postPhase frozenAt heldAfter)

/-- Shift now leaves the residual obligation on the same canonical encoding
and dispatcher as boot/feed/starved/count/watch entry. Its source budget and
copy idleness are supplied by the consumer's existing trace. -/
theorem cases_of_remaining (rest : RestCommands)
    (hother : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC 0 1 0 w st Tc → CanonTrace 0 w st Tc →
      ∀ (m : Mirrored1 (tapeCount 0)) (p : RoutedState),
        PalPeg.LocalShadowConcrete.ArrivedOnRun (localGood (spare := 0)) (postPhase 0 1 0) w
          (heldAfter (Tc w.length) st) m →
        ¬ frozenAt w m → Enc w (absSC m) p →
        PalPeg.FrameFunction.starvedTest (absSC m) = false →
        Tick (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 (absSC m)
          (successor w (absSC m)) →
        ¬ PalPeg.PhysicalScanCount.CountAtRest (absSC m) →
        ¬ PalPeg.PhysicalBoundaryCount.CountWatch (absSC m) →
        ¬ PalPeg.PhysicalBoundaryCount.CountBackReady (absSC m) →
        (absSC m).ctl.mode ≠ .shift →
        Enc w (successor w (absSC m)) ((machine rest).apply blankM p none)) :
    TickCases (machine rest) blankM Enc := by
  constructor
  · intro w st Tc hpre hcanon m p hon hnotFrozen he hs
    exact forward_starved rest w (absSC m) p he hs
  · intro w st Tc hpre hcanon m p hon hnotFrozen he hs htick
    by_cases hshift : (absSC m).ctl.mode = .shift
    · exact forward_shift rest w (absSC m) p he hshift hs
        (PalPeg.PhysicalShift.copyIdle_onRun w st Tc hpre m hon.onRun hnotFrozen hshift)
        (PalPeg.PhysicalShift.remainingBound_onRun w st Tc hpre m hon.onRun hnotFrozen) htick
    have hprevious := previous_nonshift rest w (absSC m) p he hshift
    by_cases hrest : PalPeg.PhysicalScanCount.CountAtRest (absSC m)
    · rw [hprevious]
      obtain ⟨hm, hc, hidle, hsearch⟩ := hrest
      exact PalPeg.PhysicalSnapshotMachine.forward_atRest rest w (absSC m) p he hm hs hc hidle hsearch
    by_cases hwatch : PalPeg.PhysicalBoundaryCount.CountWatch (absSC m)
    · rw [hprevious]
      obtain ⟨hm, hc, wm, hw⟩ := hwatch
      exact PalPeg.PhysicalSnapshotMachine.forward_watch rest w (absSC m) p he hm hs hc htick wm hw
    by_cases hback : PalPeg.PhysicalBoundaryCount.CountBackReady (absSC m)
    · rw [hprevious]
      have hperiod := PalPeg.PhysicalChainShape.period_onRun w st Tc hpre m hon.onRun hnotFrozen
      obtain ⟨hm, hc, first, last, xs, h, lag, credit, ver, hchain⟩ :=
        PalPeg.PhysicalBoundaryCount.entry_of_backReady hperiod.1 hback
      exact PalPeg.PhysicalSnapshotMachine.forward_entry rest w (absSC m) p he first last xs h lag credit ver hchain hm hs hc hperiod.2
    exact hother w st Tc hpre hcanon m p hon hnotFrozen he hs htick hrest hwatch hback hshift

/-- info: 'PalPeg.PhysicalSnapshotShiftDispatch.forward_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forward_shift

/-- info: 'PalPeg.PhysicalSnapshotShiftDispatch.cases_of_remaining' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cases_of_remaining

end PalPeg.PhysicalSnapshotShiftDispatch
