import PalPeg.PhysicalShiftSource
import PalPeg.PhysicalBoundaryCount

/-! # Shift entry in the common finite physical dispatcher

The additional branch uses the same control, tapes, radius and encoding as the
count/shift machine. Selection is from source windows; it adds no machine tick.
-/
set_option autoImplicit false
namespace PalPeg.PhysicalShiftDispatch
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract PalPeg.PhysicalBootFeed
open PalPeg.PhysicalTickDispatch PalPeg.PhysicalScanCount
open PalPeg.PhysicalCacheInvariant (Running running_core)
open PalPeg.PhysicalCacheMachine (successor)
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilFinalAssembly2 (centreC placeC)
open PalPeg.GalilScaffoldInputHead (read left)
open PalPeg.GalilScaffoldChainVerifier (right canRight)
open PalPeg.GalilScaffoldCounter (positive)
open PalPeg.Local (LocalStep readWin)
open PalPeg.LocalRoleRouting (decode)
open PalPeg.CloseoutCheckW (PreTraceIMW CanonTrace)
open PalPeg.LocalReplayParked (Mirrored1)
open PalPeg.LocalBlankState (tapeCount)
open PalPeg.LocalSysConcrete (absSC)
open PalPeg.ShadowedLocalFinal (localGood postPhase heldAfter frozenAt)

abbrev RoutedControl := PalPeg.LocalRoleRouting.Control PalPeg.PhysicalContract.Control tapeCountM
abbrev RoutedState := PalPeg.PhysicalRoles.PhysicalState
abbrev RoutedStep := LocalStep (Fin 2) RoutedControl Γm tapeCountM macroRadius
abbrev RoutedCore := PalPeg.LocalRoleRouting.Config CoreControl Γm tapeCountM
abbrev Enc := PalPeg.PhysicalBoundaryCount.Enc

def liftConfig (p : RoutedCore) : RoutedState := ((p.1.1, .inr p.1.2), p.2)

/-- Lift a running step through the already existing boot tag. -/
noncomputable def liftStep
    (L : LocalStep (Fin 2) (PalPeg.LocalRoleRouting.Control CoreControl tapeCountM)
      Γm tapeCountM macroRadius) (fallback : RoutedStep) : RoutedStep where
  next := fun q input ws => match q.2 with
    | .inl _ => fallback.next q input ws
    | .inr c => let result := L.next (q.1, c) input ws
               ((result.1.1, .inr result.1.2), result.2)
  disp_le := by
    intro q input ws j
    cases h : q.2 with
    | inl tag => exact fallback.disp_le q input ws j
    | inr c => exact L.disp_le (q.1, c) input ws j

theorem lift_apply
    (L : LocalStep (Fin 2) (PalPeg.LocalRoleRouting.Control CoreControl tapeCountM)
      Γm tapeCountM macroRadius) (fallback : RoutedStep) (p : RoutedCore)
    (input : Option (Fin 2)) :
    (liftStep L fallback).apply blankM (liftConfig p) input =
      liftConfig (L.apply blankM p input) := rfl

noncomputable def select
    (test : RoutedControl → Option (Fin 2) →
      (Fin tapeCountM → PalPeg.Local.Window Γm macroRadius) → Bool)
    (yes no : RoutedStep) : RoutedStep where
  next := fun q input ws => if test q input ws then yes.next q input ws else no.next q input ws
  disp_le := by
    intro q input ws j
    split
    · exact yes.disp_le q input ws j
    · exact no.disp_le q input ws j

theorem select_apply (test : RoutedControl → Option (Fin 2) →
      (Fin tapeCountM → PalPeg.Local.Window Γm macroRadius) → Bool)
    (yes no : RoutedStep) (p : RoutedState) (input : Option (Fin 2)) :
    (select test yes no).apply blankM p input =
      if test p.1 input (fun j => readWin blankM macroRadius (p.2 j))
      then yes.apply blankM p input else no.apply blankM p input := by
  by_cases h : test p.1 input (fun j => readWin blankM macroRadius (p.2 j)) = true <;>
    simp only [LocalStep.apply, select, h, Bool.false_eq_true, if_true, if_false]

/-- All guard reads are logical, even after preceding boundary rotations. -/
def microWindows (roles : Equiv.Perm (Fin tapeCountM))
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm macroRadius) :=
  fun j => PalPeg.LocalStepFusion.windowAfter macroRadius microRadius (ws (roles j)) []

noncomputable def entryRead (q : CoreControl)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm microRadius) : Bool :=
  decide (q.ctl.mode = .scan) && decide (q.ctl.clock.val = 1) &&
    decide (q.chainTag = .watchers) && !starvedRead q ws &&
    !agreeTest q ws && scanShiftRead q ws

noncomputable def entryTest (q : RoutedControl) (input : Option (Fin 2))
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm macroRadius) : Bool :=
  match q.2, input with
  | .inr c, none => entryRead c (microWindows q.1 ws)
  | _, _ => false

noncomputable def consumeTest (q : RoutedControl) (_input : Option (Fin 2))
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm macroRadius) : Bool :=
  match q.2 with
  | .inr c => counterPositiveTest c (microWindows q.1 ws) 11
  | .inl _ => false

noncomputable def machine (rest : RestCommands) : RoutedStep :=
  let old := PalPeg.PhysicalBoundaryCount.machine rest
  select entryTest
    (select consumeTest (liftStep (PalPeg.PhysicalShiftTick.step true) old)
      (liftStep (PalPeg.PhysicalShiftTick.step false) old)) old

theorem apply_previous (rest : RestCommands) (p : RoutedState) (input : Option (Fin 2))
    (h : entryTest p.1 input (fun j => readWin blankM macroRadius (p.2 j)) = false) :
    (machine rest).apply blankM p input =
      (PalPeg.PhysicalBoundaryCount.machine rest).apply blankM p input := by
  rw [machine, select_apply, h, if_neg Bool.false_ne_true]

theorem microWindows_read (w : List (Fin 2)) (x : State GalilVM) (p : RoutedCore)
    (he : Running w x (decode p)) :
    microWindows p.1.1 (fun j => readWin blankM macroRadius (p.2 j)) =
      (fun j => readWin blankM microRadius ((decode p).2 j)) := by
  obtain ⟨T, hT, ht⟩ := running_core he
  funext j
  apply PalPeg.LocalStepFusion.windowAfter_readWin blankM _ [] (by decide)
  have hm := hT.1.2.margins (slotIndex.symm j)
  have hmT : macroRadius ≤ PalPeg.Local.pos (T j) := by
    simpa only [Equiv.apply_symm_apply, margin] using hm
  exact (ht j).1 ▸ hmT

/-- A source condition, with no assumption about the physical result. -/
def Entry (w : List (Fin 2)) (x : State GalilVM) : Prop :=
  x.ctl.mode = .scan ∧ x.ctl.clock = 1 ∧
    ∃ wm, x.vm.chain = .watch wm ∧
      read (left x.vm.left) ≠ read (right x.vm.right) ∧
      shiftGuardTest (compareFun (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) x.vm) = true

theorem agreeRead_running (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : Running w x p) (hcan : canRight x.vm.right) :
    agreeTest p.1 (fun j => readWin blankM microRadius (p.2 j)) =
      decide (read (left x.vm.left) = read (right x.vm.right)) := by
  apply read_from_running agreeTest _ w x p (running_core he)
  intro T hT
  simpa only [tapesOf, Equiv.apply_symm_apply] using
    agreeTest_of_encoded hT.1.2 (by decide : 1 ≤ microRadius) micro_le_margin hcan

theorem starvedRead_micro (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : Running w x p) :
    starvedRead p.1 (fun j => readWin blankM microRadius (p.2 j)) =
      PalPeg.FrameFunction.starvedTest x := by
  apply read_from_running starvedRead _ w x p (running_core he)
  intro T hT
  simpa only [tapesOf, Equiv.apply_symm_apply] using
    starvedRead_eq hT.1 (by decide : 1 ≤ microRadius) micro_le_margin

theorem entryRead_iff (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : Running w x p) (hs : PalPeg.FrameFunction.starvedTest x = false)
    {y : State GalilVM}
    (htick : Tick (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x y) :
    entryRead p.1 (fun j => readWin blankM microRadius (p.2 j)) = true ↔ Entry w x := by
  have hmode : p.1.ctl.mode = x.ctl.mode := by
    obtain ⟨T, hT, _⟩ := running_core he
    exact congrArg PalPeg.GalilScaffoldController.Control.mode hT.1.1.ctl
  have hclock : p.1.ctl.clock = x.ctl.clock := by
    obtain ⟨T, hT, _⟩ := running_core he
    exact congrArg PalPeg.GalilScaffoldController.Control.clock hT.1.1.ctl
  have htag : p.1.chainTag = chainTagOf x.vm.chain := by
    obtain ⟨T, hT, _⟩ := running_core he; exact hT.1.1.chainTag
  rw [entryRead, hmode, hclock, htag, starvedRead_micro w x p he, hs]
  simp only [Bool.not_false, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq,
    Bool.not_eq_true']
  constructor
  · rintro ⟨⟨⟨⟨hm, hc⟩, ht⟩, ha⟩, hg⟩
    have hwatch : ∃ wm, x.vm.chain = .watch wm := by
      cases h : x.vm.chain <;> simp_all [chainTagOf]
    obtain ⟨wm, hw⟩ := hwatch
    have hcan : canRight x.vm.right := by
      apply (canRightTest_iff _).mpr
      simpa [PalPeg.FrameFunction.starvedTest, PalPeg.FrameFunction.starvedOf, hm] using hs
    rw [agreeRead_running w x p he hcan, decide_eq_false_iff_not] at ha
    rw [PalPeg.PhysicalCompareGuard.scanShiftRead_running w x p he hm hs htick wm hw ha] at hg
    exact ⟨hm, hc, wm, hw, ha, hg⟩
  · rintro ⟨hm, hc, wm, hw, hne, hg⟩
    have hcan : canRight x.vm.right := by
      apply (canRightTest_iff _).mpr
      simpa [PalPeg.FrameFunction.starvedTest, PalPeg.FrameFunction.starvedOf, hm] using hs
    refine ⟨⟨⟨⟨hm, hc⟩, by rw [hw]; rfl⟩, ?_⟩, ?_⟩
    · rw [agreeRead_running w x p he hcan]
      exact decide_eq_false hne
    · rw [PalPeg.PhysicalCompareGuard.scanShiftRead_running w x p he hm hs htick wm hw hne]
      exact hg

theorem entryTest_iff (w : List (Fin 2)) (x : State GalilVM) (p : RoutedState)
    (he : Enc w x p) (hs : PalPeg.FrameFunction.starvedTest x = false)
    {y : State GalilVM}
    (htick : Tick (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x y) :
    entryTest p.1 none (fun j => readWin blankM macroRadius (p.2 j)) = true ↔ Entry w x := by
  rcases p with ⟨⟨roles, q⟩, T⟩
  cases q with
  | inl tag => rw [he.1, initial_starved] at hs; cases hs
  | inr q =>
    change entryRead q (microWindows roles (fun j => readWin blankM macroRadius (T j))) = true ↔ _
    rw [microWindows_read w x ((roles, q), T) he]
    exact entryRead_iff w x _ he hs htick

theorem consumeTest_running (w : List (Fin 2)) (x : State GalilVM) (p : RoutedCore)
    (he : Running w x (decode p)) (wm : PalPeg.GalilScaffoldChainWatch.State)
    (hw : x.vm.chain = .watch wm) :
    consumeTest (liftConfig p).1 none (fun j => readWin blankM macroRadius ((liftConfig p).2 j)) =
      positive wm.lag := by
  change counterPositiveTest p.1.2
    (microWindows p.1.1 (fun j => readWin blankM macroRadius (p.2 j))) 11 = _
  rw [microWindows_read w x p he]
  apply read_from_running (fun q ws => counterPositiveTest q ws 11) _ w x (decode p) (running_core he)
  intro T hT
  simpa only [tapesOf, Equiv.apply_symm_apply] using
    counterPositiveTest_eq hT.1.2 (by decide : 1 ≤ microRadius) micro_le_margin 11 wm.lag
      (by simp [counterOf, hw])

/-- Keep the two large compiled steps opaque while selecting one. -/
theorem select_lift_apply
    (test : RoutedControl → Option (Fin 2) →
      (Fin tapeCountM → PalPeg.Local.Window Γm macroRadius) → Bool)
    (steps : Bool → LocalStep (Fin 2) (PalPeg.LocalRoleRouting.Control CoreControl tapeCountM)
      Γm tapeCountM macroRadius) (fallback : RoutedStep) (p : RoutedCore)
    (input : Option (Fin 2)) (consume : Bool)
    (h : test (liftConfig p).1 input
      (fun j => readWin blankM macroRadius ((liftConfig p).2 j)) = consume) :
    (select test (liftStep (steps true) fallback) (liftStep (steps false) fallback)).apply
      blankM (liftConfig p) input = liftConfig ((steps consume).apply blankM p input) := by
  rw [select_apply, h]
  cases consume <;> simp only [Bool.false_eq_true, if_false, if_true, lift_apply]

/-- The finite choice executes the complete routed entry in one sweep. -/
theorem apply_entry (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : RoutedCore) (he : Running w x (decode p))
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hw : x.vm.chain = .watch wm)
    (hs : PalPeg.FrameFunction.starvedTest x = false) {y : State GalilVM}
    (htick : Tick (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x y)
    (hentry : Entry w x) :
    (machine rest).apply blankM (liftConfig p) none =
      liftConfig ((PalPeg.PhysicalShiftTick.step (positive wm.lag)).apply blankM p none) := by
  have hg := (entryTest_iff w x (liftConfig p) he hs htick).mpr hentry
  rw [machine, select_apply, hg, if_pos rfl]
  exact select_lift_apply consumeTest PalPeg.PhysicalShiftTick.step
    (PalPeg.PhysicalBoundaryCount.machine rest) p none (positive wm.lag)
    (consumeTest_running w x p he wm hw)

theorem comparison_of_entry (w : List (Fin 2)) (x : State GalilVM)
    (hs : PalPeg.FrameFunction.starvedTest x = false) {y : State GalilVM}
    (htick : Tick (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x y)
    (he : Entry w x) :
    ∃ t, compareFound (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0 x.vm t ∧
      ¬ (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0).matched t ∧ shiftGuardVM t := by
  obtain ⟨hm, hc, wm, hw, hne, hg⟩ := he
  have hcan : canRight x.vm.right := by
    apply (canRightTest_iff _).mpr
    simpa [PalPeg.FrameFunction.starvedTest, PalPeg.FrameFunction.starvedOf, hm] using hs
  have hcompare : ∃ t, compareFound (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0 x.vm t := by
    cases htick <;> simp_all
    all_goals first
      | exact ⟨_, ‹(galilFrameS _ _ _).compare _ _›⟩
      | skip
    case scan_wait c s t hm h hb => exact False.elim (h.2 hcan)
    case restart c s t hm hb =>
      change restartVM 0 s t at hb
      obtain ⟨wm', hbroken, _⟩ := hb
      rw [hw] at hbroken
      cases hbroken
  obtain ⟨t, ht⟩ := hcompare
  have hfun := compare_eq_compareFun ht
  refine ⟨t, ht, ?_, ?_⟩
  · change ¬ read t.left = read t.right
    rw [hfun, (compareFun_cursors _ x.vm).1, (compareFun_cursors _ x.vm).2]
    exact hne
  · rw [hfun]
    exact (shiftGuardTest_iff _).mpr hg

/-- Every source condition is supplied by the actual final-consumer run. -/
theorem forward_entry (rest : RestCommands) (w : List (Fin 2))
    (st : ℕ → State GalilVM) (Tc : ℕ → ℕ)
    (hpre : PreTraceIMW centreC placeC 0 1 0 w st Tc)
    (m : Mirrored1 (tapeCount 0)) (p : RoutedState)
    (hon : PalPeg.LocalShadowConcrete.ArrivedOnRun (localGood (spare := 0))
      (postPhase 0 1 0) w (heldAfter (Tc w.length) st) m)
    (hnf : ¬ frozenAt w m) (he : Enc w (absSC m) p)
    (hs : PalPeg.FrameFunction.starvedTest (absSC m) = false)
    (htick : Tick (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048
      (absSC m) (successor w (absSC m)))
    (hentry : Entry w (absSC m)) :
    Enc w (successor w (absSC m)) ((machine rest).apply blankM p none) := by
  obtain ⟨t, hcmp, hmis, hg⟩ := comparison_of_entry w (absSC m) hs htick hentry
  rcases p with ⟨⟨roles, q⟩, T⟩
  cases q with
  | inl tag => rw [he.1, initial_starved] at hs; cases hs
  | inr q =>
    obtain ⟨wm, hw, hout⟩ := PalPeg.PhysicalShiftSource.running_onRun w st Tc hpre m
      ((roles, q), T) hon hnf he hentry.1 hentry.2.1 hs t hcmp hmis hg
    change Enc w _ ((machine rest).apply blankM (liftConfig ((roles, q), T)) none)
    rw [apply_entry rest w (absSC m) ((roles, q), T) he wm hw hs htick hentry]
    exact hout

theorem entryTest_starved (w : List (Fin 2)) (x : State GalilVM) (p : RoutedState)
    (he : Enc w x p) (hs : PalPeg.FrameFunction.starvedTest x = true) :
    entryTest p.1 none (fun j => readWin blankM macroRadius (p.2 j)) = false := by
  rcases p with ⟨⟨roles, q⟩, T⟩
  cases q with
  | inl tag => rfl
  | inr q =>
    change entryRead q (microWindows roles _) = false
    rw [microWindows_read w x ((roles, q), T) he]
    have hr : starvedRead q (fun j => readWin blankM microRadius (T (roles j))) =
        PalPeg.FrameFunction.starvedTest x := starvedRead_micro w x (decode ((roles, q), T)) he
    change entryRead q (fun j => readWin blankM microRadius (T (roles j))) = false
    simp only [entryRead, hr, hs, Bool.not_true, Bool.and_false, Bool.false_and]

theorem forward_starved (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : RoutedState) (he : Enc w x p) (hs : PalPeg.FrameFunction.starvedTest x = true) :
    Enc w x ((machine rest).apply blankM p none) := by
  rw [apply_previous rest p none (entryTest_starved w x p he hs)]
  exact PalPeg.PhysicalBoundaryCount.forward_starved rest w x p he hs

theorem forward_feed (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : RoutedState) (a : Fin 2) (he : Enc w x p) :
    Enc w (PalPeg.GalilArriveChain.arriveState' a x) ((machine rest).apply blankM p (some a)) := by
  rw [apply_previous rest p (some a) (by cases h : p.1.2 <;> simp only [entryTest, h])]
  exact PalPeg.PhysicalBoundaryCount.forward_feed rest w x p a he

/-- Every abstract scan-shift arm satisfies the dispatcher source condition. -/
theorem entry_of_compare (w : List (Fin 2)) (x : State GalilVM) (t : GalilVM)
    (hm : x.ctl.mode = .scan) (hc : x.ctl.clock = 1)
    (hcmp : compareFound (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0 x.vm t)
    (hmis : ¬ (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0).matched t)
    (hg : shiftGuardVM t) : Entry w x := by
  obtain ⟨wm, hw, _, _⟩ := PalPeg.PhysicalShiftStart.source_of_guard hcmp hmis hg
  have hfun := compare_eq_compareFun hcmp
  refine ⟨hm, hc, wm, hw, ?_, ?_⟩
  · change ¬ read t.left = read t.right at hmis
    rw [hfun, (compareFun_cursors _ x.vm).1, (compareFun_cursors _ x.vm).2] at hmis
    exact hmis
  · rw [← hfun]
    exact (shiftGuardTest_iff _).mp hg

/-- The remaining-case contract excludes shift entry on the same concrete
machine that already supplies boot, feed, count and the entire shift mode. -/
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
        ¬ CountAtRest (absSC m) → ¬ PalPeg.PhysicalBoundaryCount.CountWatch (absSC m) →
        ¬ PalPeg.PhysicalBoundaryCount.CountBackReady (absSC m) → (absSC m).ctl.mode ≠ .shift →
        ¬ Entry w (absSC m) →
        Enc w (successor w (absSC m)) ((machine rest).apply blankM p none)) :
    TickCases (machine rest) blankM Enc := by
  constructor
  · intro w st Tc hpre hcanon m p hon hnotFrozen he hs
    exact forward_starved rest w (absSC m) p he hs
  · intro w st Tc hpre hcanon m p hon hnotFrozen he hs htick
    by_cases hentry : Entry w (absSC m)
    · exact forward_entry rest w st Tc hpre m p hon hnotFrozen he hs htick hentry
    have htest : entryTest p.1 none (fun j => readWin blankM macroRadius (p.2 j)) = false :=
      Bool.eq_false_iff.mpr (fun h => hentry ((entryTest_iff w (absSC m) p he hs htick).mp h))
    have hprevious := apply_previous rest p none htest
    by_cases hrest : CountAtRest (absSC m)
    · rw [hprevious]
      obtain ⟨hmode, hclock, hidle, hsearch⟩ := hrest
      exact PalPeg.PhysicalBoundaryCount.forward_atRest rest w (absSC m) p he hmode hs hclock hidle hsearch
    by_cases hwatch : PalPeg.PhysicalBoundaryCount.CountWatch (absSC m)
    · rw [hprevious]
      obtain ⟨hmode, hclock, wm, hchain⟩ := hwatch
      exact PalPeg.PhysicalBoundaryCount.forward_watch rest w (absSC m) p he hmode hs hclock htick wm hchain
    by_cases hback : PalPeg.PhysicalBoundaryCount.CountBackReady (absSC m)
    · rw [hprevious]
      have hperiod := PalPeg.PhysicalChainShape.period_onRun w st Tc hpre m hon.onRun hnotFrozen
      obtain ⟨hmode, hclock, first, last, xs, h, lag, credit, ver, hchain⟩ :=
        PalPeg.PhysicalBoundaryCount.entry_of_backReady hperiod.1 hback
      exact (PalPeg.PhysicalBoundaryCount.forward_entry rest w (absSC m) p he
        first last xs h lag credit ver hchain hmode hs hclock hperiod.2).1
    by_cases hshift : (absSC m).ctl.mode = .shift
    · rw [hprevious]
      exact PalPeg.PhysicalBoundaryCount.forward_shift rest w (absSC m) p he hshift hs
        (PalPeg.PhysicalShift.copyIdle_onRun w st Tc hpre m hon.onRun hnotFrozen hshift)
        (PalPeg.PhysicalShift.remainingBound_onRun w st Tc hpre m hon.onRun hnotFrozen) htick
    exact hother w st Tc hpre hcanon m p hon hnotFrozen he hs htick hrest hwatch hback hshift hentry

/-- info: 'PalPeg.PhysicalShiftDispatch.forward_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forward_entry

/-- info: 'PalPeg.PhysicalShiftDispatch.cases_of_remaining' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cases_of_remaining

end PalPeg.PhysicalShiftDispatch
