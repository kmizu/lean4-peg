import PalPeg.PhysicalSnapshotCount
import PalPeg.PhysicalSnapshotInvariant

/-! # The common dispatcher carrying the restart snapshots

Boot, feed and ordinary waiting reuse the existing machine. Successful watch
count selects the joint snapshot row, and watch entry selects the six-carrier
reset row. The strengthened canonical encoding is shared by every proof here.
-/
set_option autoImplicit false
namespace PalPeg.PhysicalSnapshotMachine
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract
open PalPeg.PhysicalRestartStorage
open PalPeg.PhysicalSearchSnapshots (saved)
open PalPeg.PhysicalSnapshotInvariant (Enc OldEnc)
open PalPeg.PhysicalScanCount (RestCommands countState)
open PalPeg.PhysicalShiftDispatch (RoutedState RoutedStep RoutedControl RoutedCore liftConfig liftStep select select_apply)
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.Local (readWin)
open PalPeg.LocalRoleRouting (decode)
open PalPeg.GalilFinalAssembly2 (centreC placeC)
open PalPeg.PhysicalCacheMachine (successor)

noncomputable def matchTest (q : RoutedControl) (input : Option (Fin 2))
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm macroRadius) : Bool :=
  match q.2, input with
  | .inr c, none => !PalPeg.PhysicalTickDispatch.starvedRead c (fun j => ws (q.1 j)) &&
      PalPeg.PhysicalCacheMachine.prepareRead c (fun j => ws (q.1 j))
  | _, _ => false

noncomputable def entryTest (q : RoutedControl) (input : Option (Fin 2))
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm macroRadius) : Bool :=
  match q.2, input with
  | .inr c, none => !PalPeg.PhysicalTickDispatch.starvedRead c (fun j => ws (q.1 j)) &&
      PalPeg.PhysicalWatchEntry.entryRead c (fun j => ws (q.1 j))
  | _, _ => false

noncomputable def machine (rest : RestCommands) : RoutedStep :=
  let old := PalPeg.PhysicalShiftDispatch.machine rest
  select entryTest (liftStep (PalPeg.LocalRoleRouting.hold PalPeg.PhysicalSearchRecycle.entryStep) old)
    (select matchTest (liftStep (PalPeg.PhysicalSnapshotCount.step rest) old) old)

theorem apply_previous (rest : RestCommands) (p : RoutedState) (input : Option (Fin 2))
    (he : entryTest p.1 input (fun j => readWin blankM macroRadius (p.2 j)) = false)
    (hm : matchTest p.1 input (fun j => readWin blankM macroRadius (p.2 j)) = false) :
    (machine rest).apply blankM p input = (PalPeg.PhysicalShiftDispatch.machine rest).apply blankM p input := by
  rw [machine, select_apply, he, if_neg Bool.false_ne_true, select_apply, hm, if_neg Bool.false_ne_true]

theorem enc_initial (w : List (Fin 2)) :
    Enc w initialState (PalPeg.PhysicalRoles.initialControl, fun _ => PalPeg.Program.STape.blankTape blankM) :=
  PalPeg.PhysicalSnapshotInvariant.enc_initial w

theorem forward_feed (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : RoutedState) (a : Fin 2) (he : Enc w x p) :
    Enc w (PalPeg.GalilArriveChain.arriveState' a x) ((machine rest).apply blankM p (some a)) := by
  rw [apply_previous rest p (some a) (by cases hq : p.1.2 <;> simp [entryTest, hq]) (by cases hq : p.1.2 <;> simp [matchTest, hq])]
  exact PalPeg.PhysicalSnapshotInvariant.feed w x p _ a he
    (fun y hy => PalPeg.PhysicalShiftDispatch.forward_feed rest w y p a hy)

theorem tests_starved (w : List (Fin 2)) (x : State GalilVM) (p : RoutedState)
    (he : OldEnc w x p) (hs : PalPeg.FrameFunction.starvedTest x = true) :
    entryTest p.1 none (fun j => readWin blankM macroRadius (p.2 j)) = false ∧
      matchTest p.1 none (fun j => readWin blankM macroRadius (p.2 j)) = false := by
  rcases p with ⟨⟨roles, q⟩, T⟩
  cases q with
  | inl tag => exact ⟨rfl, rfl⟩
  | inr q =>
    have hr := PalPeg.PhysicalTickDispatch.starvedRead_running
      (PalPeg.PhysicalCacheInvariant.running_core (p := (q, fun j => T (roles j))) he)
    simp only [entryTest, matchTest]
    rw [hr, hs]
    exact ⟨rfl, rfl⟩

theorem forward_starved (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : RoutedState) (he : Enc w x p) (hs : PalPeg.FrameFunction.starvedTest x = true) :
    Enc w x ((machine rest).apply blankM p none) := by
  obtain ⟨y, hr, hy⟩ := he.1
  have hsy : PalPeg.FrameFunction.starvedTest y = true := (related_starved hr).trans hs
  obtain ⟨hentry, hmatch⟩ := tests_starved w y p hy hsy
  rw [apply_previous rest p none hentry hmatch]
  apply PalPeg.PhysicalSnapshotInvariant.preserve w x p _ he
  intro z hz henc
  exact PalPeg.PhysicalShiftDispatch.forward_starved rest w z p henc ((related_starved hz).trans hs)

/-- A watch source can never select the back-to-watch initialization row. -/
theorem entryTest_watch (w : List (Fin 2)) (x : State GalilVM) (p : RoutedCore)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hw : x.vm.chain = .watch wm)
    (he : PalPeg.PhysicalCacheInvariant.Running w x (decode p)) :
    entryTest (liftConfig p).1 none (fun j => readWin blankM macroRadius (p.2 j)) = false := by
  have htag : p.1.2.chainTag = .watchers := by
    obtain ⟨T, hT, _⟩ := PalPeg.PhysicalCacheInvariant.running_core he
    change (decode p).1.chainTag = _
    rw [hT.1.1.chainTag, hw]; rfl
  simp [entryTest, liftConfig, PalPeg.PhysicalWatchEntry.entryRead, htag]

theorem matchTest_match (w : List (Fin 2)) (x : State GalilVM) (p : RoutedCore)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hw : x.vm.chain = .watch wm)
    (he : PalPeg.PhysicalCacheInvariant.Running w x (decode p))
    (hm : x.ctl.mode = .scan) (hs : PalPeg.FrameFunction.starvedTest x = false) (hc : 1 < x.ctl.clock)
    (a : Fin 3) (ht : PalPeg.GalilScaffoldChainConsume.symbol wm.machine.control.period.focus = some a)
    (ha : PalPeg.GalilScaffoldInputHead.read (PalPeg.GalilScaffoldChainVerifier.right wm.machine.verifier) = some a)
    (hl : PalPeg.GalilScaffoldCounter.positive wm.lag = true)
    (hcan : PalPeg.GalilScaffoldChainVerifier.canRight wm.machine.verifier) :
    matchTest (liftConfig p).1 none (fun j => readWin blankM macroRadius (p.2 j)) = true := by
  have hp := PalPeg.PhysicalCacheMachine.prepareRead_match w x (decode p)
    (PalPeg.PhysicalCacheInvariant.running_core he) hm hs hc wm hw a ht ha hl hcan
  have hr := PalPeg.PhysicalTickDispatch.starvedRead_running (PalPeg.PhysicalCacheInvariant.running_core he)
  change (!PalPeg.PhysicalTickDispatch.starvedRead (decode p).1
    (fun j => readWin blankM macroRadius ((decode p).2 j)) &&
    PalPeg.PhysicalCacheMachine.prepareRead (decode p).1
      (fun j => readWin blankM macroRadius ((decode p).2 j))) = true
  rw [hr, hs, hp]; rfl

/-- Successful watch count now discharges the whole canonical encoding,
including both extra last copies, on this common dispatcher. -/
theorem forward_match (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : RoutedState) (he : Enc w x p)
    (hm : x.ctl.mode = .scan) (hs : PalPeg.FrameFunction.starvedTest x = false) (hc : 1 < x.ctl.clock)
    {y : State GalilVM}
    (htick : Tick (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x y)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hw : x.vm.chain = .watch wm) (a : Fin 3)
    (ht : PalPeg.GalilScaffoldChainConsume.symbol wm.machine.control.period.focus = some a)
    (ha : PalPeg.GalilScaffoldInputHead.read (PalPeg.GalilScaffoldChainVerifier.right wm.machine.verifier) = some a)
    (hl : PalPeg.GalilScaffoldCounter.positive wm.lag = true) :
    Enc w (successor w x) ((machine rest).apply blankM p none) := by
  obtain ⟨h, age, spare, hi, hh⟩ := he.2 wm (Or.inl hw)
  rcases p with ⟨⟨roles, q⟩, T⟩
  cases q with
  | inl tag =>
    have hstarved : PalPeg.FrameFunction.starvedTest (saved x wm.machine.control.boundary wm.machine.control.last spare) = false := hs
    rw [hh.1, PalPeg.PhysicalBootFeed.initial_starved] at hstarved
    cases hstarved
  | inr q =>
    let p : RoutedCore := ((roles, q), T)
    let sx := saved x wm.machine.control.boundary wm.machine.control.last spare
    have hcan := PalPeg.PhysicalCountReady.verifier_canRight_of_countTick w htick hm hc wm hw hl
    have hentry := entryTest_watch w sx p wm hw hh
    have hmatch := matchTest_match w sx p wm hw hh hm hs hc a ht ha hl hcan
    change entryTest (liftConfig p).1 none
      (fun j => readWin blankM macroRadius ((liftConfig p).2 j)) = false at hentry
    change matchTest (liftConfig p).1 none
      (fun j => readWin blankM macroRadius ((liftConfig p).2 j)) = true at hmatch
    change Enc w (successor w x) ((machine rest).apply blankM (liftConfig p) none)
    rw [machine, select_apply, hentry, if_neg Bool.false_ne_true,
      select_apply, hmatch, if_pos rfl, PalPeg.PhysicalShiftDispatch.lift_apply]
    obtain ⟨hout, hinv⟩ := PalPeg.PhysicalSnapshotCount.forward_match rest w x p wm hw
      spare h age hi hh hm hs hc htick a ht ha hl
    apply PalPeg.PhysicalSnapshotInvariant.of_watching w (successor w x) _ (PalPeg.GalilScaffoldChainWatch.caught wm)
      (Or.inl (by rw [PalPeg.PhysicalCacheMachine.match_successor w x hm hs hc wm hw a ht ha hl]; rfl))
      h (PalPeg.ChainBoundaryCache.nextAge wm.machine.control age) _ hinv
    exact hout

/-- Count background never reads the dormant search values and preserves
those values in its representative, including the watch-to-broken transition. -/
theorem successor_saved_count (w : List (Fin 2)) (x : State GalilVM)
    (boundary last spare : PalPeg.GalilScaffoldCounter.Counter)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hw : x.vm.chain = .watch wm)
    (hm : x.ctl.mode = .scan) (hs : PalPeg.FrameFunction.starvedTest x = false) (hc : 1 < x.ctl.clock) :
    successor w (saved x boundary last spare) = saved (successor w x) boundary last spare := by
  have hr : restartGuardTest x.vm = false := by simp [restartGuardTest, hw]
  have hrs : restartGuardTest (saved x boundary last spare).vm = false := hr
  have hss : PalPeg.FrameFunction.starvedTest (saved x boundary last spare) = false := hs
  rw [successor, PalPeg.PhysicalGuardProbe.tickFun_nonstarved_count _ _ 0 1 0 w _ 2048 (saved x boundary last spare) hm hss hrs hc,
    successor, PalPeg.PhysicalGuardProbe.tickFun_nonstarved_count _ _ 0 1 0 w _ 2048 _ hm hs hr hc]
  change (⟨_, backgroundFun _ (replace x.vm boundary last spare spare)⟩ : State GalilVM) = _
  rw [background_replace _ x.vm boundary last spare spare (by simp [hw])]
  rfl

/-- The comparison-only shift entry cannot intercept any count tick. -/
theorem old_count_previous (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : RoutedState) (he : OldEnc w x p) (hc : 1 < x.ctl.clock) :
    (PalPeg.PhysicalShiftDispatch.machine rest).apply blankM p none =
      (PalPeg.PhysicalBoundaryCount.machine rest).apply blankM p none := by
  apply PalPeg.PhysicalShiftDispatch.apply_previous
  rcases p with ⟨⟨roles, q⟩, T⟩
  cases q with
  | inl tag => rfl
  | inr q =>
    have hclock : q.ctl.clock.val ≠ 1 := by
      obtain ⟨U, hU, _⟩ := PalPeg.PhysicalCacheInvariant.running_core
        (p := (q, fun j => T (roles j))) he
      have heq := congrArg PalPeg.GalilScaffoldController.Control.clock hU.1.1.ctl
      change q.ctl.clock.val = x.ctl.clock at heq
      omega
    simp [PalPeg.PhysicalShiftDispatch.entryTest, PalPeg.PhysicalShiftDispatch.entryRead, hclock]

/-- Failed/no consumption keeps both the old roles and the six new carriers. -/
theorem apply_count_previous (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : RoutedCore) (wm : PalPeg.GalilScaffoldChainWatch.State) (hw : x.vm.chain = .watch wm)
    (he : PalPeg.PhysicalCacheInvariant.Running w x (decode p)) (hc : 1 < x.ctl.clock)
    (hp : PalPeg.PhysicalCacheMachine.prepareRead (decode p).1
      (fun j => readWin blankM macroRadius ((decode p).2 j)) = false) :
    (machine rest).apply blankM (liftConfig p) none =
      (PalPeg.PhysicalBoundaryCount.machine rest).apply blankM (liftConfig p) none := by
  have hentry := entryTest_watch w x p wm hw he
  have hmatch : matchTest (liftConfig p).1 none
      (fun j => readWin blankM macroRadius ((liftConfig p).2 j)) = false := by
    change (_ && PalPeg.PhysicalCacheMachine.prepareRead (decode p).1
      (fun j => readWin blankM macroRadius ((decode p).2 j))) = false
    rw [hp, Bool.and_false]
  rw [apply_previous rest _ none hentry hmatch]
  exact old_count_previous rest w x (liftConfig p) he hc

theorem forward_mismatch (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : RoutedState) (he : Enc w x p)
    (hm : x.ctl.mode = .scan) (hs : PalPeg.FrameFunction.starvedTest x = false) (hc : 1 < x.ctl.clock)
    {y : State GalilVM}
    (htick : Tick (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x y)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hw : x.vm.chain = .watch wm) (a : Fin 3)
    (ht : PalPeg.GalilScaffoldChainConsume.symbol wm.machine.control.period.focus = some a)
    (ha : PalPeg.GalilScaffoldInputHead.read (PalPeg.GalilScaffoldChainVerifier.right wm.machine.verifier) ≠ some a)
    (hl : PalPeg.GalilScaffoldCounter.positive wm.lag = true) :
    Enc w (successor w x) ((machine rest).apply blankM p none) := by
  obtain ⟨h, age, spare, hi, hh⟩ := he.2 wm (Or.inl hw)
  rcases p with ⟨⟨roles, q⟩, T⟩
  cases q with
  | inl tag =>
    have hstarved : PalPeg.FrameFunction.starvedTest (saved x wm.machine.control.boundary wm.machine.control.last spare) = false := hs
    rw [hh.1, PalPeg.PhysicalBootFeed.initial_starved] at hstarved; cases hstarved
  | inr q =>
    let p : RoutedCore := ((roles, q), T)
    let sx := saved x wm.machine.control.boundary wm.machine.control.last spare
    have hcan := PalPeg.PhysicalCountReady.verifier_canRight_of_countTick w htick hm hc wm hw hl
    have hp := PalPeg.PhysicalCountMismatch.prepareRead_mismatch w sx (decode p) hh wm hw a ht ha hcan
    have heq := apply_count_previous rest w sx p wm hw hh hc hp
    change Enc w (successor w x) ((machine rest).apply blankM (liftConfig p) none)
    rw [heq]
    have hout := PalPeg.PhysicalBoundaryCount.forward_mismatch rest w sx (liftConfig p) hh hm hs hc
      wm hw a ht ha hl hcan
    rw [show sx = saved x wm.machine.control.boundary wm.machine.control.last spare from rfl,
      successor_saved_count w x _ _ _ wm hw hm hs hc] at hout
    apply PalPeg.PhysicalSnapshotInvariant.of_watching w (successor w x) _
      (PalPeg.PhysicalCountMismatch.brokenWatch wm)
      (Or.inr (by rw [PalPeg.PhysicalCountMismatch.mismatch_successor w x hm hs hc wm hw a ht ha hl]; rfl))
      h age spare hi
    exact hout

theorem quiet_successor (w : List (Fin 2)) (x : State GalilVM)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hw : x.vm.chain = .watch wm)
    (hm : x.ctl.mode = .scan) (hs : PalPeg.FrameFunction.starvedTest x = false) (hc : 1 < x.ctl.clock)
    (hl : PalPeg.GalilScaffoldCounter.positive wm.lag = false) : successor w x = countState x := by
  have hr : restartGuardTest x.vm = false := by simp [restartGuardTest, hw]
  rw [successor, PalPeg.PhysicalGuardProbe.tickFun_nonstarved_count _ _ 0 1 0 w _ 2048 _ hm hs hr hc]
  change (⟨_, backgroundFun _ x.vm⟩ : State GalilVM) = _
  rw [backgroundFun_of_active _ x.vm (by simp [hw]), hw]
  simp only [chainStepFun, hl, Bool.false_eq_true, if_false]
  rw [← hw]
  rfl

theorem forward_quiet (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : RoutedState) (he : Enc w x p)
    (hm : x.ctl.mode = .scan) (hs : PalPeg.FrameFunction.starvedTest x = false) (hc : 1 < x.ctl.clock)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hw : x.vm.chain = .watch wm)
    (hl : PalPeg.GalilScaffoldCounter.positive wm.lag = false) :
    Enc w (successor w x) ((machine rest).apply blankM p none) := by
  obtain ⟨h, age, spare, hi, hh⟩ := he.2 wm (Or.inl hw)
  rcases p with ⟨⟨roles, q⟩, T⟩
  cases q with
  | inl tag =>
    have hstarved : PalPeg.FrameFunction.starvedTest (saved x wm.machine.control.boundary wm.machine.control.last spare) = false := hs
    rw [hh.1, PalPeg.PhysicalBootFeed.initial_starved] at hstarved; cases hstarved
  | inr q =>
    let p : RoutedCore := ((roles, q), T)
    let sx := saved x wm.machine.control.boundary wm.machine.control.last spare
    have hp := PalPeg.PhysicalWatchIdle.prepareRead_quiet w sx (decode p) hh wm hw hl
    change Enc w (successor w x) ((machine rest).apply blankM (liftConfig p) none)
    rw [apply_count_previous rest w sx p wm hw hh hc hp]
    have hout := PalPeg.PhysicalBoundaryCount.forward_quiet rest w sx (liftConfig p) hh hm hs hc wm hw hl
    rw [show sx = saved x wm.machine.control.boundary wm.machine.control.last spare from rfl,
      successor_saved_count w x _ _ _ wm hw hm hs hc] at hout
    apply PalPeg.PhysicalSnapshotInvariant.of_watching w (successor w x) _ wm
      (Or.inl (by rw [quiet_successor w x wm hw hm hs hc hl]; exact hw)) h age spare hi
    exact hout

/-- All watch count cases use the same stronger encoding and dispatcher.
No token, direction, lag-sign, verdict, spare or target-copy premise remains. -/
theorem forward_watch (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : RoutedState) (he : Enc w x p)
    (hm : x.ctl.mode = .scan) (hs : PalPeg.FrameFunction.starvedTest x = false) (hc : 1 < x.ctl.clock)
    {y : State GalilVM}
    (htick : Tick (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x y)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hw : x.vm.chain = .watch wm) :
    Enc w (successor w x) ((machine rest).apply blankM p none) := by
  cases hl : PalPeg.GalilScaffoldCounter.positive wm.lag with
  | false => exact forward_quiet rest w x p he hm hs hc wm hw hl
  | true =>
    obtain ⟨h, age, spare, hi, _⟩ := he.2 wm (Or.inl hw)
    obtain ⟨a, ht⟩ := PalPeg.PhysicalBoundaryCount.cursor_symbol hi.cursor
    by_cases ha : PalPeg.GalilScaffoldInputHead.read
        (PalPeg.GalilScaffoldChainVerifier.right wm.machine.verifier) = some a
    · exact forward_match rest w x p he hm hs hc htick wm hw a ht ha hl
    · exact forward_mismatch rest w x p he hm hs hc htick wm hw a ht ha hl

theorem entry_successor (w : List (Fin 2)) (x : State GalilVM)
    (v : PalPeg.GalilScaffoldChainPeriod.Tape) (h lag credit : PalPeg.GalilScaffoldCounter.Counter)
    (ver : PalPeg.GalilScaffoldInputHead.PlaceHead)
    (hb : x.vm.chain = .back v h lag credit ver)
    (hf : PalPeg.GalilScaffoldChainPeriod.isFirst v.focus = true)
    (hm : x.ctl.mode = .scan) (hs : PalPeg.FrameFunction.starvedTest x = false) (hc : 1 < x.ctl.clock) :
    successor w x = countState (PalPeg.PhysicalWatchEntry.watchState x v lag credit ver) := by
  have hr : restartGuardTest x.vm = false := by simp [restartGuardTest, hb]
  rw [successor, PalPeg.PhysicalGuardProbe.tickFun_nonstarved_count _ _ 0 1 0 w _ 2048 x hm hs hr hc]
  change (⟨_, backgroundFun _ x.vm⟩ : State GalilVM) = _
  rw [backgroundFun_of_active _ x.vm (by simp [hb]), hb]
  simp only [chainStepFun, hf, if_true]
  rfl

/-- Back-to-watch entry creates both snapshot triples on this same machine and
stronger Enc. All values come from its real reset sweep, even when source search
storage already differs from the canonical state. -/
theorem forward_entry (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : RoutedState) (he : Enc w x p)
    (first last : Fin 3) (xs : List (Fin 3)) (h lag credit : PalPeg.GalilScaffoldCounter.Counter)
    (ver : PalPeg.GalilScaffoldInputHead.PlaceHead)
    (hb : x.vm.chain = .back ⟨[], .first first,
      xs.map PalPeg.GalilScaffoldChainPeriod.Token.plain ++ [.last last]⟩ h lag credit ver)
    (hm : x.ctl.mode = .scan) (hs : PalPeg.FrameFunction.starvedTest x = false) (hc : 1 < x.ctl.clock)
    (hperiod : PalPeg.ChainStoredPeriod.Stored x.vm.chain) :
    Enc w (successor w x) ((machine rest).apply blankM p none) := by
  obtain ⟨y, hr, hy⟩ := he.1
  have hchain := PalPeg.PhysicalSnapshotInvariant.chain_related hr
  have hby := hchain.trans hb
  have hmy : y.ctl.mode = .scan := (congrArg (fun c => c.mode) hr.1).symm.trans hm
  have hsy : PalPeg.FrameFunction.starvedTest y = false := (related_starved hr).trans hs
  have hcy : 1 < y.ctl.clock := by rw [← hr.1]; exact hc
  have hpy : PalPeg.ChainStoredPeriod.Stored y.vm.chain := by rw [hchain]; exact hperiod
  rcases p with ⟨⟨roles, q⟩, T⟩
  cases q with
  | inl tag => rw [hy.1, PalPeg.PhysicalBootFeed.initial_starved] at hsy; cases hsy
  | inr q =>
    let p : RoutedCore := ((roles, q), T)
    have hh := PalPeg.PhysicalWatchEntry.entryRead_running w y (decode p) _ h lag credit ver hby rfl
      (PalPeg.PhysicalCacheInvariant.running_core hy) hmy hsy hcy
    have hrRead := PalPeg.PhysicalTickDispatch.starvedRead_running
      (p := decode p) (PalPeg.PhysicalCacheInvariant.running_core (p := decode p) hy)
    have hentry : entryTest (liftConfig p).1 none
        (fun j => readWin blankM macroRadius ((liftConfig p).2 j)) = true := by
      change (!PalPeg.PhysicalTickDispatch.starvedRead (decode p).1
        (fun j => readWin blankM macroRadius ((decode p).2 j)) &&
        PalPeg.PhysicalWatchEntry.entryRead (decode p).1
          (fun j => readWin blankM macroRadius ((decode p).2 j))) = true
      rw [hrRead, hsy, hh]; rfl
    change Enc w (successor w x) ((machine rest).apply blankM (liftConfig p) none)
    rw [machine, select_apply, hentry, if_pos rfl, PalPeg.PhysicalShiftDispatch.lift_apply]
    let v : PalPeg.GalilScaffoldChainPeriod.Tape := ⟨[], .first first,
      xs.map PalPeg.GalilScaffoldChainPeriod.Token.plain ++ [.last last]⟩
    let wm : PalPeg.GalilScaffoldChainWatch.State := ⟨⟨ver, PalPeg.GalilScaffoldChainInputSupply.watchControl v⟩, lag, credit⟩
    have htarget : (successor w x).vm.chain = .watch wm := by
      rw [entry_successor w x v h lag credit ver hb rfl hm hs hc]; rfl
    have hi : PalPeg.ChainBoundaryCache.Inv (xs.length + 1) 0 wm.machine.control
        PalPeg.GalilScaffoldCounter.reset := PalPeg.ChainBoundaryCache.inv_ready first last xs
    apply PalPeg.PhysicalSnapshotInvariant.of_watching w (successor w x) _ wm (Or.inl htarget)
      (xs.length + 1) 0 PalPeg.GalilScaffoldCounter.reset hi
    change PalPeg.PhysicalCacheInvariant.Running w (saved (successor w x)
      PalPeg.GalilScaffoldCounter.reset PalPeg.GalilScaffoldCounter.reset PalPeg.GalilScaffoldCounter.reset)
      (decode ((PalPeg.LocalRoleRouting.hold PalPeg.PhysicalSearchRecycle.entryStep).apply blankM p none))
    rw [PalPeg.LocalRoleRouting.decode_hold]
    have hout := PalPeg.PhysicalSearchSnapshots.entry_saved w y (decode p) first last xs h lag credit ver
      hby hy hmy hsy hcy hpy
    have hsaved := PalPeg.PhysicalSnapshotInvariant.saved_related (related_tick w hr)
      PalPeg.GalilScaffoldCounter.reset PalPeg.GalilScaffoldCounter.reset PalPeg.GalilScaffoldCounter.reset
    change saved (successor w y) _ _ _ = saved (successor w x) _ _ _ at hsaved
    rw [hsaved] at hout
    exact hout

/-- Idle/missed search retains its storage representative and never creates a
watch cache. This carries the already completed static count case forward. -/
theorem forward_atRest (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : RoutedState) (he : Enc w x p)
    (hm : x.ctl.mode = .scan) (hs : PalPeg.FrameFunction.starvedTest x = false) (hc : 1 < x.ctl.clock)
    (hidle : x.vm.chain = .idle)
    (hsearch : x.vm.search.mode = .idle ∨ x.vm.search.mode = .missed) :
    Enc w (successor w x) ((machine rest).apply blankM p none) := by
  obtain ⟨y, hr, hy⟩ := he.1
  have hmy : y.ctl.mode = .scan := (congrArg (fun c => c.mode) hr.1).symm.trans hm
  have hsy : PalPeg.FrameFunction.starvedTest y = false := (related_starved hr).trans hs
  have hcy : 1 < y.ctl.clock := by rw [← hr.1]; exact hc
  have hidley := (PalPeg.PhysicalSnapshotInvariant.chain_related hr).trans hidle
  have hsearchy : y.vm.search.mode = .idle ∨ y.vm.search.mode = .missed := by
    have hh := hr.2.1
    unfold Same at hh
    rw [hh]
    exact hsearch
  have hnext : (successor w x).vm.chain = .idle := by
    have hg : restartGuardTest x.vm = false := by simp [restartGuardTest, hidle]
    rw [successor, PalPeg.PhysicalGuardProbe.tickFun_nonstarved_count _ _ 0 1 0 w _ 2048 x hm hs hg hc]
    change (backgroundFun _ x.vm).chain = .idle
    rw [background_dormant _ x.vm (Or.inr hsearch)]
    simp only [hidle, chainStepFun]
  have hentry : entryTest p.1 none (fun j => readWin blankM macroRadius (p.2 j)) = false := by
    rcases p with ⟨⟨roles, q⟩, T⟩
    cases q with
    | inl tag => rfl
    | inr q =>
      obtain ⟨U, hU, _⟩ := PalPeg.PhysicalCacheInvariant.running_core
        (p := (q, fun j => T (roles j))) hy
      have ht : q.chainTag = .idle := by rw [hU.1.1.chainTag, hidley]; rfl
      simp [entryTest, PalPeg.PhysicalWatchEntry.entryRead, ht]
  have hmatch : matchTest p.1 none (fun j => readWin blankM macroRadius (p.2 j)) = false := by
    rcases p with ⟨⟨roles, q⟩, T⟩
    cases q with
    | inl tag => rfl
    | inr q =>
      obtain ⟨U, hU, _⟩ := PalPeg.PhysicalCacheInvariant.running_core
        (p := (q, fun j => T (roles j))) hy
      have ht : q.chainTag = .idle := by rw [hU.1.1.chainTag, hidley]; rfl
      simp [matchTest, PalPeg.PhysicalCacheMachine.prepareRead, chainConsumesTest, ht]
  rw [apply_previous rest p none hentry hmatch, old_count_previous rest w y p hy hcy]
  refine ⟨⟨successor w y, related_tick w hr,
    PalPeg.PhysicalBoundaryCount.forward_atRest rest w y p hy hmy hsy hcy hidley hsearchy⟩, ?_⟩
  intro wm hw
  rcases hw with hw | hw <;> rw [hnext] at hw <;> cases hw

open PalPeg.CloseoutCheckW (PreTraceIMW CanonTrace)
open PalPeg.LocalSysConcrete (absSC)
open PalPeg.LocalReplayParked (Mirrored1)
open PalPeg.LocalBlankState (tapeCount)
open PalPeg.ShadowedLocalFinal (localGood postPhase frozenAt heldAfter)

/-- The canonical consumer now uses the same snapshot-bearing Enc for initial
state, arrivals, all starved states, static count, all watch count, and watch
entry. Shift/comparison/restart and other modes remain explicit obligations on
this machine; older proofs using only CoreInv do not discharge them silently. -/
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
        Enc w (successor w (absSC m)) ((machine rest).apply blankM p none)) :
    TickCases (machine rest) blankM Enc := by
  constructor
  · intro w st Tc hpre hcanon m p hon hnotFrozen he hs
    exact forward_starved rest w (absSC m) p he hs
  · intro w st Tc hpre hcanon m p hon hnotFrozen he hs htick
    by_cases hrest : PalPeg.PhysicalScanCount.CountAtRest (absSC m)
    · obtain ⟨hm, hc, hidle, hsearch⟩ := hrest
      exact forward_atRest rest w (absSC m) p he hm hs hc hidle hsearch
    by_cases hwatch : PalPeg.PhysicalBoundaryCount.CountWatch (absSC m)
    · obtain ⟨hm, hc, wm, hw⟩ := hwatch
      exact forward_watch rest w (absSC m) p he hm hs hc htick wm hw
    by_cases hback : PalPeg.PhysicalBoundaryCount.CountBackReady (absSC m)
    · have hperiod := PalPeg.PhysicalChainShape.period_onRun w st Tc hpre m hon.onRun hnotFrozen
      obtain ⟨hm, hc, first, last, xs, h, lag, credit, ver, hchain⟩ :=
        PalPeg.PhysicalBoundaryCount.entry_of_backReady hperiod.1 hback
      exact forward_entry rest w (absSC m) p he first last xs h lag credit ver hchain hm hs hc hperiod.2
    exact hother w st Tc hpre hcanon m p hon hnotFrozen he hs htick hrest hwatch hback

/-- info: 'PalPeg.PhysicalSnapshotMachine.cases_of_remaining' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cases_of_remaining

/-- info: 'PalPeg.PhysicalSnapshotMachine.forward_watch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forward_watch

/-- info: 'PalPeg.PhysicalSnapshotMachine.forward_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forward_entry

/-- info: 'PalPeg.PhysicalSnapshotMachine.forward_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forward_match

/-- info: 'PalPeg.PhysicalSnapshotMachine.forward_feed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forward_feed

end PalPeg.PhysicalSnapshotMachine
