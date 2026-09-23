import PalPeg.PhysicalBoundaryRotate
import PalPeg.PhysicalCacheMachine
import PalPeg.PhysicalCountMismatch
import PalPeg.PhysicalWatchIdle
import PalPeg.PhysicalChainShape
import PalPeg.PhysicalPeriodMirror
import PalPeg.PhysicalShift

/-!
# Every count step of a watching chain

Successful consumption, failed comparison and a nonpositive lag use one machine.
Spare preparation, VM motion and clock decrement share one physical step.
At FIRST/LAST the same output is decoded with the finite boundary permutation
and its matching sign permutation. The source cache comes from the common Enc.
-/
set_option autoImplicit false
namespace PalPeg.PhysicalBoundaryCount
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract PalPeg.PhysicalBootFeed
open PalPeg.PhysicalScanCount PalPeg.PhysicalTickDispatch PalPeg.PhysicalCountConsume
open PalPeg.PhysicalConsumeStage PalPeg.PhysicalBoundaryRotate
open PalPeg.PhysicalCacheInvariant (Running Cache running_core running_cache of_watching_cache)
open PalPeg.PhysicalSpare (Rep spareIndex)
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilFinalAssembly2 (centreC placeC)
open PalPeg.GalilScaffoldChainWatch (caught)
open PalPeg.ChainBoundaryCache (boundaryEvent nextAge nextSpare Inv)
open PalPeg.GalilScaffoldCounter (Canonical)
open PalPeg.Local (readWin)
open PalPeg.Program (STape)

/-- Observational result of the completed step. Rotation changes only names. -/
noncomputable def completed (boundary : Bool) (p : CoreState) : CoreState :=
  if boundary then rotateCore p else p

theorem running_match (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : Running w x p) (hmode : x.ctl.mode = .scan)
    (hs : PalPeg.FrameFunction.starvedTest x = false) (hclock : 1 < x.ctl.clock)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm) (a : Fin 3)
    (htok : PalPeg.GalilScaffoldChainConsume.symbol wm.machine.control.period.focus = some a)
    (hseen : PalPeg.GalilScaffoldInputHead.read
      (PalPeg.GalilScaffoldChainVerifier.right wm.machine.verifier) = some a)
    (hlag : PalPeg.GalilScaffoldCounter.positive wm.lag = true)
    (hcan : PalPeg.GalilScaffoldChainVerifier.canRight wm.machine.verifier) :
    Running w (countState (caughtState x wm))
      (completed (boundaryEvent wm.machine.control)
        ((PalPeg.PhysicalCountSpare.countStep rest).apply blankM p none)) := by
  have hcache := running_cache he
  rw [Cache, hchain] at hcache
  obtain ⟨h, age, spare, hi, hr, hmirror⟩ := hcache
  have hrestart : restartGuardTest x.vm = false := by simp [restartGuardTest, hchain]
  have hbase : PalPeg.MachineStep.sweepClosure blankM (CoreEnc w) (countState (stagedState x wm))
      ((countedStep (workStep rest)).apply blankM p none) := by
    rw [counted_apply, countRead_running (running_core he) hmode hs hrestart hclock]
    simp only [if_true]
    exact PalPeg.PhysicalScanCount.running_clockDown
      (running_staged rest w x p (running_core he) hmode hs hclock wm hchain a htok hseen
        (cursor_left hi.cursor a htok hseen) hlag hcan)
  obtain ⟨hstage, hrep⟩ := PalPeg.PhysicalSpare.overlay_preserves (countedStep (workStep rest)) w
    (countState (stagedState x wm)) p spare none hbase rfl hr
  have hmirrorNext := PalPeg.PhysicalPeriodMirror.count_scan rest w x p (running_core he)
    hmode hs hclock hrestart h
    (by simpa only [PalPeg.PhysicalCacheInvariant.mirrorMagnitude, hmode, reduceCtorEq, if_false] using hmirror)
  have hphase : p.1.chainPhase = wm.machine.control.phase := by
    obtain ⟨T, hT, _⟩ := running_core he
    simpa only [hchain, chainConsumeOf] using hT.1.1.chainPhase
  rw [hphase] at hrep
  have hinv : Inv h (nextAge wm.machine.control age) (caught wm).machine.control
      (nextSpare wm.machine.control spare) := by
    simpa only [caught, PalPeg.GalilScaffoldChainVerifier.consume, hseen] using
      PalPeg.ChainBoundaryCache.inv_consume hi a htok
  have hevent : (PalPeg.GalilScaffoldChainPeriod.isFirst wm.machine.control.period.focus ||
      PalPeg.GalilScaffoldChainConsume.isLast wm.machine.control.period.focus) = boundaryEvent wm.machine.control := rfl
  cases hb : boundaryEvent wm.machine.control with
  | false =>
    have hstaged : stagedState x wm = caughtState x wm := by
      have hc : stagedWatch wm = caught wm := by
        unfold stagedWatch
        simp only [caught, PalPeg.GalilScaffoldChainVerifier.consume, hseen,
          PalPeg.GalilScaffoldChainConsume.consume, htok, decide_true, if_true]
        simp only [hevent, hb, Bool.false_eq_true, if_false]
      simp only [stagedState, caughtState, hc]
    rw [completed, if_neg Bool.false_ne_true]
    rw [hstaged] at hstage
    apply of_watching_cache (caught wm) (Or.inl rfl) hstage
    exact ⟨h, age+1, _, by simpa only [nextAge, nextSpare, hb, Bool.false_eq_true, if_false] using hinv, hrep, by
      simpa only [PalPeg.PhysicalCountSpare.countStep, PalPeg.PhysicalCacheInvariant.mirrorMagnitude,
        countState, caughtState, hmode, reduceCtorEq, if_false] using hmirrorNext⟩
  | true =>
    have hspareCanonical : Canonical spare := by
      obtain ⟨seg, ha, _⟩ := hr
      rw [← ha]
      exact PalPeg.LocalCounter.absCtr_canonical _ _
    have hd : Canonical wm.machine.control.distance := by
      obtain ⟨T, hT, _⟩ := running_core he
      obtain ⟨seg, ha, _⟩ := hT.1.2.counters 13 wm.machine.control.distance (by simp [counterOf, hchain])
      rw [← ha]
      exact PalPeg.LocalCounter.absCtr_canonical _ _
    rw [PalPeg.ChainBoundaryCache.spare_eq_at_boundary hi hb hspareCanonical hd] at hrep
    have hboundary : (caught wm).machine.control.boundary = PalPeg.GalilScaffoldCounter.inc wm.machine.control.distance := by
      simp only [caught, PalPeg.GalilScaffoldChainVerifier.consume, hseen,
        PalPeg.GalilScaffoldChainConsume.consume, htok, decide_true, if_true, hevent, hb]
    have hlast : (caught wm).machine.control.last = wm.machine.control.boundary := by
      simp only [caught, PalPeg.GalilScaffoldChainVerifier.consume, hseen,
        PalPeg.GalilScaffoldChainConsume.consume, htok, decide_true, if_true, hevent, hb]
    obtain ⟨hout, hlastRep⟩ := running_rotate w (countState x)
      ((PalPeg.PhysicalCountSpare.countStep rest).apply blankM p none) wm hstage hboundary hlast hrep
    rw [completed, if_pos rfl]
    apply of_watching_cache (caught wm) (Or.inl rfl) hout
    refine ⟨h, 0, _, by simpa only [nextAge, nextSpare, hb, if_true] using hinv, hlastRep, ?_⟩
    have hm := PalPeg.PhysicalRoles.boundaryRoles_other PalPeg.PhysicalPeriodMirror.mirrorIndex
      (by simp [PalPeg.PhysicalPeriodMirror.mirrorIndex, mirrorSlot, counterSlot])
      (by simp [PalPeg.PhysicalPeriodMirror.mirrorIndex, mirrorSlot, counterSlot])
      (by simp [PalPeg.PhysicalPeriodMirror.mirrorIndex, mirrorSlot, counterSlot])
    simpa only [rotateCore, hm, PalPeg.PhysicalCacheInvariant.mirrorMagnitude,
      countState, caughtState, hmode, reduceCtorEq, if_false] using hmirrorNext

/-- info: 'PalPeg.PhysicalBoundaryCount.running_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms running_match

/-- FIRST/LAST is observed in the same window as the consuming branch. -/
noncomputable def eventRead (_q : CoreControl)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm macroRadius) : Bool :=
  PalPeg.GalilScaffoldChainPeriod.isFirst (decToken (centreRead ws periodSlot)) ||
    PalPeg.GalilScaffoldChainConsume.isLast (decToken (centreRead ws periodSlot))

noncomputable def boundaryRead (q : CoreControl)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm macroRadius) : Bool :=
  !starvedRead q ws && PalPeg.PhysicalCacheMachine.prepareRead q ws && eventRead q ws

noncomputable def changeRead (q : Control) (input : Option (Fin 2))
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm macroRadius) : Bool :=
  match q, input with
  | .inr c, none => boundaryRead c ws
  | _, _ => false

def turnControl : Control → Control
  | .inl tag => .inl tag
  | .inr q => .inr (rotateControl q)

/-- Update the finite signs in the same result whose roles are exchanged. -/
noncomputable def signedStep (rest : RestCommands) :
    PalPeg.Local.LocalStep (Fin 2) Control Γm tapeCountM macroRadius where
  next := fun q input ws =>
    let r := (PalPeg.PhysicalCacheMachine.machine rest).next q input ws
    (if changeRead q input ws then turnControl r.1 else r.1, r.2)
  disp_le := (PalPeg.PhysicalCacheMachine.machine rest).disp_le

noncomputable def roleChange : PalPeg.LocalRoleRouting.RoleChange (Fin 2) Control Γm tapeCountM macroRadius :=
  fun q input ws => if changeRead q input ws then PalPeg.PhysicalRoles.boundaryRoles else Equiv.refl _

noncomputable def machine (rest : RestCommands) :=
  PalPeg.LocalRoleRouting.route (signedStep rest) roleChange

abbrev Enc := PalPeg.PhysicalCacheMachine.routedEnc

noncomputable def completedOuter (boundary : Bool) (p : PhysicalState) : PhysicalState :=
  if boundary then (turnControl p.1, fun j => p.2 (PalPeg.PhysicalRoles.boundaryRoles j)) else p

theorem signed_apply (rest : RestCommands) (p : PhysicalState) (input : Option (Fin 2)) :
    (signedStep rest).apply blankM p input =
      (if changeRead p.1 input (fun j => readWin blankM macroRadius (p.2 j)) then
        turnControl ((PalPeg.PhysicalCacheMachine.machine rest).apply blankM p input).1
      else ((PalPeg.PhysicalCacheMachine.machine rest).apply blankM p input).1,
        ((PalPeg.PhysicalCacheMachine.machine rest).apply blankM p input).2) := rfl

/-- The equation exposes an actual single routed sweep, not two ticks. -/
theorem decode_machine (rest : RestCommands) (p : PalPeg.PhysicalRoles.PhysicalState)
    (input : Option (Fin 2)) :
    PalPeg.LocalRoleRouting.decode ((machine rest).apply blankM p input) =
      completedOuter (changeRead p.1.2 input
        (fun j => readWin blankM macroRadius ((PalPeg.LocalRoleRouting.decode p).2 j)))
        ((PalPeg.PhysicalCacheMachine.machine rest).apply blankM (PalPeg.LocalRoleRouting.decode p) input) := by
  rw [machine, PalPeg.LocalRoleRouting.decode_route, signed_apply]
  simp only [roleChange, PalPeg.LocalRoleRouting.decode]
  by_cases hb : changeRead p.1.2 input (fun j => readWin blankM macroRadius (p.2 (p.1.1 j))) = true <;>
    simp only [completedOuter, hb, Bool.false_eq_true, if_true, if_false, Equiv.refl_apply, Prod.eta]

theorem boundaryRead_match (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : Running w x p) (hmode : x.ctl.mode = .scan)
    (hs : PalPeg.FrameFunction.starvedTest x = false) (hclock : 1 < x.ctl.clock)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm) (a : Fin 3)
    (htok : PalPeg.GalilScaffoldChainConsume.symbol wm.machine.control.period.focus = some a)
    (hseen : PalPeg.GalilScaffoldInputHead.read
      (PalPeg.GalilScaffoldChainVerifier.right wm.machine.verifier) = some a)
    (hlag : PalPeg.GalilScaffoldCounter.positive wm.lag = true)
    (hcan : PalPeg.GalilScaffoldChainVerifier.canRight wm.machine.verifier) :
    boundaryRead p.1 (fun j => readWin blankM macroRadius (p.2 j)) = boundaryEvent wm.machine.control := by
  have hp := PalPeg.PhysicalCacheMachine.prepareRead_match w x p (running_core he)
    hmode hs hclock wm hchain a htok hseen hlag hcan
  rw [boundaryRead, starvedRead_running (running_core he), hs, hp]
  simp only [Bool.not_false, Bool.true_and]
  apply read_from_running eventRead (fun _ => boundaryEvent wm.machine.control) w x p (running_core he)
  intro T hT
  have hperiod : periodOf x = some wm.machine.control.period := by simp [periodOf, hchain]
  have htoken := centreRead_periodSlot (K := macroRadius) hT.1.2 (le_refl margin) _ hperiod
  have hdec : decToken (centreRead (fun j => readWin blankM macroRadius (T j)) periodSlot) =
      wm.machine.control.period.focus := by
    simpa only [tapesOf, Equiv.apply_symm_apply, decToken_encToken, encPeriod] using congrArg decToken htoken
  simp only [eventRead, hdec, boundaryEvent]

/-- Both period directions and FIRST/LAST use the same concrete machine. -/
theorem forward_match (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : PalPeg.PhysicalRoles.PhysicalState) (he : Enc w x p)
    (hmode : x.ctl.mode = .scan) (hs : PalPeg.FrameFunction.starvedTest x = false) (hclock : 1 < x.ctl.clock)
    {y : State GalilVM}
    (htick : Tick (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x y)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm) (a : Fin 3)
    (htok : PalPeg.GalilScaffoldChainConsume.symbol wm.machine.control.period.focus = some a)
    (hseen : PalPeg.GalilScaffoldInputHead.read
      (PalPeg.GalilScaffoldChainVerifier.right wm.machine.verifier) = some a)
    (hlag : PalPeg.GalilScaffoldCounter.positive wm.lag = true) :
    Enc w (PalPeg.PhysicalCacheMachine.successor w x) ((machine rest).apply blankM p none) := by
  have hcan := PalPeg.PhysicalCountReady.verifier_canRight_of_countTick w htick hmode hclock wm hchain hlag
  rw [PalPeg.PhysicalCacheMachine.match_successor w x hmode hs hclock wm hchain a htok hseen hlag]
  change PalPeg.PhysicalCacheInvariant.Enc w _ (PalPeg.LocalRoleRouting.decode _)
  rw [decode_machine]
  rcases p with ⟨⟨roles, q⟩, T⟩
  cases q with
  | inl tag => rw [he.1, initial_starved] at hs; cases hs
  | inr q =>
    let U := fun j => T (roles j)
    change PalPeg.PhysicalCacheInvariant.Enc w _
      (completedOuter (boundaryRead q (fun j => readWin blankM macroRadius (U j)))
        ((PalPeg.PhysicalCacheMachine.machine rest).apply blankM (.inr q, U) none))
    rw [boundaryRead_match w x (q, U) he hmode hs hclock wm hchain a htok hseen hlag hcan,
      PalPeg.PhysicalCacheMachine.machine, apply_active _ w x (q, U) (running_core he) hs,
      PalPeg.PhysicalCacheMachine.selected_match rest w x (q, U) (running_core he) hmode hs hclock
        wm hchain a htok hseen hlag hcan]
    have hout := running_match rest w x (q, U) he hmode hs hclock wm hchain a htok hseen hlag hcan
    cases hb : boundaryEvent wm.machine.control <;>
      simpa only [completedOuter, completed, hb, if_true, Bool.false_eq_true, if_false,
        turnControl, rotateCore, PalPeg.PhysicalCacheInvariant.Enc] using hout

/-- info: 'PalPeg.PhysicalBoundaryCount.forward_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forward_match

theorem enc_initial (w : List (Fin 2)) :
    Enc w initialState (PalPeg.PhysicalRoles.initialControl, fun _ => STape.blankTape blankM) :=
  PalPeg.PhysicalCacheMachine.routed_initial w

/-- Transfer already proved cases when the finite source test retains the roles. -/
theorem enc_unchanged (rest : RestCommands) (w : List (Fin 2)) (y : State GalilVM)
    (p : PalPeg.PhysicalRoles.PhysicalState) (input : Option (Fin 2))
    (ht : changeRead p.1.2 input
      (fun j => readWin blankM macroRadius ((PalPeg.LocalRoleRouting.decode p).2 j)) = false) :
    Enc w y ((machine rest).apply blankM p input) ↔
      PalPeg.PhysicalCacheInvariant.Enc w y
        ((PalPeg.PhysicalCacheMachine.machine rest).apply blankM (PalPeg.LocalRoleRouting.decode p) input) := by
  change PalPeg.PhysicalCacheInvariant.Enc w y (PalPeg.LocalRoleRouting.decode _) ↔ _
  rw [decode_machine, ht, completedOuter, if_neg Bool.false_ne_true]

theorem changeRead_starved (w : List (Fin 2)) (x : State GalilVM) (p : PhysicalState)
    (he : PalPeg.PhysicalCacheInvariant.Enc w x p) (hs : PalPeg.FrameFunction.starvedTest x = true) :
    changeRead p.1 none (fun j => readWin blankM macroRadius (p.2 j)) = false := by
  rcases p with ⟨q, T⟩
  cases q with
  | inl tag => rfl
  | inr q =>
    change boundaryRead q (fun j => readWin blankM macroRadius (T j)) = false
    simp only [boundaryRead, starvedRead_running (running_core he), hs, Bool.not_true, Bool.false_and]

theorem changeRead_unwatched (w : List (Fin 2)) (x : State GalilVM) (p : PhysicalState)
    (he : PalPeg.PhysicalCacheInvariant.Enc w x p) (htag : chainTagOf x.vm.chain ≠ .watchers) :
    changeRead p.1 none (fun j => readWin blankM macroRadius (p.2 j)) = false := by
  rcases p with ⟨q, T⟩
  cases q with
  | inl tag => rfl
  | inr q =>
    obtain ⟨ideal, hi, ht⟩ := running_core he
    have hq : q.chainTag ≠ .watchers := by rw [hi.1.1.chainTag]; exact htag
    simp [changeRead, boundaryRead, PalPeg.PhysicalCacheMachine.prepareRead, chainConsumesTest, hq]

theorem forward_feed (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : PalPeg.PhysicalRoles.PhysicalState) (a : Fin 2) (he : Enc w x p) :
    Enc w (PalPeg.GalilArriveChain.arriveState' a x) ((machine rest).apply blankM p (some a)) := by
  rw [enc_unchanged rest w _ p (some a) (by cases p.1.2 <;> rfl)]
  exact PalPeg.PhysicalCacheMachine.forward_feed rest w x (PalPeg.LocalRoleRouting.decode p) a he

theorem forward_starved (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : PalPeg.PhysicalRoles.PhysicalState) (he : Enc w x p)
    (hs : PalPeg.FrameFunction.starvedTest x = true) :
    Enc w x ((machine rest).apply blankM p none) := by
  rw [enc_unchanged rest w x p none (changeRead_starved w x (PalPeg.LocalRoleRouting.decode p) he hs)]
  exact PalPeg.PhysicalCacheMachine.forward_starved rest w x (PalPeg.LocalRoleRouting.decode p) he hs

theorem forward_atRest (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : PalPeg.PhysicalRoles.PhysicalState) (he : Enc w x p)
    (hmode : x.ctl.mode = .scan) (hs : PalPeg.FrameFunction.starvedTest x = false)
    (hclock : 1 < x.ctl.clock) (hidle : x.vm.chain = .idle)
    (hsearch : x.vm.search.mode = .idle ∨ x.vm.search.mode = .missed) :
    Enc w (PalPeg.PhysicalCacheMachine.successor w x) ((machine rest).apply blankM p none) := by
  rw [enc_unchanged rest w _ p none (changeRead_unwatched w x (PalPeg.LocalRoleRouting.decode p) he
    (by simp [hidle, chainTagOf]))]
  exact PalPeg.PhysicalCacheMachine.forward_atRest rest w x (PalPeg.LocalRoleRouting.decode p)
    he hmode hs hclock hidle hsearch

theorem forward_entry (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : PalPeg.PhysicalRoles.PhysicalState) (he : Enc w x p)
    (first last : Fin 3) (xs : List (Fin 3)) (h lag credit : PalPeg.GalilScaffoldCounter.Counter)
    (ver : PalPeg.GalilScaffoldInputHead.PlaceHead)
    (hback : x.vm.chain = .back ⟨[], .first first, xs.map PalPeg.GalilScaffoldChainPeriod.Token.plain ++ [.last last]⟩ h lag credit ver)
    (hmode : x.ctl.mode = .scan) (hs : PalPeg.FrameFunction.starvedTest x = false) (hclock : 1 < x.ctl.clock)
    (hperiod : PalPeg.ChainStoredPeriod.Stored x.vm.chain) :
    Enc w (PalPeg.PhysicalCacheMachine.successor w x) ((machine rest).apply blankM p none) ∧
      Rep true (PalPeg.GalilScaffoldCounter.ofNat (xs.length + 1))
        ((PalPeg.LocalRoleRouting.decode ((machine rest).apply blankM p none)).2
          PalPeg.PhysicalPeriodMirror.mirrorIndex) := by
  have hkeep := changeRead_unwatched w x (PalPeg.LocalRoleRouting.decode p) he
    (by simp [hback, chainTagOf])
  change changeRead p.1.2 none
    (fun j => readWin blankM macroRadius ((PalPeg.LocalRoleRouting.decode p).2 j)) = false at hkeep
  constructor
  · rw [enc_unchanged rest w _ p none hkeep]
    exact PalPeg.PhysicalCacheMachine.forward_entry rest w x (PalPeg.LocalRoleRouting.decode p)
      he first last xs h lag credit ver hback hmode hs hclock hperiod
  · rw [decode_machine, hkeep, completedOuter, if_neg Bool.false_ne_true]
    exact PalPeg.PhysicalCacheMachine.periodMirror_entry rest w x (PalPeg.LocalRoleRouting.decode p)
      he hperiod first last xs h lag credit ver hback hmode hs hclock

/-- The common cursor invariant always provides a real period symbol. -/
theorem cursor_symbol {h age : ℕ} {tape : PalPeg.GalilScaffoldChainPeriod.Tape} {forward : Bool}
    (hc : PalPeg.ChainBoundaryCache.Cursor h age tape forward) :
    ∃ a, PalPeg.GalilScaffoldChainConsume.symbol tape.focus = some a := by
  obtain ⟨passed, future, first, last, hp, hlen, ht⟩ := hc
  cases forward <;> simp only [Bool.false_eq_true, if_false, if_true] at ht
  all_goals
    cases future with
    | nil =>
      have hf := (List.cons.inj (by simpa using ht.2)).1
      simp [hf, PalPeg.GalilScaffoldChainConsume.symbol]
    | cons a rest =>
      have hf := (List.cons.inj (by simpa using ht.2)).1
      exact ⟨a, by simp [hf, PalPeg.GalilScaffoldChainConsume.symbol]⟩

theorem forward_mismatch (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : PalPeg.PhysicalRoles.PhysicalState) (he : Enc w x p)
    (hmode : x.ctl.mode = .scan) (hs : PalPeg.FrameFunction.starvedTest x = false) (hclock : 1 < x.ctl.clock)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm) (a : Fin 3)
    (htok : PalPeg.GalilScaffoldChainConsume.symbol wm.machine.control.period.focus = some a)
    (hseen : PalPeg.GalilScaffoldInputHead.read
      (PalPeg.GalilScaffoldChainVerifier.right wm.machine.verifier) ≠ some a)
    (hlag : PalPeg.GalilScaffoldCounter.positive wm.lag = true)
    (hcan : PalPeg.GalilScaffoldChainVerifier.canRight wm.machine.verifier) :
    Enc w (PalPeg.PhysicalCacheMachine.successor w x) ((machine rest).apply blankM p none) := by
  have hkeep : changeRead p.1.2 none
      (fun j => readWin blankM macroRadius ((PalPeg.LocalRoleRouting.decode p).2 j)) = false := by
    rcases p with ⟨⟨roles, q⟩, T⟩
    cases q with
    | inl tag => rfl
    | inr q =>
      have hp := PalPeg.PhysicalCountMismatch.prepareRead_mismatch w x (q, fun j => T (roles j))
        he wm hchain a htok hseen hcan
      change boundaryRead q (fun j => readWin blankM macroRadius (T (roles j))) = false
      simp only [boundaryRead, hp, Bool.and_false, Bool.false_and]
  rw [enc_unchanged rest w _ p none hkeep]
  exact PalPeg.PhysicalCountMismatch.forward_count rest w x (PalPeg.LocalRoleRouting.decode p)
    he hmode hs hclock wm hchain a htok hseen hlag hcan

/-- A positive-lag watch count consumes in either direction, on any real token,
and for either verdict. Period and verifier readiness come from Enc/legal Tick. -/
theorem forward_consume (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : PalPeg.PhysicalRoles.PhysicalState) (he : Enc w x p)
    (hmode : x.ctl.mode = .scan) (hs : PalPeg.FrameFunction.starvedTest x = false) (hclock : 1 < x.ctl.clock)
    {y : State GalilVM}
    (htick : Tick (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x y)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm)
    (hlag : PalPeg.GalilScaffoldCounter.positive wm.lag = true) :
    Enc w (PalPeg.PhysicalCacheMachine.successor w x) ((machine rest).apply blankM p none) := by
  have hsymbol : ∃ a, PalPeg.GalilScaffoldChainConsume.symbol wm.machine.control.period.focus = some a := by
    rcases p with ⟨⟨roles, q⟩, T⟩
    cases q with
    | inl tag => rw [he.1, initial_starved] at hs; cases hs
    | inr q =>
      have hc := running_cache (p := (q, fun j => T (roles j))) he
      rw [Cache, hchain] at hc
      obtain ⟨h, age, spare, hi, hr⟩ := hc
      exact cursor_symbol hi.cursor
  obtain ⟨a, htok⟩ := hsymbol
  by_cases hseen : PalPeg.GalilScaffoldInputHead.read
      (PalPeg.GalilScaffoldChainVerifier.right wm.machine.verifier) = some a
  · exact forward_match rest w x p he hmode hs hclock htick wm hchain a htok hseen hlag
  · exact forward_mismatch rest w x p he hmode hs hclock wm hchain a htok hseen hlag
      (PalPeg.PhysicalCountReady.verifier_canRight_of_countTick w htick hmode hclock wm hchain hlag)

/-- info: 'PalPeg.PhysicalBoundaryCount.forward_consume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forward_consume

/-- With no pending lag, this machine retains its roles and all cache data. -/
theorem forward_quiet (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : PalPeg.PhysicalRoles.PhysicalState) (he : Enc w x p)
    (hmode : x.ctl.mode = .scan) (hs : PalPeg.FrameFunction.starvedTest x = false) (hclock : 1 < x.ctl.clock)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm)
    (hlag : PalPeg.GalilScaffoldCounter.positive wm.lag = false) :
    Enc w (PalPeg.PhysicalCacheMachine.successor w x) ((machine rest).apply blankM p none) := by
  have hkeep : changeRead p.1.2 none
      (fun j => readWin blankM macroRadius ((PalPeg.LocalRoleRouting.decode p).2 j)) = false := by
    rcases p with ⟨⟨roles, q⟩, T⟩
    cases q with
    | inl tag => rfl
    | inr q =>
      have hp := PalPeg.PhysicalWatchIdle.prepareRead_quiet w x (q, fun j => T (roles j)) he wm hchain hlag
      change boundaryRead q (fun j => readWin blankM macroRadius (T (roles j))) = false
      simp only [boundaryRead, hp, Bool.and_false, Bool.false_and]
  rw [enc_unchanged rest w _ p none hkeep]
  exact PalPeg.PhysicalWatchIdle.forward_count rest w x (PalPeg.LocalRoleRouting.decode p)
    he hmode hs hclock wm hchain hlag

/-- Every count step with a watching chain: no token, direction, lag-sign or
verdict hypotheses remain. The caller supplies its existing legal Tick. -/
theorem forward_watch (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : PalPeg.PhysicalRoles.PhysicalState) (he : Enc w x p)
    (hmode : x.ctl.mode = .scan) (hs : PalPeg.FrameFunction.starvedTest x = false) (hclock : 1 < x.ctl.clock)
    {y : State GalilVM}
    (htick : Tick (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x y)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm) :
    Enc w (PalPeg.PhysicalCacheMachine.successor w x) ((machine rest).apply blankM p none) := by
  cases hlag : PalPeg.GalilScaffoldCounter.positive wm.lag with
  | false => exact forward_quiet rest w x p he hmode hs hclock wm hchain hlag
  | true => exact forward_consume rest w x p he hmode hs hclock htick wm hchain hlag

/-- info: 'PalPeg.PhysicalBoundaryCount.forward_watch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forward_watch

/-- The complete watch count case. -/
def CountWatch (x : State GalilVM) : Prop :=
  x.ctl.mode = .scan ∧ 1 < x.ctl.clock ∧
    ∃ wm : PalPeg.GalilScaffoldChainWatch.State, x.vm.chain = .watch wm

open PalPeg.CloseoutCheckW (PreTraceIMW CanonTrace)
open PalPeg.LocalSysConcrete (absSC)
open PalPeg.LocalReplayParked (Mirrored1)
open PalPeg.LocalShadowConcrete (OnRun)
open PalPeg.LocalBlankState (tapeCount)
open PalPeg.ShadowedLocalFinal (localGood postPhase frozenAt heldAfter)
open PalPeg.PhysicalCacheMachine (successor)

/-- The actual count entry guard: a back chain whose cursor reads FIRST.
The complete period shape is supplied from OnRun at the final call site. -/
def CountBackReady (x : State GalilVM) : Prop :=
  x.ctl.mode = .scan ∧ 1 < x.ctl.clock ∧
    ∃ v h lag credit ver, x.vm.chain = .back v h lag credit ver ∧
      PalPeg.GalilScaffoldChainPeriod.isFirst v.focus = true

theorem entry_of_backReady {x : State GalilVM}
    (hb : PalPeg.GalilBranchInvariants.BlockInv x.vm.chain) (hready : CountBackReady x) :
    PalPeg.PhysicalCacheMachine.CountWatchEntry x := by
  obtain ⟨hmode, hclock, v, h, lag, credit, ver, hback, hfirst⟩ := hready
  rw [hback] at hb
  obtain ⟨first, last, xs, hv⟩ := PalPeg.PhysicalChainShape.first_shape hb hfirst
  exact ⟨hmode, hclock, first, last, xs, h, lag, credit, ver, by rw [← hv]; exact hback⟩

/-- Shift bypasses count preparation, watch entry and clock decrement. -/
theorem selected_shift (rest : RestCommands) (p : CoreState) (hmode : p.1.ctl.mode = .shift) :
    (PalPeg.PhysicalCacheMachine.activeStep rest).apply blankM p none =
      (workStep rest).apply blankM p none := by
  have hc : countRead p.1 (fun j => readWin blankM macroRadius (p.2 j)) = false := by
    simp only [countRead, hmode, reduceCtorEq, decide_false, Bool.false_and]
  have he : PalPeg.PhysicalWatchEntry.entryRead p.1
      (fun j => readWin blankM macroRadius (p.2 j)) = false := by
    simp only [PalPeg.PhysicalWatchEntry.entryRead, hc, Bool.false_and]
  have hp : PalPeg.PhysicalCacheMachine.prepareRead p.1
      (fun j => readWin blankM macroRadius (p.2 j)) = false := by
    simp only [PalPeg.PhysicalCacheMachine.prepareRead, hc, Bool.false_and]
  rw [PalPeg.PhysicalCacheMachine.activeStep, PalPeg.PhysicalWatchEntry.withWatchEntry,
    branch_apply, he, if_neg Bool.false_ne_true, branch_apply, hp,
    if_neg Bool.false_ne_true, counted_apply, hc, if_neg Bool.false_ne_true]

/-- The entire shift mode, including exhaustion, on the same routed machine
and encoding. Both run-side conditions are supplied from the consumer's OnRun. -/
theorem forward_shift (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : PalPeg.PhysicalRoles.PhysicalState) (he : Enc w x p)
    (hmode : x.ctl.mode = .shift) (hs : PalPeg.FrameFunction.starvedTest x = false)
    (hcopy : CopyIdle x.vm) (hbound : PalPeg.PhysicalShift.RemainingBound x) {y : State GalilVM}
    (htick : Tick (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x y) :
    Enc w (PalPeg.PhysicalCacheMachine.successor w x) ((machine rest).apply blankM p none) := by
  change PalPeg.PhysicalCacheInvariant.Enc w _ (PalPeg.LocalRoleRouting.decode _)
  rw [decode_machine]
  rcases p with ⟨⟨roles, q⟩, T⟩
  cases q with
  | inl tag => rw [he.1, initial_starved] at hs; cases hs
  | inr q =>
    let U := fun j => T (roles j)
    have hcore := running_core he
    have hm : q.ctl.mode = .shift := by
      obtain ⟨ideal, hi, _⟩ := hcore
      have hc := congrArg PalPeg.GalilScaffoldController.Control.mode hi.1.1.ctl
      exact hc.trans hmode
    have hchange : boundaryRead q (fun j => readWin blankM macroRadius (U j)) = false := by
      simp only [boundaryRead, PalPeg.PhysicalCacheMachine.prepareRead, countRead,
        hm, reduceCtorEq, decide_false, Bool.false_and, Bool.and_false]
    change PalPeg.PhysicalCacheInvariant.Enc w _
      (completedOuter (boundaryRead q (fun j => readWin blankM macroRadius (U j)))
        ((PalPeg.PhysicalCacheMachine.machine rest).apply blankM (.inr q, U) none))
    rw [hchange, completedOuter, if_neg Bool.false_ne_true,
      PalPeg.PhysicalCacheMachine.machine, apply_active _ w x (q, U) hcore hs,
      selected_shift rest (q, U) hm]
    have hout := PalPeg.PhysicalShift.running_mode rest w x (q, U) he hmode hcopy hbound htick
    generalize hstep : (workStep rest).apply blankM (q, U) none = result at hout ⊢
    exact hout

/-- info: 'PalPeg.PhysicalBoundaryCount.forward_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forward_shift

/-- The abstract guard of the now-connected moving shift case. -/
def ShiftMoving (x : State GalilVM) : Prop :=
  x.ctl.mode = .shift ∧ (PalPeg.GalilTickFun3.ShiftRemaining x.vm ∨
    PalPeg.GalilTickFun3.CopyRemaining x.vm)

/-- This is exactly the merged frame guard; the copy alternative is not discarded. -/
theorem shiftMoving_iff (w : List (Fin 2)) (x : State GalilVM) :
    ShiftMoving x ↔ x.ctl.mode = .shift ∧
      (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0).remainingPos x.vm := by
  rfl

/-- The final contract uses the actual role-changing machine for every case. -/
theorem cases_of_remaining (rest : RestCommands)
    (hother : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC 0 1 0 w st Tc → CanonTrace 0 w st Tc →
      ∀ (m : Mirrored1 (tapeCount 0)) (p : PalPeg.PhysicalRoles.PhysicalState),
        PalPeg.LocalShadowConcrete.ArrivedOnRun (localGood (spare := 0)) (postPhase 0 1 0) w (heldAfter (Tc w.length) st) m →
        ¬ frozenAt w m → Enc w (absSC m) p →
        PalPeg.FrameFunction.starvedTest (absSC m) = false →
        Tick (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 (absSC m)
          (successor w (absSC m)) →
        ¬ CountAtRest (absSC m) → ¬ CountWatch (absSC m) → ¬ CountBackReady (absSC m) →
        (absSC m).ctl.mode ≠ .shift →
        Enc w (successor w (absSC m)) ((machine rest).apply blankM p none)) :
    TickCases (machine rest) blankM Enc := by
  constructor
  · intro w st Tc hpre hcanon m p hon hnotFrozen he hs
    exact forward_starved rest w (absSC m) p he hs
  · intro w st Tc hpre hcanon m p hon hnotFrozen he hs htick
    by_cases hrest : CountAtRest (absSC m)
    · obtain ⟨hmode, hclock, hidle, hsearch⟩ := hrest
      exact forward_atRest rest w (absSC m) p he hmode hs hclock hidle hsearch
    · by_cases hwatch : CountWatch (absSC m)
      · obtain ⟨hmode, hclock, wm, hchain⟩ := hwatch
        exact forward_watch rest w (absSC m) p he hmode hs hclock htick wm hchain
      · by_cases hentry : CountBackReady (absSC m)
        · have hperiod := PalPeg.PhysicalChainShape.period_onRun w st Tc hpre m hon.onRun hnotFrozen
          obtain ⟨hmode, hclock, first, last, xs, h, lag, credit, ver, hback⟩ :=
            entry_of_backReady hperiod.1 hentry
          exact (forward_entry rest w (absSC m) p he first last xs h lag credit ver hback
            hmode hs hclock hperiod.2).1
        · by_cases hshift : (absSC m).ctl.mode = .shift
          · exact forward_shift rest w (absSC m) p he hshift hs
              (PalPeg.PhysicalShift.copyIdle_onRun w st Tc hpre m hon.onRun hnotFrozen hshift)
              (PalPeg.PhysicalShift.remainingBound_onRun w st Tc hpre m hon.onRun hnotFrozen) htick
          · exact hother w st Tc hpre hcanon m p hon hnotFrozen he hs htick hrest hwatch hentry hshift

/-- info: 'PalPeg.PhysicalBoundaryCount.cases_of_remaining' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cases_of_remaining

end PalPeg.PhysicalBoundaryCount
