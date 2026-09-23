import PalPeg.PhysicalSearchSnapshots
import PalPeg.PhysicalShiftDispatch

/-! # Watch count with the independent restart snapshots

The count VM row is the existing PhysicalCountSpare.countStep. The original
boundary rotation and both additional snapshot rotations are installed by one
finite role update after that same physical sweep. No target-copy premise is
left at the concrete count interface.
-/
set_option autoImplicit false
namespace PalPeg.PhysicalSnapshotCount
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract
open PalPeg.PhysicalSearchSnapshots
open PalPeg.PhysicalSearchRecycle (resetSlot)
open PalPeg.PhysicalCacheInvariant (Running running_core)
open PalPeg.PhysicalScanCount (RestCommands countState)
open PalPeg.PhysicalCountConsume (caughtState)
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilScaffoldCounter (Counter)
open PalPeg.ChainBoundaryCache (Inv boundaryEvent nextSpare nextAge)
open PalPeg.Local (LocalStep readWin)
open PalPeg.LocalRoleRouting (decode)
open PalPeg.GalilFinalAssembly2 (centreC placeC)

/-- The old three-role permutation leaves every reclaimed carrier fixed. -/
theorem boundary_keeps (j : Fin tapeCountM) (hj : resetSlot (slotIndex.symm j) = true) :
    PalPeg.PhysicalRoles.boundaryRoles j = j := by
  apply PalPeg.PhysicalRoles.boundaryRoles_other
  all_goals
    intro he
    rw [he, Equiv.symm_apply_apply] at hj
    cases hj

/-- A permutation which fixes the selected carriers also preserves membership
of their complement. The ordinary boundary permutation therefore cannot move
any VM output into the six snapshot slots. -/
theorem mask_boundary (j : Fin tapeCountM) :
    resetSlot (slotIndex.symm (PalPeg.PhysicalRoles.boundaryRoles j)) =
      resetSlot (slotIndex.symm j) := by
  by_cases hj : resetSlot (slotIndex.symm j) = true
  · rw [boundary_keeps j hj]
  · have hn : resetSlot (slotIndex.symm (PalPeg.PhysicalRoles.boundaryRoles j)) ≠ true := by
      intro hh
      have he := PalPeg.PhysicalRoles.boundaryRoles.injective (boundary_keeps _ hh)
      rw [he] at hh
      exact hj hh
    exact (Bool.eq_false_iff.mpr hn).trans (Bool.eq_false_iff.mpr hj).symm

/-- Role exchange of the original cache commutes with overlaying the six
independent carriers. Signs and tape identities are both accounted for. -/
theorem rotate_mix (base update : CoreState) :
    PalPeg.PhysicalBoundaryRotate.rotateCore (mix base update) =
      mix (PalPeg.PhysicalBoundaryRotate.rotateCore base) update := by
  apply Prod.ext
  · simp only [PalPeg.PhysicalBoundaryRotate.rotateCore, mix,
      PalPeg.PhysicalBoundaryRotate.rotateControl, withSigns]
    congr 1
    funext c
    fin_cases c <;> rfl
  · funext j
    simp only [PalPeg.PhysicalBoundaryRotate.rotateCore, mix, mask_boundary]
    by_cases hj : resetSlot (slotIndex.symm j) = true
    · simp only [hj, if_true, boundary_keeps j hj]
    · simp only [hj, Bool.false_eq_true, if_false]

theorem completed_mix (event : Bool) (base update : CoreState) :
    PalPeg.PhysicalBoundaryCount.completed event (mix base update) =
      mix (PalPeg.PhysicalBoundaryCount.completed event base) update := by
  cases event
  · rfl
  · exact rotate_mix base update

/-- All three rotations use one role register; their carrier sets are disjoint. -/
noncomputable def jointRoles : PalPeg.PhysicalRoles.Roles :=
  rotateRoles.trans PalPeg.PhysicalRoles.boundaryRoles

def finishControl (event : Bool) (q : CoreControl) : CoreControl :=
  if event then
    let old := PalPeg.PhysicalBoundaryRotate.rotateControl q
    withSigns old (rotatedBits old)
  else q

noncomputable def signed (rest : RestCommands) (phase : Fin 5) (event : Bool) :
    PalPeg.PhysicalBootFeed.CoreStep where
  next := fun q input ws =>
    let result := (overlay (spareCounts phase) (PalPeg.PhysicalCountSpare.countStep rest)).next q input ws
    (finishControl event result.1, result.2)
  disp_le := (overlay (spareCounts phase) (PalPeg.PhysicalCountSpare.countStep rest)).disp_le

noncomputable def row (rest : RestCommands) (phase : Fin 5) (event : Bool) :=
  PalPeg.LocalRoleRouting.route (signed rest phase event)
    (fun _ _ _ => if event then jointRoles else Equiv.refl _)

theorem signed_apply (rest : RestCommands) (phase : Fin 5) (event : Bool)
    (p : CoreState) (input : Option (Fin 2)) :
    (signed rest phase event).apply blankM p input =
      (finishControl event
        ((overlay (spareCounts phase) (PalPeg.PhysicalCountSpare.countStep rest)).apply blankM p input).1,
        ((overlay (spareCounts phase) (PalPeg.PhysicalCountSpare.countStep rest)).apply blankM p input).2) := rfl

/-- The actual sweep realizes the VM update and both boundary caches together. -/
theorem decode_row (rest : RestCommands) (phase : Fin 5) (event : Bool)
    (p : PalPeg.PhysicalShiftDispatch.RoutedCore) (input : Option (Fin 2)) :
    decode ((row rest phase event).apply blankM p input) =
      completed event (PalPeg.PhysicalBoundaryCount.completed event
        ((overlay (spareCounts phase) (PalPeg.PhysicalCountSpare.countStep rest)).apply blankM (decode p) input)) := by
  rw [row, PalPeg.LocalRoleRouting.decode_route, signed_apply]
  cases event <;> rfl

/-- The count VM proof supplies the base side of snapshot maintenance. Its
verifier readiness is a source fact, already available from the legal Tick. -/
theorem running_match (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : PalPeg.PhysicalShiftDispatch.RoutedCore)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm)
    (spare : Counter) (h age : ℕ) (hi : Inv h age wm.machine.control spare)
    (he : Running w (saved x wm.machine.control.boundary wm.machine.control.last spare) (decode p))
    (hm : x.ctl.mode = .scan) (hs : PalPeg.FrameFunction.starvedTest x = false) (hc : 1 < x.ctl.clock)
    (a : Fin 3) (htok : PalPeg.GalilScaffoldChainConsume.symbol wm.machine.control.period.focus = some a)
    (hseen : PalPeg.GalilScaffoldInputHead.read
      (PalPeg.GalilScaffoldChainVerifier.right wm.machine.verifier) = some a)
    (hlag : PalPeg.GalilScaffoldCounter.positive wm.lag = true)
    (hcan : PalPeg.GalilScaffoldChainVerifier.canRight wm.machine.verifier) :
    let t := PalPeg.GalilScaffoldChainConsume.consume wm.machine.control (some a)
    Running w (saved (countState (caughtState x wm)) t.boundary t.last (nextSpare wm.machine.control spare))
      (decode ((row rest wm.machine.control.phase (boundaryEvent wm.machine.control)).apply blankM p none)) ∧
      Inv h (nextAge wm.machine.control age) t (nextSpare wm.machine.control spare) := by
  let sx := saved x wm.machine.control.boundary wm.machine.control.last spare
  have hsource : sx.vm.chain = .watch wm := hchain
  have hstarved : PalPeg.FrameFunction.starvedTest sx = false := hs
  have hbase := PalPeg.PhysicalBoundaryCount.running_match rest w sx (decode p) he hm hstarved hc
    wm hsource a htok hseen hlag hcan
  have hd : PalPeg.GalilScaffoldCounter.Canonical wm.machine.control.distance := by
    obtain ⟨T, hT, _⟩ := he
    obtain ⟨seg, ha, _⟩ := hT.1.1.1.2.counters 13 wm.machine.control.distance
      (by simp [counterOf, saved, put, PhysicalRestartStorage.replace, hchain])
    exact ha ▸ PalPeg.LocalCounter.absCtr_canonical seg _
  have hout := consume_mix w x (countState (caughtState sx wm)) (decode p) _
    wm.machine.control spare h age hi hd he hbase a htok
  rw [decode_row, overlay, overlayWith_apply]
  change Running w _ (completed _ (PalPeg.PhysicalBoundaryCount.completed _ (mix _ _))) ∧ _
  rw [completed_mix]
  simpa only [sx, saved, put, countState, caughtState, PhysicalRestartStorage.replace] using hout

/-- Finite source-window selection for the successful-watch row. -/
noncomputable def step (rest : RestCommands) :
    LocalStep (Fin 2) (PalPeg.LocalRoleRouting.Control CoreControl tapeCountM) Γm tapeCountM macroRadius where
  next := fun q input ws =>
    (row rest q.2.chainPhase
      (PalPeg.PhysicalBoundaryCount.eventRead q.2 (fun j => ws (q.1 j)))).next q input ws
  disp_le := fun q input ws j => (row rest q.2.chainPhase
    (PalPeg.PhysicalBoundaryCount.eventRead q.2 (fun k => ws (q.1 k)))).disp_le q input ws j

set_option maxRecDepth 2048 in
theorem step_apply (rest : RestCommands) (p : PalPeg.PhysicalShiftDispatch.RoutedCore)
    (input : Option (Fin 2)) :
    (step rest).apply blankM p input =
      (row rest p.1.2.chainPhase (PalPeg.PhysicalBoundaryCount.eventRead p.1.2
        (fun j => readWin blankM macroRadius ((decode p).2 j)))).apply blankM p input := by
  simp only [LocalStep.apply, step, decode]

/-- Successful count, including FIRST/LAST and either direction, on one concrete
row with no base/hbase or target-copy assumptions. -/
theorem forward_match (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : PalPeg.PhysicalShiftDispatch.RoutedCore)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm)
    (spare : Counter) (h age : ℕ) (hi : Inv h age wm.machine.control spare)
    (he : Running w (saved x wm.machine.control.boundary wm.machine.control.last spare) (decode p))
    (hm : x.ctl.mode = .scan) (hs : PalPeg.FrameFunction.starvedTest x = false) (hc : 1 < x.ctl.clock)
    {y : State GalilVM}
    (htick : Tick (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x y)
    (a : Fin 3) (htok : PalPeg.GalilScaffoldChainConsume.symbol wm.machine.control.period.focus = some a)
    (hseen : PalPeg.GalilScaffoldInputHead.read
      (PalPeg.GalilScaffoldChainVerifier.right wm.machine.verifier) = some a)
    (hlag : PalPeg.GalilScaffoldCounter.positive wm.lag = true) :
    let wm' := PalPeg.GalilScaffoldChainWatch.caught wm
    Running w (saved (PalPeg.PhysicalCacheMachine.successor w x)
      wm'.machine.control.boundary wm'.machine.control.last (nextSpare wm.machine.control spare))
      (decode ((step rest).apply blankM p none)) ∧
      Inv h (nextAge wm.machine.control age) wm'.machine.control (nextSpare wm.machine.control spare) := by
  have hcan := PalPeg.PhysicalCountReady.verifier_canRight_of_countTick w htick hm hc wm hchain hlag
  obtain ⟨hp, hb⟩ := source_reads w (saved x wm.machine.control.boundary wm.machine.control.last spare)
    (decode p) wm hchain he
  change PalPeg.PhysicalBoundaryCount.eventRead p.1.2
    (fun j => readWin blankM macroRadius ((decode p).2 j)) = _ at hb
  rw [step_apply, show p.1.2.chainPhase = wm.machine.control.phase from hp, hb]
  rw [PalPeg.PhysicalCacheMachine.match_successor w x hm hs hc wm hchain a htok hseen hlag]
  simpa only [PalPeg.GalilScaffoldChainWatch.caught, PalPeg.GalilScaffoldChainVerifier.consume, hseen] using
    running_match rest w x p wm hchain spare h age hi he hm hs hc a htok hseen hlag hcan

/-- info: 'PalPeg.PhysicalSnapshotCount.forward_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forward_match

end PalPeg.PhysicalSnapshotCount
