import PalPeg.PhysicalSnapshotEntry

/-! # Snapshot-preserving shift entry through all twelve view slots -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PalPeg.PhysicalSnapshotEntryTick
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract
open PalPeg.PhysicalSearchSnapshots (saved put)
open PalPeg.PhysicalCacheInvariant (Running CoreInv running_core)
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilScaffoldCounter (Counter)
open PalPeg.ChainBoundaryCache (Inv)
open PalPeg.Program PalPeg.Local PalPeg.CloseoutCoreEnc12 PalPeg.LocalStepFusion
open PalPeg.GalilScaffoldChainVerifier (canRight)
open PalPeg.PhysicalShiftStart (entryState)
open PalPeg.PhysicalWatchStep (afterInternal)
open PalPeg.PhysicalSnapshotWatch (goodSpare goodAge)
open PalPeg.PhysicalShiftTick (commands moved)

noncomputable def row (consume : Bool) : ActRule (Fin 2) CoreControl Γm tapeCountM microRadius :=
  PalPeg.LocalRoleFusion.flatten (PalPeg.PhysicalSnapshotEntry.plan consume)

noncomputable def roles (consume : Bool) :
    PalPeg.LocalRoleRouting.RoleChange (Fin 2) CoreControl Γm tapeCountM microRadius :=
  PalPeg.LocalRoleFusion.finalRoles (PalPeg.PhysicalSnapshotEntry.plan consume)

noncomputable def next (consume : Bool) (q : CoreControl) (input : Option (Fin 2))
    (ws : Fin tapeCountM → Window Γm microRadius) : CoreControl :=
  {(row consume).nq q input ws with onLetterBit := scanRightOnLetter q ws, leftFirstBit := scanLeftFirst q ws}

noncomputable def rule (consume : Bool) : ActRule (Fin 2) CoreControl Γm tapeCountM microRadius :=
  tickRule (by decide) (next consume) (fun _ _ _ => commands consume) (row consume).acts (row consume).len_le

theorem roles_head (consume : Bool) (q : CoreControl) (input : Option (Fin 2))
    (ws : Fin tapeCountM → Window Γm microRadius) (v : Fin 4) (i : Fin 12) :
    roles consume q input ws (slotIndex (headSlot v i)) = slotIndex (headSlot v i) := by
  have hentry : PalPeg.PhysicalShiftEntry.entryRoles (slotIndex (headSlot v i)) = slotIndex (headSlot v i) := by
    apply PalPeg.PhysicalShiftEntry.roles_other
    all_goals intro h; have hh := slotIndex.injective h; simp [headSlot, counterSlot, mirrorSlot] at hh
  have hsnapshot : PalPeg.PhysicalSearchSnapshots.rotateRoles (slotIndex (headSlot v i)) = slotIndex (headSlot v i) := by
    simp only [PalPeg.PhysicalSearchSnapshots.rotateRoles, Equiv.trans_apply, Equiv.symm_apply_apply]
    rw [PalPeg.PhysicalSearchSnapshots.rotate_other _ rfl]
  have hboundary : PalPeg.PhysicalRoles.boundaryRoles (slotIndex (headSlot v i)) = slotIndex (headSlot v i) := by
    apply PalPeg.PhysicalRoles.boundaryRoles_other
    all_goals intro h; have hh := slotIndex.injective h; simp [headSlot, counterSlot] at hh
  have hchange {K : ℕ} (c : CoreControl) (a : Option (Fin 2)) (windows : Fin tapeCountM → Window Γm K) :
      PalPeg.PhysicalSnapshotWatch.change c a windows (slotIndex (headSlot v i)) = slotIndex (headSlot v i) := by
    simp only [PalPeg.PhysicalSnapshotWatch.change]
    split <;> simp only [Equiv.trans_apply, hsnapshot, hboundary, Equiv.refl_apply]
  have hfirst (c : CoreControl) (a : Option (Fin 2)) (windows : Fin tapeCountM → Window Γm 32) :
      PalPeg.PhysicalSnapshotWatch.firstChange consume c a windows (slotIndex (headSlot v i)) = slotIndex (headSlot v i) := by
    simp only [PalPeg.PhysicalSnapshotWatch.firstChange]
    split <;> simp only [hchange, Equiv.refl_apply]
  simp only [roles, PalPeg.LocalRoleFusion.finalRoles, PalPeg.PhysicalSnapshotEntry.plan,
    PalPeg.PhysicalSnapshotWatch.plan, seqRule, PalPeg.LocalRoleFusion.routeRule,
    PalPeg.PhysicalShiftStart.entryChange, Equiv.trans_apply, hentry, hchange, hfirst, Equiv.refl_apply]

/-- Refresh the two cursor observations after an arbitrary proved storage
update; changing the dormant values does not affect either observation. -/
theorem next_control (consume : Bool) (w arrived : List (Fin 2)) (x : State GalilVM)
    (values : Fin 4 → Counter) (p : CoreState) (henc : CoreEnc w x p)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (q : CoreControl)
    (hcontrol : EncControl w (entryState consume (put x values) wm) q)
    (hright : canRight x.vm.right)
    (hrep : PalPeg.GalilScaffoldInputTrace.Represents x.vm.right.head arrived)
    (hlen : arrived.length ≤ w.length) :
    EncControl w (moved consume (put x values) wm)
      {q with onLetterBit := scanRightOnLetter p.1 (fun j => readWin blankM microRadius (p.2 j)), leftFirstBit := scanLeftFirst p.1 (fun j => readWin blankM microRadius (p.2 j))} := by
  refine ⟨hcontrol.ctl, hcontrol.chainTag, hcontrol.chainPhase, hcontrol.chainForward, hcontrol.chainBroken,
    hcontrol.fppMode, hcontrol.fppFinalStage, hcontrol.fppPc, hcontrol.fppDone, hcontrol.dpPc, hcontrol.dpDone,
    hcontrol.searchMode, hcontrol.searchFinalStage, hcontrol.searchQuarter, hcontrol.periodOnly, ?_, ?_, ?_⟩
  · intro i place hp
    apply hcontrol.placeGap i place
    fin_cases i <;> exact hp
  · let T := fun slot => p.2 (slotIndex slot)
    have ht : tapesOf T = p.2 := by funext j; simp [T, tapesOf]
    have hread := scanRightOnLetter_eq w arrived henc.1.2 micro_le_margin hright hrep hlen
    rw [ht] at hread
    exact hread
  · let T := fun slot => p.2 (slotIndex slot)
    have ht : tapesOf T = p.2 := by funext j; simp [T, tapesOf]
    have hread := scanLeftFirst_eq henc.1.2 (by decide : 1 ≤ microRadius) micro_le_margin
    rw [ht] at hread
    exact hread

/-- All three moving cursors and the nonhead copy updates share the existing
twelve-slot execution. The target storage values come from the source plan. -/
theorem running_ideal (consume : Bool) (w arrived : List (Fin 2)) (x : State GalilVM)
    (p : CoreState) (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm)
    (spare : Counter) (h age : ℕ) (hInv : Inv h age wm.machine.control spare)
    (henc : CoreInv w (saved x wm.machine.control.boundary wm.machine.control.last spare) p)
    (hmode : x.ctl.mode = .scan)
    (hfirst : consume = true → PalPeg.GalilScaffoldChainWatch.Good wm)
    (hsecond : PalPeg.GalilScaffoldChainWatch.Good (afterInternal consume wm))
    (hright : canRight x.vm.right)
    (hrep : PalPeg.GalilScaffoldInputTrace.Represents x.vm.right.head arrived)
    (hlen : arrived.length ≤ w.length) :
    let watched := PalPeg.GalilScaffoldChainWatch.immediate (afterInternal consume wm)
    let result := idealRun (rule consume) blankM p none 12
    Running w (saved (moved consume x wm) watched.machine.control.boundary watched.machine.control.last
      (goodSpare consume wm spare))
      (result.1, fun j => result.2 (roles consume p.1 none (fun k => readWin blankM microRadius (p.2 k)) j)) := by
  dsimp only
  generalize htrajectory : idealRun (rule consume) blankM p none = trajectory
  let sx := saved x wm.machine.control.boundary wm.machine.control.last spare
  let watched := PalPeg.GalilScaffoldChainWatch.immediate (afterInternal consume wm)
  let values : Fin 4 → Counter := fun i => if i = 0 then watched.machine.control.boundary
    else if i = 1 then watched.machine.control.last else goodSpare consume wm spare
  let tx := put sx values
  have hsource : Running w sx p := ⟨p.2, henc, fun _ => ⟨rfl, fun _ => rfl⟩⟩
  have hnonhead := (PalPeg.PhysicalSnapshotEntry.running_ideal consume w x p wm hchain
    spare h age hInv hsource hmode hfirst hsecond).2
  have hcontrol : EncControl w (entryState consume tx wm)
      ((row consume).nq p.1 none (fun j => readWin blankM microRadius (p.2 j))) := by
    obtain ⟨_, hi, _⟩ := hnonhead
    exact hi.1.1.1.1
  have hrun := PalPeg.PhysicalTickAssembly.running_tick (row consume) (roles consume) (next consume)
    (fun _ _ _ => commands consume) w sx (entryState consume tx wm) (moved consume tx wm) p none
    henc.1.1 hnonhead (roles_head consume p.1 none _) ⟨rfl, rfl, rfl⟩
    (next_control consume w arrived sx values p henc.1.1 wm _ hcontrol hright hrep hlen)
    (PalPeg.PhysicalShiftTick.headMove consume) (PalPeg.PhysicalShiftTick.headOp_commands consume)
    (fun v => by rw [PalPeg.PhysicalShiftTick.moved_heads consume tx wm hchain v]; simp only [Option.isSome_map]; rfl)
    (fun v head hh => by rw [PalPeg.PhysicalShiftTick.moved_heads consume tx wm hchain v]; rw [show headOf tx v = some head from hh]; rfl)
    (PalPeg.PhysicalShiftTick.source_heads sx wm hchain)
    (PalPeg.PhysicalShiftTick.ready consume sx wm hchain hright hfirst hsecond)
    (fun _ => rfl) (fun _ => rfl) (PalPeg.PhysicalShiftTick.moved_counters consume tx wm) rfl rfl rfl
    (PalPeg.PhysicalShiftTick.moved_cache consume tx wm)
  generalize hother : idealRun (tickRule (by decide : 2 ≤ microRadius) (next consume)
    (fun _ _ _ => commands consume) (row consume).acts (row consume).len_le)
    blankM p none = other at hrun
  have heq : other = trajectory := hother.symm.trans htrajectory
  rw [heq] at hrun
  exact hrun

noncomputable def step (consume : Bool) :
    PalPeg.Local.LocalStep (Fin 2) (PalPeg.LocalRoleRouting.Control CoreControl tapeCountM) Γm tapeCountM macroRadius :=
  PalPeg.LocalRoleRouting.route (compStep (iterRule (rule consume) 12))
    (PalPeg.PhysicalTickAssembly.macroRoles (roles consume))

/-- One real macro sweep includes the original view moves and every restart
snapshot update, at the unchanged radius 1536. -/
theorem running (consume : Bool) (w arrived : List (Fin 2)) (x : State GalilVM)
    (p : PalPeg.PhysicalShiftDispatch.RoutedCore)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm)
    (spare : Counter) (h age : ℕ) (hInv : Inv h age wm.machine.control spare)
    (henc : Running w (saved x wm.machine.control.boundary wm.machine.control.last spare)
      (PalPeg.LocalRoleRouting.decode p)) (hmode : x.ctl.mode = .scan)
    (hfirst : consume = true → PalPeg.GalilScaffoldChainWatch.Good wm)
    (hsecond : PalPeg.GalilScaffoldChainWatch.Good (afterInternal consume wm))
    (hright : canRight x.vm.right)
    (hrep : PalPeg.GalilScaffoldInputTrace.Represents x.vm.right.head arrived)
    (hlen : arrived.length ≤ w.length) :
    let watched := PalPeg.GalilScaffoldChainWatch.immediate (afterInternal consume wm)
    Inv h (goodAge consume wm age) watched.machine.control (goodSpare consume wm spare) ∧
      Running w (saved (moved consume x wm) watched.machine.control.boundary watched.machine.control.last
        (goodSpare consume wm spare)) (PalPeg.LocalRoleRouting.decode ((step consume).apply blankM p none)) := by
  have hnextInv := (PalPeg.PhysicalSnapshotEntry.running_ideal consume w x
    (PalPeg.LocalRoleRouting.decode p) wm hchain spare h age hInv henc hmode hfirst hsecond).1
  refine ⟨hnextInv, ?_⟩
  exact PalPeg.PhysicalTickAssembly.running_fused_route (rule consume) (roles consume)
    w _ _ p none henc (fun T hT => running_ideal consume w arrived x (_, T) wm hchain
      spare h age hInv hT hmode hfirst hsecond hright hrep hlen)

/-- info: 'PalPeg.PhysicalSnapshotEntryTick.running' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms running

end PalPeg.PhysicalSnapshotEntryTick
