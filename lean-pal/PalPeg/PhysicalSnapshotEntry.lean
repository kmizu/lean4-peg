import PalPeg.PhysicalSnapshotWatch

/-! # Restart snapshots through the complete shift-entry nonhead plan

The two comparison quanta and the existing common entry row use 32+32+64
cells of lookaround, within the unchanged micro radius 128.
-/
set_option autoImplicit false
namespace PalPeg.PhysicalSnapshotEntry
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract
open PalPeg.PhysicalSearchSnapshots (saved put)
open PalPeg.PhysicalCacheInvariant (Running running_core)
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilScaffoldCounter (Counter)
open PalPeg.ChainBoundaryCache (Inv)
open PalPeg.Program PalPeg.Local PalPeg.CloseoutCoreEnc12 PalPeg.LocalStepFusion
open PalPeg.LocalRoleFusion (logicalStep routeRule)
open PalPeg.PhysicalShiftStart (entryState pairedState entryRule entryChange)
open PalPeg.PhysicalWatchStep (afterInternal)
open PalPeg.PhysicalSnapshotWatch (goodSpare goodAge)

noncomputable def plan (consume : Bool) :
    ActRule (Fin 2) (PalPeg.LocalRoleRouting.Control CoreControl tapeCountM) Γm tapeCountM microRadius :=
  seqRule (PalPeg.PhysicalSnapshotWatch.plan consume) (routeRule entryRule entryChange)

theorem plan_ideal (consume : Bool) (p : CoreState)
    (hmargin : ∀ j, microRadius ≤ pos (p.2 j)) :
    PalPeg.LocalRoleRouting.decode (idealStep (plan consume) blankM ((Equiv.refl _, p.1), p.2) none) =
      logicalStep entryRule entryChange blankM
        (PalPeg.LocalRoleRouting.decode (idealStep (PalPeg.PhysicalSnapshotWatch.plan consume)
          blankM ((Equiv.refl _, p.1), p.2) none)) none := by
  have hseq := seqRule_ideal blankM (PalPeg.PhysicalSnapshotWatch.plan consume)
    (routeRule entryRule entryChange) ((Equiv.refl _, p.1), p.2) none hmargin
  exact (congrArg PalPeg.LocalRoleRouting.decode hseq).trans
    (PalPeg.LocalRoleFusion.decode_routeRule entryRule entryChange blankM _ none)

/-- Entry changes the common counters and lends the h mirror to remaining;
all six prepared snapshot tapes retain their canonical values. -/
theorem running_ideal (consume : Bool) (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm)
    (spare : Counter) (h age : ℕ) (hInv : Inv h age wm.machine.control spare)
    (henc : Running w (saved x wm.machine.control.boundary wm.machine.control.last spare) p)
    (hmode : x.ctl.mode = .scan)
    (hfirst : consume = true → PalPeg.GalilScaffoldChainWatch.Good wm)
    (hsecond : PalPeg.GalilScaffoldChainWatch.Good (afterInternal consume wm)) :
    let next := PalPeg.GalilScaffoldChainWatch.immediate (afterInternal consume wm)
    Inv h (goodAge consume wm age) next.machine.control (goodSpare consume wm spare) ∧
      Running w (saved (entryState consume x wm) next.machine.control.boundary next.machine.control.last (goodSpare consume wm spare))
        (PalPeg.LocalRoleRouting.decode (idealStep (plan consume) blankM ((Equiv.refl _, p.1), p.2) none)) := by
  obtain ⟨hnextInv, hpair⟩ := PalPeg.PhysicalSnapshotWatch.running_good_ideal
    consume w x p wm hchain spare h age hInv henc hfirst hsecond
  let next := PalPeg.GalilScaffoldChainWatch.immediate (afterInternal consume wm)
  let held := {next with machine := {next.machine with verifier := wm.machine.verifier}}
  let sx := saved (pairedState consume x wm) next.machine.control.boundary next.machine.control.last (goodSpare consume wm spare)
  have hwatch : sx.vm.chain = .watch held := by
    simp [sx, saved, put, PalPeg.PhysicalRestartStorage.replace, pairedState,
      stepState, chainVerifierBack, held, next]
  have hentry := PalPeg.PhysicalShiftStart.running_entry w sx _ hpair
    (by change x.ctl.mode ≠ .shift; rw [hmode]; decide) held hwatch
  have hmargin : ∀ j, microRadius ≤ pos (p.2 j) := fun j =>
    micro_le_margin.trans (running_margin (running_core henc) j)
  refine ⟨hnextInv, ?_⟩
  rw [plan_ideal consume p hmargin]
  exact hentry

/-- One real sweep runs the complete nonhead entry plan, including the two
possible snapshot rotations and the remaining/h-mirror role swap. -/
theorem running (consume : Bool) (w : List (Fin 2)) (x : State GalilVM)
    (p : PalPeg.PhysicalShiftDispatch.RoutedCore)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm)
    (spare : Counter) (h age : ℕ) (hInv : Inv h age wm.machine.control spare)
    (henc : Running w (saved x wm.machine.control.boundary wm.machine.control.last spare)
      (PalPeg.LocalRoleRouting.decode p)) (hmode : x.ctl.mode = .scan)
    (hfirst : consume = true → PalPeg.GalilScaffoldChainWatch.Good wm)
    (hsecond : PalPeg.GalilScaffoldChainWatch.Good (afterInternal consume wm)) :
    let next := PalPeg.GalilScaffoldChainWatch.immediate (afterInternal consume wm)
    Inv h (goodAge consume wm age) next.machine.control (goodSpare consume wm spare) ∧
      Running w (saved (entryState consume x wm) next.machine.control.boundary next.machine.control.last (goodSpare consume wm spare))
        (PalPeg.LocalRoleRouting.decode ((PalPeg.LocalRoleFusion.compiled (plan consume)).apply blankM p none)) := by
  obtain ⟨hnextInv, hideal⟩ := running_ideal consume w x (PalPeg.LocalRoleRouting.decode p)
    wm hchain spare h age hInv henc hmode hfirst hsecond
  have hmargin : ∀ j, microRadius ≤ pos ((PalPeg.LocalRoleRouting.decode p).2 j) := fun j =>
    micro_le_margin.trans (running_margin (running_core henc) j)
  obtain ⟨hcontrol, htapes⟩ := PalPeg.LocalRoleFusion.compiled_apply (plan consume) blankM p none hmargin
  refine ⟨hnextInv, ?_⟩
  exact PalPeg.MachineStep.sweepClosed_sweepClosure blankM (PalPeg.PhysicalCacheInvariant.CoreInv w)
    _ _ _ hideal hcontrol.symm htapes

/-- info: 'PalPeg.PhysicalSnapshotEntry.running' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms running

end PalPeg.PhysicalSnapshotEntry
