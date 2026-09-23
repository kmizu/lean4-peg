import PalPeg.PhysicalBootFeed

/-!
# The outer none-step dispatcher

The physical starvation test uses the same source windows as the scan phase.
It takes priority over restart and count. The active step is an explicit data
parameter until the remaining mode rows have been connected; boot and feed
remain the already verified branches of the same machine.
-/
set_option autoImplicit false

namespace PalPeg.PhysicalTickDispatch
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract PalPeg.PhysicalBootFeed
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilFinalAssembly2 (centreC placeC)
open PalPeg.Program (STape)
open PalPeg.Local (LocalStep readWin)

/-- The second half-step only changes which value of the gap bit permits a move. -/
noncomputable def availableAfterRight {K : ℕ} (q : CoreControl)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) (v : Fin 4) : Bool :=
  let tops := PalPeg.ConcreteLocalMachine.viewTopsOfWindows (q.micro v).2.1 (viewWindows v ws)
  q.gap v || tops.near.isSome || tops.front.isSome

theorem availableAfterRight_eq {K : ℕ} {x : State GalilVM} {q : CoreControl}
    {T : Slot → STape Γm}
    (henc : EncTapes margin x q.polarity q.gap q.micro q.fppLive q.dpLive T)
    (hmargin : K ≤ margin) (v : Fin 4) (head : PalPeg.GalilScaffoldInputHead.PlaceHead)
    (hhead : headOf x v = some head) :
    availableAfterRight q (fun tape => readWin blankM K (tapesOf T tape)) v =
      canRightTest (PalPeg.GalilScaffoldChainVerifier.right head) := by
  obtain ⟨view, viewTapes, habs, hrep, hslots, hcells, hwf⟩ := henc.heads v head hhead
  have htops := PalPeg.ConcreteLocalMachine.viewTopsOfWindows_eq hmargin hcells hrep
  unfold availableAfterRight
  rw [viewWindows_of_encoded v T viewTapes hslots, htops, hrep.gap, ← habs]
  obtain ⟨letters, hnear⟩ := PalPeg.LocalViewCells.near_letters hcells
  cases hgap : view.gap <;>
    simp [PalPeg.ConcreteLocalMachine.viewTops, PalPeg.RTQueue.head?_eq hwf,
      PalPeg.LocalArrival.absHead', canRightTest, PalPeg.GalilScaffoldChainVerifier.right,
      hgap, hnear]
  cases letters <;> cases PalPeg.RTQueue.toList view.far <;> simp

/-- `remainsTest` already combines the shift and copy remaining-work tests. -/
noncomputable def starvedRead {K : ℕ} (q : CoreControl)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) : Bool :=
  PalPeg.FrameFunction.starvedOf q.ctl.mode
    (availableTest q ws 2) (availableTest q ws 1) (availableTest q ws 0)
    (availableAfterRight q ws 0) (remainsTest q.polarity ws) false

theorem starvedRead_eq {K : ℕ} {w : List (Fin 2)} {x : State GalilVM}
    {q : CoreControl} {T : Slot → STape Γm}
    (henc : PalPeg.PhysicalEncoding.Enc w margin x (q, T))
    (hK : 1 ≤ K) (hmargin : K ≤ margin) :
    starvedRead q (fun tape => readWin blankM K (tapesOf T tape)) =
      PalPeg.FrameFunction.starvedTest x := by
  have hmode := congrArg PalPeg.GalilScaffoldController.Control.mode henc.1.ctl
  change q.ctl.mode = x.ctl.mode at hmode
  unfold starvedRead
  rw [hmode, availableTest_eq henc.2 hmargin 2 x.vm.right rfl,
    availableTest_eq henc.2 hmargin 1 x.vm.center rfl,
    availableTest_eq henc.2 hmargin 0 x.vm.left rfl,
    availableAfterRight_eq henc.2 hmargin 0 x.vm.left rfl,
    remainsTest_eq henc.2 hK hmargin centreC placeC 0 1 0 w]
  simp only [PalPeg.FrameFunction.starvedTest, PalPeg.FrameFunction.starvedOf,
    PalPeg.FrameFunction.galilFrameFun, Bool.or_false]

/-- Every window observable can be transported from the ideal encoding to its sweep closure. -/
theorem read_from_running {K : ℕ} (observe : CoreControl →
    (Fin tapeCountM → PalPeg.Local.Window Γm K) → Bool)
    (spec : State GalilVM → Bool) (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (henc : PalPeg.MachineStep.sweepClosure blankM (CoreEnc w) x p)
    (hexact : ∀ T, CoreEnc w x (p.1, T) →
      observe p.1 (fun tape => readWin blankM K (T tape)) = spec x) :
    observe p.1 (fun tape => readWin blankM K (p.2 tape)) = spec x := by
  obtain ⟨T, hT, hteq⟩ := henc
  have hws : (fun tape => readWin blankM K (p.2 tape)) =
      (fun tape => readWin blankM K (T tape)) := by
    funext tape
    exact (readWin_congr_teqG (hteq tape)).symm
  rw [hws]
  exact hexact T hT

theorem starvedRead_running {w : List (Fin 2)} {x : State GalilVM} {p : CoreState}
    (henc : PalPeg.MachineStep.sweepClosure blankM (CoreEnc w) x p) :
    starvedRead p.1 (fun tape => readWin blankM macroRadius (p.2 tape)) =
      PalPeg.FrameFunction.starvedTest x := by
  apply read_from_running starvedRead PalPeg.FrameFunction.starvedTest w x p henc
  intro T hT
  simpa only [tapesOf, Equiv.apply_symm_apply] using
    starvedRead_eq hT.1 (by decide : 1 ≤ macroRadius) (le_refl margin)

noncomputable def branchStep
    (test : CoreControl → (Fin tapeCountM → PalPeg.Local.Window Γm macroRadius) → Bool)
    (yes no : CoreStep) : CoreStep where
  next := fun q input ws => if test q ws then yes.next q input ws else no.next q input ws
  disp_le := by
    intro q input ws tape
    split
    · exact yes.disp_le q input ws tape
    · exact no.disp_le q input ws tape

theorem branch_apply
    (test : CoreControl → (Fin tapeCountM → PalPeg.Local.Window Γm macroRadius) → Bool)
    (yes no : CoreStep) (p : CoreState) (input : Option (Fin 2)) :
    (branchStep test yes no).apply blankM p input =
      if test p.1 (fun tape => readWin blankM macroRadius (p.2 tape)) then
        yes.apply blankM p input else no.apply blankM p input := by
  by_cases h : test p.1 (fun tape => readWin blankM macroRadius (p.2 tape)) = true
  · simp only [LocalStep.apply, branchStep, h, if_true]
  · simp only [LocalStep.apply, branchStep, h, Bool.false_eq_true, if_false]

noncomputable def guardedStep (active : CoreStep) : CoreStep :=
  branchStep starvedRead feedStep active

theorem guarded_apply (active : CoreStep) (p : CoreState) (input : Option (Fin 2)) :
    (guardedStep active).apply blankM p input =
      if starvedRead p.1 (fun tape => readWin blankM macroRadius (p.2 tape)) then
        feedStep.apply blankM p input else active.apply blankM p input :=
  branch_apply starvedRead feedStep active p input

noncomputable def machine (active : CoreStep) := machineStep (guardedStep active)

/-- The entire starved case of the final none-step contract, with no run-side premise. -/
theorem forward_starved (active : CoreStep) (w : List (Fin 2))
    (x : State GalilVM) (p : PhysicalState)
    (henc : PalPeg.PhysicalContract.Enc w x p)
    (hstarved : PalPeg.FrameFunction.starvedTest x = true) :
    PalPeg.PhysicalContract.Enc w x ((machine active).apply blankM p none) := by
  rcases p with ⟨q, T⟩
  cases q with
  | inl bootTag =>
    cases bootTag
    have hx := henc.1
    subst x
    exact boot_none (guardedStep active) w T henc
  | inr control =>
    simp only [machine, machine_apply_none (guardedStep active) (control, T)]
    rw [enc_running, guarded_apply, starvedRead_running henc, if_pos hstarved]
    exact PalPeg.PhysicalFeed.running_feed w x (control, T) none henc

/-- Source-window dispatch under nonstarvation exposes the same active step.
Restart/count/comparison are classified inside that step, after this guard. -/
theorem apply_active (active : CoreStep) (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (henc : PalPeg.MachineStep.sweepClosure blankM (CoreEnc w) x p)
    (hstarved : PalPeg.FrameFunction.starvedTest x = false) :
    (machine active).apply blankM (Sum.inr p.1, p.2) none =
      (Sum.inr (active.apply blankM p none).1, (active.apply blankM p none).2) := by
  simp only [machine, machine_apply_none, guarded_apply, starvedRead_running henc, hstarved,
    Bool.false_eq_true, if_false]

/-- info: 'PalPeg.PhysicalTickDispatch.forward_starved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forward_starved

end PalPeg.PhysicalTickDispatch
