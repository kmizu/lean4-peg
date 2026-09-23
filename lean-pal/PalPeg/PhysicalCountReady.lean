import PalPeg.PhysicalScanCount

/-!
# Readiness supplied by the existing relational tick

The final consumer already supplies a legal abstract tick. A positive-lag
watching chain can only take a verifier-consuming constructor when its verifier
can advance. Retaining that proof avoids a second derivation from the trace.
-/
set_option autoImplicit false

namespace PalPeg.PhysicalCountReady
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilScaffoldChainVerifier (canRight)
open PalPeg.GalilFinalAssembly2 (centreC placeC)

theorem verifier_canRight_of_background (P : Shared) (q : ℕ) (first : Fin 9)
    {s t : GalilVM} (hbg : (galilFrameS P q first).background s t)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : s.chain = .watch wm)
    (hlag : PalPeg.GalilScaffoldCounter.positive wm.lag = true) :
    canRight wm.machine.verifier := by
  obtain ⟨mid, hstep, _⟩ := backgroundS_chainTick P q first hbg
    (by rw [hchain]; exact fun h => ChainVM.noConfusion h)
  rw [hchain] at hstep
  cases hstep with
  | watchStep _ _ hi =>
    cases hi with
    | idle hz => simp [hlag] at hz
    | take _ hgood => exact hgood.1
  | watchBreak _ hb => exact hb.2.1

theorem verifier_canRight_of_countTick (w : List (Fin 2))
    {x y : State GalilVM}
    (htick : Tick (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x y)
    (hmode : x.ctl.mode = .scan) (hclock : 1 < x.ctl.clock)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm)
    (hlag : PalPeg.GalilScaffoldCounter.positive wm.lag = true) :
    canRight wm.machine.verifier := by
  cases htick <;> simp_all
  all_goals first
    | exact verifier_canRight_of_background _ 1 0 ‹_› wm hchain hlag
    | skip
  case restart c s t hm hb =>
    change restartVM 0 s t at hb
    obtain ⟨wm', hbroken, _⟩ := hb
    rw [hchain] at hbroken
    cases hbroken

open PalPeg.PhysicalEncoding PalPeg.PhysicalContract

/-- The view assembler quantifies over any represented view. Its availability
comes from the window observable, so no uniqueness of a view representation or
literal equality of swept tapes is required. -/
theorem moveRight_ready {K : ℕ} {x : State GalilVM} {q : CoreControl}
    {T : Slot → PalPeg.Program.STape Γm}
    (henc : EncTapes margin x q.polarity q.gap q.micro q.fppLive q.dpLive T)
    (hmargin : K ≤ margin) (v : Fin 4) (head : PalPeg.GalilScaffoldInputHead.PlaceHead)
    (hhead : headOf x v = some head) (hcan : canRight head)
    (view : PalPeg.LocalInputView.InputView)
    (hview : HeadSlotsRepAt margin q.gap q.micro T v view) : HeadReady .moveRight view := by
  obtain ⟨viewTapes, hrep, hslots, hcells, hwf⟩ := hview
  have htops : PalPeg.ConcreteLocalMachine.viewTopsOfWindows (q.micro v).2.1
      (viewWindows v (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)))
        = PalPeg.ConcreteLocalMachine.viewTops view := by
    rw [viewWindows_of_encoded v T viewTapes hslots]
    exact PalPeg.ConcreteLocalMachine.viewTopsOfWindows_eq hmargin hcells hrep
  have htest := availableTest_of_view q _ v view htops hrep.gap hcells hwf
  rw [availableTest_eq henc hmargin v head hhead] at htest
  have hav := (canRightTest_iff _).mpr (htest.symm.trans ((canRightTest_iff _).mp hcan))
  intro hgap hnear
  simpa [canRight, PalPeg.LocalArrival.absHead', hgap, hnear] using hav

/-- info: 'PalPeg.PhysicalCountReady.verifier_canRight_of_countTick' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms verifier_canRight_of_countTick

/-- info: 'PalPeg.PhysicalCountReady.moveRight_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms moveRight_ready

end PalPeg.PhysicalCountReady
