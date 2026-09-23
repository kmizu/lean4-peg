import PalPeg.PhysicalSpare
import PalPeg.PhysicalCountConsume

/-!
# Plain count consumption with the next-boundary spare prepared concurrently

This is the existing encoded VM step, clock decrement and spare update in one
local step of the existing radius. Its source cache invariant is retained in
the conclusion. Supplying this invariant at watch entry, preserving it in the
other branches and adding the boundary rotation remain dispatcher obligations.
-/
set_option autoImplicit false
namespace PalPeg.PhysicalCountSpare
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract PalPeg.PhysicalSpare
open PalPeg.PhysicalScanCount PalPeg.PhysicalCountConsume
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilFinalAssembly2 (centreC placeC)
open PalPeg.ChainBoundaryCache (Inv advanceCounter rate)
open PalPeg.GalilScaffoldCounter (Counter)

noncomputable def countStep (rest : RestCommands) := overlay (countedStep (workStep rest))

/-- VM, clock and spare all advance in the same physical step. The head's
availability comes from the legal abstract tick already carried by the consumer. -/
theorem forward_plain (rest : RestCommands) (w : List (Fin 2))
    (x : State GalilVM) (p : CoreState)
    (henc : PalPeg.MachineStep.sweepClosure blankM (CoreEnc w) x p)
    (hmode : x.ctl.mode = .scan) (hstarved : PalPeg.FrameFunction.starvedTest x = false)
    (hclock : 1 < x.ctl.clock) {y : State GalilVM}
    (htick : Tick (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x y)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm) (a : Fin 3)
    (htok : wm.machine.control.period.focus = .plain a)
    (hseen : PalPeg.GalilScaffoldInputHead.read
      (PalPeg.GalilScaffoldChainVerifier.right wm.machine.verifier) = some a)
    (hforward : wm.machine.control.forward = true)
    (hlag : PalPeg.GalilScaffoldCounter.positive wm.lag = true)
    (spare : Counter) (h age : ℕ) (hinv : Inv h age wm.machine.control spare)
    (hrep : Rep (p.1.polarity 10) spare (p.2 spareIndex)) :
    PalPeg.MachineStep.sweepClosure blankM (CoreEnc w) (countState (caughtState x wm))
      ((countStep rest).apply blankM p none) ∧
    ∃ nextSpare : Counter,
      Rep (((countStep rest).apply blankM p none).1.polarity 10) nextSpare
        (((countStep rest).apply blankM p none).2 spareIndex) ∧
      Inv h (age+1) (PalPeg.GalilScaffoldChainWatch.caught wm).machine.control nextSpare := by
  have hcan := PalPeg.PhysicalCountReady.verifier_canRight_of_countTick w htick hmode hclock
    wm hchain hlag
  have hrestart : restartGuardTest x.vm = false := by simp [restartGuardTest, hchain]
  have hbase : PalPeg.MachineStep.sweepClosure blankM (CoreEnc w) (countState (caughtState x wm))
      ((countedStep (workStep rest)).apply blankM p none) := by
    rw [counted_apply, countRead_running henc hmode hstarved hrestart hclock]
    simp only [if_true]
    exact running_clockDown (running_consume rest w x p henc hmode hstarved hclock
      wm hchain a htok hseen hforward hlag hcan)
  obtain ⟨hout, hspare⟩ := overlay_preserves (countedStep (workStep rest)) w
    (countState (caughtState x wm)) p spare none hbase rfl hrep
  refine ⟨hout, advanceCounter (rate wm.machine.control.phase) spare, ?_, ?_⟩
  · have hphase : p.1.chainPhase = wm.machine.control.phase := by
      obtain ⟨T, hT, _⟩ := henc
      have hp := hT.1.1.chainPhase
      rw [hchain] at hp
      exact hp
    simpa only [countStep, hphase] using hspare
  · have hconsume := PalPeg.ChainBoundaryCache.inv_consume hinv a
      (by simp only [htok, PalPeg.GalilScaffoldChainConsume.symbol])
    simpa only [PalPeg.GalilScaffoldChainWatch.caught, PalPeg.GalilScaffoldChainVerifier.consume,
      hseen, PalPeg.ChainBoundaryCache.nextAge, PalPeg.ChainBoundaryCache.nextSpare,
      PalPeg.ChainBoundaryCache.boundaryEvent, htok, PalPeg.GalilScaffoldChainPeriod.isFirst,
      PalPeg.GalilScaffoldChainConsume.isLast, Bool.false_or, Bool.false_eq_true, if_false]
      using hconsume

/-- info: 'PalPeg.PhysicalCountSpare.forward_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forward_plain

end PalPeg.PhysicalCountSpare
