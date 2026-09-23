import PalPeg.PhysicalCacheMachine

/-!
# Watch count without pending verifier work

A nonpositive lag leaves the chain untouched. The existing count rule still
performs background erasure and clock decrement, retaining the common cache.
-/
set_option autoImplicit false
namespace PalPeg.PhysicalWatchIdle
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract PalPeg.PhysicalBootFeed
open PalPeg.PhysicalScanCount PalPeg.PhysicalTickDispatch
open PalPeg.PhysicalCacheInvariant (Running running_core)
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.Local (readWin)

/-- The lag test is read from its represented signed counter, at either radius. -/
theorem noConsume {K : ℕ} {w : List (Fin 2)} {x : State GalilVM} {q : CoreControl}
    {T : Slot → PalPeg.Program.STape Γm} (he : PalPeg.PhysicalEncoding.Enc w margin x (q, T))
    (hK : 1 ≤ K) (hm : K ≤ margin)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm)
    (hlag : PalPeg.GalilScaffoldCounter.positive wm.lag = false) :
    chainConsumesTest q (fun j => readWin blankM K (tapesOf T j)) = false := by
  apply Bool.eq_false_iff.mpr
  intro ht
  have hp := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp ht).1).2
  obtain ⟨hpol, hcell⟩ := Bool.and_eq_true_iff.mp hp
  have hpositive := (counterPositive_iff_belowRead he.2 hK hm 11 wm.lag
    (by simp [counterOf, hchain])).mpr ⟨hpol, of_decide_eq_true hcell⟩
  rw [hlag] at hpositive
  cases hpositive

theorem noConsume_running {K : ℕ} (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : Running w x p) (hK : 1 ≤ K) (hm : K ≤ margin)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm)
    (hlag : PalPeg.GalilScaffoldCounter.positive wm.lag = false) :
    chainConsumesTest p.1 (fun j => readWin blankM K (p.2 j)) = false := by
  apply read_from_running chainConsumesTest (fun _ => false) w x p (running_core he)
  intro T hT
  simpa only [tapesOf, Equiv.apply_symm_apply] using noConsume hT.1 hK hm wm hchain hlag

theorem running_quiet (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : Running w x p) (hmode : x.ctl.mode = .scan)
    (hs : PalPeg.FrameFunction.starvedTest x = false) (hclock : 1 < x.ctl.clock)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm)
    (hlag : PalPeg.GalilScaffoldCounter.positive wm.lag = false) :
    Running w x ((workStep rest).apply blankM p none) := by
  have hrestart : restartGuardTest x.vm = false := by simp [restartGuardTest, hchain]
  apply PalPeg.PhysicalCacheInvariant.running_fused (workRule rest) w x x p none he
  intro T hT
  have hqmode := congrArg PalPeg.GalilScaffoldController.Control.mode hT.1.1.1.1.ctl
  change p.1.ctl.mode = x.ctl.mode at hqmode
  have hcount := countRead_eq hT.1.1.1 (by decide : 1 ≤ microRadius) micro_le_margin
    hmode hs hrestart hclock
  have hp : scanPhase p.1 (fun j => readWin blankM microRadius (T j)) ≠ .compare := by
    have hc := of_decide_eq_true (Bool.and_eq_true_iff.mp hcount).2
    simp only [tapesOf, Equiv.apply_symm_apply] at hc
    rw [hc]
    decide
  have hn : chainConsumesTest p.1 (fun j => readWin blankM microRadius (T j)) = false := by
    simpa only [tapesOf, Equiv.apply_symm_apply] using noConsume hT.1.1.1
      (by decide : 1 ≤ microRadius) micro_le_margin wm hchain hlag
  exact PalPeg.PhysicalCacheMachine.core_still rest w x (p.1, T) hT (hqmode.trans hmode) hp hn

theorem prepareRead_quiet (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : Running w x p) (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm)
    (hlag : PalPeg.GalilScaffoldCounter.positive wm.lag = false) :
    PalPeg.PhysicalCacheMachine.prepareRead p.1 (fun j => readWin blankM macroRadius (p.2 j)) = false := by
  simp only [PalPeg.PhysicalCacheMachine.prepareRead,
    noConsume_running w x p he (by decide : 1 ≤ macroRadius) (le_refl margin) wm hchain hlag,
    Bool.and_false, Bool.false_and]

theorem selected_quiet (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : Running w x p) (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm)
    (hlag : PalPeg.GalilScaffoldCounter.positive wm.lag = false) :
    (PalPeg.PhysicalCacheMachine.activeStep rest).apply blankM p none =
      (countedStep (workStep rest)).apply blankM p none := by
  have htag : p.1.chainTag = .watchers := by
    obtain ⟨T, hT, _⟩ := running_core he
    rw [hT.1.1.chainTag, hchain]
    rfl
  have hentry : PalPeg.PhysicalWatchEntry.entryRead p.1 (fun j => readWin blankM macroRadius (p.2 j)) = false := by
    simp [PalPeg.PhysicalWatchEntry.entryRead, htag]
  rw [PalPeg.PhysicalCacheMachine.activeStep, PalPeg.PhysicalWatchEntry.withWatchEntry, branch_apply, hentry]
  simp only [Bool.false_eq_true, if_false]
  rw [branch_apply, prepareRead_quiet w x p he wm hchain hlag]
  rfl

theorem forward_count (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : PhysicalState) (he : PalPeg.PhysicalCacheInvariant.Enc w x p)
    (hmode : x.ctl.mode = .scan) (hs : PalPeg.FrameFunction.starvedTest x = false) (hclock : 1 < x.ctl.clock)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm)
    (hlag : PalPeg.GalilScaffoldCounter.positive wm.lag = false) :
    PalPeg.PhysicalCacheInvariant.Enc w (PalPeg.PhysicalCacheMachine.successor w x)
      ((PalPeg.PhysicalCacheMachine.machine rest).apply blankM p none) := by
  have hrestart : restartGuardTest x.vm = false := by simp [restartGuardTest, hchain]
  have hactive : x.vm.chain ≠ .idle := by simp [hchain]
  have hsuccessor : PalPeg.PhysicalCacheMachine.successor w x = countState x := by
    rw [PalPeg.PhysicalCacheMachine.successor,
      PalPeg.PhysicalGuardProbe.tickFun_nonstarved_count _ _ 0 1 0 w _ 2048 x hmode hs hrestart hclock]
    change (⟨_, backgroundFun _ x.vm⟩ : State GalilVM) = _
    rw [backgroundFun_of_active _ x.vm hactive, hchain]
    simp only [chainStepFun, hlag, Bool.false_eq_true, if_false]
    rw [← hchain]
    rfl
  rw [hsuccessor]
  rcases p with ⟨q, T⟩
  cases q with
  | inl tag => rw [he.1, initial_starved] at hs; cases hs
  | inr q =>
    rw [PalPeg.PhysicalCacheMachine.machine,
      apply_active (PalPeg.PhysicalCacheMachine.activeStep rest) w x (q, T) (running_core he) hs]
    change Running w (countState x) ((PalPeg.PhysicalCacheMachine.activeStep rest).apply blankM (q, T) none)
    rw [selected_quiet rest w x (q, T) he wm hchain hlag,
      counted_apply, countRead_running (running_core he) hmode hs hrestart hclock]
    simp only [if_true]
    exact PalPeg.PhysicalCacheMachine.running_clockDown
      (running_quiet rest w x (q, T) he hmode hs hclock wm hchain hlag)

/-- info: 'PalPeg.PhysicalWatchIdle.forward_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forward_count

end PalPeg.PhysicalWatchIdle
