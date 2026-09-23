import PalPeg.PhysicalDpBank

/-! Every already-connected active row now carries the DP cleanup invariant.
The source cases, including their canonical trace and legal Tick premises,
are unchanged. The remaining rows concern this same actual cleanup machine. -/
set_option autoImplicit false
namespace PalPeg.PhysicalDpCleanupDispatch
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract
open PalPeg.PhysicalDpCleanup (Config Enc machine forget)
open PalPeg.PhysicalShiftDispatch (RoutedStep RoutedState RoutedCore liftConfig Entry)
open PalPeg.PhysicalCacheMachine (successor)
open PalPeg.PhysicalDpBank (RunningKeeps key bankBit)
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.Program PalPeg.Local PalPeg.CloseoutCoreEnc12

attribute [local irreducible] PalPeg.PhysicalLoanDispatch.machine

/-- Control preservation is read from the actual next function, before any
abstract postcondition is used. -/
theorem running_result (L : RoutedStep) (hl : RunningKeeps L) (p : RoutedCore) (a : Option (Fin 2)) :
    ∃ target : RoutedCore, L.apply blankM (liftConfig p) a = liftConfig target ∧
      target.1.2.dpLive = p.1.2.dpLive ∧
      ∀ bank i, target.1.1 (slotIndex (dpSlotOf bank i)) = p.1.1 (slotIndex (dpSlotOf bank i)) := by
  have h : key (L.apply blankM (liftConfig p) a).1 = key (liftConfig p).1 :=
    hl p.1.1 p.1.2 a (fun j => readWin blankM macroRadius (p.2 j))
  generalize hout : L.apply blankM (liftConfig p) a = result at h ⊢
  rcases result with ⟨⟨roles,q⟩,T⟩
  have hb := congrArg Prod.fst h
  have hr := congrArg Prod.snd h
  cases q with
  | inl tag => simp only [key,bankBit,liftConfig,reduceCtorEq] at hb
  | inr q =>
    refine ⟨((roles,q),T),rfl,Option.some.inj hb,?_⟩
    intro bank i
    exact congrFun (congrFun hr bank) i

/-- Any existing transition proof on Loan Enc transfers to the extra finite
cleanup state. It does not assume its new target invariant. -/
theorem forward_of_previous (rest : PalPeg.PhysicalScanCount.RestCommands)
    (w : List (Fin 2)) (x y : State GalilVM) (p : Config) (a : Option (Fin 2))
    (he : Enc w x p)
    (hy : PalPeg.PhysicalLoanInvariant.Enc w y
      ((PalPeg.PhysicalLoanDispatch.machine rest).apply blankM (forget p) a)) :
    Enc w y ((machine rest).apply blankM p a) := by
  rcases p with ⟨⟨⟨roles,q⟩,phases⟩,T⟩
  cases q with
  | inl tag =>
    cases tag
    refine ⟨?_,PalPeg.PhysicalDpCleanupBoot.boot_progress rest roles phases T a
      (PalPeg.PhysicalDpCleanupBoot.boot_source w x roles T he.1)⟩
    change PalPeg.PhysicalLoanInvariant.Enc w y
      (forget ((PalPeg.PhysicalDpCleanup.wrap _).apply blankM _ a))
    rw [PalPeg.PhysicalDpCleanupBoot.wrap_boot]
    exact hy
  | inr q =>
    obtain ⟨target,ht,hb,hr⟩ := running_result (PalPeg.PhysicalLoanDispatch.machine rest)
      (PalPeg.PhysicalDpBank.machine rest) ((roles,q),T) a
    change PalPeg.PhysicalLoanInvariant.Enc w y
      ((PalPeg.PhysicalLoanDispatch.machine rest).apply blankM (liftConfig ((roles,q),T)) a) at hy
    rw [ht] at hy
    exact PalPeg.PhysicalDpCleanup.forward_kept (PalPeg.PhysicalLoanDispatch.machine rest)
      w x y ((roles,q),T) target phases a he hy ht hb
      (fun i => by rw [hr,hb])

/-- These are exactly the source cases removed from the previous residual. -/
def Handled (w : List (Fin 2)) (x : State GalilVM) : Prop :=
  PalPeg.PhysicalScanCount.CountAtRest x ∨ PalPeg.PhysicalBoundaryCount.CountWatch x ∨
  PalPeg.PhysicalBoundaryCount.CountBackReady x ∨ x.ctl.mode = .shift ∨ Entry w x ∨
  PalPeg.PhysicalGrowCount.CountGrow x ∨ PalPeg.PhysicalGrowMatchCase.MatchGrow x

open PalPeg.GalilFinalAssembly2 (centreC placeC)
open PalPeg.CloseoutCheckW (PreTraceIMW CanonTrace)
open PalPeg.LocalSysConcrete (absSC)
open PalPeg.LocalReplayParked (Mirrored1)
open PalPeg.LocalBlankState (tapeCount)
open PalPeg.ShadowedLocalFinal (localGood postPhase frozenAt heldAfter)

theorem forward_handled (rest : PalPeg.PhysicalScanCount.RestCommands)
    (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ)
    (hpre : PreTraceIMW centreC placeC 0 1 0 w st Tc) (hcanon : CanonTrace 0 w st Tc)
    (m : Mirrored1 (tapeCount 0)) (p : Config)
    (hon : PalPeg.LocalShadowConcrete.ArrivedOnRun (localGood (spare := 0)) (postPhase 0 1 0) w
      (heldAfter (Tc w.length) st) m)
    (hnotFrozen : ¬ frozenAt w m) (he : Enc w (absSC m) p)
    (hs : PalPeg.FrameFunction.starvedTest (absSC m) = false)
    (htick : Tick (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 (absSC m)
      (successor w (absSC m))) (hh : Handled w (absSC m)) :
    Enc w (successor w (absSC m)) ((machine rest).apply blankM p none) := by
  apply forward_of_previous rest w (absSC m) _ p none he
  apply PalPeg.PhysicalLoanDispatch.active_of_remaining rest w st Tc hpre hcanon m
    (forget p) hon hnotFrozen he.1 hs htick
  intro hrest hwatch hback hshift hentry hgrow hmatch
  rcases hh with hh | hh | hh | hh | hh | hh | hh <;> contradiction

/-- Same source exclusions as LoanDispatch, now with the actual 118-tape
machine and its running cleanup phases all the way to the final tick API. -/
theorem cases_of_remaining (rest : PalPeg.PhysicalScanCount.RestCommands)
    (hother : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC 0 1 0 w st Tc → CanonTrace 0 w st Tc →
      ∀ (m : Mirrored1 (tapeCount 0)) (p : Config),
        PalPeg.LocalShadowConcrete.ArrivedOnRun (localGood (spare := 0)) (postPhase 0 1 0) w
          (heldAfter (Tc w.length) st) m →
        ¬ frozenAt w m → Enc w (absSC m) p →
        PalPeg.FrameFunction.starvedTest (absSC m) = false →
        Tick (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 (absSC m)
          (successor w (absSC m)) →
        ¬ PalPeg.PhysicalScanCount.CountAtRest (absSC m) →
        ¬ PalPeg.PhysicalBoundaryCount.CountWatch (absSC m) →
        ¬ PalPeg.PhysicalBoundaryCount.CountBackReady (absSC m) →
        (absSC m).ctl.mode ≠ .shift → ¬ Entry w (absSC m) →
        ¬ PalPeg.PhysicalGrowCount.CountGrow (absSC m) →
        ¬ PalPeg.PhysicalGrowMatchCase.MatchGrow (absSC m) →
        Enc w (successor w (absSC m)) ((machine rest).apply blankM p none)) :
    TickCases (machine rest) blankM Enc := by
  classical
  constructor
  · intro w st Tc hpre hcanon m p hon hf he hs
    exact PalPeg.PhysicalDpCleanupBoot.forward_starved rest w (absSC m) p he hs
  · intro w st Tc hpre hcanon m p hon hf he hs htick
    by_cases hh : Handled w (absSC m)
    · exact forward_handled rest w st Tc hpre hcanon m p hon hf he hs htick hh
    · simp only [Handled,not_or] at hh
      exact hother w st Tc hpre hcanon m p hon hf he hs htick
        hh.1 hh.2.1 hh.2.2.1 hh.2.2.2.1 hh.2.2.2.2.1 hh.2.2.2.2.2.1 hh.2.2.2.2.2.2

/-- info: 'PalPeg.PhysicalDpCleanupDispatch.forward_of_previous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forward_of_previous

/-- info: 'PalPeg.PhysicalDpCleanupDispatch.forward_handled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forward_handled

/-- info: 'PalPeg.PhysicalDpCleanupDispatch.cases_of_remaining' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cases_of_remaining

end PalPeg.PhysicalDpCleanupDispatch
