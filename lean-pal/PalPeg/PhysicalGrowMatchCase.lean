import PalPeg.PhysicalGrowMatchTick

/-! # Selecting and supplying a complete positive-work grow comparison -/
set_option autoImplicit false
namespace PalPeg.PhysicalGrowMatchCase
attribute [local instance] Classical.propDecidable
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.PhysicalLoanInvariant (Balanced NeedsLoan Enc enc_partial)
open PalPeg.PhysicalDebtMirror (RebuildingCore Rebuilding repaired repair)
open PalPeg.PhysicalGrowMatchTick (target step)
open PalPeg.PhysicalGrowCount (Observations observations observations_control chainTag_idle)
open PalPeg.PhysicalShiftDispatch (RoutedCore liftConfig)
open PalPeg.PhysicalCacheMachine (successor)
open PalPeg.GalilFinalAssembly2 (centreC placeC)
open PalPeg.GalilScaffoldCounter (positive)
open PalPeg.GalilScaffoldInputHead (left read)
open PalPeg.GalilScaffoldChainVerifier (right canRight)
open PalPeg.Local (readWin Window)
open PalPeg.LocalRoleRouting (decode)

def MatchGrow (x : State GalilVM) : Prop :=
  (x.ctl.mode = .scan ∧ x.ctl.clock ≤ 1 ∧ x.vm.chain = .idle ∧ x.vm.search.mode = .grow) ∧
  positive x.vm.search.work = true ∧ read (left x.vm.left) = read (right x.vm.right)

theorem needs_source (x : State GalilVM) (hg : MatchGrow x) : NeedsLoan x :=
  ⟨hg.1.1, hg.1.2.2.1, by simp [searchActive, hg.1.2.2.2]⟩

theorem needs_target (w : List (Fin 2)) (x : State GalilVM) (hg : MatchGrow x) : NeedsLoan (target w x) :=
  needs_source x hg

theorem right_ready (x : State GalilVM) (hm : x.ctl.mode = .scan)
    (hs : PalPeg.FrameFunction.starvedTest x = false) : canRight x.vm.right := by
  apply (canRightTest_iff _).mpr
  simpa [PalPeg.FrameFunction.starvedTest, PalPeg.FrameFunction.starvedOf, hm] using hs

theorem successor_eq (w : List (Fin 2)) (x : State GalilVM) (hg : MatchGrow x)
    (hs : PalPeg.FrameFunction.starvedTest x = false) : successor w x = target w x := by
  let P := PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w
  have hr : restartGuardTest x.vm = false := by simp [restartGuardTest, hg.1.2.2.1]
  have ha : canRightTest x.vm.right = true := (canRightTest_iff _).mp (right_ready x hg.1.1 hs)
  have hm : PalPeg.FrameFunction.matchedTest (scanLens.get (compareFun P x.vm)) = true := by
    rw [matchedTest_compareFun]
    exact decide_eq_true hg.2.2
  have hv := PalPeg.PhysicalGrowMatch.matched_grow P x hg.1.2.2.1 hg.1.2.2.2 hg.2.1 hg.2.2
  change (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w).matchedPlace x.ctl.replaying
    ((PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w).compare x.vm) = PalPeg.PhysicalGrowMatch.moved x at hv
  unfold successor tickFun
  rw [hg.1.1]
  change (if restartGuardTest x.vm then _ else if !x.ctl.replaying && !canRightTest x.vm.right then _ else if 1 < x.ctl.clock then _ else if PalPeg.FrameFunction.matchedTest (scanLens.get (compareFun P x.vm)) then _ else _) = _
  rw [hr, if_neg Bool.false_ne_true, ha]
  simp only [Bool.not_true, Bool.and_false, Bool.false_eq_true, if_false]
  rw [if_neg (Nat.not_lt_of_ge hg.1.2.1), if_pos hm]
  rw [hv]
  rfl

noncomputable def guard (q : CoreControl) (ws : Fin tapeCountM → Window Γm macroRadius) : Bool :=
  decide (q.ctl.mode = .scan ∧ q.ctl.clock.val ≤ 1 ∧ q.chainTag = .idle ∧ q.searchMode = .grow) &&
    counterPositiveTest q ws 7 && agreeTest q ws

theorem agree_repaired {K : ℕ} (q : CoreControl) (T : Fin tapeCountM → PalPeg.Program.STape Γm) :
    agreeTest q (fun j => readWin blankM K (repaired T j)) =
      agreeTest q (fun j => readWin blankM K (T j)) := by
  simp only [agreeTest, leavingLetter, landingLetter, PalPeg.PhysicalDebtFeed.view_repaired]
  rfl

theorem guard_core (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : RebuildingCore w x p) (hs : PalPeg.FrameFunction.starvedTest x = false) :
    guard p.1 (fun j => readWin blankM macroRadius (p.2 j)) = decide (MatchGrow x) := by
  have ho := observations_control he.1.1.1.1.1
  change Observations x p.1 at ho
  have hw := counterPositiveTest_eq he.1.1.1.1.2 (K := macroRadius)
    (by decide) (le_refl margin) 7 x.vm.search.work rfl
  have hw' : counterPositiveTest p.1 (fun j => readWin blankM macroRadius (p.2 j)) 7 = positive x.vm.search.work := by
    simpa [counterPositiveTest, counterZeroTest, belowRead, tapesOf, repaired, repair, counterSlot, mirrorSlot] using hw
  by_cases hm : x.ctl.mode = .scan
  · have ha := agreeTest_of_encoded he.1.1.1.1.2 (by decide : 1 ≤ macroRadius)
      (le_refl margin) (right_ready x hm hs)
    have ha' : agreeTest p.1 (fun j => readWin blankM macroRadius (p.2 j)) =
        decide (read (left x.vm.left) = read (right x.vm.right)) := by
      simpa only [tapesOf, Equiv.apply_symm_apply, agree_repaired] using ha
    simp only [guard, ho.1, ho.2.1, ho.2.2.1, ho.2.2.2, hw', ha']
    rw [Bool.eq_iff_iff]
    simp [MatchGrow, chainTag_idle, and_assoc]
  · simp [guard, ho.1, hm, MatchGrow]

theorem guard_running (w : List (Fin 2)) (x : State GalilVM) (p : RoutedCore)
    (he : Enc w x (liftConfig p)) (hs : PalPeg.FrameFunction.starvedTest x = false) :
    guard (decode p).1 (fun j => readWin blankM macroRadius ((decode p).2 j)) = decide (MatchGrow x) := by
  by_cases hn : NeedsLoan x
  · obtain ⟨T, ht, heq⟩ := ((enc_partial w x _ hn).mp he).2
    have hw : (fun j => readWin blankM macroRadius ((decode p).2 j)) =
        (fun j => readWin blankM macroRadius (T j)) := by
      funext j
      exact (readWin_congr_teqG (heq j)).symm
    rw [hw]
    exact guard_core w x ((decode p).1, T) ht hs
  · have ho := observations w x p he
    have hp : ¬ (p.1.2.ctl.mode = .scan ∧ p.1.2.ctl.clock.val ≤ 1 ∧
        p.1.2.chainTag = .idle ∧ p.1.2.searchMode = .grow) := by
      intro h
      apply hn
      refine ⟨ho.1.symm.trans h.1, (chainTag_idle _).mp (ho.2.2.1.symm.trans h.2.2.1), ?_⟩
      have hmode := ho.2.2.2.symm.trans h.2.2.2
      simp [searchActive, hmode]
    have hg : ¬ MatchGrow x := fun h => hn (needs_source x h)
    simp only [guard, show (decode p).1 = p.1.2 from rfl, hp, decide_false, Bool.false_and, hg]

theorem forward (w arrived : List (Fin 2)) (x : State GalilVM) (p : RoutedCore)
    (he : Enc w x (liftConfig p)) (hg : MatchGrow x)
    (hs : PalPeg.FrameFunction.starvedTest x = false)
    (hrep : PalPeg.GalilScaffoldInputTrace.Represents x.vm.right.head arrived)
    (hlen : arrived.length ≤ w.length) :
    Enc w (successor w x) (liftConfig (step.apply blankM p none)) := by
  obtain ⟨hb, hr⟩ := (enc_partial w x _ (needs_source x hg)).mp he
  rw [successor_eq w x hg hs]
  apply (enc_partial w _ _ (needs_target w x hg)).mpr
  refine ⟨PalPeg.PhysicalGrowMatch.balanced x hb, ?_⟩
  exact PalPeg.PhysicalGrowMatchTick.running w arrived x p hr hb hg.1.2.2.1
    (right_ready x hg.1.1 hs) hrep hlen

/-- info: 'PalPeg.PhysicalGrowMatchCase.guard_running' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms guard_running

/-- info: 'PalPeg.PhysicalGrowMatchCase.forward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forward

end PalPeg.PhysicalGrowMatchCase
