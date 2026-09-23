import PalPeg.PhysicalGrowStorage

/-! # The positive-work grow count as one real physical sweep -/
set_option autoImplicit false
namespace PalPeg.PhysicalGrowCount
attribute [local instance] Classical.propDecidable
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract
open PalPeg.PhysicalDebtMirror (RebuildingCore Rebuilding repaired)
open PalPeg.PhysicalDebtRebuild (paid)
open PalPeg.PhysicalGrowStorage (prepared)
open PalPeg.PhysicalLoanInvariant (Balanced NeedsLoan)
open PalPeg.PhysicalScanCount (countState clockDown)
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilScaffoldCounter (value positive inc)
open PalPeg.Program PalPeg.Local PalPeg.CloseoutCoreEnc12 PalPeg.LocalStepFusion
open PalPeg.GalilFinalAssembly2 (centreC placeC)

def grown (x : State GalilVM) : State GalilVM := paid (paid (prepared x))

def CountGrow (x : State GalilVM) : Prop :=
  x.ctl.mode = .scan ∧ 1 < x.ctl.clock ∧ x.vm.chain = .idle ∧
    x.vm.search.mode = .grow ∧ positive x.vm.search.work = true

theorem needs_source (x : State GalilVM) (hg : CountGrow x) : NeedsLoan x :=
  ⟨hg.1, hg.2.2.1, by simp [searchActive, hg.2.2.2.1]⟩

theorem needs_target (x : State GalilVM) (hg : CountGrow x) : NeedsLoan (countState (grown x)) :=
  needs_source x hg

theorem balanced_grown (x : State GalilVM) (hb : Balanced x) : Balanced (grown x) := by
  refine ⟨hb.1, ?_⟩
  exact PalPeg.PhysicalDebtRebuild.paid_balance _ (PalPeg.PhysicalDebtRebuild.paid_balance _ hb.2)

theorem background_grow (P : Shared) (x : State GalilVM)
    (hi : x.vm.chain = .idle) (hm : x.vm.search.mode = .grow) (hw : positive x.vm.search.work = true) :
    backgroundFun P x.vm = (grown x).vm := by
  simp only [backgroundFun, searchEffectFun, hi, searchLens, searchStepFun, hm,
    hw, if_true, SearchVM.toPrep, SearchVM.ofPrep, PalPeg.GalilScaffoldStagePrepare.growStep,
    PalPeg.GalilScaffoldStagePrepare.runState,
    PalPeg.GalilScaffoldPreparePaced.afterAdvance, chainBorn, ChainVM.isIdle,
    Bool.true_and, Bool.false_eq_true, decide_false, chainAtFun, if_false, afterBirth_false]
  simp [grown, paid, prepared, PalPeg.ChainBoundaryCache.advanceCounter,
    PalPeg.GalilScaffoldGrow.add, scanLens, hm, hi] <;> rfl

theorem successor_eq (w : List (Fin 2)) (x : State GalilVM)
    (hg : CountGrow x) (hs : PalPeg.FrameFunction.starvedTest x = false) :
    PalPeg.PhysicalCacheMachine.successor w x = countState (grown x) := by
  have hr : restartGuardTest x.vm = false := by simp [restartGuardTest, hg.2.2.1]
  rw [PalPeg.PhysicalCacheMachine.successor,
    PalPeg.PhysicalGuardProbe.tickFun_nonstarved_count _ _ 0 1 0 w _ 2048 x hg.1 hs hr hg.2.1]
  change (⟨_, backgroundFun _ x.vm⟩ : State GalilVM) = _
  rw [background_grow _ x hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2]
  rfl

noncomputable def body : ActRule (Fin 2) CoreControl Γm tapeCountM 96 :=
  seqRule PalPeg.PhysicalGrowStorage.rule PalPeg.PhysicalDebtRebuild.doubleRule

/-- Storage and both debt payments execute inside the same combined source
window. The second payment observes the first's zero crossing. -/
theorem body_ideal (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : Rebuilding w x p) (hb : Balanced x) :
    Rebuilding w (grown x) (idealStep body blankM p none) := by
  have hfirst := PalPeg.PhysicalGrowStorage.rebuilding_ideal w x p he
  let middle := idealStep PalPeg.PhysicalGrowStorage.rule blankM p none
  have hpay := PalPeg.PhysicalDebtRebuild.running_ideal w (prepared x) middle hfirst hb.2 none
  have hpay2 := PalPeg.PhysicalDebtRebuild.running_ideal w (paid (prepared x)) _ hpay
    (PalPeg.PhysicalDebtRebuild.paid_balance (prepared x) hb.2) none
  rw [body, seqRule_ideal blankM _ _ p none (fun j =>
    (show 32 + 64 ≤ margin by decide).trans (PalPeg.PhysicalDebtRebuild.sweep_margin w x p he j))]
  rw [PalPeg.PhysicalDebtRebuild.doubleRule, seqRule_ideal blankM _ _ _ none (fun j =>
    (show 32 + 32 ≤ margin by decide).trans (PalPeg.PhysicalDebtRebuild.sweep_margin w (prepared x) middle hfirst j))]
  exact hpay2

theorem rebuilding_clockDown (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : Rebuilding w x p) : Rebuilding w (countState x) (clockDown p.1, p.2) := by
  obtain ⟨T, hT, ht⟩ := he
  refine ⟨T, ?_, ht⟩
  exact ⟨⟨⟨PalPeg.PhysicalScanCount.core_clockDown hT.1.1.1, hT.1.1.2⟩, hT.1.2⟩, hT.2⟩

/-- The shared macro radius is a wider observation window, not extra ticks. -/
noncomputable def windows (ws : Fin tapeCountM → Window Γm macroRadius) :
    Fin tapeCountM → Window Γm 96 := fun j => windowAfter macroRadius 96 (ws j) []

noncomputable def rule : ActRule (Fin 2) CoreControl Γm tapeCountM macroRadius where
  nq := fun q input ws => clockDown (body.nq q input (windows ws))
  acts := fun q input ws => body.acts q input (windows ws)
  len_le := fun q input ws j => (body.len_le q input (windows ws) j).trans (by decide : 96 ≤ macroRadius)
noncomputable def step := compStep rule

theorem windows_read (T : Fin tapeCountM → STape Γm) (hm : ∀ j, macroRadius ≤ pos (T j)) :
    windows (fun j => readWin blankM macroRadius (T j)) = (fun j => readWin blankM 96 (T j)) := by
  funext j
  exact windowAfter_readWin blankM (T j) [] (by decide) (hm j)

theorem rule_ideal (p : CoreState) (hm : ∀ j, macroRadius ≤ pos (p.2 j)) :
    idealStep rule blankM p none =
      (clockDown (idealStep body blankM p none).1, (idealStep body blankM p none).2) := by
  simp only [idealStep, rule, windows_read p.2 hm]

theorem running (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : Rebuilding w x p) (hb : Balanced x) :
    Rebuilding w (countState (grown x)) (step.apply blankM p none) := by
  have hm : ∀ j, macroRadius ≤ pos (p.2 j) := PalPeg.PhysicalDebtRebuild.sweep_margin w x p he
  have hi := rebuilding_clockDown w (grown x) _ (body_ideal w x p he hb)
  rw [← rule_ideal p hm] at hi
  obtain ⟨hc, ht⟩ := compStep_apply rule blankM p none hm
  exact PalPeg.MachineStep.sweepClosed_sweepClosure blankM (RebuildingCore w)
    _ _ _ hi hc.symm ht


open PalPeg.PhysicalShiftDispatch (RoutedCore liftConfig)
open PalPeg.LocalRoleRouting (decode hold)

/-- Grow selection reads only finite control and the work counter's top. -/
noncomputable def guard (q : CoreControl) (ws : Fin tapeCountM → Window Γm macroRadius) : Bool :=
  decide (q.ctl.mode = .scan ∧ 1 < q.ctl.clock.val ∧ q.chainTag = .idle ∧ q.searchMode = .grow) &&
    counterPositiveTest q ws 7

theorem chainTag_idle (chain : ChainVM) : chainTagOf chain = .idle ↔ chain = .idle := by cases chain <;> simp [chainTagOf]

def Observations (x : State GalilVM) (q : CoreControl) : Prop :=
  q.ctl.mode = x.ctl.mode ∧ q.ctl.clock.val = x.ctl.clock ∧
    q.chainTag = chainTagOf x.vm.chain ∧ q.searchMode = x.vm.search.mode

theorem observations_control {w : List (Fin 2)} {x : State GalilVM} {q : CoreControl}
    (he : EncControl w x q) : Observations x q :=
  ⟨congrArg PalPeg.GalilScaffoldController.Control.mode he.ctl,
    congrArg PalPeg.GalilScaffoldController.Control.clock he.ctl, he.chainTag, he.searchMode⟩

theorem guard_core (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : RebuildingCore w x p) :
    guard p.1 (fun j => readWin blankM macroRadius (p.2 j)) = decide (CountGrow x) := by
  have ho := observations_control he.1.1.1.1.1
  change Observations x p.1 at ho
  have hw := counterPositiveTest_eq he.1.1.1.1.2 (K := macroRadius)
    (by decide) (le_refl margin) 7 x.vm.search.work rfl
  have hw' : counterPositiveTest p.1 (fun j => readWin blankM macroRadius (p.2 j)) 7 =
      positive x.vm.search.work := by
    simpa [counterPositiveTest, counterZeroTest, belowRead, tapesOf, repaired,
      PalPeg.PhysicalDebtMirror.repair, counterSlot, mirrorSlot] using hw
  simp only [guard, ho.1, ho.2.1, ho.2.2.1, ho.2.2.2, hw']
  rw [Bool.eq_iff_iff]
  simp [CountGrow, chainTag_idle, and_assoc]

theorem observations (w : List (Fin 2)) (x : State GalilVM) (p : RoutedCore)
    (he : PalPeg.PhysicalLoanInvariant.Enc w x (liftConfig p)) : Observations x p.1.2 := by
  by_cases hn : NeedsLoan x
  · obtain ⟨T, ht, _⟩ := ((PalPeg.PhysicalLoanInvariant.enc_partial w x _ hn).mp he).2
    exact observations_control ht.1.1.1.1.1
  · obtain ⟨y, hr, hy⟩ := ((PalPeg.PhysicalLoanInvariant.enc_full w x _ hn).mp he).1
    obtain ⟨T, ht, _⟩ := hy
    have ho := observations_control ht.1.1.1.1
    have hmode : y.vm.search.mode = x.vm.search.mode := by
      have hsame := hr.2.1
      unfold PalPeg.PhysicalRestartStorage.Same at hsame
      rw [hsame]
      rfl
    exact ⟨ho.1.trans (congrArg PalPeg.GalilScaffoldController.Control.mode hr.1.symm),
      ho.2.1.trans (congrArg PalPeg.GalilScaffoldController.Control.clock hr.1.symm),
      ho.2.2.1.trans (congrArg chainTagOf (PalPeg.PhysicalSnapshotInvariant.chain_related hr)),
      ho.2.2.2.trans hmode⟩

theorem guard_running (w : List (Fin 2)) (x : State GalilVM) (p : RoutedCore)
    (he : PalPeg.PhysicalLoanInvariant.Enc w x (liftConfig p)) :
    guard (decode p).1 (fun j => readWin blankM macroRadius ((decode p).2 j)) = decide (CountGrow x) := by
  by_cases hn : NeedsLoan x
  · obtain ⟨T, ht, heq⟩ := ((PalPeg.PhysicalLoanInvariant.enc_partial w x _ hn).mp he).2
    have hw : (fun j => readWin blankM macroRadius ((decode p).2 j)) =
        (fun j => readWin blankM macroRadius (T j)) := by
      funext j
      exact (readWin_congr_teqG (heq j)).symm
    rw [hw]
    exact guard_core w x ((decode p).1, T) ht
  · have ho := observations w x p he
    have hp : ¬ (p.1.2.ctl.mode = .scan ∧ 1 < p.1.2.ctl.clock.val ∧
        p.1.2.chainTag = .idle ∧ p.1.2.searchMode = .grow) := by
      intro h
      apply hn
      refine ⟨ho.1.symm.trans h.1, (chainTag_idle _).mp (ho.2.2.1.symm.trans h.2.2.1), ?_⟩
      have hmode := ho.2.2.2.symm.trans h.2.2.2
      simp [searchActive, hmode]
    have hg : ¬ CountGrow x := fun h => hn (needs_source x h)
    simp only [guard, show (decode p).1 = p.1.2 from rfl, hp, decide_false, Bool.false_and, hg]

/-- The source encoding supplies both balance and the partial mirror; no
condition on the target tapes is accepted. -/
theorem forward (w : List (Fin 2)) (x : State GalilVM) (p : RoutedCore)
    (he : PalPeg.PhysicalLoanInvariant.Enc w x (liftConfig p))
    (hg : CountGrow x) (hs : PalPeg.FrameFunction.starvedTest x = false) :
    PalPeg.PhysicalLoanInvariant.Enc w (PalPeg.PhysicalCacheMachine.successor w x)
      (liftConfig ((hold step).apply blankM p none)) := by
  obtain ⟨hb, hr⟩ := (PalPeg.PhysicalLoanInvariant.enc_partial w x _ (needs_source x hg)).mp he
  rw [successor_eq w x hg hs]
  apply (PalPeg.PhysicalLoanInvariant.enc_partial w _ _ (needs_target x hg)).mpr
  refine ⟨balanced_grown x hb, ?_⟩
  change Rebuilding w _ (decode _)
  rw [PalPeg.LocalRoleRouting.decode_hold]
  exact running w x (decode p) hr hb

/-- info: 'PalPeg.PhysicalGrowCount.running' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms running

/-- info: 'PalPeg.PhysicalGrowCount.forward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forward

end PalPeg.PhysicalGrowCount
