import PalPeg.PhysicalDebtRebuild

/-! # Input arrival and starvation observations with the rebuilding radius mirror

The existing twelve-slot head executor never observes the borrowed mirror.
Completing its proof view commutes with that executor, while the actual partial
mirror keeps its own value and position.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PalPeg.PhysicalDebtFeed
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract
open PalPeg.PhysicalDebtMirror (repair repaired mirrorIndex credit RebuildingCore Rebuilding)
open PalPeg.PhysicalFeed (feedRule feedState)
open PalPeg.PhysicalBootFeed (feedStep)
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.Program PalPeg.Local PalPeg.CloseoutCoreEnc12 PalPeg.LocalStepFusion

noncomputable def complete (p : CoreState) : CoreState := (p.1, repaired p.2)

theorem view_repaired {K : ℕ} (T : Fin tapeCountM → STape Γm) (v : Fin 4) :
    viewWindows v (fun j => readWin blankM K (repaired T j)) =
      viewWindows v (fun j => readWin blankM K (T j)) := by
  funext i k
  simp [viewWindows, repaired, repair, headSlot, mirrorSlot]

theorem head_control_repaired (q : CoreControl) (T : Fin tapeCountM → STape Γm) (slot : Fin 11) :
    headControlStep (K := microRadius) (by decide) q slot (fun j => readWin blankM microRadius (repaired T j)) =
      headControlStep (by decide) q slot (fun j => readWin blankM microRadius (T j)) := by
  have hn : (fun v => viewNextOfHead (K := microRadius) (by decide) q v slot
      (fun j => readWin blankM microRadius (repaired T j))) =
      (fun v => viewNextOfHead (K := microRadius) (by decide) q v slot
        (fun j => readWin blankM microRadius (T j))) := by
    funext v
    exact congrArg (fun ws => PalPeg.ConcreteLocalMachine.viewNext (Fin 2) (K := microRadius)
      (by decide) slot (q.commands v) (viewControlOf q v) ws) (view_repaired T v)
  exact congrArg (fun f : Fin 4 → PalPeg.ConcreteLocalMachine.ViewControl =>
    {q with gap := fun v => (f v).1, job := fun v => (f v).2.1, micro := fun v => ((q.micro v).1, (f v).2.2)}) hn

theorem feed_nq_congr (q : CoreControl) (input : Option (Fin 2))
    (ws₁ ws₂ : Fin tapeCountM → Window Γm microRadius)
    (hh : ∀ slot, headControlStep (by decide) q slot ws₁ = headControlStep (by decide) q slot ws₂) :
    feedRule.nq q input ws₁ = feedRule.nq q input ws₂ := by
  by_cases hz : q.slot.val = 0
  · simp only [feedRule, tickRule, hz, if_true]
    rfl
  · simp only [feedRule, tickRule, hz, if_false]
    exact congrArg (fun c : CoreControl => {c with slot := slotAdvance q.slot})
      (hh ⟨q.slot.val - 1, by have := q.slot.isLt; omega⟩)

theorem feed_nq_repaired (q : CoreControl) (T : Fin tapeCountM → STape Γm) (input : Option (Fin 2)) :
    feedRule.nq q input (fun j => readWin blankM microRadius (repaired T j)) =
      feedRule.nq q input (fun j => readWin blankM microRadius (T j)) :=
  feed_nq_congr q input _ _ (head_control_repaired q T)

theorem feed_acts_repaired (q : CoreControl) (T : Fin tapeCountM → STape Γm)
    (input : Option (Fin 2)) (j : Fin tapeCountM) :
    feedRule.acts q input (fun k => readWin blankM microRadius (repaired T k)) j =
      feedRule.acts q input (fun k => readWin blankM microRadius (T k)) j := by
  simp only [feedRule, tickRule, headViewActs, view_repaired]

theorem feed_mirror_acts (q : CoreControl) (ws : Fin tapeCountM → Window Γm microRadius)
    (input : Option (Fin 2)) (m : Fin 7) : feedRule.acts q input ws (slotIndex (mirrorSlot m)) = [] := by
  by_cases h : q.slot.val = 0
  · simp only [feedRule, tickRule, h, if_true, Equiv.symm_apply_apply]; rfl
  · simp only [feedRule, tickRule, h, if_false]
    rw [Equiv.symm_apply_apply]

theorem step_complete (p : CoreState) (input : Option (Fin 2)) :
    idealStep feedRule blankM (complete p) input = complete (idealStep feedRule blankM p input) := by
  apply Prod.ext
  · exact feed_nq_repaired p.1 p.2 input
  · funext j
    change actList blankM (repaired p.2 j)
      (feedRule.acts p.1 input (fun k => readWin blankM microRadius (repaired p.2 k)) j) = _
    rw [feed_acts_repaired]
    by_cases hj : j = mirrorIndex
    · subst j
      simp [complete, repaired, repair, mirrorIndex, idealStep, feed_mirror_acts, mirrorSlot]
    · have hn : slotIndex.symm j ≠ mirrorSlot 2 := by
        intro h
        apply hj
        rw [mirrorIndex, ← h, Equiv.apply_symm_apply]
      simp [complete, repaired, repair, idealStep, hn]

theorem run_complete (p : CoreState) (input : Option (Fin 2)) (n : ℕ) :
    idealRun feedRule blankM (complete p) input n = complete (idealRun feedRule blankM p input n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [idealRun_step, idealRun_step, ih, step_complete]

theorem run_mirror (p : CoreState) (input : Option (Fin 2)) (n : ℕ) (m : Fin 7) :
    (idealRun feedRule blankM p input n).2 (slotIndex (mirrorSlot m)) = p.2 (slotIndex (mirrorSlot m)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [idealRun_step]
    change actList blankM _ (feedRule.acts _ _ _ (slotIndex (mirrorSlot m))) = _
    rw [feed_mirror_acts]
    exact ih

theorem credit_feed (input : Option (Fin 2)) (x : State GalilVM) : credit (feedState input x) = credit x := by
  cases input <;> rfl

/-- The full head proof survives proof completion, and the physical partial
mirror is carried separately through the same twelve steps. -/
theorem core_feed (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (input : Option (Fin 2)) (he : RebuildingCore w x p) :
    RebuildingCore w (feedState input x) (idealRun feedRule blankM p input 12) := by
  have hbase := PalPeg.PhysicalCacheInvariant.core_feed w x (complete p) input he.1
  rw [run_complete] at hbase
  refine ⟨hbase, ?_⟩
  obtain ⟨seg, ha, ht⟩ := he.2
  have hp : (idealRun feedRule blankM p input 12).1.polarity = p.1.polarity :=
    PalPeg.PhysicalCacheInvariant.arrival_polarity (fun _ _ _ _ => []) (by intros; simp) p input he.1.1.1.2.1
  refine ⟨seg, ?_, ?_⟩
  · rw [hp, credit_feed]; exact ha
  · change (idealRun feedRule blankM p input 12).2 (slotIndex (mirrorSlot 2)) = _
    rw [run_mirror]; exact ht

/-- Generic fusion keeps the large head executor opaque during transport. -/
theorem running_fused (R : ActRule (Fin 2) CoreControl Γm tapeCountM microRadius)
    (w : List (Fin 2)) (x y : State GalilVM) (p : CoreState)
    (input : Option (Fin 2)) (he : Rebuilding w x p)
    (hstep : ∀ T, RebuildingCore w x (p.1, T) → RebuildingCore w y (idealRun R blankM (p.1, T) input 12)) :
    Rebuilding w y ((compStep (iterRule R 12)).apply blankM p input) := by
  obtain ⟨T, hT, ht⟩ := he
  have hm : ∀ j, macroRadius ≤ pos (T j) := fun j =>
    PalPeg.PhysicalDebtRebuild.core_margin w x (p.1, T) hT j
  have hmp : ∀ j, macroRadius ≤ pos (p.2 j) := fun j => (ht j).1 ▸ hm j
  obtain ⟨hc, hteq⟩ := idealStep_congr_teqG (iterRule R 12) blankM p.1 T p.2 ht input
  rw [iterRule_ideal blankM R 12 (p.1, T) input hm, idealIter_eq_idealRun] at hc hteq
  obtain ⟨hr, hs⟩ := compStep_apply (iterRule R 12) blankM p input hmp
  refine ⟨(idealRun R blankM (p.1, T) input 12).2, ?_,
    fun j => PalPeg.MachineStep.teqG_trans (hteq j) (hs j)⟩
  rw [hr]
  change RebuildingCore w y ((idealStep (iterRule R 12) blankM p input).1, _)
  rw [← hc]
  exact hstep T hT

/-- Actual arrival sweep, including input=None used by the starvation arm. -/
theorem running_feed (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (input : Option (Fin 2)) (he : Rebuilding w x p) :
    Rebuilding w (feedState input x) (feedStep.apply blankM p input) :=
  running_fused feedRule w x (feedState input x) p input he
    (fun T hT => core_feed w x (p.1, T) input hT)

theorem starved_repaired {K : ℕ} (q : CoreControl) (T : Fin tapeCountM → STape Γm) :
    PalPeg.PhysicalTickDispatch.starvedRead q (fun j => readWin blankM K (repaired T j)) =
      PalPeg.PhysicalTickDispatch.starvedRead q (fun j => readWin blankM K (T j)) := by
  simp only [PalPeg.PhysicalTickDispatch.starvedRead, availableTest,
    PalPeg.PhysicalTickDispatch.availableAfterRight, view_repaired]
  simp [remainsTest, belowRead, centreRead, repaired, repair, counterSlot, placeSlot, mirrorSlot] <;> rfl

theorem starved_running (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : Rebuilding w x p) :
    PalPeg.PhysicalTickDispatch.starvedRead p.1 (fun j => readWin blankM macroRadius (p.2 j)) =
      PalPeg.FrameFunction.starvedTest x := by
  obtain ⟨T, hT, ht⟩ := he
  have hw : (fun j => readWin blankM macroRadius (p.2 j)) =
      (fun j => readWin blankM macroRadius (T j)) := by
    funext j
    exact (readWin_congr_teqG (ht j)).symm
  rw [hw, ← starved_repaired]
  simpa only [complete, tapesOf, Equiv.apply_symm_apply] using
    PalPeg.PhysicalTickDispatch.starvedRead_eq hT.1.1.1.1 (by decide : 1 ≤ macroRadius) (le_refl margin)

/-- info: 'PalPeg.PhysicalDebtFeed.running_feed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms running_feed

/-- info: 'PalPeg.PhysicalDebtFeed.starved_running' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms starved_running

end PalPeg.PhysicalDebtFeed
