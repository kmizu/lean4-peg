import PalPeg.PhysicalBoundary
import PalPeg.LocalHeadRep

/-!
# One physical input arrival

The none/some interface is shared by boot and normal input. An input arrival
keeps the controller and non-head components and appends the letter to all four
views in the existing twelve-step rule. No future input is used by the rule.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace PalPeg.PhysicalFeed
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract PalPeg.PhysicalBoundary
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.Program (STape)
open PalPeg.CloseoutCoreEnc12 (Act ActRule compStep)
open PalPeg.LocalStepFusion
open PalPeg.ConcreteLocalMachine (commandOfLetter headAfter)

def feedState (input : Option (Fin 2)) (x : State GalilVM) : State GalilVM :=
  match input with
  | none => x
  | some a => PalPeg.GalilArriveChain.arriveState' a x

theorem feed_counters (input : Option (Fin 2)) (x : State GalilVM) :
    counterOf (feedState input x) = counterOf x := by
  cases input with
  | none => rfl
  | some a =>
    funext c
    fin_cases c <;> cases h : x.vm.chain <;>
      simp [feedState, counterOf, PalPeg.GalilArriveChain.arriveState',
        PalPeg.GalilArriveChain.arriveVM', PalPeg.GalilArriveChain.arriveChain, h,
        PalPeg.GalilArriveChain.arriveW, PalPeg.LocalTracking.arriveVM]

theorem feed_places (input : Option (Fin 2)) (x : State GalilVM) :
    placeOf (feedState input x) = placeOf x := by
  cases input with
  | none => rfl
  | some a =>
    funext i
    fin_cases i <;> cases h : x.vm.chain <;>
      simp [feedState, placeOf, PalPeg.GalilArriveChain.arriveState',
        PalPeg.GalilArriveChain.arriveVM', PalPeg.GalilArriveChain.arriveChain, h,
        PalPeg.LocalTracking.arriveVM]

theorem feed_period (input : Option (Fin 2)) (x : State GalilVM) :
    periodOf (feedState input x) = periodOf x := by
  cases input with
  | none => rfl
  | some a =>
    cases h : x.vm.chain <;>
      simp [feedState, periodOf, PalPeg.GalilArriveChain.arriveState',
        PalPeg.GalilArriveChain.arriveVM', PalPeg.GalilArriveChain.arriveChain, h,
        PalPeg.GalilArriveChain.arriveW, PalPeg.LocalTracking.arriveVM]

theorem feed_answer (input : Option (Fin 2)) (x : State GalilVM) :
    answerOf (feedState input x) = answerOf x := by
  cases input with
  | none => rfl
  | some a =>
    cases h : x.vm.chain <;>
      simp [feedState, answerOf, PalPeg.GalilArriveChain.arriveState',
        PalPeg.GalilArriveChain.arriveVM', PalPeg.GalilArriveChain.arriveChain, h,
        PalPeg.LocalTracking.arriveVM]

theorem feed_heads (input : Option (Fin 2)) (x : State GalilVM) (v : Fin 4) :
    headOf (feedState input x) v = (headOf x v).map (headAfter input) := by
  cases input with
  | none => cases h : headOf x v <;> simp [feedState, h, headAfter]
  | some a =>
    fin_cases v <;> cases h : x.vm.chain <;>
      simp [feedState, headOf, PalPeg.GalilArriveChain.arriveState',
        PalPeg.GalilArriveChain.arriveVM', PalPeg.GalilArriveChain.arriveChain, h,
        PalPeg.GalilArriveChain.arriveW, PalPeg.LocalTracking.arriveVM, headAfter,
        PalPeg.GalilTickArrive.arrivePH]

theorem encControl_feed {w : List (Fin 2)} {x : State GalilVM} {q : CoreControl}
    (h : EncControl w x q) (input : Option (Fin 2)) :
    EncControl w (feedState input x) q := by
  cases input with
  | none => exact h
  | some a =>
    have hchainTag : chainTagOf (PalPeg.GalilArriveChain.arriveChain a x.vm.chain)
        = chainTagOf x.vm.chain := by cases x.vm.chain <;> rfl
    have hchainConsume : chainConsumeOf (PalPeg.GalilArriveChain.arriveChain a x.vm.chain)
        = chainConsumeOf x.vm.chain := by cases x.vm.chain <;> rfl
    refine { h with chainTag := ?_, chainPhase := ?_, chainForward := ?_, chainBroken := ?_, placeGap := ?_, onLetter := ?_, leftFirst := ?_ }
    · exact h.chainTag.trans hchainTag.symm
    · exact h.chainPhase.trans (congrArg Prod.fst hchainConsume).symm
    · exact h.chainForward.trans (congrArg (fun z => z.2.1) hchainConsume).symm
    · exact h.chainBroken.trans (congrArg (fun z => z.2.2) hchainConsume).symm
    · intro i place hp
      exact h.placeGap i place (by rw [← congrFun (feed_places (some a) x) i]; exact hp)
    · exact h.onLetter
    · exact h.leftFirst

def commands (_q : CoreControl) (input : Option (Fin 2))
    (_ws : Fin tapeCountM → PalPeg.Local.Window Γm microRadius) :
    Fin 4 → PalPeg.ConcreteLocalMachine.ViewCommand := fun _ => commandOfLetter input

abbrev InputActs := CoreControl → Option (Fin 2) →
  (Fin tapeCountM → PalPeg.Local.Window Γm microRadius) → Fin tapeCountM → List (Act Γm)

noncomputable def arrivalRule (baseActs : InputActs)
    (baseLen : ∀ q i ws j, (baseActs q i ws j).length ≤ microRadius) :
    ActRule (Fin 2) CoreControl Γm tapeCountM microRadius :=
  tickRule (by decide) (fun q _ _ => q) commands baseActs baseLen

/-- This head theorem is independent of the non-head actions, so boot may write
the floor markers while the same slot receives its first letter. -/
theorem head_afterTick (baseActs : InputActs)
    (baseLen : ∀ q i ws j, (baseActs q i ws j).length ≤ microRadius)
    (p : CoreState) (input : Option (Fin 2)) (v : Fin 4)
    (hslot : p.1.slot.val = 0) (howed : (p.1.micro v).2.2.2 = 0)
    (view : PalPeg.LocalInputView.InputView)
    (hview : HeadSlotsRepAt margin p.1.gap p.1.micro
      (fun slot => p.2 (slotIndex slot)) v view) :
    HeadSlotsRepAt margin
      (idealRun (arrivalRule baseActs baseLen) blankM p input 12).1.gap
      (idealRun (arrivalRule baseActs baseLen) blankM p input 12).1.micro
      (fun slot => (idealRun (arrivalRule baseActs baseLen) blankM p input 12).2 (slotIndex slot)) v
      (PalPeg.ConcreteLocalMachine.viewApply (commandOfLetter input) view) := by
  obtain ⟨viewTapes, hrep, hslots, hcells, hwf⟩ := hview
  simp only [arrivalRule]
  generalize hrun : idealRun (tickRule (by decide : 2 ≤ microRadius)
    (fun q _ _ => q) commands baseActs baseLen) blankM p input = run
  have hzero : run 0 = p := by rw [← hrun]; rfl
  have hcommand : (run 1).1.commands v = commandOfLetter input := by
    rw [← hrun]
    exact commands_afterFirstStep (by decide) (fun q _ _ => q) commands baseActs baseLen p input hslot v
  obtain ⟨hrepNext, _, hslotsNext⟩ := headTick_of_tickRule
    (by decide : 2 ≤ microRadius) micro_le_margin (fun q _ _ => q) commands baseActs baseLen
    v p input hslot (fun step => (run step).1)
    (fun step slot => (run step).2 (slotIndex slot))
    (fun _ => by rw [hrun]) (fun _ _ => by rw [hrun]) view hwf hcells viewTapes
    (by rw [hzero]; exact hslots) (by rw [hzero]; exact hrep) (by rw [hzero]; exact howed)
  rw [hcommand] at hrepNext
  have hshape := PalPeg.ConcreteLocalMachine.wf_viewApply_commandOfLetter hwf hcells input
  exact ⟨_, hrepNext, hslotsNext, hshape.2, hshape.1⟩

/-- The non-head initialization and the input arrival happen in the same tick.
For normal feed `prepared` is the source tape family; for boot it is the family
obtained by installing the floor markers and zero counters at step zero. -/
theorem encoded_afterFeed (baseActs : InputActs)
    (baseLen : ∀ q i ws j, (baseActs q i ws j).length ≤ microRadius)
    (w : List (Fin 2)) (x : State GalilVM) (p : CoreState) (input : Option (Fin 2))
    (prepared : Slot → STape Γm)
    (henc : PalPeg.PhysicalEncoding.Enc w margin x (p.1, prepared))
    (hheads : ∀ v i, p.2 (slotIndex (headSlot v i)) = prepared (headSlot v i))
    (hprepared : ∀ slot, (∀ v i, slot ≠ headSlot v i) →
      PalPeg.CloseoutCoreEnc12.actList blankM (p.2 (slotIndex slot))
        (baseActs p.1 input (fun tape => PalPeg.Local.readWin blankM microRadius (p.2 tape))
          (slotIndex slot)) = prepared slot)
    (hboundary : MacroBoundary p.1) :
    CoreEnc w (feedState input x) (idealRun
      (arrivalRule baseActs baseLen)
      blankM p input 12) := by
  simp only [arrivalRule]
  generalize hrun : idealRun (tickRule (by decide : 2 ≤ microRadius)
    (fun q _ _ => q) commands baseActs baseLen) blankM p input = run
  have hfree : headFreeFields (run 12).1 = headFreeFields p.1 := by
    rw [← hrun]
    exact tickRule_headFree (by decide) (fun q _ _ => q) commands baseActs baseLen p input
      hboundary.1
  have hparts : (run 12).1.polarity = p.1.polarity ∧
      (run 12).1.fppLive = p.1.fppLive ∧ (run 12).1.dpLive = p.1.dpLive := by
    simp only [headFreeFields, Prod.mk.injEq] at hfree
    exact ⟨hfree.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      hfree.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      hfree.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩
  have hviewSource : ∀ v view, HeadSlotsRepAt margin p.1.gap p.1.micro prepared v view →
      HeadSlotsRepAt margin p.1.gap p.1.micro (fun slot => p.2 (slotIndex slot)) v view := by
    rintro v view ⟨viewTapes, hrep, hslots, hcells, hwf⟩
    exact ⟨viewTapes, hrep, fun i => (hheads v i).trans (hslots i), hcells, hwf⟩
  have hviewNext : ∀ v view, HeadSlotsRepAt margin p.1.gap p.1.micro prepared v view →
      HeadSlotsRepAt margin (run 12).1.gap (run 12).1.micro
        (fun slot => (run 12).2 (slotIndex slot)) v
        (PalPeg.ConcreteLocalMachine.viewApply (commandOfLetter input) view) := by
    intro v view hv
    have hnext := head_afterTick baseActs baseLen p input v hboundary.1 (hboundary.2 v) view
      (hviewSource v view hv)
    simpa only [arrivalRule, hrun] using hnext
  refine ⟨⟨encControl_congr hfree.symm (encControl_feed henc.1 input), ?_⟩, ?_⟩
  · refine encTapes_replaceHeadsOfState (z := x) henc.2
      (fun i => by cases input <;> rfl) (fun i => by cases input <;> rfl)
      (feed_counters input x) (feed_places input x) (feed_period input x) (feed_answer input x)
      ?_ ?_ hparts.1 hparts.2.1 hparts.2.2 ?_ ?_
    · intro slot hnotHead
      have hslot : (slotIndex.symm (slotIndex slot)).isLeft = false := by
        rw [Equiv.symm_apply_apply]
        cases slot with
        | inl pair => exact (hnotHead pair.1 pair.2 rfl).elim
        | inr other => rfl
      rw [← hrun, tickRule_otherSlots (by decide) (fun q _ _ => q) commands baseActs baseLen
        p input hboundary.1 (slotIndex slot) hslot]
      exact hprepared slot hnotHead
    · intro v i
      obtain ⟨view, hv⟩ := all_heads_represented henc.2 v
      obtain ⟨viewTapes, hrep, hslots, _, _⟩ := hviewNext v view hv
      dsimp only at hslots ⊢
      rw [hslots i, pos_mapTape]
      exact hrep.margin_le_pos (by decide : 2 ≤ margin) (le_refl margin) i
    · intro v head hh
      rw [feed_heads] at hh
      cases hold : headOf x v with
      | none => simp [hold] at hh
      | some old =>
        have hhead : headAfter input old = head := by simpa [hold] using hh
        obtain ⟨view, viewTapes, habs, hrep, hslots, hcells, hwf⟩ := henc.2.heads v old hold
        obtain ⟨nextTapes, hrepNext, hslotsNext, hcellsNext, hwfNext⟩ :=
          hviewNext v view ⟨viewTapes, hrep, hslots, hcells, hwf⟩
        refine ⟨_, nextTapes, ?_, hrepNext, hslotsNext, hcellsNext, hwfNext⟩
        rw [PalPeg.ConcreteLocalMachine.absHead'_viewApply_commandOfLetter hwf input, habs, hhead]
    · intro _
      obtain ⟨view, hv⟩ := all_heads_represented henc.2 3
      exact ⟨_, hviewNext 3 view hv⟩
  · rw [← hrun]
    apply macroBoundary_of_heads (fun q _ _ => q) commands baseActs baseLen p input hboundary
    intro v
    obtain ⟨view, hv⟩ := all_heads_represented henc.2 v
    exact ⟨view, hviewSource v view hv⟩

noncomputable def feedRule : ActRule (Fin 2) CoreControl Γm tapeCountM microRadius :=
  tickRule (by decide) (fun q _ _ => q) commands (fun _ _ _ _ => []) (by intros; simp)

theorem core_feed (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (input : Option (Fin 2)) (henc : CoreEnc w x p) :
    CoreEnc w (feedState input x) (idealRun feedRule blankM p input 12) :=
  encoded_afterFeed (fun _ _ _ _ => []) (by intros; simp) w x p input
    (fun slot => p.2 (slotIndex slot)) henc.1 (fun _ _ => rfl) (fun _ _ => rfl) henc.2

/-- One real fused feed step, on exactly the running encoding used by the final
consumer. Every internal head/queue condition comes from that encoding. -/
theorem running_feed (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (input : Option (Fin 2))
    (henc : PalPeg.MachineStep.sweepClosure blankM (CoreEnc w) x p) :
    PalPeg.MachineStep.sweepClosure blankM (CoreEnc w) (feedState input x)
      ((compStep (iterRule feedRule 12)).apply blankM p input) :=
  running_fused_step feedRule w x (feedState input x) p input henc
    (fun ideal h => core_feed w x (p.1, ideal) input h)

/-- info: 'PalPeg.PhysicalFeed.running_feed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms running_feed

end PalPeg.PhysicalFeed
