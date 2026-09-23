import PalPeg.PhysicalFeed
import PalPeg.LocalBlankSweep
import PalPeg.LocalViewInit

/-!
# Blank boot and the first input

The first sweep supplies the physical margin. Step zero writes the finite
floor/zero-counter layout, and the eleven view steps receive the same input
letter as normal feed. There is no preliminary tick and no input buffering delay.
-/
set_option autoImplicit false
namespace PalPeg.PhysicalBootFeed
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract PalPeg.PhysicalFeed
open PalPeg.PhysicalBoundary
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.Program (STape)
open PalPeg.CloseoutCoreEnc12 (Act ActRule compStep actList)
open PalPeg.CloseoutCoreStep (Γc blankc)
open PalPeg.LocalStepFusion
open PalPeg.LocalBlankState (blankView zeroTape)

/-- Only finite control fields; neither the word nor its length is stored. -/
noncomputable def bootControl : CoreControl where
  ctl := ⟨.init, 2048, false, false, false, false⟩
  chainTag := .idle
  chainPhase := 0
  chainForward := false
  chainBroken := false
  fppMode := .run
  fppFinalStage := false
  fppPc := some ⟨0, by have := fppBound_gt_start; omega⟩
  fppDone := true
  dpPc := some ⟨0, by unfold dpBound; omega⟩
  dpDone := true
  searchMode := .idle
  searchFinalStage := false
  searchQuarter := 0
  periodOnly := false
  placeGap := fun _ => false
  onLetterBit := false
  leftFirstBit := false
  polarity := fun _ => true
  gap := fun _ => true
  micro := fun _ => (.incLength, PalPeg.ConcreteLocalMachine.initControl.2.2)
  job := fun _ => none
  commands := fun _ => .stay
  slot := 0
  fppLive := false
  dpLive := false

theorem initialState_eq : initialState =
    ⟨PalPeg.GalilScaffoldController.initial 2048, PalPeg.GalilBootVM.initVM0 []⟩ := rfl

theorem boot_boundary : MacroBoundary bootControl := ⟨rfl, fun _ => rfl⟩

theorem boot_control (w : List (Fin 2)) : EncControl w initialState bootControl where
  ctl := rfl
  chainTag := rfl
  chainPhase := rfl
  chainForward := rfl
  chainBroken := rfl
  fppMode := rfl
  fppFinalStage := rfl
  fppPc := rfl
  fppDone := rfl
  dpPc := rfl
  dpDone := rfl
  searchMode := rfl
  searchFinalStage := rfl
  searchQuarter := rfl
  periodOnly := rfl
  placeGap := by
    intro i place hp
    rw [initialState_eq] at hp
    fin_cases i <;> simp [placeOf, PalPeg.GalilBootVM.initVM0] at hp <;> subst place <;> rfl
  onLetter := rfl
  leftFirst := rfl

def viewTape (height : ℕ) : STape Γc :=
  PalPeg.CloseoutCoreEnc18.dTape (List.replicate height none) []

theorem viewTape_rep (height : ℕ) :
    PalPeg.ConcreteLocalMachine.StackTape (viewTape height) (List.replicate height none) :=
  ⟨[], rfl, fun _ => rfl⟩

theorem viewTape_map (height : ℕ) :
    mapTape encCell (viewTape height) =
      (⟨List.replicate height blankM, blankM, []⟩ : STape Γm) := by
  cases height with
  | zero => rfl
  | succ n =>
    simp only [viewTape, List.replicate_succ, PalPeg.CloseoutCoreEnc18.dTape,
      mapTape, List.map_append, List.map_replicate, List.map_cons, List.map_nil]
    change (⟨List.replicate n blankM ++ [blankM], blankM, []⟩ : STape Γm) = _
    rw [← List.replicate_succ', List.replicate_succ]

theorem view_blank_rep : PalPeg.ConcreteLocalMachine.ViewRep margin blankView true
    (bootControl.micro 0) (fun _ => viewTape margin) := by
  have h := PalPeg.ConcreteLocalMachine.viewRep_empty_of_seals
    (by decide : 1 ≤ margin) (fun _ => viewTape_rep margin)
    PalPeg.ConcreteLocalMachine.MicroOp.incLength
  exact ⟨rfl, h.queue, h.back, h.near⟩

def shiftedBlank : STape Γm := ⟨List.replicate margin blankM, blankM, []⟩
def zeroCounter : STape Γm := padLeft margin (mapTape encSeg zeroTape)
def floorBlank : STape Γm := padLeft margin (STape.blankTape blankM)

noncomputable def preparedTapes (slot : Slot) : STape Γm :=
  if slot.isLeft then shiftedBlank
  else if (counterCarrier slot).isSome then zeroCounter else floorBlank

theorem prepared_head (v : Fin 4) (i : Fin 12) :
    preparedTapes (headSlot v i) = mapTape encCell (viewTape margin) := by
  rw [viewTape_map]
  rfl

theorem initial_view (v : Fin 4) :
    HeadSlotsRepAt margin bootControl.gap bootControl.micro preparedTapes v blankView :=
  ⟨fun _ => viewTape margin, view_blank_rep, prepared_head v,
    ⟨[], rfl⟩, PalPeg.LocalBlankState.wf_blankView⟩

theorem prepared_enc (w : List (Fin 2)) :
    PalPeg.PhysicalEncoding.Enc w margin initialState (bootControl, preparedTapes) := by
  refine ⟨boot_control w, ?_⟩
  refine {
    margins := ?_
    heads := ?_
    idleHead := fun _ => ⟨blankView, initial_view 3⟩
    fpp := fun _ => rfl
    dp := fun _ => rfl
    idleShape := fun _ => ⟨STape.blankTape 6, rfl⟩
    counters := ?_
    places := ?_
    mirrors := ?_
    period := ?_
    answer := ?_ }
  · intro slot
    change margin ≤ PalPeg.Local.pos (preparedTapes slot)
    unfold preparedTapes
    split
    · simp [shiftedBlank, PalPeg.Local.pos]
    · split <;> simp only [zeroCounter, floorBlank, pos_padLeft, pos_mapTape] <;> omega
  · intro v head hh
    rw [initialState_eq] at hh
    have hv : v ≠ 3 := by
      intro heq
      subst v
      simp [headOf, PalPeg.GalilBootVM.initVM0] at hh
    have heq : head = PalPeg.GalilScaffoldChainInputSupply.initialHead [] := by
      fin_cases v <;> simp [headOf, PalPeg.GalilBootVM.initVM0] at hh ⊢ <;>
        first | exact hh.symm | exact (hv rfl).elim
    subst head
    exact ⟨blankView, fun _ => viewTape margin, rfl, view_blank_rep,
      prepared_head v, ⟨[], rfl⟩, PalPeg.LocalBlankState.wf_blankView⟩
  · intro c value hc
    have hvalue : value = PalPeg.GalilScaffoldCounter.reset := by
      rw [initialState_eq] at hc
      fin_cases c <;> simp [counterOf, PalPeg.GalilBootVM.initVM0] at hc <;> exact hc.symm
    subst value
    refine ⟨zeroTape, rfl, ?_⟩
    simp [preparedTapes, counterCarrier, zeroCounter]
  · intro i place hp
    have heq : place = PalPeg.GalilBootVM.emptyPlace := by
      rw [initialState_eq] at hp
      fin_cases i <;> simp [placeOf, PalPeg.GalilBootVM.initVM0] at hp <;> exact hp.symm
    subst place
    refine ⟨STape.blankTape blankc, [], ?_, ?_, rfl⟩
    · intro a; simp
    · exact ⟨[], rfl, fun _ => rfl⟩
  · intro m value hc
    have hvalue : value = PalPeg.GalilScaffoldCounter.reset := by
      rw [initialState_eq] at hc
      fin_cases m <;> simp [mirrorSource, counterOf, PalPeg.GalilBootVM.initVM0] at hc <;>
        exact hc.symm
    subst value
    refine ⟨zeroTape, rfl, ?_⟩
    simp [preparedTapes, counterCarrier, zeroCounter]
  · intro tape hp
    change (none : Option PalPeg.GalilScaffoldChainPeriod.Tape) = some tape at hp
    cases hp
  · intro tape hp
    change (none : Option PalPeg.GalilScaffoldTape.Tape) = some tape at hp
    cases hp

/-- The head tapes are already stacks of seals at the sweep's new origin.
Every other slot gets a floor; counter carriers also get their zero separator. -/
def bootActsAt (slot : Slot) : List (Act Γm) :=
  if slot.isLeft then []
  else if (counterCarrier slot).isSome then
    [some (bottomM, .right), some (encSeg PalPeg.LocalCounter.sep, .right),
      some (encSeg PalPeg.LocalCounter.sep, .stay)]
  else [some (bottomM, .right)]

noncomputable def bootActs : InputActs := fun _ _ _ tape => bootActsAt (slotIndex.symm tape)

theorem bootActs_bound : ∀ q input ws tape, (bootActs q input ws tape).length ≤ microRadius := by
  intro q input ws tape
  unfold bootActs bootActsAt
  split
  · decide
  · split <;> decide

noncomputable def bootRule : ActRule (Fin 2) CoreControl Γm tapeCountM microRadius :=
  arrivalRule bootActs bootActs_bound

theorem bootActs_prepared (slot : Slot) :
    actList blankM shiftedBlank (bootActsAt slot) = preparedTapes slot := by
  unfold bootActsAt preparedTapes
  split
  · rfl
  · split <;> rfl

theorem boot_core (w : List (Fin 2)) (input : Option (Fin 2)) :
    CoreEnc w (feedState input initialState)
      (idealRun bootRule blankM (bootControl, fun _ => shiftedBlank) input 12) := by
  unfold bootRule
  apply encoded_afterFeed bootActs bootActs_bound w initialState
    (bootControl, fun _ => shiftedBlank) input preparedTapes (prepared_enc w)
  · intro v i
    rfl
  · intro slot _
    simpa only [bootActs, Equiv.symm_apply_apply] using bootActs_prepared slot
  · exact boot_boundary

theorem shiftedBlank_pos : PalPeg.Local.pos shiftedBlank = margin := by
  simp [shiftedBlank, PalPeg.Local.pos]

theorem shiftedBlank_blank : PalPeg.LocalBlankSweep.AllBlank blankM shiftedBlank := by
  intro pos
  simp [PalPeg.Local.rd, PalPeg.Local.toList, shiftedBlank, ← List.replicate_succ']

/-- Blank-edge transport with the rule kept abstract during the proof. -/
theorem sweep_from_blank {K : ℕ} (R : ActRule (Fin 2) CoreControl Γm tapeCountM K)
    (E : State GalilVM → CoreState → Prop) (x : State GalilVM)
    (q : CoreControl) (input : Option (Fin 2)) (T U : Fin tapeCountM → STape Γm)
    (hT : ∀ tape, PalPeg.CloseoutCoreEnc12.TEqG blankM (STape.blankTape blankM) (T tape))
    (hpos : ∀ tape, PalPeg.Local.pos (U tape) = K)
    (hblank : ∀ tape, PalPeg.LocalBlankSweep.AllBlank blankM (U tape))
    (hideal : E x (idealStep R blankM (q, U) input)) :
    PalPeg.MachineStep.sweepClosure blankM E x ((compStep R).apply blankM (q, T) input) := by
  obtain ⟨hcontrol, htapes⟩ := PalPeg.LocalBlankSweep.compStep_apply_blankEdge blankM
    R q input T U (fun tape => (hT tape).1.symm)
    (fun tape pos => (hT tape).2 pos ▸ PalPeg.LocalBlankSweep.allBlank_blankTape blankM pos)
    hpos hblank
  refine ⟨(idealStep R blankM (q, U) input).2, ?_, htapes⟩
  rw [hcontrol]
  exact hideal

/-- The first physical step accepts the actual left-edge blank configuration,
and the same input is delivered to the four views before it returns. -/
theorem boot_sweep (w : List (Fin 2)) (input : Option (Fin 2))
    (T : Fin tapeCountM → STape Γm)
    (hT : ∀ tape, PalPeg.CloseoutCoreEnc12.TEqG blankM (STape.blankTape blankM) (T tape)) :
    PalPeg.MachineStep.sweepClosure blankM (CoreEnc w) (feedState input initialState)
      ((compStep (iterRule bootRule 12)).apply blankM (bootControl, T) input) := by
  apply sweep_from_blank (iterRule bootRule 12) (CoreEnc w) (feedState input initialState)
    bootControl input T (fun _ => shiftedBlank) hT
    (fun _ => shiftedBlank_pos) (fun _ => shiftedBlank_blank)
  rw [iterRule_ideal blankM bootRule 12 (bootControl, fun _ => shiftedBlank) input
    (fun _ => shiftedBlank_pos.ge), idealIter_eq_idealRun]
  exact boot_core w input

/-- info: 'PalPeg.PhysicalBootFeed.boot_sweep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boot_sweep

/-- The remaining normal none-step is supplied once; both boot and feed are
fixed here and use the same alphabet, control, tapes and macro radius. -/
abbrev CoreStep := PalPeg.Local.LocalStep (Fin 2) CoreControl Γm tapeCountM macroRadius

noncomputable def bootStep : CoreStep := compStep (iterRule bootRule 12)
noncomputable def feedStep : CoreStep := compStep (iterRule feedRule 12)

noncomputable def selectStep (noneStep : CoreStep) (q : Control)
    (input : Option (Fin 2)) : CoreControl × CoreStep :=
  match q with
  | .inl _ => (bootControl, bootStep)
  | .inr control =>
    match input with
    | none => (control, noneStep)
    | some _ => (control, feedStep)

noncomputable def machineStep (noneStep : CoreStep) :
    PalPeg.Local.LocalStep (Fin 2) Control Γm tapeCountM macroRadius where
  next := fun q input ws =>
    let selected := selectStep noneStep q input
    let result := selected.2.next selected.1 input ws
    (Sum.inr result.1, result.2)
  disp_le := fun q input ws tape =>
    (selectStep noneStep q input).2.disp_le (selectStep noneStep q input).1 input ws tape

theorem machine_apply (noneStep : CoreStep) (q : Control) (T : Fin tapeCountM → STape Γm)
    (input : Option (Fin 2)) :
    (machineStep noneStep).apply blankM (q, T) input =
      (Sum.inr (((selectStep noneStep q input).2).apply blankM
        ((selectStep noneStep q input).1, T) input).1,
        (((selectStep noneStep q input).2).apply blankM
          ((selectStep noneStep q input).1, T) input).2) := rfl

theorem machine_apply_boot (noneStep : CoreStep) (input : Option (Fin 2))
    (T : Fin tapeCountM → STape Γm) :
    (machineStep noneStep).apply blankM (Sum.inl (), T) input =
      (Sum.inr (bootStep.apply blankM (bootControl, T) input).1,
        (bootStep.apply blankM (bootControl, T) input).2) := by
  rw [machine_apply]
  simp only [selectStep]

theorem machine_apply_feed (noneStep : CoreStep) (a : Fin 2) (p : CoreState) :
    (machineStep noneStep).apply blankM (Sum.inr p.1, p.2) (some a) =
      (Sum.inr (feedStep.apply blankM p (some a)).1,
        (feedStep.apply blankM p (some a)).2) := by
  rw [machine_apply]
  simp only [selectStep, Prod.eta]

theorem machine_apply_none (noneStep : CoreStep) (p : CoreState) :
    (machineStep noneStep).apply blankM (Sum.inr p.1, p.2) none =
      (Sum.inr (noneStep.apply blankM p none).1, (noneStep.apply blankM p none).2) := rfl

theorem enc_running (w : List (Fin 2)) (x : State GalilVM) (p : CoreState) :
    PalPeg.PhysicalContract.Enc w x (Sum.inr p.1, p.2) ↔
      PalPeg.MachineStep.sweepClosure blankM (CoreEnc w) x p := Iff.rfl

/-- The final consumer's input step, including the first letter on blank tapes.
The theorem holds for any choice of the remaining none-step, with no hypothesis
about that step and no side condition about input availability. -/
theorem forwardFeed (noneStep : CoreStep) (w : List (Fin 2))
    (x : State GalilVM) (p : PhysicalState) (a : Fin 2)
    (henc : PalPeg.PhysicalContract.Enc w x p) :
    PalPeg.PhysicalContract.Enc w (PalPeg.GalilArriveChain.arriveState' a x)
      ((machineStep noneStep).apply blankM p (some a)) := by
  rcases p with ⟨q, T⟩
  cases q with
  | inl bootTag =>
    cases bootTag
    obtain ⟨rfl, hblank⟩ := henc
    rw [machine_apply_boot]
    rw [enc_running]
    exact boot_sweep w (some a) T hblank
  | inr control =>
    rw [machine_apply_feed noneStep a (control, T)]
    rw [enc_running]
    exact running_feed w x (control, T) (some a) henc

/-- The first none-step changes only the representation, as required when the
empty initial abstract state is starved. This is an ordinary scheduled step. -/
theorem boot_none (noneStep : CoreStep) (w : List (Fin 2))
    (T : Fin tapeCountM → STape Γm)
    (henc : PalPeg.PhysicalContract.Enc w initialState (initialControl, T)) :
    PalPeg.PhysicalContract.Enc w initialState
      ((machineStep noneStep).apply blankM (initialControl, T) none) := by
  simp only [initialControl] at henc ⊢
  rw [machine_apply_boot]
  rw [enc_running]
  exact boot_sweep w none T henc.2

theorem initial_starved : PalPeg.FrameFunction.starvedTest initialState = true := rfl

theorem first_letter_unstarves (a : Fin 2) :
    PalPeg.FrameFunction.starvedTest (feedState (some a) initialState) = false := rfl

/-- info: 'PalPeg.PhysicalBootFeed.forwardFeed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forwardFeed

/-- info: 'PalPeg.PhysicalBootFeed.boot_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boot_none

end PalPeg.PhysicalBootFeed
