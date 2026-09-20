import PalPeg.LocalQueueProgram

/-!
# The first step of the queue machine: from blank tapes to the empty queue

`compStep_apply` needs every head at least `K` cells from the left edge, and a machine starts on
blank tapes with its heads at the edge.  So the first step is verified directly on `sweep`.

The seal of the sealed layout is the blank symbol, so a bottom of `K` seals is a blank tape with
its head at position `K`.  A step without actions from the edge does exactly that: the `K` left
moves of the sweep are clamped at the edge, the window written back is blank, and the final right
moves bring the head to `K`.  After this one step the ten tapes represent the empty queue.
-/

set_option autoImplicit false

namespace PalPeg.ConcreteLocalMachine

open PalPeg
open PalPeg.CloseoutCoreStep (Γc blankc)
open PalPeg.CloseoutCoreEnc (cellSym)
open PalPeg.CloseoutCoreEnc12 (Act actList ActRule compStep TEqG winAfter dAfter)
open PalPeg.CloseoutCoreEnc18 (dTape)
open PalPeg.CloseoutCoreEnc25 (SOp RTag roleOf)
open PalPeg.Local (Window idx idx_val pos rd toList readWin readWin_eq sweep cPhase pos_cPhase
  rd_cPhase pos_mvLN pos_mvRN rd_mvLN rd_mvRN)
open PalPeg.Program (STape)
open PalPeg.RTQueue (Queue)

/-- A tape whose cells are all blank. -/
def AllBlank (tape : STape Γc) : Prop := ∀ p, rd blankc tape p = blankc

/-- **A step without actions from the left edge**: the head goes to `K`, the tape stays blank. -/
theorem sweep_blank_edge (K : ℕ) {tape : STape Γc} (hedge : pos tape = 0)
    (hblank : AllBlank tape) {window : Window Γc K} (hwindow : ∀ i, window i = blankc) :
    pos (sweep blankc K tape window 0) = K ∧ AllBlank (sweep blankc K tape window 0) := by
  have htoNat : ((0 : ℤ) + (K : ℤ)).toNat = K := by omega
  constructor
  · rw [sweep, pos_mvRN, pos_cPhase, pos_mvRN, pos_mvLN, htoNat, hedge]
    omega
  · intro p
    have hmargin : 2 * K ≤ pos ((PalPeg.Local.mvR blankc)^[2 * K]
        ((PalPeg.Local.mvL blankc)^[K] tape)) := by
      rw [pos_mvRN, pos_mvLN]
      omega
    rw [sweep, rd_mvRN, rd_cPhase _ _ _ _ hmargin, rd_mvRN, rd_mvLN]
    split
    · exact hwindow _
    · exact hblank p

theorem allBlank_blankTape : AllBlank (STape.blankTape blankc) := by
  intro p
  show ([] ++ blankc :: ([] : List Γc)).getD p blankc = blankc
  cases p with
  | zero => rfl
  | succ n => rfl

theorem readWin_allBlank {K : ℕ} {tape : STape Γc} (hblank : AllBlank tape)
    (i : Fin (2 * K + 1)) : readWin blankc K tape i = blankc := by
  rw [readWin_eq]
  exact hblank _

/-- The cells of a stack of seals are blank. -/
theorem allBlank_dTape_seals (height : ℕ) :
    AllBlank (dTape (List.replicate height none) []) := by
  intro p
  cases height with
  | zero =>
    show ([] ++ blankc :: ([] : List Γc)).getD p blankc = blankc
    cases p <;> rfl
  | succ n =>
    show (((List.replicate n (none : Option (Fin 2))).map cellSym ++ [blankc]).reverse
      ++ cellSym none :: ([] : List Γc)).getD p blankc = blankc
    have hall : ∀ x ∈ ((List.replicate n (none : Option (Fin 2))).map cellSym ++ [blankc]).reverse
        ++ cellSym none :: ([] : List Γc), x = blankc := by
      intro x hx
      simp only [List.mem_append, List.mem_reverse, List.mem_map, List.mem_replicate,
        List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with (⟨cell, ⟨-, hcell⟩, hx⟩ | hx) | hx
      · rw [← hx, hcell]; rfl
      · exact hx
      · rw [hx]; rfl
    rw [List.getD_eq_getElem?_getD]
    cases hget : (((List.replicate n (none : Option (Fin 2))).map cellSym ++ [blankc]).reverse
      ++ cellSym none :: ([] : List Γc))[p]? with
    | none => rfl
    | some x => exact hall x (List.mem_of_getElem? hget)

/-- A blank tape with its head at `K` is a stack of `K` seals. -/
theorem stackTape_of_blank {K : ℕ} {tape : STape Γc} (hpos : pos tape = K)
    (hblank : AllBlank tape) : StackTape tape (List.replicate K none) := by
  refine ⟨[], ?_, fun p => ?_⟩
  · rw [hpos, pos_dTape, List.length_replicate]
  · rw [hblank p, allBlank_dTape_seals K p]

theorem sealed_replicate (height : ℕ) :
    Sealed (List.replicate height (none : Option (Fin 2))) := by
  intro a
  cases height <;> simp [List.replicate_succ]

/-! ## The idle step and the first step -/

section Init

variable {K : ℕ} {Terminal : Type}

/-- Past the end of its program, with nothing owed, the machine makes no action on any tape. -/
theorem programRule_acts_idle (hK : 2 ≤ K) {control : ProgramControl}
    (hidle : currentOp control = .incLength) (howed : control.2.2.2.2 = 0)
    (input : Option Terminal) (windows : Fin 10 → Window Γc K) (tape : Fin 10) :
    (programRule Terminal hK).acts control input windows tape = [] := by
  show (microRule Terminal hK).acts (currentOp control, control.2.2) input windows tape = []
  rw [hidle]
  by_cases htape : tape.val < 8
  · have hcast : tape = Fin.castLE (by omega : 8 ≤ 10) ⟨tape.val, htape⟩ := Fin.ext rfl
    rw [hcast, microRule_acts_queue]
    rfl
  · by_cases hpositive : tape = positiveTape
    · rw [hpositive, microRule_acts_positive]
      show cellActsOfTop (lengthDeltas (lengthMoveOf .incLength _ _ control.2.2.2.2) _ _).1 false _
        = []
      rw [howed]
      rfl
    · have hnegative : tape = negativeTape := by
        apply Fin.ext
        have hne : tape.val ≠ 8 := fun h => hpositive (Fin.ext h)
        show tape.val = 9
        omega
      rw [hnegative, microRule_acts_negative]
      show cellActsOfTop (lengthDeltas (lengthMoveOf .incLength _ _ control.2.2.2.2) _ _).2 false _
        = []
      rw [howed]
      rfl

/-- The control the machine starts in: no job running (the counter is past the end of the
program), idle, nothing owed. -/
def initControl : ProgramControl := (.snoc 0, 10, (0, false), .idle, 0)

theorem currentOp_initControl : currentOp initControl = .incLength := rfl

/-- **Ten stacks of `K` seals represent the empty queue.** -/
theorem microRep_empty_of_seals {tapes : Fin 10 → STape Γc}
    (htape : ∀ tape, StackTape (tapes tape) (List.replicate K none)) (micro : MicroOp) :
    MicroRep K RTQueue.empty (micro, initControl.2.2) tapes := by
  refine ⟨⟨fun _ => List.replicate K none, fun _ => List.replicate K none,
      List.replicate K none, rfl, ⟨fun ro => ?_, fun _ => sealed_replicate K⟩,
      fun _ => by rw [List.length_replicate], fun tape _ => htape _, sealed_replicate K,
      by rw [List.length_replicate], htape _⟩,
    0, List.replicate K none, List.replicate K none, ?_, sealed_replicate K,
    by rw [List.length_replicate], htape _, sealed_replicate K,
    by rw [List.length_replicate], htape _⟩
  · cases ro <;> rfl
  · show (0 : ℤ) + ((0 : Fin 3).val : ℤ) + lengthDebt RTQueue.empty.state
      = ((RTQueue.empty : Queue (Fin 2)).lenf : ℤ) - ((RTQueue.empty : Queue (Fin 2)).lenr : ℤ)
    rfl

/-- **The first step: from blank tapes to the empty queue.**  One step of the machine from its
initial control on blank tapes leaves the control as it is and the ten tapes representing the
empty queue, with every bottom `K` seals high. -/
theorem programInit (hK : 2 ≤ K) (input : Option Terminal) (micro : MicroOp) :
    ((programLocalStep Terminal hK).apply blankc
        (initControl, fun _ => STape.blankTape blankc) input).1 = initControl ∧
      MicroRep K RTQueue.empty (micro, initControl.2.2)
        ((programLocalStep Terminal hK).apply blankc
          (initControl, fun _ => STape.blankTape blankc) input).2 := by
  have hwindow : ∀ tape : Fin 10, ∀ i,
      readWin blankc K ((fun _ : Fin 10 => STape.blankTape blankc) tape) i = blankc :=
    fun _ i => readWin_allBlank allBlank_blankTape i
  have htape : ∀ tape : Fin 10,
      StackTape (((programLocalStep Terminal hK).apply blankc
        (initControl, fun _ => STape.blankTape blankc) input).2 tape)
        (List.replicate K none) := by
    intro tape
    have hacts := programRule_acts_idle (Terminal := Terminal) hK currentOp_initControl rfl input
      (fun tape => readWin blankc K ((fun _ : Fin 10 => STape.blankTape blankc) tape)) tape
    show StackTape (sweep blankc K (STape.blankTape blankc)
      (winAfter K (readWin blankc K (STape.blankTape blankc))
        ((programRule Terminal hK).acts initControl input
          (fun tape => readWin blankc K ((fun _ : Fin 10 => STape.blankTape blankc) tape)) tape))
      (dAfter K (readWin blankc K (STape.blankTape blankc))
        ((programRule Terminal hK).acts initControl input
          (fun tape => readWin blankc K ((fun _ : Fin 10 => STape.blankTape blankc) tape)) tape)))
      _
    rw [hacts]
    have hdisplacement : dAfter K (readWin blankc K (STape.blankTape blankc)) ([] : List (Act Γc))
        = 0 := by
      unfold dAfter
      simp
    rw [hdisplacement]
    obtain ⟨hpos, hblank⟩ := sweep_blank_edge K (tape := STape.blankTape blankc) rfl
      allBlank_blankTape (window := winAfter K (readWin blankc K (STape.blankTape blankc)) [])
      (fun i => by
        show (readWin blankc K (STape.blankTape blankc)) (idx K (i : ℕ)) = blankc
        exact readWin_allBlank allBlank_blankTape _)
    exact stackTape_of_blank hpos hblank
  refine ⟨?_, ?_⟩
  · -- the control: no sub-step runs, the counter is clamped at the end
    show (programRule Terminal hK).nq initControl input _ = initControl
    show (initControl.1, nextCounter initControl.2.1,
      ((microRule Terminal hK).nq (currentOp initControl, initControl.2.2) input _).2)
        = initControl
    rw [currentOp_initControl, microRule_nq_none hK _ input _ rfl]
    rfl
  · exact microRep_empty_of_seals htape micro

#print axioms programInit

end Init

end PalPeg.ConcreteLocalMachine
