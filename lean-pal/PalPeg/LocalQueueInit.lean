import PalPeg.LocalQueueProgram

/-!
# The first step of a machine: from blank tapes

`compStep_apply` needs every head at least `K` cells from the left edge, and a machine starts on
blank tapes with its heads at the edge.  The `K` left moves of the sweep are clamped at the edge,
so from there the sweep does what it does from a blank tape whose head stands at `K`
(`sweep_blank_edge_shifted`), and the first step of any rule needs no margin
(`compStep_apply_blankEdge`).

The seal of the sealed layout is the blank symbol, so a blank tape with its head at position
`margin` is a stack of `margin` seals, and ten of them represent the empty queue.
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

/-- From the left edge of a blank tape the sweep does what it does from a blank tape
whose head stands at `K`. -/
theorem sweep_blank_edge_shifted (K : ℕ) {edge shifted : STape Γc} (hedge : pos edge = 0)
    (hedgeBlank : AllBlank edge) (hshifted : pos shifted = K) (hshiftedBlank : AllBlank shifted)
    (window : Window Γc K) (displacement : ℤ) :
    TEqG blankc (sweep blankc K shifted window displacement)
      (sweep blankc K edge window displacement) := by
  constructor
  · rw [sweep, sweep, pos_mvRN, pos_cPhase, pos_mvRN, pos_mvLN, pos_mvRN, pos_cPhase, pos_mvRN,
      pos_mvLN, hedge, hshifted]
    omega
  · intro p
    have hmarginEdge : 2 * K ≤ pos ((PalPeg.Local.mvR blankc)^[2 * K]
        ((PalPeg.Local.mvL blankc)^[K] edge)) := by
      rw [pos_mvRN, pos_mvLN]; omega
    have hmarginShifted : 2 * K ≤ pos ((PalPeg.Local.mvR blankc)^[2 * K]
        ((PalPeg.Local.mvL blankc)^[K] shifted)) := by
      rw [pos_mvRN, pos_mvLN]; omega
    rw [sweep, sweep, rd_mvRN, rd_cPhase _ _ _ _ hmarginShifted, rd_mvRN, rd_mvLN, rd_mvRN,
      rd_cPhase _ _ _ _ hmarginEdge, rd_mvRN, rd_mvLN]
    simp only [pos_mvRN, pos_mvLN, hedge, hshifted, hedgeBlank p, hshiftedBlank p]
    simp

/-- **The first step needs no margin.**  From blank tapes at the left edge, a step of
`compStep R` is, up to `TEqG`, the rule's actions applied to blank tapes whose heads stand at
`K`; the control is the rule's. -/
theorem compStep_apply_blankEdge {Terminal Q : Type} {tapeCount K : ℕ}
    (R : ActRule Terminal Q Γc tapeCount K) (control : Q) (input : Option Terminal)
    (edge shifted : Fin tapeCount → STape Γc) (hedge : ∀ tape, pos (edge tape) = 0)
    (hedgeBlank : ∀ tape, AllBlank (edge tape)) (hshifted : ∀ tape, pos (shifted tape) = K)
    (hshiftedBlank : ∀ tape, AllBlank (shifted tape)) :
    ((compStep R).apply blankc (control, edge) input).1
        = R.nq control input (fun tape => readWin blankc K (shifted tape)) ∧
      ∀ tape, TEqG blankc
        (actList blankc (shifted tape)
          (R.acts control input (fun tape => readWin blankc K (shifted tape)) tape))
        (((compStep R).apply blankc (control, edge) input).2 tape) := by
  have hwindows : (fun tape => readWin blankc K (edge tape))
      = fun tape => readWin blankc K (shifted tape) := by
    funext tape i
    rw [readWin_allBlank (hedgeBlank tape), readWin_allBlank (hshiftedBlank tape)]
  refine ⟨?_, fun tape => ?_⟩
  · show R.nq control input (fun tape => readWin blankc K (edge tape)) = _
    rw [hwindows]
  · have hideal := PalPeg.CloseoutCoreEnc12.teq_sweep_actList blankc K (shifted tape)
      (R.acts control input (fun tape => readWin blankc K (shifted tape)) tape)
      (R.len_le _ _ _ _) (hshifted tape).ge
    have hsame := sweep_blank_edge_shifted K (hedge tape) (hedgeBlank tape) (hshifted tape)
      (hshiftedBlank tape)
      (winAfter K (readWin blankc K (shifted tape))
        (R.acts control input (fun tape => readWin blankc K (shifted tape)) tape))
      (dAfter K (readWin blankc K (shifted tape))
        (R.acts control input (fun tape => readWin blankc K (shifted tape)) tape))
    have hgoal : ((compStep R).apply blankc (control, edge) input).2 tape
        = sweep blankc K (edge tape)
            (winAfter K (readWin blankc K (shifted tape))
              (R.acts control input (fun tape => readWin blankc K (shifted tape)) tape))
            (dAfter K (readWin blankc K (shifted tape))
              (R.acts control input (fun tape => readWin blankc K (shifted tape)) tape)) := by
      show sweep blankc K (edge tape) _ _ = _
      simp only [hwindows]
      rfl
    rw [hgoal]
    exact ⟨hideal.1.trans hsame.1, fun p => (hideal.2 p).trans (hsame.2 p)⟩

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

/-- The control the machine starts in: no job running (the counter is past the end of the
program), idle, nothing owed. -/
def initControl : ProgramControl := (.snoc 0, 10, (0, false), .idle, 0)

/-- **Ten stacks of `K` seals represent the empty queue.** -/
theorem microRep_empty_of_seals {margin : ℕ} {tapes : Fin 10 → STape Γc}
    (htape : ∀ tape, StackTape (tapes tape) (List.replicate margin none)) (micro : MicroOp) :
    MicroRep margin RTQueue.empty (micro, initControl.2.2) tapes := by
  refine ⟨⟨fun _ => List.replicate margin none, fun _ => List.replicate margin none,
      List.replicate margin none, rfl, ⟨fun ro => ?_, fun _ => sealed_replicate margin⟩,
      fun _ => by rw [List.length_replicate], fun tape _ => htape _, sealed_replicate margin,
      by rw [List.length_replicate], htape _⟩,
    0, List.replicate margin none, List.replicate margin none, ?_, sealed_replicate margin,
    by rw [List.length_replicate], htape _, sealed_replicate margin,
    by rw [List.length_replicate], htape _⟩
  · cases ro <;> rfl
  · show (0 : ℤ) + ((0 : Fin 3).val : ℤ) + lengthDebt RTQueue.empty.state
      = ((RTQueue.empty : Queue (Fin 2)).lenf : ℤ) - ((RTQueue.empty : Queue (Fin 2)).lenr : ℤ)
    rfl

end Init

end PalPeg.ConcreteLocalMachine
