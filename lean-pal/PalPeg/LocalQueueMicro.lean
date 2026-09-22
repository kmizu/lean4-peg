import PalPeg.LocalQueueLength

/-!
# The micro-programmed queue machine

Ten tapes, micro-operations `sub` / `checkStart` / `incLength`, the representation `MicroRep`,
and the soundness of the rule before the sweep (`microRule_sound`).
-/

set_option autoImplicit false

namespace PalPeg.ConcreteLocalMachine

open PalPeg
open PalPeg.CloseoutCoreEnc20 (Delta)
open PalPeg.CloseoutCoreEnc21 (SRole SRoles SInj sinj_iff toAddr toAddr_eq pushRearD tailD revD
  appStartD appD invalDoneD sRoleList finish rotPerm donePerm rotRolesS doneRolesS
  exec2_eq_finish)
open PalPeg.CloseoutCoreEnc20 (rotStart dApply check_rot)
open PalPeg.CloseoutCoreStep (Γc blankc)
open PalPeg.CloseoutCoreEnc (cellSym)
open PalPeg.CloseoutCoreEnc12 (Act actList actOnG ActRule compStep compStep_apply TEqG)
open PalPeg.Local (Window idx idx_val pos rd rd_pos rd_eq readWin readWin_eq pos_applyAction
  rd_applyAction)
open PalPeg.Program (STape)
open PalPeg.CloseoutCoreEnc18 (dTape topSym popActs pushActs pop_dTape push_dTape)
open PalPeg.CloseoutCoreEnc25 (SOp RTag rotTag doneTag roleOf roleOf_rotTag roleOf_doneTag
  sinj_roleOf sbound_roleOf isIdle isDone isIdle_eq isDone_eq sApply deltaOf tagStep invalDelta execDelta
  toAddr_keep)
open PalPeg.RTQueue (Queue RotationState)

/-! ## The micro-programmed queue machine

Ten tapes: `0`–`7` are the tapes of `queueRule`, `8` and `9` the positive and negative marks of
the length counter.  A micro-operation is a sub-step, the rotation test of `RTQueue.check`, or
one increment of the length counter paying a unit of what the counter owes. -/

inductive MicroOp where
  | sub (op : SOp)
  | checkStart
  | incLength
  deriving DecidableEq

/-- The control: the micro-operation, the role tag, the rotation phase, the units owed to the
length counter. -/
abbrev MicroControl : Type := MicroOp × RTag × RotationPhase × Fin 3

/-- The sub-step a micro-operation runs, if any: `checkStart` starts a rotation exactly when the
control is idle and the length counter is negative. -/
def effectiveOp : MicroOp → RotationPhase → Bool → Option SOp
  | .sub op, _, _ => some op
  | .checkStart, .idle, true => some .rotStart
  | _, _, _ => none

inductive LengthMove where
  | stay | decrement | increment
  deriving DecidableEq

/-- What a micro-operation does to the length counter tapes now. -/
def lengthMoveOf (micro : MicroOp) (effective : Option SOp) (view : QueueView) (owed : Fin 3) :
    LengthMove :=
  match micro, effective with
  | .incLength, _ => if owed.val = 0 then .stay else .increment
  | _, some op => if lengthDeltaOfView op view = -1 then .decrement else .stay
  | _, none => .stay

/-- The units owed after a micro-operation: a reversing rotation step owes two, an increment
pays one. -/
def owedAfter (micro : MicroOp) (effective : Option SOp) (view : QueueView) (owed : Fin 3) :
    Fin 3 :=
  match micro, effective with
  | .incLength, _ => ⟨owed.val - 1, by omega⟩
  | _, some op => if lengthDeltaOfView op view = 2 then 2 else owed
  | _, none => owed

section MicroRule

variable {K : ℕ}

def positiveTape : Fin 10 := 8
def negativeTape : Fin 10 := 9

/-- The windows of the eight queue tapes. -/
def queueWindows (windows : Fin 10 → Window Γc K) : Fin 8 → Window Γc K :=
  fun tape => windows (Fin.castLE (by omega) tape)

def lengthDeltas (move : LengthMove) (positiveEmpty negativeEmpty : Bool) : Delta × Delta :=
  match move with
  | .stay => (.keep, .keep)
  | .decrement => decrementDeltas positiveEmpty
  | .increment => incrementDeltas negativeEmpty

/-- **The micro-programmed queue machine as a rule.** -/
def microRule (Terminal : Type) (hK : 2 ≤ K) : ActRule Terminal MicroControl Γc 10 K where
  nq := fun control input windows =>
    let negativeNonempty := (symLetter (centreSym (windows negativeTape))).isSome
    let effective := effectiveOp control.1 control.2.2.1 negativeNonempty
    let view := queueViewOfWindows (SOp.exec, control.2.1, control.2.2.1) (queueWindows windows)
    let owed := owedAfter control.1 effective view control.2.2.2
    match effective with
    | some op =>
        let next := (queueRule Terminal hK).nq (op, control.2.1, control.2.2.1) input
          (queueWindows windows)
        (control.1, next.2.1, next.2.2, owed)
    | none => (control.1, control.2.1, control.2.2.1, owed)
  acts := fun control input windows tape =>
    let negativeNonempty := (symLetter (centreSym (windows negativeTape))).isSome
    let positiveEmpty := (symLetter (centreSym (windows positiveTape))).isNone
    let effective := effectiveOp control.1 control.2.2.1 negativeNonempty
    let view := queueViewOfWindows (SOp.exec, control.2.1, control.2.2.1) (queueWindows windows)
    if htape : tape.val < 8 then
      match effective with
      | some op =>
          (queueRule Terminal hK).acts (op, control.2.1, control.2.2.1) input
            (queueWindows windows) ⟨tape.val, htape⟩
      | none => []
    else
      let deltas := lengthDeltas (lengthMoveOf control.1 effective view control.2.2.2)
        positiveEmpty (!negativeNonempty)
      if tape.val = 8 then cellActsOfTop deltas.1 false (centreSym (windows tape))
      else cellActsOfTop deltas.2 false (centreSym (windows tape))
  len_le := fun control input windows tape => by
    dsimp only
    split
    · split
      · exact (queueRule Terminal hK).len_le _ _ _ _
      · simp
    · split
      · exact le_trans (cellActsOfTop_length _ _ _) hK
      · exact le_trans (cellActsOfTop_length _ _ _) hK

/-- The local step of the micro-programmed queue machine. -/
def microLocalStep (Terminal : Type) (hK : 2 ≤ K) :
    PalPeg.Local.LocalStep Terminal MicroControl Γc 10 K :=
  compStep (microRule Terminal hK)

end MicroRule

/-! ## The representation of the micro-programmed machine -/

theorem QueueRep.of_teqG {K : ℕ} {q : Queue (Fin 2)} {control : QueueControl}
    {tapes tapes' : Fin 8 → STape Γc} (hrep : QueueRep K q control tapes)
    (hteq : ∀ tape, TEqG blankc (tapes tape) (tapes' tape)) : QueueRep K q control tapes' := by
  obtain ⟨stack, junk, bottom, hphase, hlays, hheight, htapes, hsealed, hbottom, hcounter⟩ := hrep
  exact ⟨stack, junk, bottom, hphase, hlays, hheight,
    fun tape htape => (htapes tape htape).of_teqG (hteq tape), hsealed, hbottom,
    hcounter.of_teqG (hteq validTape)⟩

/-- A pop of marks over a bottom meets a mark, not the bottom. -/
theorem cellApply_marks (delta : Delta) (marks : List (Fin 2)) (bottom : List (Option (Fin 2)))
    (hpop : delta = .pop → marks ≠ []) :
    cellApply delta false (marks.map some ++ bottom) = (dApply delta marks).map some ++ bottom := by
  cases delta with
  | keep => rfl
  | push a => rfl
  | pop =>
    cases marks with
    | nil => exact absurd rfl (hpop rfl)
    | cons mark rest => rfl

theorem topLetter_marks_isNone {marks : List (Fin 2)} {bottom : List (Option (Fin 2))}
    (hsealed : Sealed bottom) :
    (topLetter (marks.map some ++ bottom)).isNone = marks.isEmpty := by
  rw [topLetter_sealed hsealed]
  cases marks <;> rfl

theorem lengthDeltaOfView_cases (op : SOp) (view : QueueView) :
    lengthDeltaOfView op view = -1 ∨ lengthDeltaOfView op view = 0 ∨
      lengthDeltaOfView op view = 2 := by
  obtain ⟨frontEmpty, rotation⟩ := view
  cases op with
  | snocPush a => simp [lengthDeltaOfView]
  | tailPop => cases frontEmpty <;> simp [lengthDeltaOfView]
  | inval => simp [lengthDeltaOfView]
  | rotStart => simp [lengthDeltaOfView]
  | install => simp [lengthDeltaOfView]
  | exec =>
    cases rotation with
    | idle => simp [lengthDeltaOfView, execLengthDelta]
    | done => simp [lengthDeltaOfView, execLengthDelta]
    | appending validZero forwardHead rebuilt => simp [lengthDeltaOfView, execLengthDelta]
    | reversing forwardHead reverseHead single =>
      cases forwardHead <;> cases reverseHead <;> cases single <;>
        simp [lengthDeltaOfView, execLengthDelta]

/-- The sub-step a micro-operation runs on the abstract queue, if any. -/
def abstractOp (micro : MicroOp) (q : Queue (Fin 2)) : Option SOp :=
  match micro with
  | .sub op => some op
  | .checkStart => if q.lenr ≤ q.lenf then none else some .rotStart
  | .incLength => none

/-- The queue after a micro-operation. -/
def microApply (micro : MicroOp) (q : Queue (Fin 2)) : Queue (Fin 2) :=
  match abstractOp micro q with
  | some op => sApply op q
  | none => q

/-- The control after a micro-operation. -/
def microControlAfter (control : MicroControl) (q : Queue (Fin 2)) : MicroControl :=
  match abstractOp control.1 q with
  | some op =>
      (control.1, tagStep op q control.2.1, rotationPhase (sApply op q).state,
        owedAfter control.1 (some op) (queueView q) control.2.2.2)
  | none =>
      (control.1, control.2.1, control.2.2.1,
        owedAfter control.1 none (queueView q) control.2.2.2)

/-- **The micro-programmed machine represents the queue and its length counter**: the queue
tapes as in `QueueRep`, and the two mark tapes carry a signed value that, with the units still
owed, is the lazy length counter. -/
def MicroRep (K : ℕ) (q : Queue (Fin 2)) (control : MicroControl)
    (tapes : Fin 10 → STape Γc) : Prop :=
  QueueRep K q (SOp.exec, control.2.1, control.2.2.1)
      (fun tape => tapes (Fin.castLE (by omega) tape)) ∧
    ∃ (counter : ℤ) (positiveBottom negativeBottom : List (Option (Fin 2))),
      LengthCounter q (counter + (control.2.2.2.val : ℤ)) ∧
      Sealed positiveBottom ∧ K ≤ positiveBottom.length ∧
      StackTape (tapes positiveTape) ((positiveMarks counter).map some ++ positiveBottom) ∧
      Sealed negativeBottom ∧ K ≤ negativeBottom.length ∧
      StackTape (tapes negativeTape) ((negativeMarks counter).map some ++ negativeBottom)

section MicroSound

variable {K : ℕ} {Terminal : Type}

/-- The sub-step the rule runs: from the control and the top of the negative length tape. -/
def ruleOp (control : MicroControl) (windows : Fin 10 → Window Γc K) : Option SOp :=
  effectiveOp control.1 control.2.2.1 (symLetter (centreSym (windows negativeTape))).isSome

/-- The observation the rule makes of the queue tapes. -/
def ruleView (control : MicroControl) (windows : Fin 10 → Window Γc K) : QueueView :=
  queueViewOfWindows (SOp.exec, control.2.1, control.2.2.1) (queueWindows windows)

theorem microRule_nq_some (hK : 2 ≤ K) (control : MicroControl) (input : Option Terminal)
    (windows : Fin 10 → Window Γc K) {op : SOp} (hop : ruleOp control windows = some op) :
    (microRule Terminal hK).nq control input windows
      = (control.1,
          ((queueRule Terminal hK).nq (op, control.2.1, control.2.2.1) input
            (queueWindows windows)).2.1,
          ((queueRule Terminal hK).nq (op, control.2.1, control.2.2.1) input
            (queueWindows windows)).2.2,
          owedAfter control.1 (some op) (ruleView control windows) control.2.2.2) := by
  unfold ruleOp at hop
  show (match effectiveOp control.1 control.2.2.1
      (symLetter (centreSym (windows negativeTape))).isSome with
    | some op => _
    | none => _) = _
  rw [hop]
  rfl

theorem microRule_nq_none (hK : 2 ≤ K) (control : MicroControl) (input : Option Terminal)
    (windows : Fin 10 → Window Γc K) (hop : ruleOp control windows = none) :
    (microRule Terminal hK).nq control input windows
      = (control.1, control.2.1, control.2.2.1,
          owedAfter control.1 none (ruleView control windows) control.2.2.2) := by
  unfold ruleOp at hop
  show (match effectiveOp control.1 control.2.2.1
      (symLetter (centreSym (windows negativeTape))).isSome with
    | some op => _
    | none => _) = _
  rw [hop]
  rfl

theorem microRule_acts_queue (hK : 2 ≤ K) (control : MicroControl) (input : Option Terminal)
    (windows : Fin 10 → Window Γc K) (tape : Fin 8) :
    (microRule Terminal hK).acts control input windows (Fin.castLE (by omega) tape)
      = match ruleOp control windows with
        | some op =>
            (queueRule Terminal hK).acts (op, control.2.1, control.2.2.1) input
              (queueWindows windows) tape
        | none => [] := by
  have htape : (Fin.castLE (by omega : 8 ≤ 10) tape).val < 8 := tape.isLt
  show (if h : (Fin.castLE (by omega : 8 ≤ 10) tape).val < 8 then _ else _) = _
  rw [dif_pos htape]
  rfl

/-- The move of the length counter the rule makes. -/
def ruleLengthDeltas (control : MicroControl) (windows : Fin 10 → Window Γc K) : Delta × Delta :=
  lengthDeltas
    (lengthMoveOf control.1 (ruleOp control windows) (ruleView control windows) control.2.2.2)
    (symLetter (centreSym (windows positiveTape))).isNone
    (!(symLetter (centreSym (windows negativeTape))).isSome)

theorem microRule_acts_positive (hK : 2 ≤ K) (control : MicroControl) (input : Option Terminal)
    (windows : Fin 10 → Window Γc K) :
    (microRule Terminal hK).acts control input windows positiveTape
      = cellActsOfTop (ruleLengthDeltas control windows).1 false
          (centreSym (windows positiveTape)) := rfl

theorem microRule_acts_negative (hK : 2 ≤ K) (control : MicroControl) (input : Option Terminal)
    (windows : Fin 10 → Window Γc K) :
    (microRule Terminal hK).acts control input windows negativeTape
      = cellActsOfTop (ruleLengthDeltas control windows).2 false
          (centreSym (windows negativeTape)) := rfl

end MicroSound

section MicroSoundness

variable {K : ℕ} {Terminal : Type}

theorem topLetter_marks_isSome {marks : List (Fin 2)} {bottom : List (Option (Fin 2))}
    (hsealed : Sealed bottom) :
    (topLetter (marks.map some ++ bottom)).isSome = !marks.isEmpty := by
  rw [topLetter_sealed hsealed]
  cases marks <;> rfl

/-- **The micro-programmed rule is sound before the sweep.**  `hfront`, `hstart`, `hrot` are
facts of the Hood–Melville invariant, each asked only of the micro-operation that needs it;
`howed` and `hnoStart` are facts of the micro-program (a rotation step runs with nothing owed; a
rotation is started by `checkStart` only). -/
theorem microRule_sound (hK : 2 ≤ K) {margin : ℕ} (hmarginLe : K ≤ margin)
    {q : Queue (Fin 2)} {control : MicroControl}
    {tapes : Fin 10 → STape Γc} (hrep : MicroRep margin q control tapes) (input : Option Terminal)
    (hfront : control.1 = .sub .tailPop → q.front ≠ [] → 1 ≤ q.lenf)
    (hstart : control.1 = .checkStart → q.state = .idle → ¬ q.lenr ≤ q.lenf →
      q.lenr = q.front.length + 1)
    (hrot : control.1 = .checkStart → q.lenf < q.lenr → q.state = .idle)
    (howed : control.1 ≠ .incLength → control.2.2.2 = 0)
    (hnoStart : control.1 ≠ .sub .rotStart) :
    (∀ tape : Fin 10, margin ≤ pos (tapes tape)) ∧
      (microRule Terminal hK).nq control input (fun tape => readWin blankc K (tapes tape))
        = microControlAfter control q ∧
      ∀ tapes' : Fin 10 → STape Γc,
        (∀ tape, TEqG blankc
          (actList blankc (tapes tape)
            ((microRule Terminal hK).acts control input
              (fun tape => readWin blankc K (tapes tape)) tape))
          (tapes' tape)) →
        MicroRep margin (microApply control.1 q) (microControlAfter control q) tapes' := by
  obtain ⟨hqueue, counter, positiveBottom, negativeBottom, hlength, hsealedP, hheightP, htapeP,
    hsealedN, hheightN, htapeN⟩ := hrep
  let windows : Fin 10 → Window Γc K := fun tape => readWin blankc K (tapes tape)
  let queueTapes : Fin 8 → STape Γc := fun tape => tapes (Fin.castLE (by omega) tape)
  have hwindows : queueWindows windows = fun tape => readWin blankc K (queueTapes tape) := rfl
  -- the observation of the queue tapes
  have hview : ruleView control windows = queueView q := by
    obtain ⟨stack, junk, bottom, hphase, hlays, hheight, htapes, hsealed, hbottom,
      hcounterTape⟩ := hqueue
    exact (queueViewOfWindows_eq (K := K) (by omega) hphase hlays
      (fun i => hmarginLe.trans (hheight i)) htapes hsealed (hmarginLe.trans hbottom)
      hcounterTape).2
  have hphase : control.2.2.1 = rotationPhase q.state := by
    obtain ⟨stack, junk, bottom, hphase, -⟩ := hqueue
    exact hphase
  -- the tops of the length tapes
  have hpositiveHeight : K ≤ ((positiveMarks counter).map some ++ positiveBottom).length := by
    simp only [List.length_append]; omega
  have hnegativeHeight : K ≤ ((negativeMarks counter).map some ++ negativeBottom).length := by
    simp only [List.length_append]; omega
  have hpositiveTop : centreSym (windows positiveTape)
      = topSym ((positiveMarks counter).map some ++ positiveBottom) :=
    htapeP.centreSym_eq hpositiveHeight
  have hnegativeTop : centreSym (windows negativeTape)
      = topSym ((negativeMarks counter).map some ++ negativeBottom) :=
    htapeN.centreSym_eq hnegativeHeight
  have hpositiveEmpty : (symLetter (centreSym (windows positiveTape))).isNone
      = (positiveMarks counter).isEmpty := by
    rw [hpositiveTop, ← topLetter_eq_sym, topLetter_marks_isNone hsealedP]
  have hnegativeNonempty : (symLetter (centreSym (windows negativeTape))).isSome
      = !(negativeMarks counter).isEmpty := by
    rw [hnegativeTop, ← topLetter_eq_sym, topLetter_marks_isSome hsealedN]
  -- the sub-step the rule runs is the abstract one
  have hop : ruleOp control windows = abstractOp control.1 q := by
    unfold ruleOp
    rw [hnegativeNonempty]
    cases hmicro : control.1 with
    | sub op => rfl
    | incLength => rfl
    | checkStart =>
      have hzero : control.2.2.2 = 0 := howed (by rw [hmicro]; simp)
      have hcounter : LengthCounter q counter := by
        rw [hzero] at hlength
        simpa using hlength
      have hiff := startsRotation_iff hcounter (hrot hmicro)
      have hsign := negative_iff_marks counter
      show effectiveOp .checkStart control.2.2.1 (!(negativeMarks counter).isEmpty)
        = if q.lenr ≤ q.lenf then none else some .rotStart
      by_cases hle : q.lenr ≤ q.lenf
      · rw [if_pos hle]
        have hnot : ¬ (rotationPhase q.state = .idle ∧ counter < 0) := fun h => hiff.mpr h hle
        rw [hphase]
        cases hidle : rotationPhase q.state with
        | idle =>
          have hnonnegative : ¬ counter < 0 := fun h => hnot ⟨hidle, h⟩
          have hempty : (negativeMarks counter).isEmpty = true := by
            cases hvalue : (negativeMarks counter).isEmpty with
            | true => rfl
            | false => exact absurd (hsign.mpr hvalue) hnonnegative
          rw [hempty]
          rfl
        | reversing => rfl
        | appending => rfl
        | done => rfl
      · rw [if_neg hle]
        obtain ⟨hidle, hnegative⟩ := hiff.mp hle
        rw [hphase, hidle, hsign.mp hnegative]
        rfl
  -- the margins
  obtain ⟨hqueueMargin, -, -⟩ := queueRule_sound (Terminal := Terminal) hK hmarginLe hqueue input
  have hmargin : ∀ tape : Fin 10, margin ≤ pos (tapes tape) := by
    intro tape
    by_cases htape : tape.val < 8
    · exact hqueueMargin ⟨tape.val, htape⟩
    · by_cases hpositive : tape = positiveTape
      · rw [hpositive, htapeP.pos_eq]
        simp only [List.length_append]; omega
      · have hnegative : tape = negativeTape := by
          apply Fin.ext
          have hne : tape.val ≠ 8 := fun h => hpositive (Fin.ext h)
          show tape.val = 9
          omega
        rw [hnegative, htapeN.pos_eq]
        simp only [List.length_append]; omega
  have howedZero : control.1 ≠ .incLength → LengthCounter q counter := by
    intro hne
    rw [howed hne] at hlength
    simpa using hlength
  refine ⟨hmargin, ?_, ?_⟩
  · -- the next control
    unfold microControlAfter
    cases hab : abstractOp control.1 q with
    | none =>
      rw [microRule_nq_none hK control input windows (hop.trans hab), hview]
    | some op =>
      rw [microRule_nq_some hK control input windows (hop.trans hab), hview, hwindows]
      have hq : QueueRep margin q (op, control.2.1, control.2.2.1) queueTapes := hqueue
      obtain ⟨-, hnq, -⟩ := queueRule_sound (Terminal := Terminal) hK hmarginLe hq input
      rw [hnq]
  · intro tapes' hacts
    unfold microApply microControlAfter
    cases hab : abstractOp control.1 q with
    | none =>
      -- the queue tapes are kept, the length counter may take one increment
      show MicroRep margin q (control.1, control.2.1, control.2.2.1,
        owedAfter control.1 none (queueView q) control.2.2.2) tapes'
      have hruleNone := hop.trans hab
      refine ⟨QueueRep.of_teqG hqueue (fun tape => ?_), ?_⟩
      · have h := hacts (Fin.castLE (by omega) tape)
        rw [microRule_acts_queue, hruleNone] at h
        exact h
      · have hdeltas : ruleLengthDeltas control windows
            = lengthDeltas (lengthMoveOf control.1 none (queueView q) control.2.2.2)
                (positiveMarks counter).isEmpty (negativeMarks counter).isEmpty := by
          unfold ruleLengthDeltas
          rw [hruleNone, hview, hpositiveEmpty, hnegativeNonempty, Bool.not_not]
        have hP := hacts positiveTape
        have hN := hacts negativeTape
        rw [microRule_acts_positive, hdeltas, hpositiveTop] at hP
        rw [microRule_acts_negative, hdeltas, hnegativeTop] at hN
        by_cases hpay : control.1 = .incLength ∧ control.2.2.2.val ≠ 0
        · -- one increment, one unit paid
          obtain ⟨hmicro, howedPositive⟩ := hpay
          obtain ⟨hincP, hincN⟩ := marks_increment counter
          have hmove : lengthMoveOf control.1 none (queueView q) control.2.2.2 = .increment := by
            rw [hmicro]; simp [lengthMoveOf, howedPositive]
          rw [hmove] at hP hN
          refine ⟨counter + 1, positiveBottom, negativeBottom, ?_, hsealedP, hheightP, ?_,
            hsealedN, hheightN, ?_⟩
          · have hafter : ((owedAfter control.1 none (queueView q) control.2.2.2).val : ℤ)
                = (control.2.2.2.val : ℤ) - 1 := by
              rw [hmicro]
              simp only [owedAfter]
              omega
            rw [hafter]
            have h := hlength
            unfold LengthCounter at h ⊢
            omega
          · refine StackTape.of_teqG ?_ hP
            rw [← hincP, ← cellApply_marks _ _ _ (by
              intro hpopEq
              simp only [lengthDeltas, incrementDeltas] at hpopEq
              split at hpopEq <;> simp at hpopEq)]
            exact htapeP.cellApply _ _
          · refine StackTape.of_teqG ?_ hN
            rw [← hincN, ← cellApply_marks _ _ _ (by
              intro hpopEq
              simp only [lengthDeltas, incrementDeltas] at hpopEq
              split at hpopEq
              · simp at hpopEq
              · next hnonempty =>
                intro hnil
                rw [hnil] at hnonempty
                simp at hnonempty)]
            exact htapeN.cellApply _ _
        · -- nothing moves
          have hmove : lengthMoveOf control.1 none (queueView q) control.2.2.2 = .stay := by
            cases hmicro : control.1 with
            | sub op => rw [hmicro] at hab; cases hab
            | checkStart => rfl
            | incLength =>
              have hzero : control.2.2.2.val = 0 := by
                by_contra hne
                exact hpay ⟨hmicro, hne⟩
              simp [lengthMoveOf, hzero]
          have hafter : owedAfter control.1 none (queueView q) control.2.2.2 = control.2.2.2 := by
            cases hmicro : control.1 with
            | sub op => rw [hmicro] at hab; cases hab
            | checkStart => rfl
            | incLength =>
              have hzero : control.2.2.2.val = 0 := by
                by_contra hne
                exact hpay ⟨hmicro, hne⟩
              apply Fin.ext
              simp only [owedAfter]
              omega
          rw [hmove] at hP hN
          rw [hafter]
          exact ⟨counter, positiveBottom, negativeBottom, hlength, hsealedP, hheightP,
            htapeP.of_teqG hP, hsealedN, hheightN, htapeN.of_teqG hN⟩
    | some op =>
      show MicroRep margin (sApply op q) (control.1, tagStep op q control.2.1,
        rotationPhase (sApply op q).state,
        owedAfter control.1 (some op) (queueView q) control.2.2.2) tapes'
      have hruleSome := hop.trans hab
      have hnotInc : control.1 ≠ .incLength := by
        intro hmicro
        rw [hmicro] at hab
        cases hab
      have hcounter := howedZero hnotInc
      have hq : QueueRep margin q (op, control.2.1, control.2.2.1) queueTapes := hqueue
      obtain ⟨-, -, hsound⟩ := queueRule_sound (Terminal := Terminal) hK hmarginLe hq input
      have hqueue' := hsound (fun tape => tapes' (Fin.castLE (by omega) tape)) (fun tape => by
        have h := hacts (Fin.castLE (by omega) tape)
        rw [microRule_acts_queue, hruleSome] at h
        exact h)
      refine ⟨hqueue', ?_⟩
      -- the length counter
      have hstartOp : op = .rotStart → q.state = .idle → q.lenr = q.front.length + 1 := by
        intro hopEq hidle
        cases hmicro : control.1 with
        | sub op' =>
          rw [hmicro] at hab
          have : op' = op := Option.some.inj hab
          exact absurd (by rw [hmicro, this, hopEq]) hnoStart
        | incLength => exact absurd hmicro hnotInc
        | checkStart =>
          rw [hmicro] at hab
          by_cases hle : q.lenr ≤ q.lenf
          · simp [abstractOp, hle] at hab
          · exact hstart hmicro hidle hle
      have hfrontOp : op = .tailPop → q.front ≠ [] → 1 ≤ q.lenf := by
        intro hopEq
        cases hmicro : control.1 with
        | sub op' =>
          rw [hmicro] at hab
          have hsame : op' = op := Option.some.inj hab
          exact hfront (by rw [hmicro, hsame, hopEq])
        | incLength => exact absurd hmicro hnotInc
        | checkStart =>
          rw [hmicro] at hab
          by_cases hle : q.lenr ≤ q.lenf
          · simp [abstractOp, hle] at hab
          · simp [abstractOp, hle] at hab
            rw [← hab] at hopEq
            cases hopEq
      have hnext := lengthCounter_sApply op q counter hcounter hfrontOp hstartOp
      have hdeltas : ruleLengthDeltas control windows
          = lengthDeltas (lengthMoveOf control.1 (some op) (queueView q) control.2.2.2)
              (positiveMarks counter).isEmpty (negativeMarks counter).isEmpty := by
        unfold ruleLengthDeltas
        rw [hruleSome, hview, hpositiveEmpty, hnegativeNonempty, Bool.not_not]
      have hP := hacts positiveTape
      have hN := hacts negativeTape
      rw [microRule_acts_positive, hdeltas, hpositiveTop] at hP
      rw [microRule_acts_negative, hdeltas, hnegativeTop] at hN
      have hmoveOf : lengthMoveOf control.1 (some op) (queueView q) control.2.2.2
          = if lengthDeltaOfView op (queueView q) = -1 then .decrement else .stay := by
        cases hmicro : control.1 with
        | incLength => exact absurd hmicro hnotInc
        | sub op' => rfl
        | checkStart => rfl
      have howedOf : owedAfter control.1 (some op) (queueView q) control.2.2.2
          = if lengthDeltaOfView op (queueView q) = 2 then 2 else control.2.2.2 := by
        cases hmicro : control.1 with
        | incLength => exact absurd hmicro hnotInc
        | sub op' => rfl
        | checkStart => rfl
      have hzero : control.2.2.2 = 0 := howed hnotInc
      rw [hmoveOf] at hP hN
      rw [howedOf, hzero]
      rcases lengthDeltaOfView_cases op (queueView q) with hdelta | hdelta | hdelta
      · -- a decrement now
        rw [hdelta, if_pos rfl] at hP hN
        rw [hdelta] at hnext
        obtain ⟨hdecP, hdecN⟩ := marks_decrement counter
        refine ⟨counter - 1, positiveBottom, negativeBottom, ?_, hsealedP, hheightP, ?_,
          hsealedN, hheightN, ?_⟩
        · rw [if_neg (by omega)]
          have h := hnext
          unfold LengthCounter at h ⊢
          simp only [Fin.val_zero, Int.natCast_zero] at h ⊢
          omega
        · refine StackTape.of_teqG ?_ hP
          rw [← hdecP, ← cellApply_marks _ _ _ (by
            intro hpopEq
            simp only [lengthDeltas, decrementDeltas] at hpopEq
            split at hpopEq
            · simp at hpopEq
            · next hnonempty =>
              intro hnil
              rw [hnil] at hnonempty
              simp at hnonempty)]
          exact htapeP.cellApply _ _
        · refine StackTape.of_teqG ?_ hN
          rw [← hdecN, ← cellApply_marks _ _ _ (by
            intro hpopEq
            simp only [lengthDeltas, decrementDeltas] at hpopEq
            split at hpopEq <;> simp at hpopEq)]
          exact htapeN.cellApply _ _
      · -- nothing moves, nothing owed
        rw [hdelta, if_neg (by omega)] at hP hN
        rw [hdelta] at hnext
        refine ⟨counter, positiveBottom, negativeBottom, ?_, hsealedP, hheightP,
          htapeP.of_teqG hP, hsealedN, hheightN, htapeN.of_teqG hN⟩
        rw [if_neg (by omega)]
        have h := hnext
        unfold LengthCounter at h ⊢
        simp only [Fin.val_zero, Int.natCast_zero] at h ⊢
        omega
      · -- two units owed
        rw [hdelta, if_neg (by omega)] at hP hN
        rw [hdelta] at hnext
        refine ⟨counter, positiveBottom, negativeBottom, ?_, hsealedP, hheightP,
          htapeP.of_teqG hP, hsealedN, hheightN, htapeN.of_teqG hN⟩
        rw [if_pos hdelta]
        have h := hnext
        unfold LengthCounter at h ⊢
        have htwo : ((2 : Fin 3).val : ℤ) = 2 := rfl
        rw [htwo]
        omega

#print axioms microRule_sound

end MicroSoundness

end PalPeg.ConcreteLocalMachine
