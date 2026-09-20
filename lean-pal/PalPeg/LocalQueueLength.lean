import PalPeg.LocalQueueMachine

/-!
# The queue of the local machine: the schedule and the lazy length counter

`RTQueue.snoc` / `tail` as fixed sequences of sub-steps, the signed length counter that lags
behind during the reversing phase, the local rotation test, and the counter as two mark stacks.
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

/-! ## The schedule of sub-steps

`RTQueue.snoc` and `RTQueue.tail` are fixed sequences of the sub-steps `sApply`; the only test
between them is `lenr ≤ lenf`, made once, before the two rotation steps. -/

/-- `RTQueue.check` as sub-steps: start a rotation if the rear is longer, two rotation steps,
install.  (`hrot`: a rotation is only started on an idle queue, `RTQueue.PInv.rot`.) -/
theorem check_eq_sApply (q : Queue (Fin 2)) (hrot : q.lenf < q.lenr → q.state = .idle) :
    RTQueue.check q
      = sApply .install (sApply .exec (sApply .exec
          (if q.lenr ≤ q.lenf then q else sApply .rotStart q))) := by
  by_cases hle : q.lenr ≤ q.lenf
  · rw [if_pos hle, RTQueue.check, if_pos hle, exec2_eq_finish]
    rfl
  · have hidle : q.state = .idle := hrot (Nat.lt_of_not_le hle)
    have hstart : sApply .rotStart q = rotStart q := by
      show (if isIdle q.state then rotStart q else q) = rotStart q
      rw [hidle]
      rfl
    rw [if_neg hle, hstart, check_rot q hle, exec2_eq_finish]
    rfl

theorem snoc_eq_sApply (q : Queue (Fin 2)) (a : Fin 2) :
    RTQueue.snoc q a = RTQueue.check (sApply (.snocPush a) q) := rfl

theorem tail_eq_sApply (q : Queue (Fin 2)) (hfront : q.front ≠ []) :
    RTQueue.tail q = RTQueue.check (sApply .inval (sApply .tailPop q)) := by
  obtain ⟨c, f, hcf⟩ : ∃ c f, q.front = c :: f := by
    cases hq : q.front with
    | nil => exact absurd hq hfront
    | cons c f => exact ⟨c, f, rfl⟩
  have hpop : sApply .tailPop q = { q with lenf := q.lenf - 1, front := q.front.tail } := by
    show (if q.front = [] then q else _) = _
    rw [if_neg hfront]
  unfold RTQueue.tail
  rw [hpop]
  simp only [hcf]
  rfl

#print axioms check_eq_sApply
#print axioms tail_eq_sApply

/-! ## The lazy length counter

`lenr ≤ lenf` compares the heights of two stacks, and a rotation start sets `lenf := lenf + lenr`:
neither is a bounded tape operation.  The machine keeps one signed counter `c` instead and lets
it lag behind during the reversing phase: there `c` still owes two units per element of the
forward list not yet reversed, plus two.  A rotation starts with `lenr = |front| + 1`, which is
exactly the debt, so the start does not touch `c`; each reversing step pays two. -/

/-- What the length counter still owes. -/
def lengthDebt : RotationState (Fin 2) → ℤ
  | .reversing _ f _ _ _ => 2 * (f.length : ℤ) + 2
  | _ => 0

/-- The signed length counter of the machine. -/
def LengthCounter (q : Queue (Fin 2)) (counter : ℤ) : Prop :=
  counter + lengthDebt q.state = (q.lenf : ℤ) - (q.lenr : ℤ)

def execLengthDelta : RotationView → ℤ
  | .reversing (some _) (some _) _ => 2
  | .reversing none (some _) true => 2
  | _ => 0

/-- The change of the length counter, selected from the finite observation. -/
def lengthDeltaOfView : SOp → QueueView → ℤ
  | .snocPush _, _ => -1
  | .tailPop, view => if view.frontEmpty then 0 else -1
  | .exec, view => execLengthDelta view.rotation
  | _, _ => 0

/-- **The length counter moves by a bounded amount selected from the observation.**  `hfront`
and `hstart` are facts of the Hood–Melville invariant: a non-empty front has positive recorded
length, and a rotation starts when the rear is one longer than the front. -/
theorem lengthCounter_sApply (op : SOp) (q : Queue (Fin 2)) (counter : ℤ)
    (hcounter : LengthCounter q counter)
    (hfront : op = .tailPop → q.front ≠ [] → 1 ≤ q.lenf)
    (hstart : op = .rotStart → q.state = .idle → q.lenr = q.front.length + 1) :
    LengthCounter (sApply op q) (counter + lengthDeltaOfView op (queueView q)) := by
  unfold LengthCounter at hcounter ⊢
  cases op with
  | snocPush a =>
    show counter + -1 + lengthDebt q.state = (q.lenf : ℤ) - ((q.lenr + 1 : ℕ) : ℤ)
    push_cast
    omega
  | tailPop =>
    by_cases hempty : q.front = []
    · have hview : (queueView q).frontEmpty = true := by simp [queueView, hempty]
      have hsame : sApply .tailPop q = q := by
        show (if q.front = [] then q else _) = q
        rw [if_pos hempty]
      rw [hsame]
      simp only [lengthDeltaOfView, hview, if_true]
      omega
    · have hview : (queueView q).frontEmpty = false := by
        simp [queueView, hempty]
      have hpop : sApply .tailPop q = { q with lenf := q.lenf - 1, front := q.front.tail } := by
        show (if q.front = [] then q else _) = _
        rw [if_neg hempty]
      have hpositive := hfront rfl hempty
      rw [hpop]
      simp only [lengthDeltaOfView, hview]
      show counter + (if false = true then (0 : ℤ) else -1) + lengthDebt q.state
        = ((q.lenf - 1 : ℕ) : ℤ) - (q.lenr : ℤ)
      rw [if_neg (by simp)]
      omega
  | inval =>
    show counter + 0 + lengthDebt (RTQueue.invalidate q.state) = _
    have hdebt : lengthDebt (RTQueue.invalidate q.state) = lengthDebt q.state := by
      cases q.state with
      | idle => rfl
      | done f => rfl
      | reversing ok f f' r r' => rfl
      | appending ok f' r' =>
        cases ok with
        | zero => cases r' <;> rfl
        | succ n => rfl
    rw [hdebt]
    show counter + 0 + lengthDebt q.state = (q.lenf : ℤ) - (q.lenr : ℤ)
    omega
  | rotStart =>
    cases hstate : q.state with
    | idle =>
      have hlength := hstart rfl hstate
      have hrot : sApply .rotStart q = rotStart q := by
        show (if isIdle q.state then rotStart q else q) = rotStart q
        rw [hstate]
        rfl
      rw [hrot]
      rw [hstate] at hcounter
      show counter + 0 + (2 * (q.front.length : ℤ) + 2)
        = ((q.lenf + q.lenr : ℕ) : ℤ) - ((0 : ℕ) : ℤ)
      simp only [lengthDebt] at hcounter
      push_cast
      omega
    | done f =>
      have hsame : sApply .rotStart q = q := by
        show (if isIdle q.state then rotStart q else q) = q
        rw [hstate]
        rfl
      rw [hsame, hstate]
      rw [hstate] at hcounter
      show counter + 0 + _ = _
      omega
    | reversing ok f f' r r' =>
      have hsame : sApply .rotStart q = q := by
        show (if isIdle q.state then rotStart q else q) = q
        rw [hstate]
        rfl
      rw [hsame, hstate]
      rw [hstate] at hcounter
      show counter + 0 + _ = _
      omega
    | appending ok f' r' =>
      have hsame : sApply .rotStart q = q := by
        show (if isIdle q.state then rotStart q else q) = q
        rw [hstate]
        rfl
      rw [hsame, hstate]
      rw [hstate] at hcounter
      show counter + 0 + _ = _
      omega
  | exec =>
    show counter + execLengthDelta (rotationView q.state) + lengthDebt (RTQueue.exec q.state)
      = (q.lenf : ℤ) - (q.lenr : ℤ)
    cases hstate : q.state with
    | idle => rw [hstate] at hcounter; simpa [execLengthDelta, rotationView, RTQueue.exec] using hcounter
    | done f => rw [hstate] at hcounter; simpa [execLengthDelta, rotationView, RTQueue.exec] using hcounter
    | appending ok f' r' =>
      rw [hstate] at hcounter
      cases ok with
      | zero => simpa [execLengthDelta, rotationView, RTQueue.exec, lengthDebt] using hcounter
      | succ n =>
        cases f' <;>
          simpa [execLengthDelta, rotationView, RTQueue.exec, lengthDebt] using hcounter
    | reversing ok f f' r r' =>
      rw [hstate] at hcounter
      simp only [lengthDebt] at hcounter
      cases f with
      | nil =>
        cases r with
        | nil =>
          simp [execLengthDelta, rotationView, RTQueue.exec, lengthDebt] at hcounter ⊢
          omega
        | cons y r =>
          cases r with
          | nil =>
            simp [execLengthDelta, rotationView, RTQueue.exec, lengthDebt] at hcounter ⊢
            omega
          | cons z r =>
            simp [execLengthDelta, rotationView, RTQueue.exec, lengthDebt] at hcounter ⊢
            omega
      | cons x f =>
        cases r with
        | nil =>
          simp [execLengthDelta, rotationView, RTQueue.exec, lengthDebt] at hcounter ⊢
          omega
        | cons y r =>
          simp [execLengthDelta, rotationView, RTQueue.exec, lengthDebt] at hcounter ⊢
          omega
  | install =>
    show counter + 0 + lengthDebt (finish q).state = ((finish q).lenf : ℤ) - ((finish q).lenr : ℤ)
    cases hstate : q.state <;>
      simp [finish, hstate, lengthDebt] at hcounter ⊢ <;> omega

#print axioms lengthCounter_sApply

/-- **The rotation test is local**: the rear is longer than the front exactly when the control is
idle and the length counter is negative.  (Off idle the counter lags, but a rotation is already
running and `hrot` says the rear is not longer.) -/
theorem startsRotation_iff {q : Queue (Fin 2)} {counter : ℤ}
    (hcounter : LengthCounter q counter) (hrot : q.lenf < q.lenr → q.state = .idle) :
    ¬ q.lenr ≤ q.lenf ↔ rotationPhase q.state = .idle ∧ counter < 0 := by
  unfold LengthCounter at hcounter
  constructor
  · intro hlonger
    have hidle := hrot (Nat.lt_of_not_le hlonger)
    rw [hidle] at hcounter
    simp only [lengthDebt] at hcounter
    refine ⟨by rw [hidle]; rfl, ?_⟩
    omega
  · rintro ⟨hphase, hnegative⟩
    have hidle : q.state = .idle := by
      cases hstate : q.state with
      | idle => rfl
      | done f => rw [hstate] at hphase; cases hphase
      | reversing ok f f' r r' => rw [hstate] at hphase; cases hphase
      | appending ok f' r' => rw [hstate] at hphase; cases hphase
    rw [hidle] at hcounter
    simp only [lengthDebt] at hcounter
    omega

/-- **`RTQueue.check` from finite data**: the phase in the control and the sign of the length
counter decide whether a rotation starts; then two rotation steps and the install. -/
theorem check_eq_local (q : Queue (Fin 2)) {counter : ℤ}
    (hcounter : LengthCounter q counter) (hrot : q.lenf < q.lenr → q.state = .idle) :
    RTQueue.check q
      = sApply .install (sApply .exec (sApply .exec
          (if rotationPhase q.state = .idle ∧ counter < 0 then sApply .rotStart q else q))) := by
  rw [check_eq_sApply q hrot]
  by_cases hle : q.lenr ≤ q.lenf
  · have hnot : ¬ (rotationPhase q.state = .idle ∧ counter < 0) := fun h =>
      ((startsRotation_iff hcounter hrot).mpr h) hle
    rw [if_pos hle, if_neg hnot]
  · rw [if_neg hle, if_pos ((startsRotation_iff hcounter hrot).mp hle)]

#print axioms check_eq_local

/-! ## The signed counter as two stacks of marks

A signed counter is a pair of mark stacks, positive and negative, one of them empty.  Increment
and decrement are one cell operation on one of the stacks, selected by whether the opposite stack
is empty: a bounded read. -/

/-- The positive marks of a signed value. -/
def positiveMarks (value : ℤ) : List (Fin 2) := List.replicate value.toNat 0

/-- The negative marks of a signed value. -/
def negativeMarks (value : ℤ) : List (Fin 2) := List.replicate (-value).toNat 0

/-- The operations of an increment on the two stacks, from "the negative stack is empty". -/
def incrementDeltas (negativeEmpty : Bool) : Delta × Delta :=
  if negativeEmpty then (.push 0, .keep) else (.keep, .pop)

/-- The operations of a decrement on the two stacks, from "the positive stack is empty". -/
def decrementDeltas (positiveEmpty : Bool) : Delta × Delta :=
  if positiveEmpty then (.keep, .push 0) else (.pop, .keep)

theorem positiveMarks_isEmpty (value : ℤ) :
    (positiveMarks value).isEmpty = decide (value ≤ 0) := by
  unfold positiveMarks
  rcases lt_or_ge 0 value with hpositive | hnonpositive
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, value.toNat = n + 1 := ⟨value.toNat - 1, by omega⟩
    rw [hn]
    simp [List.replicate_succ]
    omega
  · have hzero : value.toNat = 0 := by omega
    rw [hzero]
    simp
    omega

theorem negativeMarks_isEmpty (value : ℤ) :
    (negativeMarks value).isEmpty = decide (0 ≤ value) := by
  have h := positiveMarks_isEmpty (-value)
  unfold negativeMarks
  unfold positiveMarks at h
  rw [h]
  congr 1
  apply propext
  omega

/-- **Increment is one cell operation per stack, selected by the emptiness of the negative
stack.** -/
theorem marks_increment (value : ℤ) :
    dApply (incrementDeltas (negativeMarks value).isEmpty).1 (positiveMarks value)
        = positiveMarks (value + 1) ∧
      dApply (incrementDeltas (negativeMarks value).isEmpty).2 (negativeMarks value)
        = negativeMarks (value + 1) := by
  rw [negativeMarks_isEmpty]
  unfold incrementDeltas positiveMarks negativeMarks
  by_cases hnonnegative : 0 ≤ value
  · rw [decide_eq_true hnonnegative, if_pos rfl]
    have hpositive : (value + 1).toNat = value.toNat + 1 := by omega
    have hnegative : (-(value + 1)).toNat = 0 := by omega
    have hnegative' : (-value).toNat = 0 := by omega
    rw [hpositive, hnegative, hnegative']
    exact ⟨by simp [dApply, List.replicate_succ], rfl⟩
  · rw [decide_eq_false hnonnegative, if_neg (by simp)]
    have hpositive : (value + 1).toNat = 0 := by omega
    have hpositive' : value.toNat = 0 := by omega
    have hnegative : (-value).toNat = (-(value + 1)).toNat + 1 := by omega
    rw [hpositive, hpositive', hnegative]
    exact ⟨rfl, by simp [dApply, List.replicate_succ]⟩

/-- **Decrement is one cell operation per stack, selected by the emptiness of the positive
stack.** -/
theorem marks_decrement (value : ℤ) :
    dApply (decrementDeltas (positiveMarks value).isEmpty).1 (positiveMarks value)
        = positiveMarks (value - 1) ∧
      dApply (decrementDeltas (positiveMarks value).isEmpty).2 (negativeMarks value)
        = negativeMarks (value - 1) := by
  rw [positiveMarks_isEmpty]
  unfold decrementDeltas positiveMarks negativeMarks
  by_cases hnonpositive : value ≤ 0
  · rw [decide_eq_true hnonpositive, if_pos rfl]
    have hpositive : (value - 1).toNat = 0 := by omega
    have hpositive' : value.toNat = 0 := by omega
    have hnegative : (-(value - 1)).toNat = (-value).toNat + 1 := by omega
    rw [hpositive, hpositive', hnegative]
    exact ⟨rfl, by simp [dApply, List.replicate_succ]⟩
  · rw [decide_eq_false hnonpositive, if_neg (by simp)]
    have hpositive : value.toNat = (value - 1).toNat + 1 := by omega
    have hnegative : (-(value - 1)).toNat = 0 := by omega
    have hnegative' : (-value).toNat = 0 := by omega
    rw [hpositive, hnegative, hnegative']
    exact ⟨by simp [dApply, List.replicate_succ], rfl⟩

/-- The sign test: the value is negative exactly when the negative stack is not empty. -/
theorem negative_iff_marks (value : ℤ) : value < 0 ↔ (negativeMarks value).isEmpty = false := by
  rw [negativeMarks_isEmpty]
  simp

#print axioms marks_increment
#print axioms marks_decrement

end PalPeg.ConcreteLocalMachine
