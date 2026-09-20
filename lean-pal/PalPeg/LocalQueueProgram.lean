import PalPeg.LocalQueueMicro

/-!
# The micro-programs of the queue

`RTQueue.snoc` and `RTQueue.tail` — the two operations an input view makes on its queue
(`LocalInputView.arrive`, `stepRight`) — are fixed lists of micro-operations of the machine of
`PalPeg.LocalQueueMicro`.  The two increments after each rotation step pay what a reversing step
owes to the lazy length counter; on the abstract queue they do nothing.
-/

set_option autoImplicit false

namespace PalPeg.ConcreteLocalMachine

open PalPeg
open PalPeg.CloseoutCoreEnc22 (tail_hrot)
open PalPeg.CloseoutCoreEnc25 (SOp RTag sApply)
open PalPeg.RTQueue (Queue)
open PalPeg.CloseoutCoreStep (Γc blankc)
open PalPeg.CloseoutCoreEnc12 (actList TEqG ActRule compStep compStep_apply)
open PalPeg.Local (readWin pos)
open PalPeg.Program (STape)

/-- The abstract effect of a list of micro-operations. -/
def runMicro (program : List MicroOp) (q : Queue (Fin 2)) : Queue (Fin 2) :=
  program.foldl (fun queue micro => microApply micro queue) q

/-- `RTQueue.check`: the rotation test, then two rotation steps each followed by the two
increments it may owe, then the install. -/
def checkProgram : List MicroOp :=
  [.checkStart, .sub .exec, .incLength, .incLength, .sub .exec, .incLength, .incLength,
    .sub .install]

def snocProgram (a : Fin 2) : List MicroOp := .sub (.snocPush a) :: checkProgram

/-- The program of a dequeue from a non-empty front. -/
def tailProgram : List MicroOp := .sub .tailPop :: .sub .inval :: checkProgram

theorem runMicro_check (q : Queue (Fin 2)) (hrot : q.lenf < q.lenr → q.state = .idle) :
    runMicro checkProgram q = RTQueue.check q := by
  rw [check_eq_sApply q hrot]
  by_cases hle : q.lenr ≤ q.lenf
  · simp [runMicro, checkProgram, microApply, abstractOp, hle]
  · simp [runMicro, checkProgram, microApply, abstractOp, hle]

/-- **An enqueue is the program `snocProgram`.** -/
theorem runMicro_snoc {q : Queue (Fin 2)} (hq : RTQueue.Inv q) (a : Fin 2) :
    runMicro (snocProgram a) q = RTQueue.snoc q a := by
  have hrot : (sApply (.snocPush a) q).lenf < (sApply (.snocPush a) q).lenr →
      (sApply (.snocPush a) q).state = .idle := (RTQueue.snoc_pinv hq a).rot
  show runMicro checkProgram (sApply (.snocPush a) q) = _
  rw [runMicro_check _ hrot]
  rfl

/-- **A dequeue from a non-empty front is the program `tailProgram`.** -/
theorem runMicro_tail {q : Queue (Fin 2)} (hq : RTQueue.Inv q) (hfront : q.front ≠ []) :
    runMicro tailProgram q = RTQueue.tail q := by
  have hpop : sApply .tailPop q = { q with lenf := q.lenf - 1, front := q.front.tail } := by
    show (if q.front = [] then q else _) = _
    rw [if_neg hfront]
  rw [tail_eq_sApply q hfront]
  show runMicro checkProgram (sApply .inval (sApply .tailPop q)) = _
  rw [runMicro_check]
  rw [hpop]
  exact tail_hrot q hq

#print axioms runMicro_snoc
#print axioms runMicro_tail

/-! ## Running a micro-program on the machine -/

/-- What a micro-operation needs of the queue it runs on (Hood–Melville facts). -/
def MicroPremises (micro : MicroOp) (q : Queue (Fin 2)) : Prop :=
  (micro = .sub .tailPop → q.front ≠ [] → 1 ≤ q.lenf) ∧
  (micro = .checkStart →
    (q.state = .idle → ¬ q.lenr ≤ q.lenf → q.lenr = q.front.length + 1) ∧
    (q.lenf < q.lenr → q.state = .idle))

/-- The premises at every point of a program. -/
def PremisesAlong : List MicroOp → Queue (Fin 2) → Prop
  | [], _ => True
  | micro :: rest, q => MicroPremises micro q ∧ PremisesAlong rest (microApply micro q)

/-- The shape of a program the length counter can follow: nothing is owed when a sub-step or a
rotation test runs, a rotation step is followed by increments enough to pay the two units it may
owe, and a rotation is started by `checkStart` only. -/
def OwedOk : List MicroOp → ℕ → Prop
  | [], owed => owed = 0
  | .incLength :: rest, owed => OwedOk rest (owed - 1)
  | .sub .exec :: rest, owed => owed = 0 ∧ OwedOk rest 2
  | .sub .rotStart :: _, _ => False
  | _ :: rest, owed => owed = 0 ∧ OwedOk rest 0

theorem OwedOk.mono : ∀ {program : List MicroOp} {owed owed' : ℕ},
    OwedOk program owed → owed' ≤ owed → OwedOk program owed'
  | [], owed, owed', h, hle => by
    have h' : owed = 0 := h
    exact (by omega : owed' = 0)
  | .incLength :: rest, owed, owed', h, hle => by
    have h' : OwedOk rest (owed - 1) := h
    show OwedOk rest (owed' - 1)
    exact OwedOk.mono h' (by omega)
  | .checkStart :: rest, owed, owed', h, hle => by
    have h' : owed = 0 ∧ OwedOk rest 0 := h
    exact (⟨by omega, h'.2⟩ : owed' = 0 ∧ OwedOk rest 0)
  | .sub op :: rest, owed, owed', h, hle => by
    cases op with
    | exec =>
      have h' : owed = 0 ∧ OwedOk rest 2 := h
      exact (⟨by omega, h'.2⟩ : owed' = 0 ∧ OwedOk rest 2)
    | rotStart => exact (h : False).elim
    | snocPush a =>
      have h' : owed = 0 ∧ OwedOk rest 0 := h
      exact (⟨by omega, h'.2⟩ : owed' = 0 ∧ OwedOk rest 0)
    | tailPop =>
      have h' : owed = 0 ∧ OwedOk rest 0 := h
      exact (⟨by omega, h'.2⟩ : owed' = 0 ∧ OwedOk rest 0)
    | inval =>
      have h' : owed = 0 ∧ OwedOk rest 0 := h
      exact (⟨by omega, h'.2⟩ : owed' = 0 ∧ OwedOk rest 0)
    | install =>
      have h' : owed = 0 ∧ OwedOk rest 0 := h
      exact (⟨by omega, h'.2⟩ : owed' = 0 ∧ OwedOk rest 0)

theorem OwedOk.head {micro : MicroOp} {rest : List MicroOp} {owed : ℕ}
    (h : OwedOk (micro :: rest) owed) :
    (micro ≠ .incLength → owed = 0) ∧ micro ≠ .sub .rotStart := by
  cases micro with
  | incLength => exact ⟨fun hne => absurd rfl hne, by simp⟩
  | checkStart =>
    have h' : owed = 0 ∧ OwedOk rest 0 := h
    exact ⟨fun _ => h'.1, by simp⟩
  | sub op =>
    cases op with
    | rotStart => exact (h : False).elim
    | exec =>
      have h' : owed = 0 ∧ OwedOk rest 2 := h
      exact ⟨fun _ => h'.1, by simp⟩
    | snocPush a =>
      have h' : owed = 0 ∧ OwedOk rest 0 := h
      exact ⟨fun _ => h'.1, by simp⟩
    | tailPop =>
      have h' : owed = 0 ∧ OwedOk rest 0 := h
      exact ⟨fun _ => h'.1, by simp⟩
    | inval =>
      have h' : owed = 0 ∧ OwedOk rest 0 := h
      exact ⟨fun _ => h'.1, by simp⟩
    | install =>
      have h' : owed = 0 ∧ OwedOk rest 0 := h
      exact ⟨fun _ => h'.1, by simp⟩

/-- Only a rotation step can owe. -/
theorem lengthDelta_two {op : SOp} {view : QueueView} (h : lengthDeltaOfView op view = 2) :
    op = .exec := by
  obtain ⟨frontEmpty, rotation⟩ := view
  cases op with
  | exec => rfl
  | snocPush a => simp [lengthDeltaOfView] at h
  | tailPop => cases frontEmpty <;> simp [lengthDeltaOfView] at h
  | inval => simp [lengthDeltaOfView] at h
  | rotStart => simp [lengthDeltaOfView] at h
  | install => simp [lengthDeltaOfView] at h

/-- After a micro-operation the rest of the program can still be followed. -/
theorem OwedOk.tail {micro : MicroOp} {rest : List MicroOp} {owed : Fin 3} {q : Queue (Fin 2)}
    (h : OwedOk (micro :: rest) owed.val) :
    OwedOk rest (owedAfter micro (abstractOp micro q) (queueView q) owed).val := by
  cases micro with
  | incLength => exact (h : OwedOk rest (owed.val - 1))
  | checkStart =>
    have h' : owed.val = 0 ∧ OwedOk rest 0 := h
    have howed : owed = 0 := Fin.ext h'.1
    have hafter : owedAfter .checkStart (abstractOp .checkStart q) (queueView q) owed = 0 := by
      rw [howed]
      show owedAfter .checkStart (if q.lenr ≤ q.lenf then none else some .rotStart)
        (queueView q) 0 = 0
      split <;> simp [owedAfter, lengthDeltaOfView]
    rw [hafter]
    exact h'.2
  | sub op =>
    show OwedOk rest (if lengthDeltaOfView op (queueView q) = 2 then (2 : Fin 3) else owed).val
    by_cases htwo : lengthDeltaOfView op (queueView q) = 2
    · rw [if_pos htwo]
      have hexec := lengthDelta_two htwo
      subst hexec
      exact (h : owed.val = 0 ∧ OwedOk rest 2).2
    · rw [if_neg htwo]
      cases op with
      | rotStart => exact (h : False).elim
      | exec =>
        have h' : owed.val = 0 ∧ OwedOk rest 2 := h
        rw [h'.1]
        exact OwedOk.mono h'.2 (by omega)
      | snocPush a =>
        have h' : owed.val = 0 ∧ OwedOk rest 0 := h
        rw [h'.1]; exact h'.2
      | tailPop =>
        have h' : owed.val = 0 ∧ OwedOk rest 0 := h
        rw [h'.1]; exact h'.2
      | inval =>
        have h' : owed.val = 0 ∧ OwedOk rest 0 := h
        rw [h'.1]; exact h'.2
      | install =>
        have h' : owed.val = 0 ∧ OwedOk rest 0 := h
        rw [h'.1]; exact h'.2

section Run

variable {K : ℕ} {Terminal : Type}

/-- The part of the control a program moves: role tag, rotation phase, units owed. -/
abbrev MicroState : Type := (RTag × RotationPhase × Fin 3) × (Fin 10 → STape Γc)

/-- One step of the machine on a micro-operation: the next control, and — when every tape has
the margin of `compStep_apply` — the tapes up to `TEqG`. -/
def MicroStep (hK : 2 ≤ K) (input : Option Terminal) (micro : MicroOp)
    (state state' : MicroState) : Prop :=
  ((microRule Terminal hK).nq (micro, state.1) input
      (fun tape => readWin blankc K (state.2 tape))).2 = state'.1 ∧
    ((∀ tape, K ≤ pos (state.2 tape)) → ∀ tape, TEqG blankc
      (actList blankc (state.2 tape)
        ((microRule Terminal hK).acts (micro, state.1) input
          (fun tape => readWin blankc K (state.2 tape)) tape))
      (state'.2 tape))

/-- A run of the machine along a program. -/
inductive MicroRun (hK : 2 ≤ K) (input : Option Terminal) :
    List MicroOp → MicroState → MicroState → Prop
  | nil (state : MicroState) : MicroRun hK input [] state state
  | cons {micro : MicroOp} {rest : List MicroOp} {state middle final : MicroState}
      (hstep : MicroStep hK input micro state middle)
      (hrest : MicroRun hK input rest middle final) :
      MicroRun hK input (micro :: rest) state final

/-- **A run of the machine along a program is the program on the abstract queue.** -/
theorem microRun_sound (hK : 2 ≤ K) (input : Option Terminal) :
    ∀ (program : List MicroOp) (q : Queue (Fin 2)) (state final : MicroState)
      (first last : MicroOp),
      MicroRun hK input program state final →
      MicroRep K q (first, state.1) state.2 →
      OwedOk program state.1.2.2.val →
      PremisesAlong program q →
      MicroRep K (runMicro program q) (last, final.1) final.2 ∧ final.1.2.2.val = 0 := by
  intro program
  induction program with
  | nil =>
    intro q state final first last hrun hrep howed _
    cases hrun
    exact ⟨hrep, howed⟩
  | cons micro rest ih =>
    intro q state final first last hrun hrep howed hpremises
    cases hrun with
    | cons hstep hrest =>
      rename_i middle
      obtain ⟨hpremise, hpremisesRest⟩ := hpremises
      obtain ⟨howedZero, hnoStart⟩ := OwedOk.head howed
      have hrep' : MicroRep K q (micro, state.1) state.2 := hrep
      obtain ⟨hmargin, hnq, hsound⟩ := microRule_sound (Terminal := Terminal) hK hrep' input
        hpremise.1 (fun hmicro => (hpremise.2 hmicro).1) (fun hmicro => (hpremise.2 hmicro).2)
        (fun hne => Fin.ext (howedZero hne)) hnoStart
      obtain ⟨hcontrol, htapes⟩ := hstep
      have hmiddle := hsound middle.2 (htapes hmargin)
      have hmiddleControl : middle.1 = (microControlAfter (micro, state.1) q).2 := by
        rw [← hcontrol, hnq]
      have hmiddleRep : MicroRep K (microApply micro q) (micro, middle.1) middle.2 := by
        rw [hmiddleControl]
        exact hmiddle
      have howedRest : OwedOk rest middle.1.2.2.val := by
        rw [hmiddleControl]
        have htail := OwedOk.tail (q := q) howed
        unfold microControlAfter
        cases hab : abstractOp micro q with
        | none => rw [hab] at htail; exact htail
        | some op => rw [hab] at htail; exact htail
      exact ih (microApply micro q) middle final micro last hrest hmiddleRep howedRest
        hpremisesRest

#print axioms microRun_sound

theorem microPremises_trivial {micro : MicroOp} (q : Queue (Fin 2))
    (hpop : micro ≠ .sub .tailPop) (hcheck : micro ≠ .checkStart) : MicroPremises micro q :=
  ⟨fun h => absurd h hpop, fun h => absurd h hcheck⟩

/-- The premises of `checkProgram`: the two facts of the rotation test. -/
theorem premisesAlong_check {q : Queue (Fin 2)}
    (hstart : q.state = .idle → ¬ q.lenr ≤ q.lenf → q.lenr = q.front.length + 1)
    (hrot : q.lenf < q.lenr → q.state = .idle) :
    PremisesAlong checkProgram q := by
  refine ⟨⟨fun h => ?_, fun _ => ⟨hstart, hrot⟩⟩, ?_⟩
  · cases h
  · exact ⟨microPremises_trivial _ (by simp) (by simp),
      microPremises_trivial _ (by simp) (by simp),
      microPremises_trivial _ (by simp) (by simp),
      microPremises_trivial _ (by simp) (by simp),
      microPremises_trivial _ (by simp) (by simp),
      microPremises_trivial _ (by simp) (by simp),
      microPremises_trivial _ (by simp) (by simp), trivial⟩

theorem owedOk_check : OwedOk checkProgram 0 := by
  simp [checkProgram, OwedOk]

/-- **An enqueue on the machine.**  A run of the machine along `snocProgram a`, from a
representation of `q` with nothing owed, ends in a representation of `RTQueue.snoc q a` with
nothing owed. -/
theorem snocRun_sound (hK : 2 ≤ K) (input : Option Terminal) {q : Queue (Fin 2)}
    (hq : RTQueue.Inv q) (a : Fin 2) {state final : MicroState} {first : MicroOp}
    (hrun : MicroRun hK input (snocProgram a) state final)
    (hrep : MicroRep K q (first, state.1) state.2) (howed : state.1.2.2 = 0) (last : MicroOp) :
    MicroRep K (RTQueue.snoc q a) (last, final.1) final.2 ∧ final.1.2.2.val = 0 := by
  rw [← runMicro_snoc hq a]
  refine microRun_sound hK input (snocProgram a) q state final first last hrun hrep ?_ ?_
  · rw [howed]
    exact ⟨rfl, owedOk_check⟩
  · have hpinv := RTQueue.snoc_pinv hq a
    refine ⟨microPremises_trivial _ (by simp) (by simp), premisesAlong_check ?_ hpinv.rot⟩
    intro hidle hlonger
    have hlength := hpinv.lenf_eq
    have hle := hpinv.le
    have hidle' : q.state = .idle := hidle
    rw [show ({ q with lenr := q.lenr + 1, rear := a :: q.rear } : Queue (Fin 2)).state
      = q.state from rfl, hidle'] at hlength
    have hfrontList : RTQueue.frontList RTQueue.RotationState.idle q.front = q.front := rfl
    rw [hfrontList] at hlength
    show q.lenr + 1 = q.front.length + 1
    have hlonger' : ¬ q.lenr + 1 ≤ q.lenf := hlonger
    have hlength' : q.lenf = q.front.length := hlength
    have hle' : q.lenr + 1 ≤ q.lenf + 1 := hle
    omega

#print axioms snocRun_sound

/-- **A dequeue on the machine.**  A run of the machine along `tailProgram`, from a
representation of a queue with a non-empty front and nothing owed, ends in a representation of
`RTQueue.tail q` with nothing owed. -/
theorem tailRun_sound (hK : 2 ≤ K) (input : Option Terminal) {q : Queue (Fin 2)}
    (hq : RTQueue.Inv q) (hfront : q.front ≠ []) {state final : MicroState} {first : MicroOp}
    (hrun : MicroRun hK input tailProgram state final)
    (hrep : MicroRep K q (first, state.1) state.2) (howed : state.1.2.2 = 0) (last : MicroOp) :
    MicroRep K (RTQueue.tail q) (last, final.1) final.2 ∧ final.1.2.2.val = 0 := by
  rw [← runMicro_tail hq hfront]
  obtain ⟨P, hP⟩ := RTQueue.frontList_eq_append hq.sinv hq.nd
  have hpositive : 1 ≤ q.lenf := by
    rw [hq.lenf_eq, hP]
    have : 1 ≤ q.front.length := by
      cases hfr : q.front with
      | nil => exact absurd hfr hfront
      | cons x f => simp
    simp only [List.length_append]
    omega
  have hpop : sApply .tailPop q = { q with lenf := q.lenf - 1, front := q.front.tail } := by
    show (if q.front = [] then q else _) = _
    rw [if_neg hfront]
  refine microRun_sound hK input tailProgram q state final first last hrun hrep ?_ ?_
  · rw [howed]
    exact ⟨rfl, rfl, owedOk_check⟩
  · refine ⟨⟨fun _ _ => hpositive, fun h => by cases h⟩,
      microPremises_trivial _ (by simp) (by simp), ?_⟩
    show PremisesAlong checkProgram (sApply .inval (sApply .tailPop q))
    rw [hpop]
    refine premisesAlong_check ?_ (tail_hrot q hq)
    intro hidle hlonger
    -- the rear is longer than the shortened front only when no rotation is running
    have hlonger' : ¬ q.lenr ≤ q.lenf - 1 := hlonger
    have hpot := hq.pot_len
    have hstateIdle : q.state = .idle := RTQueue.eq_idle_of_rem_zero hq.nd (by
      have hle := hq.le
      omega)
    have hlength := hq.lenf_eq
    rw [hstateIdle] at hlength
    have hfrontList : RTQueue.frontList RTQueue.RotationState.idle q.front = q.front := rfl
    rw [hfrontList] at hlength
    have hle := hq.le
    show q.lenr = q.front.tail.length + 1
    have htail : q.front.tail.length + 1 = q.front.length := by
      cases hfr : q.front with
      | nil => exact absurd hfr hfront
      | cons x f => simp
    omega

#print axioms tailRun_sound

end Run

/-! ## The machine with a program counter -/

/-- The two jobs of the queue machine. -/
inductive QueueJob where
  | snoc (a : Fin 2)
  | tail
  deriving DecidableEq

def programOf : QueueJob → List MicroOp
  | .snoc a => snocProgram a
  | .tail => tailProgram

theorem programOf_length_le (job : QueueJob) : (programOf job).length ≤ 10 := by
  cases job <;> simp [programOf, snocProgram, tailProgram, checkProgram]

/-- The control: the job, the program counter, and the state a program moves. -/
abbrev ProgramControl : Type := QueueJob × Fin 11 × RTag × RotationPhase × Fin 3

/-- The micro-operation under the program counter (past the end: an increment, which does
nothing when nothing is owed). -/
def currentOp (control : ProgramControl) : MicroOp :=
  (programOf control.1).getD control.2.1.val .incLength

def nextCounter (counter : Fin 11) : Fin 11 :=
  if h : counter.val + 1 < 11 then ⟨counter.val + 1, h⟩ else counter

section ProgramMachine

variable {K : ℕ} {Terminal : Type}

/-- **The queue machine with its program counter**: the rule of `microRule` on the
micro-operation under the counter; the counter advances. -/
def programRule (Terminal : Type) (hK : 2 ≤ K) : ActRule Terminal ProgramControl Γc 10 K where
  nq := fun control input windows =>
    (control.1, nextCounter control.2.1,
      ((microRule Terminal hK).nq (currentOp control, control.2.2) input windows).2)
  acts := fun control input windows tape =>
    (microRule Terminal hK).acts (currentOp control, control.2.2) input windows tape
  len_le := fun control input windows tape => (microRule Terminal hK).len_le _ _ _ _

def programLocalStep (Terminal : Type) (hK : 2 ≤ K) :
    PalPeg.Local.LocalStep Terminal ProgramControl Γc 10 K :=
  compStep (programRule Terminal hK)

/-- The machine run on a list of inputs (it ignores them). -/
def programRun (hK : 2 ≤ K) :
    List (Option Terminal) → ProgramControl × (Fin 10 → STape Γc) →
      ProgramControl × (Fin 10 → STape Γc)
  | [], x => x
  | input :: rest, x => programRun hK rest ((programLocalStep Terminal hK).apply blankc x input)

/-- One real step is a `MicroStep` on the micro-operation under the counter. -/
theorem microStep_of_apply (hK : 2 ≤ K) (input input' : Option Terminal)
    (control : ProgramControl) (tapes : Fin 10 → STape Γc) :
    MicroStep hK input (currentOp control) (control.2.2, tapes)
        (((programLocalStep Terminal hK).apply blankc (control, tapes) input').1.2.2,
          ((programLocalStep Terminal hK).apply blankc (control, tapes) input').2) ∧
      ((programLocalStep Terminal hK).apply blankc (control, tapes) input').1.1 = control.1 ∧
      ((programLocalStep Terminal hK).apply blankc (control, tapes) input').1.2.1
        = nextCounter control.2.1 := by
  refine ⟨⟨rfl, fun hmargin => ?_⟩, rfl, rfl⟩
  exact (compStep_apply (programRule Terminal hK) blankc (control, tapes) input' hmargin).2

/-- **The real run is a `MicroRun`** along the rest of the program, and the counter ends at the
end of the program. -/
theorem microRun_of_programRun (hK : 2 ≤ K) (input : Option Terminal) :
    ∀ (inputs : List (Option Terminal)) (control : ProgramControl)
      (tapes : Fin 10 → STape Γc),
      control.2.1.val + inputs.length = (programOf control.1).length →
      MicroRun hK input ((programOf control.1).drop control.2.1.val) (control.2.2, tapes)
          ((programRun hK inputs (control, tapes)).1.2.2,
            (programRun hK inputs (control, tapes)).2) ∧
        (programRun hK inputs (control, tapes)).1.1 = control.1 ∧
        (programRun hK inputs (control, tapes)).1.2.1.val = (programOf control.1).length := by
  intro inputs
  induction inputs with
  | nil =>
    intro control tapes hlength
    have hdrop : (programOf control.1).drop control.2.1.val = [] := by
      apply List.drop_eq_nil_of_le
      simp only [List.length_nil] at hlength
      omega
    rw [hdrop]
    refine ⟨MicroRun.nil _, rfl, ?_⟩
    simp only [List.length_nil] at hlength
    exact hlength
  | cons first rest ih =>
    intro control tapes hlength
    simp only [List.length_cons] at hlength
    have hbound := programOf_length_le control.1
    have hlt : control.2.1.val < (programOf control.1).length := by omega
    obtain ⟨hstep, hjob, hcounter⟩ := microStep_of_apply hK input first control tapes
    have hnext : (nextCounter control.2.1).val = control.2.1.val + 1 := by
      unfold nextCounter
      rw [dif_pos (by omega)]
    set result := (programLocalStep Terminal hK).apply blankc (control, tapes) first
      with hresult
    have hih := ih result.1 result.2 (by rw [hjob, hcounter, hnext]; omega)
    rw [hjob, hcounter, hnext] at hih
    have hdrop : (programOf control.1).drop control.2.1.val
        = currentOp control :: (programOf control.1).drop (control.2.1.val + 1) := by
      rw [List.drop_eq_getElem_cons hlt]
      congr 1
      unfold currentOp
      rw [List.getD_eq_getElem _ _ hlt]
    rw [hdrop]
    exact ⟨MicroRun.cons hstep hih.1, hih.2.1, hih.2.2⟩

/-- **An enqueue on the real machine**: nine steps of `programLocalStep` from the start of the
`snoc a` job take a representation of `q` to a representation of `RTQueue.snoc q a`. -/
theorem programRun_snoc (hK : 2 ≤ K) {q : Queue (Fin 2)} (hq : RTQueue.Inv q) (a : Fin 2)
    (inputs : List (Option Terminal)) (hinputs : inputs.length = 9)
    {tag : RTag} {phase : RotationPhase} {tapes : Fin 10 → STape Γc} {first : MicroOp}
    (hrep : MicroRep K q (first, tag, phase, 0) tapes) (last : MicroOp) :
    MicroRep K (RTQueue.snoc q a)
        (last, (programRun hK inputs ((.snoc a, 0, tag, phase, 0), tapes)).1.2.2)
        (programRun hK inputs ((.snoc a, 0, tag, phase, 0), tapes)).2 ∧
      (programRun hK inputs ((.snoc a, 0, tag, phase, 0), tapes)).1.2.2.2.2.val = 0 := by
  obtain ⟨hrun, -, -⟩ := microRun_of_programRun hK (none : Option Terminal) inputs
    ((.snoc a, 0, tag, phase, 0) : ProgramControl) tapes (by
      simp [programOf, snocProgram, checkProgram, hinputs])
  exact snocRun_sound hK none hq a hrun hrep rfl last

/-- **A dequeue on the real machine**: ten steps from the start of the `tail` job. -/
theorem programRun_tail (hK : 2 ≤ K) {q : Queue (Fin 2)} (hq : RTQueue.Inv q)
    (hfront : q.front ≠ [])
    (inputs : List (Option Terminal)) (hinputs : inputs.length = 10)
    {tag : RTag} {phase : RotationPhase} {tapes : Fin 10 → STape Γc} {first : MicroOp}
    (hrep : MicroRep K q (first, tag, phase, 0) tapes) (last : MicroOp) :
    MicroRep K (RTQueue.tail q)
        (last, (programRun hK inputs ((.tail, 0, tag, phase, 0), tapes)).1.2.2)
        (programRun hK inputs ((.tail, 0, tag, phase, 0), tapes)).2 ∧
      (programRun hK inputs ((.tail, 0, tag, phase, 0), tapes)).1.2.2.2.2.val = 0 := by
  obtain ⟨hrun, -, -⟩ := microRun_of_programRun hK (none : Option Terminal) inputs
    ((.tail, 0, tag, phase, 0) : ProgramControl) tapes (by
      simp [programOf, tailProgram, checkProgram, hinputs])
  exact tailRun_sound hK none hq hfront hrun hrep rfl last

#print axioms programRun_snoc
#print axioms programRun_tail

end ProgramMachine

end PalPeg.ConcreteLocalMachine
