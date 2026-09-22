import PalPeg.LocalQueueLayout

/-!
# The queue of the local machine: tapes, the `ActRule`, and one step

Cell operations as tape actions selected by the top symbol, stack tapes up to `TEqG`, the rule
`queueRule` on eight tapes, the representation `QueueRep`, and its soundness before the sweep
(`queueRule_sound`) and after it (`queueRep_step`).
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

/-! ## The sub-step as tape actions

A stack is the debris tape `CloseoutCoreEnc18.dTape`: the head is on the top cell.  The sealing
`none` is the blank symbol itself (`GalilVMEncode.blank = sOpt none`): sealing leaves one blank
cell on top of the junk.  The actions of a cell operation read the stack only through its top
symbol, the focus of the tape. -/

/-- The letter a tape symbol stands for, if any. -/
def symLetter : Γc → Option (Fin 2)
  | Sum.inl cell => cell
  | _ => none

theorem topLetter_eq_sym (stack : List (Option (Fin 2))) :
    topLetter stack = symLetter (topSym stack) := by
  cases stack with
  | nil => rfl
  | cons cell rest => cases cell <;> rfl

theorem dTape_focus (stack : List (Option (Fin 2))) (debris : List Γc) :
    (dTape stack debris).focus = topSym stack := by
  cases stack <;> rfl

/-- A push, from the top symbol: rewrite the top cell, step right, write the new cell. -/
def pushActsOfTop (top : Γc) (cell : Option (Fin 2)) : List (Act Γc) :=
  [some (top, PegSeparation.RealTimeTM.Move.right),
    some (cellSym cell, PegSeparation.RealTimeTM.Move.stay)]

/-- The tape actions of one cell operation, a function of the top symbol. -/
def cellActsOfTop : Delta → Bool → Γc → List (Act Γc)
  | _, true, top => pushActsOfTop top none
  | .keep, false, _ => []
  | .pop, false, _ => popActs
  | .push a, false, top => pushActsOfTop top (some a)

/-- The debris after one cell operation. -/
def cellDebris : Delta → Bool → List (Option (Fin 2)) → List Γc → List Γc
  | _, true, _, debris => debris.tail
  | .keep, false, _, debris => debris
  | .pop, false, [], debris => debris
  | .pop, false, _ :: _, debris => blankc :: debris
  | .push _, false, _, debris => debris.tail

theorem cellActsOfTop_length (u : Delta) (sealing : Bool) (top : Γc) :
    (cellActsOfTop u sealing top).length ≤ 2 := by
  cases u <;> cases sealing <;> simp [cellActsOfTop, pushActsOfTop, popActs]

/-- **One cell operation is at most two tape actions, selected by the top symbol.** -/
theorem dTape_cellApply (u : Delta) (sealing : Bool) (stack : List (Option (Fin 2)))
    (debris : List Γc) :
    dTape (cellApply u sealing stack) (cellDebris u sealing stack debris)
      = actList blankc (dTape stack debris) (cellActsOfTop u sealing (topSym stack)) := by
  cases sealing with
  | true =>
    have hpush := (push_dTape stack debris none).symm
    cases u <;> exact hpush
  | false =>
    cases u with
    | keep => rfl
    | pop =>
      cases stack with
      | nil => rfl
      | cons cell rest => exact (pop_dTape cell rest debris).symm
    | push a => exact (push_dTape stack debris (some a)).symm

#print axioms dTape_cellApply

/-! ## The control of the queue sub-step: phase and valid counter -/

def phaseOfView : RotationView → RotationPhase
  | .idle => .idle
  | .done => .done
  | .reversing _ _ _ => .reversing
  | .appending _ _ _ => .appending

/-- The rotation phase after a sub-step, selected from the finite observation. -/
def nextPhaseOfView : SOp → RotationView → RotationPhase
  | .inval, .appending true _ true => .done
  | .rotStart, .idle => .reversing
  | .exec, .reversing none (some _) true => .appending
  | .exec, .appending true _ _ => .done
  | .install, .done => .idle
  | _, view => phaseOfView view

theorem rotationPhase_eq_view (s : RotationState (Fin 2)) :
    rotationPhase s = phaseOfView (rotationView s) := by
  cases s <;> rfl

/-- **The next phase is a function of the observation.** -/
theorem rotationPhase_sApply (op : SOp) (q : Queue (Fin 2)) :
    rotationPhase (sApply op q).state = nextPhaseOfView op (rotationView q.state) := by
  cases op with
  | snocPush a =>
    show rotationPhase q.state = _
    rw [rotationPhase_eq_view]
    cases rotationView q.state <;> rfl
  | tailPop =>
    have hstate : (sApply .tailPop q).state = q.state := by
      show (if q.front = [] then q else _).state = q.state
      split <;> rfl
    rw [hstate, rotationPhase_eq_view]
    cases rotationView q.state <;> rfl
  | inval =>
    show rotationPhase (RTQueue.invalidate q.state) = _
    cases q.state with
    | idle => rfl
    | done f => rfl
    | reversing ok f f' r r' => rfl
    | appending ok f' r' =>
      cases ok with
      | zero => cases r' <;> rfl
      | succ n => rfl
  | rotStart =>
    cases hstate : q.state <;>
      simp [sApply, isIdle, rotStart, hstate, rotationPhase, nextPhaseOfView, rotationView,
        phaseOfView]
  | exec =>
    show rotationPhase (RTQueue.exec q.state) = _
    cases q.state with
    | idle => rfl
    | done f => rfl
    | reversing ok f f' r r' =>
      cases f with
      | nil =>
        cases r with
        | nil => rfl
        | cons y r => cases r <;> rfl
      | cons x f => cases r <;> rfl
    | appending ok f' r' =>
      cases ok with
      | zero => rfl
      | succ n => cases f' <;> rfl
  | install =>
    cases hstate : q.state <;>
      simp [sApply, finish, hstate, rotationPhase, nextPhaseOfView, rotationView, phaseOfView]

/-- The valid counter as a stack of marks. -/
def validStack (s : RotationState (Fin 2)) : List (Fin 2) := List.replicate (validCount s) 0

/-- The operation on the valid counter, selected from the finite observation and the zero test of
the counter (an `inval` of a reversing rotation at count `0` keeps it: `0 - 1 = 0`, and a pop
would take a cell of the bottom). -/
def validDeltaOfView : SOp → RotationView → Bool → Delta
  | .inval, .reversing _ _ _, false => .pop
  | .inval, .appending false _ _, _ => .pop
  | .exec, .reversing (some _) (some _) _, _ => .push 0
  | .exec, .appending false (some _) _, _ => .pop
  | _, _, _ => .keep

theorem validIsZero_eq_top (s : RotationState (Fin 2)) {bottom : List (Option (Fin 2))}
    (hsealed : Sealed bottom) :
    validIsZero s = (topLetter ((validStack s).map some ++ bottom)).isNone := by
  rw [topLetter_sealed hsealed]
  unfold validIsZero validStack
  cases validCount s <;> rfl

/-- **The valid counter, as cells over a sealed bottom, moves by the selected operation.** -/
theorem validCells_sApply (op : SOp) (q : Queue (Fin 2)) (bottom : List (Option (Fin 2))) :
    cellApply (validDeltaOfView op (rotationView q.state) (validIsZero q.state)) false
        ((validStack q.state).map some ++ bottom)
      = (validStack (sApply op q).state).map some ++ bottom := by
  cases op with
  | snocPush a =>
    show _ = (validStack q.state).map some ++ bottom
    cases q.state <;> rfl
  | tailPop =>
    have hstate : (sApply .tailPop q).state = q.state := by
      show (if q.front = [] then q else _).state = q.state
      split <;> rfl
    rw [hstate]
    cases q.state <;> rfl
  | inval =>
    show _ = (validStack (RTQueue.invalidate q.state)).map some ++ bottom
    cases q.state with
    | idle => rfl
    | done f => rfl
    | reversing ok f f' r r' =>
      cases ok <;> simp [validStack, validCount, validIsZero, RTQueue.invalidate,
        validDeltaOfView, rotationView, cellApply, List.replicate_succ]
    | appending ok f' r' =>
      cases ok with
      | zero => cases r' <;> rfl
      | succ n =>
        simp [validStack, validCount, validIsZero, RTQueue.invalidate, validDeltaOfView,
          rotationView, cellApply, List.replicate_succ]
  | rotStart =>
    cases hstate : q.state <;>
      simp [sApply, isIdle, rotStart, hstate, validStack, validCount, validDeltaOfView,
        rotationView, cellApply]
  | exec =>
    show _ = (validStack (RTQueue.exec q.state)).map some ++ bottom
    cases q.state with
    | idle => rfl
    | done f => rfl
    | reversing ok f f' r r' =>
      cases f with
      | nil =>
        cases r with
        | nil => rfl
        | cons y r => cases r <;> rfl
      | cons x f =>
        cases r with
        | nil => rfl
        | cons y r =>
          simp [validStack, validCount, RTQueue.exec, validDeltaOfView, rotationView,
            cellApply, List.replicate_succ]
    | appending ok f' r' =>
      cases ok with
      | zero => rfl
      | succ n =>
        cases f' with
        | nil => rfl
        | cons x f' =>
          simp [validStack, validCount, validIsZero, RTQueue.exec, validDeltaOfView,
            rotationView, cellApply, List.replicate_succ]
  | install =>
    cases hstate : q.state <;>
      simp [sApply, finish, hstate, validStack, validCount, validDeltaOfView, rotationView,
        cellApply]

#print axioms rotationPhase_sApply
#print axioms validCells_sApply

/-! ## The queue sub-step as an `ActRule`

Eight tapes: `0`–`6` are the role stacks (`roleOf tag ro < 7`), tape `7` is the valid counter.
The control keeps the operation to run, the role tag and the rotation phase.  The rule reads, on
each tape, the cell under the head and the cell below it (the left neighbour of a debris tape). -/

/-- The control of the queue sub-step. -/
abbrev QueueControl : Type := SOp × RTag × RotationPhase

section Rule

variable {K : ℕ}

/-- The cell under the head. -/
def centreSym (window : Window Γc K) : Γc := window (idx K K)

/-- The cell below the top of a stack: the left neighbour of the head. -/
def belowSym (window : Window Γc K) : Γc := window (idx K (K - 1))

def rotationViewOfSyms (phase : RotationPhase) (validZero : Bool) (top below : SRole → Γc) :
    RotationView :=
  match phase with
  | .idle => .idle
  | .done => .done
  | .reversing =>
      .reversing (symLetter (top .fwd)) (symLetter (top .rev))
        ((symLetter (top .rev)).isSome && (symLetter (below .rev)).isNone)
  | .appending =>
      .appending validZero (symLetter (top .fwd')) (symLetter (top .rev')).isSome

/-- The observation from tape symbols. -/
def queueViewOfSyms (phase : RotationPhase) (validZero : Bool) (top below : SRole → Γc) :
    QueueView :=
  ⟨(symLetter (top .front)).isNone, rotationViewOfSyms phase validZero top below⟩

theorem queueViewOfTops_eq_syms (phase : RotationPhase) (validZero : Bool)
    (stackOf : SRole → List (Option (Fin 2))) :
    queueViewOfTops phase validZero stackOf
      = queueViewOfSyms phase validZero (fun ro => topSym (stackOf ro))
          (fun ro => topSym (stackOf ro).tail) := by
  unfold queueViewOfTops queueViewOfSyms rotationViewOfTops rotationViewOfSyms topIsSingle
  cases phase <;> simp only [topLetter_eq_sym]

/-- The tape of a role: its address, clamped into the eight tapes. -/
def roleTape (tag : RTag) (ro : SRole) : Fin 8 := ⟨min (roleOf tag ro) 6, by omega⟩

/-- The valid counter tape. -/
def validTape : Fin 8 := 7

/-- The observation the rule makes: the phase from the control, the symbols from the windows. -/
def queueViewOfWindows (control : QueueControl) (windows : Fin 8 → Window Γc K) : QueueView :=
  queueViewOfSyms control.2.2 (symLetter (centreSym (windows validTape))).isNone
    (fun ro => centreSym (windows (roleTape control.2.1 ro)))
    (fun ro => belowSym (windows (roleTape control.2.1 ro)))

/-- **The queue sub-step as a rule of the local machine**: the next control and the tape actions
are functions of the control and the windows. -/
def queueRule (Terminal : Type) (hK : 2 ≤ K) : ActRule Terminal QueueControl Γc 8 K where
  nq := fun control _ windows =>
    let view := queueViewOfWindows control windows
    (control.1, tagStepOfView control.1 view control.2.1,
      nextPhaseOfView control.1 view.rotation)
  acts := fun control _ windows tape =>
    let view := queueViewOfWindows control windows
    if tape.val < 7 then
      cellActsOfTop (deltaOfView control.1 view (roleOf control.2.1) tape.val)
        (decide ((sealRoleOfView control.1 view).map (roleOf control.2.1) = some tape.val))
        (centreSym (windows tape))
    else
      cellActsOfTop
        (validDeltaOfView control.1 view.rotation
          (symLetter (centreSym (windows validTape))).isNone)
        false (centreSym (windows tape))
  len_le := fun control _ windows tape => by
    dsimp only
    split
    · exact le_trans (cellActsOfTop_length _ _ _) hK
    · exact le_trans (cellActsOfTop_length _ _ _) hK

/-- The local step of the queue sub-step: a concrete term of `LocalStep`. -/
def queueLocalStep (Terminal : Type) (hK : 2 ≤ K) :
    PalPeg.Local.LocalStep Terminal QueueControl Γc 8 K :=
  compStep (queueRule Terminal hK)

end Rule

/-! ## A tape that represents a stack

The local machine keeps its tapes only up to `TEqG` (same head position, same cells): the sweep of
`compStep` does not return the literal `STape` term.  Reading a window and applying actions
respect `TEqG`, so a stack is represented by any tape `TEqG`-equal to its debris tape. -/

theorem teqG_actOnG {Γ : Type} {blank : Γ} {T T' : STape Γ} (h : TEqG blank T T') (a : Act Γ) :
    TEqG blank (actOnG blank T a) (actOnG blank T' a) := by
  cases a with
  | none => exact h
  | some action =>
    obtain ⟨written, move⟩ := action
    refine ⟨?_, fun p => ?_⟩
    · show pos (T.applyAction blank (written, move)) = pos (T'.applyAction blank (written, move))
      rw [pos_applyAction, pos_applyAction, h.1]
    · show rd blank (T.applyAction blank (written, move)) p
        = rd blank (T'.applyAction blank (written, move)) p
      rw [rd_applyAction, rd_applyAction, h.1, h.2 p]

theorem teqG_actList {Γ : Type} {blank : Γ} {T T' : STape Γ} (h : TEqG blank T T')
    (acts : List (Act Γ)) :
    TEqG blank (actList blank T acts) (actList blank T' acts) := by
  induction acts generalizing T T' with
  | nil => exact h
  | cons a rest ih => exact ih (teqG_actOnG h a)

theorem readWin_teqG {Γ : Type} {blank : Γ} {K : ℕ} {T T' : STape Γ} (h : TEqG blank T T') :
    readWin blank K T = readWin blank K T' := by
  funext i
  rw [readWin_eq, readWin_eq, h.1, h.2]

/-- The tape represents the stack: it is the debris tape of the stack, up to `TEqG`. -/
def StackTape (tape : STape Γc) (stack : List (Option (Fin 2))) : Prop :=
  ∃ debris : List Γc, TEqG blankc tape (dTape stack debris)

theorem pos_dTape (stack : List (Option (Fin 2))) (debris : List Γc) :
    pos (dTape stack debris) = stack.length := by
  cases stack with
  | nil => rfl
  | cons cell rest => simp [dTape, pos]

theorem StackTape.pos_eq {tape : STape Γc} {stack : List (Option (Fin 2))}
    (h : StackTape tape stack) : pos tape = stack.length := by
  obtain ⟨debris, hteq⟩ := h
  rw [hteq.1, pos_dTape]

/-- The cell under the head of a tall enough stack tape is the top symbol. -/
theorem StackTape.centreSym_eq {K : ℕ} {tape : STape Γc} {stack : List (Option (Fin 2))}
    (h : StackTape tape stack) (hmargin : K ≤ stack.length) :
    centreSym (readWin blankc K tape) = topSym stack := by
  obtain ⟨debris, hteq⟩ := h
  have hpos : K ≤ pos (dTape stack debris) := by rw [pos_dTape]; exact hmargin
  rw [readWin_teqG hteq]
  unfold centreSym
  rw [readWin_eq, idx_val (by omega), Nat.sub_add_cancel hpos, rd_pos, dTape_focus]

/-- The cell below the head of a tall enough stack tape is the top symbol of the tail. -/
theorem StackTape.belowSym_eq {K : ℕ} {tape : STape Γc} {stack : List (Option (Fin 2))}
    (h : StackTape tape stack) (hK : 1 ≤ K) (hmargin : K ≤ stack.length) :
    belowSym (readWin blankc K tape) = topSym stack.tail := by
  obtain ⟨debris, hteq⟩ := h
  have hpos : K ≤ pos (dTape stack debris) := by rw [pos_dTape]; exact hmargin
  rw [readWin_teqG hteq]
  unfold belowSym
  rw [readWin_eq, idx_val (by omega), pos_dTape,
    show stack.length - K + (K - 1) = stack.length - 1 from by omega]
  cases stack with
  | nil => simp at hmargin; omega
  | cons cell rest =>
    show rd blankc ⟨rest.map cellSym ++ [blankc], cellSym cell, debris⟩ (rest.length + 1 - 1) = _
    rw [rd_eq]
    cases rest with
    | nil => rfl
    | cons below deeper =>
      simp [topSym, List.getD_eq_getElem?_getD, List.getElem?_append_right]

/-- **One cell operation on a stack tape**: the actions selected by the top symbol lead to a tape
of the new stack. -/
theorem StackTape.cellApply {tape : STape Γc} {stack : List (Option (Fin 2))}
    (h : StackTape tape stack) (u : Delta) (sealing : Bool) :
    StackTape (actList blankc tape (cellActsOfTop u sealing (topSym stack)))
      (cellApply u sealing stack) := by
  obtain ⟨debris, hteq⟩ := h
  refine ⟨cellDebris u sealing stack debris, ?_⟩
  rw [dTape_cellApply]
  exact teqG_actList hteq _

#print axioms StackTape.belowSym_eq
#print axioms StackTape.cellApply

/-! ## The representation of a queue by the local machine, and one step -/

deriving instance Fintype for SRole

/-- Every one of the seven stack tapes carries a role. -/
theorem roleOf_surjective :
    ∀ (tag : RTag) (i : Fin 7), ∃ ro : SRole, roleOf tag ro = i.val := by decide

theorem roleTape_val (tag : RTag) (ro : SRole) : (roleTape tag ro).val = roleOf tag ro := by
  have hbound := sbound_roleOf tag ro
  show min (roleOf tag ro) 6 = roleOf tag ro
  omega

theorem StackTape.of_teqG {tape tape' : STape Γc} {stack : List (Option (Fin 2))}
    (h : StackTape tape stack) (hteq : TEqG blankc tape tape') : StackTape tape' stack := by
  obtain ⟨debris, hdebris⟩ := h
  exact ⟨debris, hteq.1.symm.trans hdebris.1, fun p => (hteq.2 p).symm.trans (hdebris.2 p)⟩

/-- **The local machine represents the queue**: the control keeps the rotation phase, the seven
stack tapes carry the sealed layout under the role tag, every junk list is at least `K` high (the
margin of `compStep_apply`; junk only grows), and tape `7` carries the valid counter over a
sealed bottom of height at least `K`. -/
def QueueRep (K : ℕ) (q : Queue (Fin 2)) (control : QueueControl)
    (tapes : Fin 8 → STape Γc) : Prop :=
  ∃ (stack junk : ℕ → List (Option (Fin 2))) (bottom : List (Option (Fin 2))),
    control.2.2 = rotationPhase q.state ∧
    LaysSealed q (roleOf control.2.1) stack junk ∧
    (∀ i, K ≤ (junk i).length) ∧
    (∀ tape : Fin 8, tape.val < 7 → StackTape (tapes tape) (stack tape.val)) ∧
    Sealed bottom ∧ K ≤ bottom.length ∧
    StackTape (tapes validTape) ((validStack q.state).map some ++ bottom)

theorem sealedJunkOf_height {K : ℕ} (op : SOp) (q : Queue (Fin 2)) (ρ : SRoles)
    {junk : ℕ → List (Option (Fin 2))} (hheight : ∀ i, K ≤ (junk i).length) :
    ∀ i, K ≤ (sealedJunkOf op q ρ junk i).length := by
  have hovr : ∀ (address : ℕ) (role : List (Fin 2)) (i : ℕ),
      K ≤ (ovrCell address (none :: (role.map some ++ junk address)) junk i).length := by
    intro address role i
    unfold ovrCell
    split
    · have := hheight address
      simp only [List.length_cons, List.length_append, List.length_map]
      omega
    · exact hheight i
  intro i
  cases op with
  | snocPush a => exact hheight i
  | tailPop => exact hheight i
  | rotStart => exact hheight i
  | inval =>
    show K ≤ (invalSealedJunk ρ junk q.state i).length
    cases q.state with
    | idle => exact hheight i
    | done f => exact hheight i
    | reversing ok f f' r r' => exact hheight i
    | appending ok f' r' =>
      cases ok with
      | succ n => exact hheight i
      | zero =>
        cases r' with
        | nil => exact hheight i
        | cons x r' => exact hovr _ _ i
  | exec =>
    show K ≤ (execSealedJunk ρ junk q.state i).length
    cases q.state with
    | idle => exact hheight i
    | done f => exact hheight i
    | reversing ok f f' r r' => exact hheight i
    | appending ok f' r' =>
      cases ok with
      | succ n => exact hheight i
      | zero => exact hovr _ _ i
  | install =>
    simp only [sealedJunkOf]
    split
    · exact hovr _ _ i
    · exact hheight i

section Step

variable {K : ℕ} {Terminal : Type}

/-- The rule observes the queue: on a representation, the observation made from the windows is
`queueView`, and the counter top gives the zero test. -/
theorem queueViewOfWindows_eq (hK : 1 ≤ K) {q : Queue (Fin 2)} {control : QueueControl}
    {tapes : Fin 8 → STape Γc} {stack junk : ℕ → List (Option (Fin 2))}
    {bottom : List (Option (Fin 2))}
    (hphase : control.2.2 = rotationPhase q.state)
    (hlays : LaysSealed q (roleOf control.2.1) stack junk)
    (hheight : ∀ i, K ≤ (junk i).length)
    (htapes : ∀ tape : Fin 8, tape.val < 7 → StackTape (tapes tape) (stack tape.val))
    (hsealed : Sealed bottom) (hbottom : K ≤ bottom.length)
    (hcounter : StackTape (tapes validTape) ((validStack q.state).map some ++ bottom)) :
    (symLetter (centreSym (readWin blankc K (tapes validTape)))).isNone = validIsZero q.state ∧
      queueViewOfWindows control (fun tape => readWin blankc K (tapes tape)) = queueView q := by
  have hzero : (symLetter (centreSym (readWin blankc K (tapes validTape)))).isNone
      = validIsZero q.state := by
    rw [hcounter.centreSym_eq (by simp only [List.length_append]; omega), ← topLetter_eq_sym,
      validIsZero_eq_top _ hsealed]
  refine ⟨hzero, ?_⟩
  have hroleHeight : ∀ ro, K ≤ (stack (roleOf control.2.1 ro)).length := fun ro => by
    rw [hlays.1 ro]
    have := hheight (roleOf control.2.1 ro)
    simp only [List.length_append]
    omega
  have hroleTape : ∀ ro, StackTape (tapes (roleTape control.2.1 ro))
      (stack (roleOf control.2.1 ro)) := fun ro => by
    have h := htapes (roleTape control.2.1 ro) (by
      rw [roleTape_val]; exact sbound_roleOf control.2.1 ro)
    rwa [roleTape_val] at h
  have htop : (fun ro => centreSym (readWin blankc K (tapes (roleTape control.2.1 ro))))
      = fun ro => topSym (stack (roleOf control.2.1 ro)) :=
    funext fun ro => (hroleTape ro).centreSym_eq (hroleHeight ro)
  have hbelow : (fun ro => belowSym (readWin blankc K (tapes (roleTape control.2.1 ro))))
      = fun ro => topSym (stack (roleOf control.2.1 ro)).tail :=
    funext fun ro => (hroleTape ro).belowSym_eq hK (hroleHeight ro)
  rw [queueView_eq_tops hlays, queueViewOfTops_eq_syms]
  show queueViewOfSyms control.2.2
      (symLetter (centreSym (readWin blankc K (tapes validTape)))).isNone
      (fun ro => centreSym (readWin blankc K (tapes (roleTape control.2.1 ro))))
      (fun ro => belowSym (readWin blankc K (tapes (roleTape control.2.1 ro)))) = _
  rw [hzero, htop, hbelow, hphase]

/-- **The rule is sound before the sweep.**  On a representation, every tape has the margin of
`compStep_apply`, the next control is the control of the sub-step, and any tapes `TEqG`-equal to
the rule's actions on the old tapes represent the queue after the sub-step.  Stated on `nq` and
`acts`, so that a machine which runs this rule on some of its tapes can use it as it is. -/
theorem queueRule_sound (hK : 2 ≤ K) {margin : ℕ} (hmarginLe : K ≤ margin)
    {q : Queue (Fin 2)} {control : QueueControl}
    {tapes : Fin 8 → STape Γc} (hrep : QueueRep margin q control tapes) (input : Option Terminal) :
    (∀ tape : Fin 8, margin ≤ pos (tapes tape)) ∧
      (queueRule Terminal hK).nq control input (fun tape => readWin blankc K (tapes tape))
        = (control.1, tagStep control.1 q control.2.1,
          rotationPhase (sApply control.1 q).state) ∧
      ∀ tapes' : Fin 8 → STape Γc,
        (∀ tape, TEqG blankc
          (actList blankc (tapes tape)
            ((queueRule Terminal hK).acts control input
              (fun tape => readWin blankc K (tapes tape)) tape))
          (tapes' tape)) →
        QueueRep margin (sApply control.1 q)
          (control.1, tagStep control.1 q control.2.1,
            rotationPhase (sApply control.1 q).state) tapes' := by
  obtain ⟨stack, junk, bottom, hphase, hlays, hheight, htapes, hsealed, hbottom, hcounter⟩ := hrep
  obtain ⟨hzero, hview⟩ := queueViewOfWindows_eq (by omega) hphase hlays
    (fun i => hmarginLe.trans (hheight i)) htapes hsealed (hmarginLe.trans hbottom) hcounter
  have hstackHeight : ∀ tape : Fin 8, tape.val < 7 → margin ≤ (stack tape.val).length := by
    intro tape htape
    obtain ⟨ro, hro⟩ := roleOf_surjective control.2.1 ⟨tape.val, htape⟩
    have hrole : roleOf control.2.1 ro = tape.val := hro
    rw [← hrole, hlays.1 ro]
    have := hheight (roleOf control.2.1 ro)
    simp only [List.length_append]
    omega
  have hmargin : ∀ tape : Fin 8, margin ≤ pos (tapes tape) := by
    intro tape
    by_cases htape : tape.val < 7
    · rw [(htapes tape htape).pos_eq]
      exact hstackHeight tape htape
    · have hlast : tape = validTape := by
        apply Fin.ext
        show tape.val = 7
        omega
      rw [hlast, hcounter.pos_eq]
      simp only [List.length_append]
      omega
  refine ⟨hmargin, ?_, fun tapes' hacts => ?_⟩
  · show (control.1,
      tagStepOfView control.1
        (queueViewOfWindows control (fun tape => readWin blankc K (tapes tape))) control.2.1,
      nextPhaseOfView control.1
        (queueViewOfWindows control (fun tape => readWin blankc K (tapes tape))).rotation) = _
    rw [hview, ← tagStep_eq_view, rotationPhase_sApply]
    rfl
  · refine ⟨fun i => cellApply (deltaOf control.1 q (roleOf control.2.1) i)
        (decide ((sealRoleOf control.1 q).map (roleOf control.2.1) = some i)) (stack i),
      sealedJunkOf control.1 q (roleOf control.2.1) junk, bottom, rfl,
      laysSealed_sApply control.1 q control.2.1 stack junk hlays,
      sealedJunkOf_height _ _ _ hheight, ?_, hsealed, hbottom, ?_⟩
    · intro tape htape
      refine StackTape.of_teqG ?_ (hacts tape)
      have hactsEq : (queueRule Terminal hK).acts control input
          (fun tape => readWin blankc K (tapes tape)) tape
          = cellActsOfTop (deltaOf control.1 q (roleOf control.2.1) tape.val)
            (decide ((sealRoleOf control.1 q).map (roleOf control.2.1) = some tape.val))
            (topSym (stack tape.val)) := by
        show (if tape.val < 7 then _ else _) = _
        rw [if_pos htape, hview, ← deltaOf_eq_view, ← sealRoleOf_eq_view,
          (htapes tape htape).centreSym_eq (hmarginLe.trans (hstackHeight tape htape))]
      rw [hactsEq]
      exact (htapes tape htape).cellApply _ _
    · refine StackTape.of_teqG ?_ (hacts validTape)
      have hactsEq : (queueRule Terminal hK).acts control input
          (fun tape => readWin blankc K (tapes tape)) validTape
          = cellActsOfTop (validDeltaOfView control.1 (rotationView q.state)
              (validIsZero q.state)) false
            (topSym ((validStack q.state).map some ++ bottom)) := by
        show cellActsOfTop
            (validDeltaOfView control.1
              (queueViewOfWindows control (fun tape => readWin blankc K (tapes tape))).rotation
              (symLetter (centreSym (readWin blankc K (tapes validTape)))).isNone)
            false (centreSym (readWin blankc K (tapes validTape))) = _
        rw [hview, hzero, hcounter.centreSym_eq (by simp only [List.length_append]; omega)]
        rfl
      rw [hactsEq, ← validCells_sApply]
      exact hcounter.cellApply _ _

/-- **One step of the local machine is one sub-step of the queue.** -/
theorem queueRep_step (hK : 2 ≤ K) {margin : ℕ} (hmarginLe : K ≤ margin)
    {q : Queue (Fin 2)} {control : QueueControl}
    {tapes : Fin 8 → STape Γc} (hrep : QueueRep margin q control tapes) (input : Option Terminal) :
    QueueRep margin (sApply control.1 q)
      ((queueLocalStep Terminal hK).apply blankc (control, tapes) input).1
      ((queueLocalStep Terminal hK).apply blankc (control, tapes) input).2 := by
  obtain ⟨hmargin, hnq, hsound⟩ := queueRule_sound (Terminal := Terminal) hK hmarginLe hrep input
  obtain ⟨hcontrol, hacts⟩ := compStep_apply (queueRule Terminal hK) blankc (control, tapes) input
    (fun tape => hmarginLe.trans (hmargin tape))
  have hcontrol' : ((queueLocalStep Terminal hK).apply blankc (control, tapes) input).1
      = (control.1, tagStep control.1 q control.2.1,
        rotationPhase (sApply control.1 q).state) := hcontrol.trans hnq
  rw [hcontrol']
  exact hsound _ hacts

#print axioms queueRule_sound
#print axioms queueRep_step

end Step

end PalPeg.ConcreteLocalMachine
