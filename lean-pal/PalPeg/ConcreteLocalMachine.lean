import PalPeg.CloseoutCoreEnc25

/-!
# The concrete local machine — the queue sub-step from a finite observation

`CloseoutCoreEnc25.deltaOf` and `tagStep` select the stack operations of one Hood–Melville
sub-step, but they take the whole abstract queue.  A finite control cannot hold a queue.  This
file gives the finite observation `QueueView` that those two functions actually read, the
selection functions on it, and the proof that they are the same functions.

What the observation contains is exactly what the branches of `deltaOf` / `tagStep` test:
whether the front is empty, the constructor of the rotation state, the heads of the lists that
are popped, whether the valid count is `0`, whether the list to reverse has exactly one element,
and whether the rebuilt list is non-empty.
-/

set_option autoImplicit false

namespace PalPeg.ConcreteLocalMachine

open PalPeg
open PalPeg.CloseoutCoreEnc20 (Delta)
open PalPeg.CloseoutCoreEnc21 (SRole SRoles toAddr pushRearD tailD revD appStartD appD invalDoneD
  sRoleList)
open PalPeg.CloseoutCoreEnc25 (SOp RTag rotTag doneTag isIdle isDone deltaOf tagStep invalDelta
  execDelta)
open PalPeg.RTQueue (Queue RotationState)

/-- The finite observation of a rotation state. -/
inductive RotationView where
  | idle
  | done
  | reversing (forwardHead reverseHead : Option (Fin 2)) (reverseIsSingle : Bool)
  | appending (validIsZero : Bool) (forwardHead : Option (Fin 2)) (rebuiltNonempty : Bool)
  deriving DecidableEq, Fintype

def RotationView.isIdle : RotationView → Bool
  | .idle => true
  | _ => false

def RotationView.isDone : RotationView → Bool
  | .done => true
  | _ => false

/-- The finite observation of a queue: one bit of the front and the view of the rotation. -/
structure QueueView where
  frontEmpty : Bool
  rotation : RotationView
  deriving DecidableEq, Fintype

def rotationView : RotationState (Fin 2) → RotationView
  | .idle => .idle
  | .done _ => .done
  | .reversing _ f _ r _ => .reversing f.head? r.head? (decide (r.length = 1))
  | .appending ok f' r' => .appending (decide (ok = 0)) f'.head? (!r'.isEmpty)

def queueView (q : Queue (Fin 2)) : QueueView :=
  ⟨q.front.isEmpty, rotationView q.state⟩

def invalDeltaOfView (ρ : SRoles) : RotationView → (ℕ → Delta)
  | .appending true _ true => toAddr ρ invalDoneD
  | _ => toAddr ρ (fun _ => .keep)

def execDeltaOfView (ρ : SRoles) : RotationView → (ℕ → Delta)
  | .reversing (some x) (some y) _ => toAddr ρ (revD x y)
  | .reversing none (some y) true => toAddr ρ (appStartD y)
  | .appending false (some x) _ => toAddr ρ (appD x)
  | _ => toAddr ρ (fun _ => .keep)

/-- The stack operations of a sub-step, selected from the finite observation. -/
def deltaOfView : SOp → QueueView → SRoles → (ℕ → Delta)
  | .snocPush a, _, ρ => toAddr ρ (pushRearD a)
  | .tailPop, v, ρ =>
      if v.frontEmpty then toAddr ρ (fun _ => .keep)
      else toAddr ρ (tailD v.rotation.isIdle)
  | .inval, v, ρ => invalDeltaOfView ρ v.rotation
  | .rotStart, _, ρ => toAddr ρ (fun _ => .keep)
  | .exec, v, ρ => execDeltaOfView ρ v.rotation
  | .install, _, ρ => toAddr ρ (fun _ => .keep)

/-- The role-tag update of a sub-step, selected from the finite observation. -/
def tagStepOfView : SOp → QueueView → RTag → RTag
  | .rotStart, v, t => if v.rotation.isIdle then rotTag t else t
  | .install, v, t => if v.rotation.isDone then doneTag t else t
  | _, _, t => t

theorem isIdle_eq_view (s : RotationState (Fin 2)) :
    isIdle s = (rotationView s).isIdle := by
  cases s <;> rfl

theorem isDone_eq_view (s : RotationState (Fin 2)) :
    isDone s = (rotationView s).isDone := by
  cases s <;> rfl

theorem invalDelta_eq_view (ρ : SRoles) (s : RotationState (Fin 2)) :
    invalDelta ρ s = invalDeltaOfView ρ (rotationView s) := by
  cases s with
  | idle => rfl
  | done f => rfl
  | reversing ok f f' r r' => rfl
  | appending ok f' r' =>
    cases ok with
    | zero => cases r' <;> simp [invalDelta, invalDeltaOfView, rotationView]
    | succ n => simp [invalDelta, invalDeltaOfView, rotationView]

theorem execDelta_eq_view (ρ : SRoles) (s : RotationState (Fin 2)) :
    execDelta ρ s = execDeltaOfView ρ (rotationView s) := by
  cases s with
  | idle => rfl
  | done f => rfl
  | reversing ok f f' r r' =>
    cases f with
    | nil =>
      cases r with
      | nil => simp [execDelta, execDeltaOfView, rotationView]
      | cons y r =>
        cases r with
        | nil => simp [execDelta, execDeltaOfView, rotationView]
        | cons z r => simp [execDelta, execDeltaOfView, rotationView]
    | cons x f =>
      cases r with
      | nil => simp [execDelta, execDeltaOfView, rotationView]
      | cons y r => simp [execDelta, execDeltaOfView, rotationView]
  | appending ok f' r' =>
    cases ok with
    | zero => cases f' <;> simp [execDelta, execDeltaOfView, rotationView]
    | succ n => cases f' <;> simp [execDelta, execDeltaOfView, rotationView]

/-- **`deltaOf` reads the queue only through the finite observation.** -/
theorem deltaOf_eq_view (op : SOp) (q : Queue (Fin 2)) (ρ : SRoles) :
    deltaOf op q ρ = deltaOfView op (queueView q) ρ := by
  cases op with
  | snocPush a => rfl
  | tailPop =>
    by_cases hfront : q.front = [] <;>
      simp [deltaOf, deltaOfView, queueView, isIdle_eq_view, hfront]
  | inval => exact invalDelta_eq_view ρ q.state
  | rotStart => rfl
  | exec => exact execDelta_eq_view ρ q.state
  | install => rfl

/-- **`tagStep` reads the queue only through the finite observation.** -/
theorem tagStep_eq_view (op : SOp) (q : Queue (Fin 2)) (t : RTag) :
    tagStep op q t = tagStepOfView op (queueView q) t := by
  cases op <;> simp [tagStep, tagStepOfView, queueView, isIdle_eq_view, isDone_eq_view]

#print axioms deltaOf_eq_view
#print axioms tagStep_eq_view

/-! ## Reading the observation from the stack tops

`CloseoutCoreEnc21.LaysS` stores a role's list on top of a junk list, so the top cell of a stack
does not tell whether the role is empty (an empty role shows the junk).  The cells of a queue
stack are `Option (Fin 2)` (`CloseoutCoreEnc20.viewTapesQ` writes `some`), and `none` is unused:
it is the **seal**.  A sealed junk list is empty or starts with `none`; then the two top cells of
a stack determine the head of the role and whether the role has exactly one element. -/

/-- A junk list is sealed: it does not start with a letter. -/
def Sealed (junk : List (Option (Fin 2))) : Prop :=
  ∀ a : Fin 2, junk.head? ≠ some (some a)

/-- The roles are laid on sealed junk. -/
def LaysSealed (q : Queue (Fin 2)) (ρ : SRoles) (stack junk : ℕ → List (Option (Fin 2))) : Prop :=
  (∀ ro, stack (ρ ro) = (sRoleList q ro).map some ++ junk (ρ ro)) ∧ ∀ i, Sealed (junk i)

/-- The letter under the top cell of a stack, if the top cell holds a letter. -/
def topLetter (stack : List (Option (Fin 2))) : Option (Fin 2) :=
  stack.head?.bind id

theorem topLetter_sealed {role : List (Fin 2)} {junk : List (Option (Fin 2))}
    (hsealed : Sealed junk) : topLetter (role.map some ++ junk) = role.head? := by
  cases role with
  | cons a rest => rfl
  | nil =>
    cases junk with
    | nil => rfl
    | cons cell rest =>
      cases cell with
      | none => rfl
      | some a => exact absurd rfl (hsealed a)

/-- Exactly one letter on top of the seal: the top cell is a letter and the second is not. -/
def topIsSingle (stack : List (Option (Fin 2))) : Bool :=
  (topLetter stack).isSome && (topLetter stack.tail).isNone

theorem topIsSingle_sealed {role : List (Fin 2)} {junk : List (Option (Fin 2))}
    (hsealed : Sealed junk) : topIsSingle (role.map some ++ junk) = decide (role.length = 1) := by
  cases role with
  | nil =>
    have htop : topLetter (([] : List (Fin 2)).map some ++ junk) = none :=
      topLetter_sealed hsealed
    unfold topIsSingle
    rw [htop]
    rfl
  | cons a rest =>
    have htop : topLetter ((a :: rest).map some ++ junk) = some a := rfl
    have htail : topLetter ((a :: rest).map some ++ junk).tail = rest.head? := by
      show topLetter (rest.map some ++ junk) = rest.head?
      exact topLetter_sealed hsealed
    unfold topIsSingle
    rw [htop, htail]
    cases rest <;> simp

/-- The constructor of a rotation state: what the finite control keeps of it. -/
inductive RotationPhase where
  | idle | reversing | appending | done
  deriving DecidableEq, Fintype

def rotationPhase : RotationState (Fin 2) → RotationPhase
  | .idle => .idle
  | .reversing _ _ _ _ _ => .reversing
  | .appending _ _ _ => .appending
  | .done _ => .done

/-- The valid count of an appending rotation is `0` (any other state: `true`, unused). -/
def validIsZero : RotationState (Fin 2) → Bool
  | .appending ok _ _ => decide (ok = 0)
  | _ => true

/-- The observation from the phase in the control, the zero test of the valid counter, and the
two top cells of the role stacks. -/
def rotationViewOfTops (phase : RotationPhase) (validZero : Bool)
    (stackOf : SRole → List (Option (Fin 2))) : RotationView :=
  match phase with
  | .idle => .idle
  | .done => .done
  | .reversing =>
      .reversing (topLetter (stackOf .fwd)) (topLetter (stackOf .rev)) (topIsSingle (stackOf .rev))
  | .appending =>
      .appending validZero (topLetter (stackOf .fwd')) (topLetter (stackOf .rev')).isSome

def queueViewOfTops (phase : RotationPhase) (validZero : Bool)
    (stackOf : SRole → List (Option (Fin 2))) : QueueView :=
  ⟨(topLetter (stackOf .front)).isNone, rotationViewOfTops phase validZero stackOf⟩

/-- **The observation is read from the stack tops**: on sealed junk, the phase, the zero test of
the valid counter and the two top cells of five role stacks give `queueView`. -/
theorem queueView_eq_tops {q : Queue (Fin 2)} {ρ : SRoles}
    {stack junk : ℕ → List (Option (Fin 2))} (hlays : LaysSealed q ρ stack junk) :
    queueView q = queueViewOfTops (rotationPhase q.state) (validIsZero q.state)
      (fun ro => stack (ρ ro)) := by
  obtain ⟨hstack, hsealed⟩ := hlays
  have htop : ∀ ro, topLetter (stack (ρ ro)) = (sRoleList q ro).head? := fun ro => by
    rw [hstack ro]; exact topLetter_sealed (hsealed _)
  have hsingle : ∀ ro, topIsSingle (stack (ρ ro)) = decide ((sRoleList q ro).length = 1) :=
    fun ro => by rw [hstack ro]; exact topIsSingle_sealed (hsealed _)
  have hfront : q.front.isEmpty = (topLetter (stack (ρ .front))).isNone := by
    rw [htop .front]
    show q.front.isEmpty = q.front.head?.isNone
    cases q.front <;> rfl
  unfold queueView queueViewOfTops
  rw [hfront]
  congr 1
  cases hstate : q.state with
  | idle => rfl
  | done f => rfl
  | reversing ok f f' r r' =>
    show RotationView.reversing f.head? r.head? (decide (r.length = 1)) = _
    simp only [rotationPhase, rotationViewOfTops, htop, hsingle, sRoleList, hstate]
  | appending ok f' r' =>
    show RotationView.appending (decide (ok = 0)) f'.head? (!r'.isEmpty) = _
    simp only [rotationPhase, rotationViewOfTops, validIsZero, htop, sRoleList, hstate]
    cases r' <;> rfl

#print axioms queueView_eq_tops

end PalPeg.ConcreteLocalMachine
