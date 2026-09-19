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
open PalPeg.CloseoutCoreEnc21 (SRole SRoles toAddr pushRearD tailD revD appStartD appD invalDoneD)
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

end PalPeg.ConcreteLocalMachine
