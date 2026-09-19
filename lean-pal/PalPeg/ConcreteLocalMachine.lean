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
open PalPeg.CloseoutCoreEnc21 (SRole SRoles SInj sinj_iff toAddr toAddr_eq pushRearD tailD revD
  appStartD appD invalDoneD sRoleList finish rotPerm donePerm rotRolesS doneRolesS)
open PalPeg.CloseoutCoreEnc20 (rotStart)
open PalPeg.CloseoutCoreEnc25 (SOp RTag rotTag doneTag roleOf roleOf_rotTag roleOf_doneTag
  sinj_roleOf isIdle isDone isIdle_eq isDone_eq sApply deltaOf tagStep invalDelta execDelta
  toAddr_keep)
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

/-! ## The sub-step on sealed stacks

The stack operations are those of `deltaOf`, on cells; in the three places where a role's list
becomes junk (`CloseoutCoreEnc25.junkOf`) that stack gets the seal `none` pushed instead of being
kept.  A pop always meets a letter: every `pop` of `deltaOf` is on a role whose list the pattern
shows to be non-empty. -/

/-- One stack operation on cells: the seal, or the `Delta` on letters. -/
def cellApply : Delta → Bool → List (Option (Fin 2)) → List (Option (Fin 2))
  | _, true, stack => none :: stack
  | .keep, false, stack => stack
  | .pop, false, stack => stack.tail
  | .push a, false, stack => some a :: stack

def invalSealRole : RotationState (Fin 2) → Option SRole
  | .appending 0 _ (_ :: _) => some .fwd'
  | _ => none

def execSealRole : RotationState (Fin 2) → Option SRole
  | .appending 0 _ _ => some .fwd'
  | _ => none

/-- The role whose stack a sub-step seals: the one whose list becomes junk. -/
def sealRoleOf : SOp → Queue (Fin 2) → Option SRole
  | .inval, q => invalSealRole q.state
  | .exec, q => execSealRole q.state
  | .install, q => if isDone q.state then some .front else none
  | _, _ => none

def ovrCell (address : ℕ) (cells : List (Option (Fin 2))) (junk : ℕ → List (Option (Fin 2))) :
    ℕ → List (Option (Fin 2)) :=
  fun i => if i = address then cells else junk i

def invalSealedJunk (ρ : SRoles) (junk : ℕ → List (Option (Fin 2))) :
    RotationState (Fin 2) → (ℕ → List (Option (Fin 2)))
  | .appending 0 f' (_ :: _) => ovrCell (ρ .fwd') (none :: (f'.map some ++ junk (ρ .fwd'))) junk
  | _ => junk

def execSealedJunk (ρ : SRoles) (junk : ℕ → List (Option (Fin 2))) :
    RotationState (Fin 2) → (ℕ → List (Option (Fin 2)))
  | .appending 0 f' _ => ovrCell (ρ .fwd') (none :: (f'.map some ++ junk (ρ .fwd'))) junk
  | _ => junk

/-- The junk after a sub-step: the sealed stack joins it. -/
def sealedJunkOf : SOp → Queue (Fin 2) → SRoles → (ℕ → List (Option (Fin 2))) →
    (ℕ → List (Option (Fin 2)))
  | .inval, q, ρ, junk => invalSealedJunk ρ junk q.state
  | .exec, q, ρ, junk => execSealedJunk ρ junk q.state
  | .install, q, ρ, junk =>
      if isDone q.state then
        ovrCell (ρ .front) (none :: (q.front.map some ++ junk (ρ .front))) junk
      else junk
  | _, _, _, junk => junk

theorem sealed_ovrCell {junk : ℕ → List (Option (Fin 2))} (hsealed : ∀ i, Sealed (junk i))
    (address : ℕ) (cells : List (Option (Fin 2))) :
    ∀ i, Sealed (ovrCell address (none :: cells) junk i) := by
  intro i a
  unfold ovrCell
  split
  · simp
  · exact hsealed i a

/-- The role-indexed form of one sub-step on sealed stacks. -/
theorem laysSealed_delta {q q' : Queue (Fin 2)} {ρ : SRoles}
    {stack junk junk' : ℕ → List (Option (Fin 2))}
    (hinj : SInj ρ) (h : LaysSealed q ρ stack junk) (uR : SRole → Delta)
    (sealRole : Option SRole)
    (hro : ∀ ro, cellApply (uR ro) (decide (sealRole = some ro))
      ((sRoleList q ro).map some ++ junk (ρ ro)) = (sRoleList q' ro).map some ++ junk' (ρ ro))
    (hsealed' : ∀ i, Sealed (junk' i)) :
    LaysSealed q' ρ
      (fun i => cellApply (toAddr ρ uR i) (decide (sealRole.map ρ = some i)) (stack i)) junk' := by
  refine ⟨fun ro => ?_, hsealed'⟩
  show cellApply (toAddr ρ uR (ρ ro)) (decide (sealRole.map ρ = some (ρ ro))) (stack (ρ ro)) = _
  have hseal : decide (sealRole.map ρ = some (ρ ro)) = decide (sealRole = some ro) := by
    cases sealRole with
    | none => simp
    | some r => simp [sinj_iff hinj]
  rw [toAddr_eq hinj, h.1 ro, hseal]
  exact hro ro

theorem cellApply_keep_fam (ρ : SRoles) (stack : ℕ → List (Option (Fin 2))) :
    (fun i => cellApply (toAddr ρ (fun _ => Delta.keep) i)
      (decide ((none : Option SRole).map ρ = some i)) (stack i)) = stack := by
  funext i
  rw [toAddr_keep]
  simp [cellApply]

/-- **One sub-step keeps the sealed layout.** -/
theorem laysSealed_sApply (op : SOp) (q : Queue (Fin 2)) (t : RTag)
    (stack junk : ℕ → List (Option (Fin 2)))
    (h : LaysSealed q (roleOf t) stack junk) :
    LaysSealed (sApply op q) (roleOf (tagStep op q t))
      (fun i => cellApply (deltaOf op q (roleOf t) i)
        (decide ((sealRoleOf op q).map (roleOf t) = some i)) (stack i))
      (sealedJunkOf op q (roleOf t) junk) := by
  have hinj : SInj (roleOf t) := sinj_roleOf t
  have hstack : ∀ ro, stack (roleOf t ro) = (sRoleList q ro).map some ++ junk (roleOf t ro) := h.1
  cases op with
  | snocPush a =>
      refine laysSealed_delta hinj h (pushRearD a) none ?_ h.2
      intro ro; cases ro <;> simp [pushRearD, cellApply, sRoleList, sApply, sealedJunkOf]
  | tailPop =>
      show LaysSealed (if q.front = [] then _ else _) (roleOf t)
        (fun i => cellApply ((if q.front = [] then _ else _ : ℕ → Delta) i)
          (decide ((none : Option SRole).map (roleOf t) = some i)) (stack i)) junk
      by_cases hf : q.front = []
      · rw [if_pos hf, if_pos hf, cellApply_keep_fam]; exact h
      · rw [if_neg hf, if_neg hf]
        refine laysSealed_delta hinj h (tailD (isIdle q.state)) none ?_ h.2
        obtain ⟨c, f, hcf⟩ : ∃ c f, q.front = c :: f := by
          cases hq : q.front with
          | nil => exact absurd hq hf
          | cons c f => exact ⟨c, f, rfl⟩
        intro ro
        cases hst : q.state <;> cases ro <;>
          simp [tailD, cellApply, sRoleList, hst, hcf, isIdle]
  | inval =>
      show LaysSealed { q with state := RTQueue.invalidate q.state } (roleOf t)
        (fun i => cellApply (invalDelta (roleOf t) q.state i)
          (decide ((invalSealRole q.state).map (roleOf t) = some i)) (stack i))
        (invalSealedJunk (roleOf t) junk q.state)
      match hst : q.state with
      | .appending 0 f' (x :: r') =>
          simp only [invalDelta, invalSealRole, invalSealedJunk]
          refine laysSealed_delta hinj h invalDoneD (some .fwd') ?_ (sealed_ovrCell h.2 _ _)
          intro ro; cases ro <;>
            simp [invalDoneD, cellApply, sRoleList, hst, RTQueue.invalidate, ovrCell,
              sinj_iff hinj]
      | .appending 0 f' [] =>
          simp only [invalDelta, invalSealRole, invalSealedJunk]
          refine laysSealed_delta hinj h (fun _ => .keep) none ?_ h.2
          intro ro; cases ro <;> simp [cellApply, sRoleList, hst, RTQueue.invalidate]
      | .appending (n + 1) f' r' =>
          simp only [invalDelta, invalSealRole, invalSealedJunk]
          refine laysSealed_delta hinj h (fun _ => .keep) none ?_ h.2
          intro ro; cases ro <;> simp [cellApply, sRoleList, hst, RTQueue.invalidate]
      | .reversing ok f f' r r' =>
          simp only [invalDelta, invalSealRole, invalSealedJunk]
          refine laysSealed_delta hinj h (fun _ => .keep) none ?_ h.2
          intro ro; cases ro <;> simp [cellApply, sRoleList, hst, RTQueue.invalidate]
      | .idle =>
          simp only [invalDelta, invalSealRole, invalSealedJunk]
          refine laysSealed_delta hinj h (fun _ => .keep) none ?_ h.2
          intro ro; cases ro <;> simp [cellApply, sRoleList, hst, RTQueue.invalidate]
      | .done f0 =>
          simp only [invalDelta, invalSealRole, invalSealedJunk]
          refine laysSealed_delta hinj h (fun _ => .keep) none ?_ h.2
          intro ro; cases ro <;> simp [cellApply, sRoleList, hst, RTQueue.invalidate]
  | rotStart =>
      show LaysSealed (if isIdle q.state then _ else _)
        (roleOf (if isIdle q.state then rotTag t else t))
        (fun i => cellApply (toAddr (roleOf t) (fun _ => Delta.keep) i)
          (decide ((none : Option SRole).map (roleOf t) = some i)) (stack i)) junk
      rw [cellApply_keep_fam]
      by_cases hi : isIdle q.state = true
      · rw [if_pos hi, if_pos hi, roleOf_rotTag]
        have hidle : q.state = .idle := isIdle_eq hi
        refine ⟨fun ro => ?_, h.2⟩
        show stack (rotRolesS (roleOf t) ro) = _
        cases ro <;> simp [rotRolesS, rotPerm, hstack, sRoleList, rotStart, hidle]
      · rw [if_neg hi, if_neg hi]; exact h
  | exec =>
      show LaysSealed { q with state := RTQueue.exec q.state } (roleOf t)
        (fun i => cellApply (execDelta (roleOf t) q.state i)
          (decide ((execSealRole q.state).map (roleOf t) = some i)) (stack i))
        (execSealedJunk (roleOf t) junk q.state)
      match hst : q.state with
      | .reversing ok (x :: f) f' (y :: r) r' =>
          simp only [execDelta, execSealRole, execSealedJunk]
          refine laysSealed_delta hinj h (revD x y) none ?_ h.2
          intro ro; cases ro <;> simp [revD, cellApply, sRoleList, hst, RTQueue.exec]
      | .reversing ok [] f' [y] r' =>
          simp only [execDelta, execSealRole, execSealedJunk]
          refine laysSealed_delta hinj h (appStartD y) none ?_ h.2
          intro ro; cases ro <;> simp [appStartD, cellApply, sRoleList, hst, RTQueue.exec]
      | .reversing ok [] f' [] r' =>
          simp only [execDelta, execSealRole, execSealedJunk]
          refine laysSealed_delta hinj h (fun _ => .keep) none ?_ h.2
          intro ro; cases ro <;> simp [cellApply, sRoleList, hst, RTQueue.exec]
      | .reversing ok [] f' (y :: z :: r) r' =>
          simp only [execDelta, execSealRole, execSealedJunk]
          refine laysSealed_delta hinj h (fun _ => .keep) none ?_ h.2
          intro ro; cases ro <;> simp [cellApply, sRoleList, hst, RTQueue.exec]
      | .reversing ok (x :: f) f' [] r' =>
          simp only [execDelta, execSealRole, execSealedJunk]
          refine laysSealed_delta hinj h (fun _ => .keep) none ?_ h.2
          intro ro; cases ro <;> simp [cellApply, sRoleList, hst, RTQueue.exec]
      | .appending 0 f' r' =>
          simp only [execDelta, execSealRole, execSealedJunk]
          refine laysSealed_delta hinj h (fun _ => .keep) (some .fwd') ?_
            (sealed_ovrCell h.2 _ _)
          intro ro; cases ro <;>
            simp [cellApply, sRoleList, hst, RTQueue.exec, ovrCell, sinj_iff hinj]
      | .appending (n + 1) (x :: f') r' =>
          simp only [execDelta, execSealRole, execSealedJunk]
          refine laysSealed_delta hinj h (appD x) none ?_ h.2
          intro ro; cases ro <;> simp [appD, cellApply, sRoleList, hst, RTQueue.exec]
      | .appending (n + 1) [] r' =>
          simp only [execDelta, execSealRole, execSealedJunk]
          refine laysSealed_delta hinj h (fun _ => .keep) none ?_ h.2
          intro ro; cases ro <;> simp [cellApply, sRoleList, hst, RTQueue.exec]
      | .idle =>
          simp only [execDelta, execSealRole, execSealedJunk]
          refine laysSealed_delta hinj h (fun _ => .keep) none ?_ h.2
          intro ro; cases ro <;> simp [cellApply, sRoleList, hst, RTQueue.exec]
      | .done f0 =>
          simp only [execDelta, execSealRole, execSealedJunk]
          refine laysSealed_delta hinj h (fun _ => .keep) none ?_ h.2
          intro ro; cases ro <;> simp [cellApply, sRoleList, hst, RTQueue.exec]
  | install =>
      by_cases hd : isDone q.state = true
      · obtain ⟨f0, hst⟩ := isDone_eq hd
        have hseal : sealRoleOf .install q = some .front := by simp [sealRoleOf, hd]
        have hjunk : sealedJunkOf .install q (roleOf t) junk
            = ovrCell (roleOf t .front)
              (none :: (q.front.map some ++ junk (roleOf t .front))) junk := by
          simp [sealedJunkOf, hd]
        have htag : tagStep .install q t = doneTag t := by simp [tagStep, hd]
        rw [hseal, hjunk, htag, roleOf_doneTag]
        refine ⟨fun ro => ?_, sealed_ovrCell h.2 _ _⟩
        show cellApply (deltaOf .install q (roleOf t) (doneRolesS (roleOf t) ro))
          (decide ((some SRole.front).map (roleOf t) = some (doneRolesS (roleOf t) ro)))
          (stack (doneRolesS (roleOf t) ro)) = _
        have hkeep : ∀ i, deltaOf .install q (roleOf t) i = Delta.keep := fun i => by
          show toAddr (roleOf t) (fun _ => Delta.keep) i = Delta.keep
          exact toAddr_keep _ i
        rw [hkeep]
        cases ro <;>
          simp [doneRolesS, donePerm, hstack, sRoleList, sApply, finish, hst, ovrCell,
            cellApply, sinj_iff hinj]
      · have hseal : sealRoleOf .install q = none := by simp [sealRoleOf, hd]
        have hjunk : sealedJunkOf .install q (roleOf t) junk = junk := by simp [sealedJunkOf, hd]
        have htag : tagStep .install q t = t := by simp [tagStep, hd]
        have hfinish : sApply .install q = q := by
          show finish q = q
          unfold finish
          cases hq : q.state with
          | done f0 => exact absurd (by simp [isDone, hq]) hd
          | idle => simp [hq]
          | reversing ok f f' r r' => simp [hq]
          | appending ok f' r' => simp [hq]
        rw [hseal, hjunk, htag, hfinish]
        have hfamily : (fun i => cellApply (deltaOf .install q (roleOf t) i)
            (decide ((none : Option SRole).map (roleOf t) = some i)) (stack i)) = stack :=
          cellApply_keep_fam (roleOf t) stack
        rw [hfamily]
        exact h

#print axioms laysSealed_sApply

/-! ## The sub-step from finite data -/

def invalSealRoleOfView : RotationView → Option SRole
  | .appending true _ true => some .fwd'
  | _ => none

def execSealRoleOfView : RotationView → Option SRole
  | .appending true _ _ => some .fwd'
  | _ => none

/-- The role a sub-step seals, selected from the finite observation. -/
def sealRoleOfView : SOp → QueueView → Option SRole
  | .inval, v => invalSealRoleOfView v.rotation
  | .exec, v => execSealRoleOfView v.rotation
  | .install, v => if v.rotation.isDone then some .front else none
  | _, _ => none

theorem sealRoleOf_eq_view (op : SOp) (q : Queue (Fin 2)) :
    sealRoleOf op q = sealRoleOfView op (queueView q) := by
  cases op with
  | snocPush a => rfl
  | tailPop => rfl
  | rotStart => rfl
  | inval =>
    show invalSealRole q.state = invalSealRoleOfView (rotationView q.state)
    cases q.state with
    | idle => rfl
    | done f => rfl
    | reversing ok f f' r r' => rfl
    | appending ok f' r' =>
      cases ok with
      | zero => cases r' <;> simp [invalSealRole, invalSealRoleOfView, rotationView]
      | succ n => simp [invalSealRole, invalSealRoleOfView, rotationView]
  | exec =>
    show execSealRole q.state = execSealRoleOfView (rotationView q.state)
    cases q.state with
    | idle => rfl
    | done f => rfl
    | reversing ok f f' r r' => rfl
    | appending ok f' r' =>
      cases ok with
      | zero => simp [execSealRole, execSealRoleOfView, rotationView]
      | succ n => simp [execSealRole, execSealRoleOfView, rotationView]
  | install =>
    show (if isDone q.state then some SRole.front else none)
      = if (rotationView q.state).isDone then some SRole.front else none
    rw [isDone_eq_view]

/-- **The queue sub-step of the local machine.**  The stack operations, the seal and the new role
tag are functions of the operation, the role tag, the rotation phase kept in the control, the
zero test of the valid counter, and the two top cells of the role stacks; they keep the sealed
layout of the abstract sub-step `sApply`. -/
theorem laysSealed_localSubStep (op : SOp) (q : Queue (Fin 2)) (t : RTag)
    (stack junk : ℕ → List (Option (Fin 2)))
    (h : LaysSealed q (roleOf t) stack junk) :
    let view := queueViewOfTops (rotationPhase q.state) (validIsZero q.state)
      (fun ro => stack (roleOf t ro))
    LaysSealed (sApply op q) (roleOf (tagStepOfView op view t))
      (fun i => cellApply (deltaOfView op view (roleOf t) i)
        (decide ((sealRoleOfView op view).map (roleOf t) = some i)) (stack i))
      (sealedJunkOf op q (roleOf t) junk) := by
  intro view
  have hview : queueView q = view := queueView_eq_tops h
  rw [← hview, ← deltaOf_eq_view, ← tagStep_eq_view, ← sealRoleOf_eq_view]
  exact laysSealed_sApply op q t stack junk h

#print axioms laysSealed_localSubStep

end PalPeg.ConcreteLocalMachine
