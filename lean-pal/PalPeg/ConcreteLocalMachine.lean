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
open PalPeg.CloseoutCoreEnc20 (rotStart dApply)
open PalPeg.CloseoutCoreStep (Γc blankc)
open PalPeg.CloseoutCoreEnc (cellSym)
open PalPeg.CloseoutCoreEnc12 (Act actList ActRule compStep)
open PalPeg.Local (Window idx)
open PalPeg.CloseoutCoreEnc18 (dTape topSym popActs pushActs pop_dTape push_dTape)
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

/-- The valid count of a rotation (`0` outside a rotation: a rotation starts and ends at `0`). -/
def validCount : RotationState (Fin 2) → ℕ
  | .reversing ok _ _ _ _ => ok
  | .appending ok _ _ => ok
  | _ => 0

/-- The valid counter as a stack of marks. -/
def validStack (s : RotationState (Fin 2)) : List (Fin 2) := List.replicate (validCount s) 0

/-- The operation on the valid counter, selected from the finite observation. -/
def validDeltaOfView : SOp → RotationView → Delta
  | .inval, .reversing _ _ _ => .pop
  | .inval, .appending false _ _ => .pop
  | .exec, .reversing (some _) (some _) _ => .push 0
  | .exec, .appending false (some _) _ => .pop
  | _, _ => .keep

/-- **The valid counter moves by an operation selected from the observation.** -/
theorem validStack_sApply (op : SOp) (q : Queue (Fin 2)) :
    validStack (sApply op q).state
      = dApply (validDeltaOfView op (rotationView q.state)) (validStack q.state) := by
  cases op with
  | snocPush a =>
    show validStack q.state = _
    cases q.state <;> rfl
  | tailPop =>
    have hstate : (sApply .tailPop q).state = q.state := by
      show (if q.front = [] then q else _).state = q.state
      split <;> rfl
    rw [hstate]
    cases q.state <;> rfl
  | inval =>
    show validStack (RTQueue.invalidate q.state) = _
    cases q.state with
    | idle => rfl
    | done f => rfl
    | reversing ok f f' r r' =>
      cases ok <;> simp [validStack, validCount, RTQueue.invalidate, validDeltaOfView,
        rotationView, dApply, List.replicate_succ]
    | appending ok f' r' =>
      cases ok with
      | zero => cases r' <;> rfl
      | succ n =>
        simp [validStack, validCount, RTQueue.invalidate, validDeltaOfView, rotationView,
          dApply, List.replicate_succ]
  | rotStart =>
    cases hstate : q.state <;>
      simp [sApply, isIdle, rotStart, hstate, validStack, validCount, validDeltaOfView,
        rotationView, dApply]
  | exec =>
    show validStack (RTQueue.exec q.state) = _
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
          simp [validStack, validCount, RTQueue.exec, validDeltaOfView, rotationView, dApply,
            List.replicate_succ]
    | appending ok f' r' =>
      cases ok with
      | zero => rfl
      | succ n =>
        cases f' with
        | nil => rfl
        | cons x f' =>
          simp [validStack, validCount, RTQueue.exec, validDeltaOfView, rotationView, dApply,
            List.replicate_succ]
  | install =>
    cases hstate : q.state <;>
      simp [sApply, finish, hstate, validStack, validCount, validDeltaOfView, rotationView,
        dApply]

theorem validIsZero_eq_top (s : RotationState (Fin 2)) (hphase : rotationPhase s = .appending) :
    validIsZero s = (topLetter ((validStack s).map some)).isNone := by
  cases s with
  | idle => cases hphase
  | done f => cases hphase
  | reversing ok f f' r r' => cases hphase
  | appending ok f' r' => cases ok <;> rfl

#print axioms rotationPhase_sApply
#print axioms validStack_sApply

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
  simp only [topLetter_eq_sym]

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
      cellActsOfTop (validDeltaOfView control.1 view.rotation) false (centreSym (windows tape))
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

end PalPeg.ConcreteLocalMachine
