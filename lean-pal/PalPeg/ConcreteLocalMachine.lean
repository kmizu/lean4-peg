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

/-- The valid count of a rotation (`0` outside a rotation: a rotation starts and ends at `0`). -/
def validCount : RotationState (Fin 2) → ℕ
  | .reversing ok _ _ _ _ => ok
  | .appending ok _ _ => ok
  | _ => 0

/-- The zero test of the valid counter. -/
def validIsZero (s : RotationState (Fin 2)) : Bool := decide (validCount s = 0)

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
    simp only [rotationPhase, rotationViewOfTops, validIsZero, validCount, htop, sRoleList,
      hstate]
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

theorem teqG_actOnG {blank : Γc} {T T' : STape Γc} (h : TEqG blank T T') (a : Act Γc) :
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

theorem teqG_actList {blank : Γc} {T T' : STape Γc} (h : TEqG blank T T') (acts : List (Act Γc)) :
    TEqG blank (actList blank T acts) (actList blank T' acts) := by
  induction acts generalizing T T' with
  | nil => exact h
  | cons a rest ih => exact ih (teqG_actOnG h a)

theorem readWin_teqG {blank : Γc} {K : ℕ} {T T' : STape Γc} (h : TEqG blank T T') :
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
theorem queueRule_sound (hK : 2 ≤ K) {q : Queue (Fin 2)} {control : QueueControl}
    {tapes : Fin 8 → STape Γc} (hrep : QueueRep K q control tapes) (input : Option Terminal) :
    (∀ tape : Fin 8, K ≤ pos (tapes tape)) ∧
      (queueRule Terminal hK).nq control input (fun tape => readWin blankc K (tapes tape))
        = (control.1, tagStep control.1 q control.2.1,
          rotationPhase (sApply control.1 q).state) ∧
      ∀ tapes' : Fin 8 → STape Γc,
        (∀ tape, TEqG blankc
          (actList blankc (tapes tape)
            ((queueRule Terminal hK).acts control input
              (fun tape => readWin blankc K (tapes tape)) tape))
          (tapes' tape)) →
        QueueRep K (sApply control.1 q)
          (control.1, tagStep control.1 q control.2.1,
            rotationPhase (sApply control.1 q).state) tapes' := by
  obtain ⟨stack, junk, bottom, hphase, hlays, hheight, htapes, hsealed, hbottom, hcounter⟩ := hrep
  obtain ⟨hzero, hview⟩ := queueViewOfWindows_eq (by omega) hphase hlays hheight htapes hsealed
    hbottom hcounter
  have hstackHeight : ∀ tape : Fin 8, tape.val < 7 → K ≤ (stack tape.val).length := by
    intro tape htape
    obtain ⟨ro, hro⟩ := roleOf_surjective control.2.1 ⟨tape.val, htape⟩
    have hrole : roleOf control.2.1 ro = tape.val := hro
    rw [← hrole, hlays.1 ro]
    have := hheight (roleOf control.2.1 ro)
    simp only [List.length_append]
    omega
  have hmargin : ∀ tape : Fin 8, K ≤ pos (tapes tape) := by
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
          (htapes tape htape).centreSym_eq (hstackHeight tape htape)]
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
theorem queueRep_step (hK : 2 ≤ K) {q : Queue (Fin 2)} {control : QueueControl}
    {tapes : Fin 8 → STape Γc} (hrep : QueueRep K q control tapes) (input : Option Terminal) :
    QueueRep K (sApply control.1 q)
      ((queueLocalStep Terminal hK).apply blankc (control, tapes) input).1
      ((queueLocalStep Terminal hK).apply blankc (control, tapes) input).2 := by
  obtain ⟨hmargin, hnq, hsound⟩ := queueRule_sound (Terminal := Terminal) hK hrep input
  obtain ⟨hcontrol, hacts⟩ := compStep_apply (queueRule Terminal hK) blankc (control, tapes) input
    hmargin
  have hcontrol' : ((queueLocalStep Terminal hK).apply blankc (control, tapes) input).1
      = (control.1, tagStep control.1 q control.2.1,
        rotationPhase (sApply control.1 q).state) := hcontrol.trans hnq
  rw [hcontrol']
  exact hsound _ hacts

#print axioms queueRule_sound
#print axioms queueRep_step

end Step

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
    (hfront : q.front ≠ [] → 1 ≤ q.lenf)
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
      have hpositive := hfront hempty
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

end PalPeg.ConcreteLocalMachine
