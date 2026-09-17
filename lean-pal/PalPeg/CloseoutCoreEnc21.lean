import PalPeg.CloseoutCoreEnc20
import Mathlib.Logic.Relation

/-!
# Closeout, step 2u: the shadow copy removes the duplication `f := front`

`CloseoutCoreEnc20` §5 left one obstruction on the six-stack layout of the
Hood–Melville queue: the rotation start aliases the stored `front` with the
reversal source `f`, the two diverge after one reversing step
(`front_fwd_sep`), and installing `f` on any *empty* stack costs one head move
per live cell (`not_bounded_install_fwd`).  This file removes the copy by a
**shadow tape** `g` that is maintained continuously, and turns the remaining
"erasures" into free role renames by letting a stack carry **junk below** its
live list.  Nothing here is about the whole machine, so

**無条件 PAL ∈ PEG は未完.**

## The design (deviations from the brief, with reasons)

* **Seven roles** (`SRole`): the six of `CloseoutCoreEnc20.QRole` plus
  `shadow`.  Its list is *derived* from the queue state (`sRoleList`): during a
  rotation `shadow = r'` (every push onto `r'` is mirrored onto `g`, two
  different addresses, one action each), at `.done f` it is `f`, and in `idle`
  it is `front`.  So no new abstract state is needed.
* **No `popped` prefix.**  The brief proposed `g = popped ++ front` with the
  prefix discarded at the next rotation start.  That does **not** fit the
  real-time budget: after a rotation that leaves `front` of length `2m+1`,
  `2m+1` tails followed by one `snoc` start a rotation on a queue of size `1`
  with a `2m+1`-element discard pending, and two more `snoc`s demand a second
  rotation before the first can finish (violating `RTQueue.PInv.rot`).
  Instead `tail` on an *idle* queue pops `front` **and** `shadow` (`tailD
  true`: one action on each of two addresses), so `g = front` exactly and the
  rotation start needs no discard at all.
* **Junk below is free** (`LaysS`, §1): the physical stack at address `ρ ro`
  is `sRoleList q ro ++ J (ρ ro)`.  A role whose list becomes `[]` while its
  tape is nonempty (the old `front` at `.done`, the leftover `f'` at
  `appending 0`) just moves its content into `J`: no head move.  The
  abstract steps only ever pop a list whose shape is `x :: _`, so the junk is
  never read.  This also disposes of `CloseoutCoreEnc20`'s "not established" 3
  (`invalidate_lays` needed `f' = []`).

## What is established (unconditional)

* **§1** `SRole`, `sRoleList`, `LaysS q ρ L J`, `SInj`, and the address
  family `toAddr ρ uR` built from a *role-indexed* delta `uR`; `laysS_delta`
  is the one lemma every list-changing step goes through.
* **§2** `SStep`: the six queue sub-steps (`snocPush`, `tailPop`, `inval`,
  `rotStart`, `exec`, `install`), and the decomposition `snoc_steps`,
  `tail_steps`, `check_steps`: every `RTQueue.snoc` / `RTQueue.tail` is a
  `ReflTransGen SStep` chain, under the HM invariant `lenf < lenr → idle`
  (`RTQueue.PInv.rot`, taken as a hypothesis here).
* **§3** the role permutations `rotRolesS` (rotation start:
  `fwd ↦ ρ shadow`, `rev ↦ ρ rear`, `rear ↦ ρ fwd`, `shadow ↦ ρ rev`) and
  `doneRolesS` (`front ↦ ρ rev'`, `rev' ↦ ρ front`), both injective.
* **§4** `sstep_lays`: **every** `SStep` is realised, from any injective
  layout, by a `Delta` family (with a new injective role table and new junk).
  The rotation start and the install are the empty family; the reversing
  step, the reversing→appending step, the appending step, the `invalidate` at
  `appending 0`, the `tail` pop and the `snoc` push are the families
  `revD`, `appStartD`, `appD`, `invalDoneD`, `tailD`, `pushRearD`.
* **§5** `moveRightS_actList`: for every `SStep` on `v.far` there is a delta
  family whose micro-action list has length `≤ 2` at **every** address of the
  cursor `viewTapesQ`, and the resulting family is again laid out.  So the
  `ρ' .fwd = ρ .rear` escape of `CloseoutCoreEnc20` is now `ρ' .fwd = ρ
  .shadow`, and it is realised, not merely unrefuted.

## What is *not* established, one line each

1. **The `moveRight` glue is not rebuilt**: `SStep` is the queue part only;
   the `near`/`back` tapes and `encTapesQ` / `shiftVm_tapeActKQ` (with
   `tViewQ` now `9`: two head tapes plus seven stacks) are not assembled.
2. **`hrot` is a hypothesis** of `check_steps`: it is `RTQueue.PInv.rot`
   (after `invalidate`, the form `RTQueue.lean` derives around line 570), not
   re-proved here.
3. **The finite control is not built**: the branch of `exec` is decided by the
   *shapes* of the role lists (`x :: _` vs `[]`); the control that reads the
   top cell of a stack to tell live from junk needs a bottom marker or the
   counters `lenf`/`lenr`/`ok`, and neither is laid out here.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutCoreEnc21

open PalPeg PalPeg.Program
open PalPeg.CloseoutCoreStep (Γc blankc)
open PalPeg.CloseoutCoreEnc12 (Act actList)
open PalPeg.CloseoutCoreEnc20 (Delta dApply viewTapesQ qActs qDebris qActs_length viewTapesQ_delta
  rotStart check_rot)
open PalPeg.LocalInputView (InputView)
open PalPeg.RTQueue (Queue RotationState)
open Relation (ReflTransGen)

/-! ## 1. Seven roles, the shadow, and layouts with junk below -/

/-- The six roles of `CloseoutCoreEnc20.QRole` plus the shadow copy `g`. -/
inductive SRole where
  | front | rear | fwd | fwd' | rev | rev' | shadow
  deriving DecidableEq

/-- The list each role carries.  The shadow is `r'` during a rotation (it
mirrors every push onto `r'`), the finished front at `.done`, and `front`
itself when idle. -/
def sRoleList (q : Queue (Fin 2)) : SRole → List (Fin 2)
  | .front => q.front
  | .rear => q.rear
  | .fwd => match q.state with
      | .reversing _ f _ _ _ => f
      | _ => []
  | .fwd' => match q.state with
      | .reversing _ _ f' _ _ => f'
      | .appending _ f' _ => f'
      | _ => []
  | .rev => match q.state with
      | .reversing _ _ _ r _ => r
      | _ => []
  | .rev' => match q.state with
      | .reversing _ _ _ _ r' => r'
      | .appending _ _ r' => r'
      | .done f => f
      | .idle => []
  | .shadow => match q.state with
      | .reversing _ _ _ _ r' => r'
      | .appending _ _ r' => r'
      | .done f => f
      | .idle => q.front

abbrev SRoles : Type := SRole → ℕ

def SInj (ρ : SRoles) : Prop := ∀ a b : SRole, ρ a = ρ b → a = b

theorem sinj_iff {ρ : SRoles} (h : SInj ρ) (a b : SRole) : ρ a = ρ b ↔ a = b :=
  ⟨h a b, fun e => e ▸ rfl⟩

/-- **Layout with junk below**: the stack at address `ρ ro` is the live list of
role `ro` on top of the junk `J (ρ ro)`. -/
def LaysS (q : Queue (Fin 2)) (ρ : SRoles) (L J : ℕ → List (Fin 2)) : Prop :=
  ∀ ro, L (ρ ro) = sRoleList q ro ++ J (ρ ro)

/-- Override the junk at one address. -/
def ovrL (a : ℕ) (l : List (Fin 2)) (J : ℕ → List (Fin 2)) : ℕ → List (Fin 2) :=
  fun i => if i = a then l else J i

/-- A role-indexed delta, spread over the addresses of the role table. -/
def toAddr (ρ : SRoles) (uR : SRole → Delta) (i : ℕ) : Delta :=
  if i = ρ .front then uR .front
  else if i = ρ .rear then uR .rear
  else if i = ρ .fwd then uR .fwd
  else if i = ρ .fwd' then uR .fwd'
  else if i = ρ .rev then uR .rev
  else if i = ρ .rev' then uR .rev'
  else if i = ρ .shadow then uR .shadow
  else .keep

theorem toAddr_eq {ρ : SRoles} (hinj : SInj ρ) (uR : SRole → Delta) (ro : SRole) :
    toAddr ρ uR (ρ ro) = uR ro := by
  cases ro <;> simp [toAddr, sinj_iff hinj]

/-- **The one lemma every list-changing step goes through**: if the delta of
each role turns its stack into the new live list on the new junk, the family
`toAddr ρ uR` lays out the new queue. -/
theorem laysS_delta {q q' : Queue (Fin 2)} {ρ : SRoles} {L J J' : ℕ → List (Fin 2)}
    (hinj : SInj ρ) (h : LaysS q ρ L J) (uR : SRole → Delta)
    (hro : ∀ ro, dApply (uR ro) (sRoleList q ro ++ J (ρ ro)) = sRoleList q' ro ++ J' (ρ ro)) :
    LaysS q' ρ (fun i => dApply (toAddr ρ uR i) (L i)) J' := by
  intro ro
  show dApply (toAddr ρ uR (ρ ro)) (L (ρ ro)) = _
  rw [toAddr_eq hinj, h ro]
  exact hro ro

/-! ## 2. The queue sub-steps and the decomposition of `snoc` / `tail` -/

/-- The six sub-steps a Hood–Melville operation is made of. -/
inductive SStep : Queue (Fin 2) → Queue (Fin 2) → Prop where
  | snocPush (q : Queue (Fin 2)) (a : Fin 2) :
      SStep q { q with lenr := q.lenr + 1, rear := a :: q.rear }
  | tailPop (q : Queue (Fin 2)) (c : Fin 2) (f : List (Fin 2)) (hfr : q.front = c :: f) :
      SStep q { q with lenf := q.lenf - 1, front := f }
  | inval (q : Queue (Fin 2)) : SStep q { q with state := RTQueue.invalidate q.state }
  | rotStart (q : Queue (Fin 2)) (hidle : q.state = .idle) : SStep q (rotStart q)
  | exec (q : Queue (Fin 2)) : SStep q { q with state := RTQueue.exec q.state }
  | install (q : Queue (Fin 2)) (f : List (Fin 2)) (hst : q.state = .done f) :
      SStep q { q with front := f, state := .idle }

/-- The install `exec2` performs when the rotation has finished. -/
def finish (q : Queue (Fin 2)) : Queue (Fin 2) :=
  match q.state with
  | .done f => { q with front := f, state := .idle }
  | _ => q

theorem exec2_eq_finish (q : Queue (Fin 2)) :
    RTQueue.exec2 q = finish { q with state := RTQueue.exec (RTQueue.exec q.state) } := by
  cases hs : RTQueue.exec (RTQueue.exec q.state) <;> simp [RTQueue.exec2, finish, hs]

theorem finish_steps (q : Queue (Fin 2)) : ReflTransGen SStep q (finish q) := by
  unfold finish
  split
  · next f hf => exact ReflTransGen.single (SStep.install q f hf)
  · exact ReflTransGen.refl

theorem exec_exec_finish_steps (q : Queue (Fin 2)) :
    ReflTransGen SStep q (finish { q with state := RTQueue.exec (RTQueue.exec q.state) }) :=
  ((ReflTransGen.single (SStep.exec q)).tail (SStep.exec _)).trans (finish_steps _)

/-- **`check` is a chain of sub-steps**, under the HM invariant that a rotation
is only started on an idle queue (`RTQueue.PInv.rot`). -/
theorem check_steps (q : Queue (Fin 2)) (hrot : q.lenf < q.lenr → q.state = .idle) :
    ReflTransGen SStep q (RTQueue.check q) := by
  by_cases hle : q.lenr ≤ q.lenf
  · rw [RTQueue.check, if_pos hle, exec2_eq_finish]
    exact exec_exec_finish_steps q
  · rw [check_rot q hle, exec2_eq_finish]
    exact (ReflTransGen.single (SStep.rotStart q (hrot (Nat.lt_of_not_le hle)))).trans
      (exec_exec_finish_steps _)

theorem snoc_steps (q : Queue (Fin 2)) (a : Fin 2)
    (hrot : q.lenf < q.lenr + 1 → q.state = .idle) :
    ReflTransGen SStep q (RTQueue.snoc q a) :=
  (ReflTransGen.single (SStep.snocPush q a)).trans (check_steps _ hrot)

theorem tail_steps (q : Queue (Fin 2))
    (hrot : q.lenf - 1 < q.lenr → RTQueue.invalidate q.state = .idle) :
    ReflTransGen SStep q (RTQueue.tail q) := by
  unfold RTQueue.tail
  split
  · exact ReflTransGen.refl
  · next c f hfr =>
      exact ((ReflTransGen.single (SStep.tailPop q c f hfr)).tail (SStep.inval _)).trans
        (check_steps _ hrot)

/-! ## 3. Role-indexed deltas and the two role permutations -/

def pushRearD (a : Fin 2) : SRole → Delta
  | .rear => .push a
  | _ => .keep

/-- `tail`: pop `front`, and pop the shadow too when idle (it is `front`). -/
def tailD (idle : Bool) : SRole → Delta
  | .front => .pop
  | .shadow => if idle then .pop else .keep
  | _ => .keep

/-- One reversing step: pop `f`, push `f'`, pop `r`, push `r'` **and** `g`. -/
def revD (x y : Fin 2) : SRole → Delta
  | .fwd => .pop
  | .fwd' => .push x
  | .rev => .pop
  | .rev' => .push y
  | .shadow => .push y
  | _ => .keep

/-- Reversing → appending: pop the last `r`, push `r'` and `g`. -/
def appStartD (y : Fin 2) : SRole → Delta
  | .rev => .pop
  | .rev' => .push y
  | .shadow => .push y
  | _ => .keep

/-- One appending step: pop `f'`, push `r'` and `g`. -/
def appD (x : Fin 2) : SRole → Delta
  | .fwd' => .pop
  | .rev' => .push x
  | .shadow => .push x
  | _ => .keep

/-- `invalidate` at `appending 0`: pop `r'` and `g`. -/
def invalDoneD : SRole → Delta
  | .rev' => .pop
  | .shadow => .pop
  | _ => .keep

/-- Rotation start: `fwd` takes the shadow, `rev` the rear, the (empty) old
`fwd` becomes the new rear, the (empty) old `rev` the new shadow. -/
def rotPerm : SRole → SRole
  | .front => .front
  | .rear => .fwd
  | .fwd => .shadow
  | .fwd' => .fwd'
  | .rev => .rear
  | .rev' => .rev'
  | .shadow => .rev

def rotRolesS (ρ : SRoles) : SRoles := fun ro => ρ (rotPerm ro)

/-- Install: `front` takes `r'`; the old front tape (now junk) takes `rev'`. -/
def donePerm : SRole → SRole
  | .front => .rev'
  | .rear => .rear
  | .fwd => .fwd
  | .fwd' => .fwd'
  | .rev => .rev
  | .rev' => .front
  | .shadow => .shadow

def doneRolesS (ρ : SRoles) : SRoles := fun ro => ρ (donePerm ro)

theorem sinj_perm (ρ : SRoles) (hinj : SInj ρ) (π : SRole → SRole)
    (hπ : ∀ a b, π a = π b → a = b) : SInj (fun ro => ρ (π ro)) :=
  fun a b hab => hπ a b (hinj _ _ hab)

theorem rotPerm_inj : ∀ a b : SRole, rotPerm a = rotPerm b → a = b := by
  intro a b; cases a <;> cases b <;> simp [rotPerm]

theorem donePerm_inj : ∀ a b : SRole, donePerm a = donePerm b → a = b := by
  intro a b; cases a <;> cases b <;> simp [donePerm]

theorem sinj_rotRolesS {ρ : SRoles} (hinj : SInj ρ) : SInj (rotRolesS ρ) :=
  sinj_perm ρ hinj rotPerm rotPerm_inj

theorem sinj_doneRolesS {ρ : SRoles} (hinj : SInj ρ) : SInj (doneRolesS ρ) :=
  sinj_perm ρ hinj donePerm donePerm_inj

/-! ## 4. Every sub-step is a delta family -/

theorem exec_cases (s : RotationState (Fin 2)) :
    (∃ ok x f f' y r r', s = .reversing ok (x :: f) f' (y :: r) r') ∨
    (∃ ok f' y r', s = .reversing ok [] f' [y] r') ∨
    (∃ f' r', s = .appending 0 f' r') ∨
    (∃ ok x f' r', s = .appending (ok + 1) (x :: f') r') ∨
    RTQueue.exec s = s := by
  cases s with
  | idle => exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  | done f => exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  | reversing ok f f' r r' =>
      cases f with
      | cons x f =>
          cases r with
          | nil => exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
          | cons y r => exact Or.inl ⟨ok, x, f, f', y, r, r', rfl⟩
      | nil =>
          cases r with
          | nil => exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
          | cons y r =>
              cases r with
              | nil => exact Or.inr (Or.inl ⟨ok, f', y, r', rfl⟩)
              | cons z r => exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  | appending ok f' r' =>
      cases ok with
      | zero => exact Or.inr (Or.inr (Or.inl ⟨f', r', rfl⟩))
      | succ ok =>
          cases f' with
          | nil => exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
          | cons x f' => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ok, x, f', r', rfl⟩)))

theorem invalidate_cases (s : RotationState (Fin 2)) :
    (∃ ok f f' r r', s = .reversing ok f f' r r') ∨
    (∃ f' x r', s = .appending 0 f' (x :: r')) ∨
    (∃ ok f' r', s = .appending (ok + 1) f' r') ∨
    RTQueue.invalidate s = s := by
  cases s with
  | idle => exact Or.inr (Or.inr (Or.inr rfl))
  | done f => exact Or.inr (Or.inr (Or.inr rfl))
  | reversing ok f f' r r' => exact Or.inl ⟨ok, f, f', r, r', rfl⟩
  | appending ok f' r' =>
      cases ok with
      | zero =>
          cases r' with
          | nil => exact Or.inr (Or.inr (Or.inr rfl))
          | cons x r' => exact Or.inr (Or.inl ⟨f', x, r', rfl⟩)
      | succ ok => exact Or.inr (Or.inr (Or.inl ⟨ok, f', r', rfl⟩))

/-- **Every queue sub-step is realised by a `Delta` family**, from any
injective layout, with an injective new role table and new junk. -/
theorem sstep_lays (q q' : Queue (Fin 2)) (hs : SStep q q') (ρ : SRoles)
    (L J : ℕ → List (Fin 2)) (hinj : SInj ρ) (h : LaysS q ρ L J) :
    ∃ (ρ' : SRoles) (J' : ℕ → List (Fin 2)) (u : ℕ → Delta),
      SInj ρ' ∧ LaysS q' ρ' (fun i => dApply (u i) (L i)) J' := by
  have hL : ∀ ro, L (ρ ro) = sRoleList q ro ++ J (ρ ro) := h
  cases hs with
  | snocPush a =>
      refine ⟨ρ, J, toAddr ρ (pushRearD a), hinj, laysS_delta hinj h _ ?_⟩
      intro ro; cases ro <;> simp [pushRearD, dApply, sRoleList]
  | tailPop c f hfr =>
      cases hst : q.state with
      | idle =>
          refine ⟨ρ, J, toAddr ρ (tailD true), hinj, laysS_delta hinj h _ ?_⟩
          intro ro; cases ro <;> simp [tailD, dApply, sRoleList, hst, hfr]
      | reversing ok f0 f' r r' =>
          refine ⟨ρ, J, toAddr ρ (tailD false), hinj, laysS_delta hinj h _ ?_⟩
          intro ro; cases ro <;> simp [tailD, dApply, sRoleList, hst, hfr]
      | appending ok f' r' =>
          refine ⟨ρ, J, toAddr ρ (tailD false), hinj, laysS_delta hinj h _ ?_⟩
          intro ro; cases ro <;> simp [tailD, dApply, sRoleList, hst, hfr]
      | done f0 =>
          refine ⟨ρ, J, toAddr ρ (tailD false), hinj, laysS_delta hinj h _ ?_⟩
          intro ro; cases ro <;> simp [tailD, dApply, sRoleList, hst, hfr]
  | inval =>
      rcases invalidate_cases q.state with
        ⟨ok, f, f', r, r', hst⟩ | ⟨f', x, r', hst⟩ | ⟨ok, f', r', hst⟩ | he
      · refine ⟨ρ, J, toAddr ρ (fun _ => .keep), hinj, laysS_delta hinj h _ ?_⟩
        intro ro; cases ro <;> simp [dApply, sRoleList, hst, RTQueue.invalidate]
      · refine ⟨ρ, ovrL (ρ .fwd') (f' ++ J (ρ .fwd')) J, toAddr ρ invalDoneD, hinj,
          laysS_delta hinj h _ ?_⟩
        intro ro; cases ro <;>
          simp [invalDoneD, dApply, sRoleList, hst, RTQueue.invalidate, ovrL, sinj_iff hinj]
      · refine ⟨ρ, J, toAddr ρ (fun _ => .keep), hinj, laysS_delta hinj h _ ?_⟩
        intro ro; cases ro <;> simp [dApply, sRoleList, hst, RTQueue.invalidate]
      · have hq : ({ q with state := RTQueue.invalidate q.state } : Queue (Fin 2)) = q := by
          rw [he]
        rw [hq]
        exact ⟨ρ, J, fun _ => .keep, hinj, h⟩
  | rotStart hidle =>
      refine ⟨rotRolesS ρ, J, fun _ => .keep, sinj_rotRolesS hinj, ?_⟩
      intro ro
      show L (rotRolesS ρ ro) = _
      cases ro <;> simp [rotRolesS, rotPerm, hL, sRoleList, rotStart, hidle]
  | exec =>
      rcases exec_cases q.state with
        ⟨ok, x, f, f', y, r, r', hst⟩ | ⟨ok, f', y, r', hst⟩ | ⟨f', r', hst⟩ |
        ⟨ok, x, f', r', hst⟩ | he
      · refine ⟨ρ, J, toAddr ρ (revD x y), hinj, laysS_delta hinj h _ ?_⟩
        intro ro; cases ro <;> simp [revD, dApply, sRoleList, hst, RTQueue.exec]
      · refine ⟨ρ, J, toAddr ρ (appStartD y), hinj, laysS_delta hinj h _ ?_⟩
        intro ro; cases ro <;> simp [appStartD, dApply, sRoleList, hst, RTQueue.exec]
      · refine ⟨ρ, ovrL (ρ .fwd') (f' ++ J (ρ .fwd')) J, toAddr ρ (fun _ => .keep), hinj,
          laysS_delta hinj h _ ?_⟩
        intro ro; cases ro <;>
          simp [dApply, sRoleList, hst, RTQueue.exec, ovrL, sinj_iff hinj]
      · refine ⟨ρ, J, toAddr ρ (appD x), hinj, laysS_delta hinj h _ ?_⟩
        intro ro; cases ro <;> simp [appD, dApply, sRoleList, hst, RTQueue.exec]
      · have hq : ({ q with state := RTQueue.exec q.state } : Queue (Fin 2)) = q := by
          rw [he]
        rw [hq]
        exact ⟨ρ, J, fun _ => .keep, hinj, h⟩
  | install f hst =>
      refine ⟨doneRolesS ρ, ovrL (ρ .front) (q.front ++ J (ρ .front)) J, fun _ => .keep,
        sinj_doneRolesS hinj, ?_⟩
      intro ro
      show L (doneRolesS ρ ro) = _
      cases ro <;> simp [doneRolesS, donePerm, hL, sRoleList, hst, ovrL, sinj_iff hinj]

/-! ## 5. Bounded micro-action lists at every address of the cursor -/

theorem viewTapesQ_far (v : InputView) (q' : Queue (Fin 2)) (L : ℕ → List (Fin 2))
    (d : ℕ → List Γc) (i : ℕ) :
    viewTapesQ { v with far := q' } L d i = viewTapesQ v L d i := by
  match i with
  | 0 => rfl
  | 1 => rfl
  | (n + 2) => rfl

/-- **Every queue sub-step of the `far` component is a bounded composite at
every address of the cursor**, and the result is laid out again.  This covers
the rotation start (`SStep.rotStart`: the empty family, `ρ' .fwd = ρ .shadow`),
the reversing / appending steps, `invalidate`, the `tail` pop, the `snoc` push
and the install. -/
theorem moveRightS_actList (v : InputView) (L J : ℕ → List (Fin 2)) (d : ℕ → List Γc)
    (ρ : SRoles) (hinj : SInj ρ) (h : LaysS v.far ρ L J) (q' : Queue (Fin 2))
    (hs : SStep v.far q') :
    ∃ (ρ' : SRoles) (J' : ℕ → List (Fin 2)) (u : ℕ → Delta),
      SInj ρ' ∧ LaysS q' ρ' (fun i => dApply (u i) (L i)) J' ∧
      ∀ i, viewTapesQ { v with far := q' } (fun i => dApply (u i) (L i)) (qDebris u L d) i
            = actList blankc (viewTapesQ v L d i) (qActs u L i) ∧ (qActs u L i).length ≤ 2 := by
  obtain ⟨ρ', J', u, hinj', hl⟩ := sstep_lays v.far q' hs ρ L J hinj h
  refine ⟨ρ', J', u, hinj', hl, fun i => ⟨?_, qActs_length u L i⟩⟩
  rw [viewTapesQ_far]
  exact viewTapesQ_delta v L d u i

end PalPeg.CloseoutCoreEnc21

#print axioms PalPeg.CloseoutCoreEnc21.toAddr_eq
#print axioms PalPeg.CloseoutCoreEnc21.laysS_delta
#print axioms PalPeg.CloseoutCoreEnc21.exec2_eq_finish
#print axioms PalPeg.CloseoutCoreEnc21.check_steps
#print axioms PalPeg.CloseoutCoreEnc21.snoc_steps
#print axioms PalPeg.CloseoutCoreEnc21.tail_steps
#print axioms PalPeg.CloseoutCoreEnc21.sinj_rotRolesS
#print axioms PalPeg.CloseoutCoreEnc21.sinj_doneRolesS
#print axioms PalPeg.CloseoutCoreEnc21.exec_cases
#print axioms PalPeg.CloseoutCoreEnc21.invalidate_cases
#print axioms PalPeg.CloseoutCoreEnc21.sstep_lays
#print axioms PalPeg.CloseoutCoreEnc21.moveRightS_actList
