import PalPeg.CloseoutCoreEnc19
import PalPeg.CloseoutCoreEnc7

/-!
# Closeout, step 2t: the real-time queue on six debris stacks, with a role table

`CloseoutCoreEnc19` §6 shows that the rotation branch of
`LocalInputView.moveRight` is **not** a bounded rewrite of the four-tape cursor
`CloseoutCoreEnc18.viewTapesD`: `RTQueue.check` sets `rear := []`, and on
address `3` of that layout this is the clearing of a `dTape`, which costs one
head move per live cell.  The reading proposed for the repair is that on the six
queue stacks of `CloseoutCoreEnc7.queueTapes6` the assignment `rear := []` is
not an erasure at all but a **role permutation**: an empty stack becomes the new
`rear`, and the old `rear` tape becomes the reversal source `r`.  This file
carries that reading out.  Nothing here is about the whole machine, so

**無条件 PAL ∈ PEG は未完.**

## What is established (unconditional)

* **§1 (the role table).**  `QRole`, `roleList`, and the layout predicate
  `Lays q ρ L`: the physical stack at address `ρ ro` carries the list of the
  logical role `ro`.  `queueTapes6_roleList` identifies `CloseoutCoreEnc7`'s
  layout with the identity table, so this is a strict generalisation of it.
* **§2 (one debris stack, one micro-step).**  `Delta` (`keep`/`pop`/`push`) and
  `dTape_delta`: every delta is an `actList` of length `≤ 2` (`dActs_length`)
  on `CloseoutCoreEnc18.dTape`, **unconditionally** — the pop of an empty stack
  is the identity, not an error.  `viewTapesQ` is the eight-tape cursor
  (`back`+`focus`, `near`, six queue stacks) and `viewTapesQ_delta` lifts
  `dTape_delta` to it address by address.
* **§3 (the rotation start writes nothing).**  `rotStart_lays`: on an idle
  queue, `RTQueue.check`'s rotation branch — `state := .reversing 0 front []
  rear []`, `rear := []` — is realised by the role table `rotRoles ρ` on the
  **same** physical family `L`.  `rotStart_actList`: the micro-action list is
  `[]` at every address.  So the reading above is correct, and
  `CloseoutCoreEnc19.not_bounded_rot_rear` is not an obstruction on six stacks:
  it only refutes the four-tape layout.
* **§4 (the rotation steps are bounded).**  `exec_reversing_lays`,
  `exec_appending_lays`, `invalidate_lays`, `tail_pop_lays`: each `RTQueue.exec`
  step, the `invalidate` of `RTQueue.tail`, and the `front` pop of
  `RTQueue.tail` are `Delta` families, hence `≤ 2` micro-actions at each of the
  eight addresses, with the role table *unchanged*.
* **§5 (the new obstruction: `front` and `f` cannot be one tape).**  The
  rotation start aliases the stored `front` with the reversal source `f`
  (`rotRoles ρ .fwd = ρ .front`), which is exactly why §3 is free.  But
  `front_fwd_sep` shows that as soon as the reversing phase has taken one step
  (`0 < ok`) the two roles hold lists of different lengths, so a single-headed
  tape cannot carry both; and `not_bounded_install_fwd` (from `pos_actList_le`
  and `not_bounded_grow`, the dual of
  `CloseoutCoreEnc19.not_bounded_clear_dTape`) shows that installing the `fwd`
  role on any stack that was *empty* costs one head move per live cell.
  `covers_idle_spare` says that under `Covers` every address of an idle queue
  other than the two live ones is empty.  So the cost the four-tape layout paid
  in the erasure `rear := []` reappears one step later in the duplication
  `f := front`.

## What is *not* established, one line each

1. **The `far` branch of `moveRight` is still not a bounded composite**: §5
   leaves exactly one escape — the `fwd` role taking over the *rear* stack
   (`ρ' .fwd = ρ .rear`), which is not refuted here; refuting it needs the
   same six-address counting for `rev`, and is the remaining work.
2. **`moveRightQ_actList` is therefore not stated**: §4 realises `tail` only up
   to that duplication, so the assembled `encTapesQ` / `shiftVm_tapeActKQ`
   (the `tView = 8` rebuild of `CloseoutCoreEnc19.encTapesD` /
   `shiftVm_tapeActK'` without the `near ≠ []` side conditions) are not built.
3. **`invalidate_lays` assumes `f' = []`**: on `appending 0` with a nonempty
   leftover `f'` the `fwd'` role is *discarded*, which is the erasure §5
   forbids; this is the second instance of the same obstruction.
4. **The spare discipline is a hypothesis**: `Covers` is assumed where it is
   used; nothing here constructs the debris columns or the free list.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutCoreEnc20

open PalPeg PalPeg.Program
open PalPeg.Local (pos)
open PalPeg.CloseoutCoreStep (Γc blankc)
open PalPeg.CloseoutCoreEnc3 (stackTape)
open PalPeg.CloseoutCoreEnc12 (Act actList actOnG actList_cons)
open PalPeg.CloseoutCoreEnc18 (dTape pos_dTape popActs pushActs pop_dTape push_dTape)
open PalPeg.CloseoutCoreEnc7 (queueTapes6)
open PalPeg.LocalInputView (InputView)
open PalPeg.RTQueue (Queue RotationState)

/-! ## 1. The six logical roles and the role table -/

/-- **The six lists a Hood–Melville queue keeps**: the stored `front` and `rear`,
and the rotation quadruple `f`, `f'`, `r`, `r'` (with `appending` reusing `f'`
and `r'`, and `done` reusing `r'`). -/
inductive QRole where
  | front | rear | fwd | fwd' | rev | rev'
  deriving DecidableEq

/-- The list a role carries in a given queue. -/
def roleList (q : Queue (Fin 2)) : QRole → List (Fin 2)
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

/-- A role table: which physical queue stack (`0`–`5`) carries which role. -/
abbrev Roles : Type := QRole → ℕ

/-- The identity table, i.e. the fixed assignment of `CloseoutCoreEnc7`. -/
def idxOf : QRole → ℕ
  | .front => 0 | .rear => 1 | .fwd => 2 | .fwd' => 3 | .rev => 4 | .rev' => 5

/-- Its inverse. -/
def roleAt : ℕ → QRole
  | 0 => .front | 1 => .rear | 2 => .fwd | 3 => .fwd' | 4 => .rev | _ => .rev'

/-- **`CloseoutCoreEnc7.queueTapes6` is the identity role table.** -/
theorem queueTapes6_roleList (q : Queue (Fin 2)) (ro : QRole) :
    queueTapes6 q (idxOf ro) = stackTape ((roleList q ro).map some) := by
  obtain ⟨lf, fr, st, lr, re⟩ := q
  cases ro <;> cases st <;> rfl

/-- **The layout predicate**: the physical family `L` carries role `ro` at
address `ρ ro`.  Distinct roles may share an address when their lists agree;
that aliasing is what makes §3 free and what §5 kills. -/
def Lays (q : Queue (Fin 2)) (ρ : Roles) (L : ℕ → List (Fin 2)) : Prop :=
  ∀ ro, L (ρ ro) = roleList q ro

/-- The physical family of the identity table. -/
def physOf (q : Queue (Fin 2)) : ℕ → List (Fin 2) := fun i => roleList q (roleAt i)

theorem lays_physOf (q : Queue (Fin 2)) : Lays q idxOf (physOf q) := by
  intro ro; cases ro <;> rfl

/-- **A layout is *covering* when every address that carries no role is empty**:
a spare stack is a clean stack. -/
def Covers (q : Queue (Fin 2)) (ρ : Roles) (L : ℕ → List (Fin 2)) : Prop :=
  Lays q ρ L ∧ ∀ i, i < 6 → L i = [] ∨ ∃ ro, ρ ro = i

/-! ## 2. One debris stack, one bounded micro-step -/

/-- The three things a queue step can do to one stack. -/
inductive Delta where
  | keep | pop | push (a : Fin 2)

def dApply : Delta → List (Fin 2) → List (Fin 2)
  | .keep, l => l
  | .pop, l => l.tail
  | .push a, l => a :: l

def dActs : Delta → List (Fin 2) → List (Act Γc)
  | .keep, _ => []
  | .pop, _ => popActs
  | .push a, l => pushActs (l.map some) (some a)

def dDebris : Delta → List (Fin 2) → List Γc → List Γc
  | .keep, _, r => r
  | .pop, [], r => r
  | .pop, _ :: _, r => blankc :: r
  | .push _, _, r => r.tail

theorem dActs_length (u : Delta) (l : List (Fin 2)) : (dActs u l).length ≤ 2 := by
  cases u with
  | keep => simp [dActs]
  | pop => simp [dActs, popActs]
  | push a => simp [dActs, pushActs]

/-- **Every delta is a composite of at most two micro-actions on a debris
stack**, with no side condition: the pop of an empty stack is the identity. -/
theorem dTape_delta (u : Delta) (l : List (Fin 2)) (r : List Γc) :
    dTape ((dApply u l).map some) (dDebris u l r)
      = actList blankc (dTape (l.map some) r) (dActs u l) := by
  cases u with
  | keep => rfl
  | pop =>
      cases l with
      | nil => rfl
      | cons a t =>
          show dTape (t.map some) (blankc :: r)
            = actList blankc (dTape (some a :: t.map some) r) popActs
          exact (pop_dTape (some a) (t.map some) r).symm
  | push a =>
      show dTape (some a :: l.map some) (r.tail)
        = actList blankc (dTape (l.map some) r) (pushActs (l.map some) (some a))
      exact (push_dTape (l.map some) r (some a)).symm

/-! ### The eight-tape cursor -/

/-- **The repaired cursor with the queue spread over six debris stacks**:
`back`+`focus`, `near`, and the physical family `L` at addresses `2`–`7`.  The
rotation *state* lives in the role table, not on the tapes. -/
def viewTapesQ (v : InputView) (L : ℕ → List (Fin 2)) (d : ℕ → List Γc) : ℕ → STape Γc
  | 0 => dTape (v.focus :: v.back) (d 0)
  | 1 => dTape v.near (d 1)
  | (n + 2) => dTape ((L n).map some) (d (n + 2))

/-- …so the cursor costs eight tapes, as `CloseoutCoreEnc7.tView8` predicted. -/
def tViewQ : ℕ := 8

def qActs (u : ℕ → Delta) (L : ℕ → List (Fin 2)) : ℕ → List (Act Γc)
  | 0 => []
  | 1 => []
  | (n + 2) => dActs (u n) (L n)

def qDebris (u : ℕ → Delta) (L : ℕ → List (Fin 2)) (d : ℕ → List Γc) : ℕ → List Γc
  | 0 => d 0
  | 1 => d 1
  | (n + 2) => dDebris (u n) (L n) (d (n + 2))

theorem qActs_length (u : ℕ → Delta) (L : ℕ → List (Fin 2)) (i : ℕ) :
    (qActs u L i).length ≤ 2 := by
  match i with
  | 0 => simp [qActs]
  | 1 => simp [qActs]
  | (n + 2) => exact dActs_length (u n) (L n)

/-- **A queue-only step is a bounded composite at every address of the cursor.**
The two head tapes are untouched; each queue stack takes its own delta. -/
theorem viewTapesQ_delta (v : InputView) (L : ℕ → List (Fin 2)) (d : ℕ → List Γc)
    (u : ℕ → Delta) (i : ℕ) :
    viewTapesQ v (fun n => dApply (u n) (L n)) (qDebris u L d) i
      = actList blankc (viewTapesQ v L d i) (qActs u L i) := by
  match i with
  | 0 => rfl
  | 1 => rfl
  | (n + 2) =>
      show dTape ((dApply (u n) (L n)).map some) (dDebris (u n) (L n) (d (n + 2)))
        = actList blankc (dTape ((L n).map some) (d (n + 2))) (dActs (u n) (L n))
      exact dTape_delta (u n) (L n) (d (n + 2))

/-! ### Naming the delta family by addresses -/

/-- Override one address. -/
def ovr (a : ℕ) (u : Delta) (g : ℕ → Delta) : ℕ → Delta := fun i => if i = a then u else g i

theorem ovr_pos (a : ℕ) (u : Delta) (g : ℕ → Delta) : ovr a u g a = u := by simp [ovr]

theorem ovr_neg (a : ℕ) (u : Delta) (g : ℕ → Delta) (i : ℕ) (h : i ≠ a) :
    ovr a u g i = g i := by simp [ovr, h]

/-- The role tables of §4 are injective; the exception is `rotRoles`, whose
aliasing is the subject of §5. -/
def Inj (ρ : Roles) : Prop := ∀ a b : QRole, ρ a = ρ b → a = b

theorem inj_ne {ρ : Roles} (h : Inj ρ) {a b : QRole} (hab : a ≠ b) : ρ a ≠ ρ b :=
  fun he => hab (h a b he)

/-! ## 3. The rotation start writes nothing -/

/-- The queue `RTQueue.check` builds when it starts a rotation. -/
def rotStart (q : Queue (Fin 2)) : Queue (Fin 2) :=
  { lenf := q.lenf + q.lenr, front := q.front,
    state := .reversing 0 q.front [] q.rear [], lenr := 0, rear := [] }

theorem check_rot (q : Queue (Fin 2)) (h : ¬ q.lenr ≤ q.lenf) :
    RTQueue.check q = RTQueue.exec2 (rotStart q) := by
  unfold RTQueue.check
  rw [if_neg h]
  rfl

/-- **The role permutation the rotation start performs.**  The stored `front`
tape becomes *also* the reversal source `f`; the old `rear` tape becomes the
reversal source `r`; the new, empty `rear` is the (empty) old `f` tape.  No
physical stack changes. -/
def rotRoles (ρ : Roles) : Roles
  | .front => ρ .front
  | .fwd => ρ .front
  | .rev => ρ .rear
  | .rear => ρ .fwd
  | .fwd' => ρ .fwd'
  | .rev' => ρ .rev'

/-- **`rear := []` is a role rename, not an erasure.**  On an idle queue the
rotation start is laid out by the *same* physical family. -/
theorem rotStart_lays (q : Queue (Fin 2)) (ρ : Roles) (L : ℕ → List (Fin 2))
    (hidle : q.state = .idle) (h : Lays q ρ L) :
    Lays (rotStart q) (rotRoles ρ) L := by
  have e2 : roleList q .fwd = [] := by simp [roleList, hidle]
  have e3 : roleList q .fwd' = [] := by simp [roleList, hidle]
  have e5 : roleList q .rev' = [] := by simp [roleList, hidle]
  intro ro
  cases ro with
  | front => exact h .front
  | rear =>
      show L (ρ .fwd) = []
      rw [h .fwd, e2]
  | fwd => exact h .front
  | fwd' =>
      show L (ρ .fwd') = []
      rw [h .fwd', e3]
  | rev => exact h .rear
  | rev' =>
      show L (ρ .rev') = []
      rw [h .rev', e5]

/-- **The rotation start is the empty composite at every address of the
cursor.**  Compare `CloseoutCoreEnc19.not_bounded_rot_rear`: on four tapes the
same transition is not realisable at any radius. -/
theorem rotStart_actList (v : InputView) (L : ℕ → List (Fin 2)) (d : ℕ → List Γc)
    (ρ : Roles) (hidle : v.far.state = .idle) (h : Lays v.far ρ L) :
    Lays (rotStart v.far) (rotRoles ρ) L ∧
      ∀ i, viewTapesQ { v with far := rotStart v.far } L d i
        = actList blankc (viewTapesQ v L d i) [] :=
  ⟨rotStart_lays v.far ρ L hidle h, fun i => by
    match i with
    | 0 => rfl
    | 1 => rfl
    | (n + 2) => rfl⟩

/-! ## 4. The rotation steps are bounded -/

/-- The delta family of one `exec` step in the reversing phase. -/
def execRevDelta (ρ : Roles) (x y : Fin 2) : ℕ → Delta :=
  ovr (ρ .fwd) .pop (ovr (ρ .fwd') (.push x)
    (ovr (ρ .rev) .pop (ovr (ρ .rev') (.push y) (fun _ => .keep))))

/-- **One reversing step is a `Delta` family**: pop `f`, push onto `f'`, pop
`r`, push onto `r'`, everything else untouched — hence `≤ 2` micro-actions at
each address, with the role table unchanged. -/
theorem exec_reversing_lays (q : Queue (Fin 2)) (ρ : Roles) (L : ℕ → List (Fin 2))
    (hinj : Inj ρ) (h : Lays q ρ L) (ok : ℕ) (x y : Fin 2) (f f' r r' : List (Fin 2))
    (hst : q.state = .reversing ok (x :: f) f' (y :: r) r') :
    Lays { q with state := .reversing (ok + 1) f (x :: f') r (y :: r') } ρ
      (fun i => dApply (execRevDelta ρ x y i) (L i)) := by
  have hf : L (ρ .fwd) = x :: f := by rw [h .fwd]; simp [roleList, hst]
  have hf' : L (ρ .fwd') = f' := by rw [h .fwd']; simp [roleList, hst]
  have hr : L (ρ .rev) = y :: r := by rw [h .rev]; simp [roleList, hst]
  have hr' : L (ρ .rev') = r' := by rw [h .rev']; simp [roleList, hst]
  intro ro
  cases ro with
  | front =>
      have n1 : ρ .front ≠ ρ .fwd := inj_ne hinj (by decide)
      have n2 : ρ .front ≠ ρ .fwd' := inj_ne hinj (by decide)
      have n3 : ρ .front ≠ ρ .rev := inj_ne hinj (by decide)
      have n4 : ρ .front ≠ ρ .rev' := inj_ne hinj (by decide)
      show dApply (execRevDelta ρ x y (ρ .front)) (L (ρ .front)) = q.front
      unfold execRevDelta
      rw [ovr_neg _ _ _ _ n1, ovr_neg _ _ _ _ n2, ovr_neg _ _ _ _ n3, ovr_neg _ _ _ _ n4]
      show L (ρ .front) = q.front
      exact h .front
  | rear =>
      have n1 : ρ .rear ≠ ρ .fwd := inj_ne hinj (by decide)
      have n2 : ρ .rear ≠ ρ .fwd' := inj_ne hinj (by decide)
      have n3 : ρ .rear ≠ ρ .rev := inj_ne hinj (by decide)
      have n4 : ρ .rear ≠ ρ .rev' := inj_ne hinj (by decide)
      show dApply (execRevDelta ρ x y (ρ .rear)) (L (ρ .rear)) = q.rear
      unfold execRevDelta
      rw [ovr_neg _ _ _ _ n1, ovr_neg _ _ _ _ n2, ovr_neg _ _ _ _ n3, ovr_neg _ _ _ _ n4]
      show L (ρ .rear) = q.rear
      exact h .rear
  | fwd =>
      show dApply (execRevDelta ρ x y (ρ .fwd)) (L (ρ .fwd)) = f
      unfold execRevDelta
      rw [ovr_pos, hf]
      rfl
  | fwd' =>
      have n1 : ρ .fwd' ≠ ρ .fwd := inj_ne hinj (by decide)
      show dApply (execRevDelta ρ x y (ρ .fwd')) (L (ρ .fwd')) = x :: f'
      unfold execRevDelta
      rw [ovr_neg _ _ _ _ n1, ovr_pos, hf']
      rfl
  | rev =>
      have n1 : ρ .rev ≠ ρ .fwd := inj_ne hinj (by decide)
      have n2 : ρ .rev ≠ ρ .fwd' := inj_ne hinj (by decide)
      show dApply (execRevDelta ρ x y (ρ .rev)) (L (ρ .rev)) = r
      unfold execRevDelta
      rw [ovr_neg _ _ _ _ n1, ovr_neg _ _ _ _ n2, ovr_pos, hr]
      rfl
  | rev' =>
      have n1 : ρ .rev' ≠ ρ .fwd := inj_ne hinj (by decide)
      have n2 : ρ .rev' ≠ ρ .fwd' := inj_ne hinj (by decide)
      have n3 : ρ .rev' ≠ ρ .rev := inj_ne hinj (by decide)
      show dApply (execRevDelta ρ x y (ρ .rev')) (L (ρ .rev')) = y :: r'
      unfold execRevDelta
      rw [ovr_neg _ _ _ _ n1, ovr_neg _ _ _ _ n2, ovr_neg _ _ _ _ n3, ovr_pos, hr']
      rfl

/-- The delta family of one `exec` step in the appending phase. -/
def execAppDelta (ρ : Roles) (x : Fin 2) : ℕ → Delta :=
  ovr (ρ .fwd') .pop (ovr (ρ .rev') (.push x) (fun _ => .keep))

/-- **One appending step is a `Delta` family**: pop `f'`, push onto `r'`. -/
theorem exec_appending_lays (q : Queue (Fin 2)) (ρ : Roles) (L : ℕ → List (Fin 2))
    (hinj : Inj ρ) (h : Lays q ρ L) (ok : ℕ) (x : Fin 2) (f' r' : List (Fin 2))
    (hst : q.state = .appending (ok + 1) (x :: f') r') :
    Lays { q with state := .appending ok f' (x :: r') } ρ
      (fun i => dApply (execAppDelta ρ x i) (L i)) := by
  have hf' : L (ρ .fwd') = x :: f' := by rw [h .fwd']; simp [roleList, hst]
  have hr' : L (ρ .rev') = r' := by rw [h .rev']; simp [roleList, hst]
  intro ro
  cases ro with
  | front =>
      have n1 : ρ .front ≠ ρ .fwd' := inj_ne hinj (by decide)
      have n2 : ρ .front ≠ ρ .rev' := inj_ne hinj (by decide)
      show dApply (execAppDelta ρ x (ρ .front)) (L (ρ .front)) = q.front
      unfold execAppDelta
      rw [ovr_neg _ _ _ _ n1, ovr_neg _ _ _ _ n2]
      exact h .front
  | rear =>
      have n1 : ρ .rear ≠ ρ .fwd' := inj_ne hinj (by decide)
      have n2 : ρ .rear ≠ ρ .rev' := inj_ne hinj (by decide)
      show dApply (execAppDelta ρ x (ρ .rear)) (L (ρ .rear)) = q.rear
      unfold execAppDelta
      rw [ovr_neg _ _ _ _ n1, ovr_neg _ _ _ _ n2]
      exact h .rear
  | fwd =>
      have n1 : ρ .fwd ≠ ρ .fwd' := inj_ne hinj (by decide)
      have n2 : ρ .fwd ≠ ρ .rev' := inj_ne hinj (by decide)
      show dApply (execAppDelta ρ x (ρ .fwd)) (L (ρ .fwd)) = []
      unfold execAppDelta
      rw [ovr_neg _ _ _ _ n1, ovr_neg _ _ _ _ n2]
      show L (ρ .fwd) = []
      rw [h .fwd]
      simp [roleList, hst]
  | fwd' =>
      show dApply (execAppDelta ρ x (ρ .fwd')) (L (ρ .fwd')) = f'
      unfold execAppDelta
      rw [ovr_pos, hf']
      rfl
  | rev =>
      have n1 : ρ .rev ≠ ρ .fwd' := inj_ne hinj (by decide)
      have n2 : ρ .rev ≠ ρ .rev' := inj_ne hinj (by decide)
      show dApply (execAppDelta ρ x (ρ .rev)) (L (ρ .rev)) = []
      unfold execAppDelta
      rw [ovr_neg _ _ _ _ n1, ovr_neg _ _ _ _ n2]
      show L (ρ .rev) = []
      rw [h .rev]
      simp [roleList, hst]
  | rev' =>
      have n1 : ρ .rev' ≠ ρ .fwd' := inj_ne hinj (by decide)
      show dApply (execAppDelta ρ x (ρ .rev')) (L (ρ .rev')) = x :: r'
      unfold execAppDelta
      rw [ovr_neg _ _ _ _ n1, ovr_pos, hr']
      rfl

/-- **`invalidate` is a `Delta` family too**, and in the only case in which it
touches a list at all (`appending 0`) it is a single pop of `r'`.  The
hypothesis `hnil : f' = []` is **not** removable: `.done r'` gives the `fwd'`
role the empty list while the `appending` state gave it `f'`, so a nonempty
leftover `f'` is discarded, and discarding is the erasure that
`CloseoutCoreEnc19.not_bounded_clear_dTape` forbids at a bounded radius.  This
is a second, independent instance of the §5 obstruction. -/
theorem invalidate_lays (q : Queue (Fin 2)) (ρ : Roles) (L : ℕ → List (Fin 2))
    (hinj : Inj ρ) (h : Lays q ρ L) (x : Fin 2) (f' r' : List (Fin 2))
    (hst : q.state = .appending 0 f' (x :: r')) (hnil : f' = []) :
    Lays { q with state := .done r' } ρ
      (fun i => dApply (ovr (ρ .rev') .pop (fun _ => .keep) i) (L i)) := by
  have hr' : L (ρ .rev') = x :: r' := by rw [h .rev']; simp [roleList, hst]
  intro ro
  cases ro with
  | front =>
      have n1 : ρ .front ≠ ρ .rev' := inj_ne hinj (by decide)
      show dApply (ovr (ρ .rev') .pop (fun _ => .keep) (ρ .front)) (L (ρ .front)) = q.front
      rw [ovr_neg _ _ _ _ n1]
      exact h .front
  | rear =>
      have n1 : ρ .rear ≠ ρ .rev' := inj_ne hinj (by decide)
      show dApply (ovr (ρ .rev') .pop (fun _ => .keep) (ρ .rear)) (L (ρ .rear)) = q.rear
      rw [ovr_neg _ _ _ _ n1]
      exact h .rear
  | fwd =>
      have n1 : ρ .fwd ≠ ρ .rev' := inj_ne hinj (by decide)
      show dApply (ovr (ρ .rev') .pop (fun _ => .keep) (ρ .fwd)) (L (ρ .fwd)) = []
      rw [ovr_neg _ _ _ _ n1]
      show L (ρ .fwd) = []
      rw [h .fwd]; simp [roleList, hst]
  | fwd' =>
      have n1 : ρ .fwd' ≠ ρ .rev' := inj_ne hinj (by decide)
      show dApply (ovr (ρ .rev') .pop (fun _ => .keep) (ρ .fwd')) (L (ρ .fwd')) = []
      rw [ovr_neg _ _ _ _ n1]
      show L (ρ .fwd') = []
      rw [h .fwd']; simp [roleList, hst, hnil]
  | rev =>
      have n1 : ρ .rev ≠ ρ .rev' := inj_ne hinj (by decide)
      show dApply (ovr (ρ .rev') .pop (fun _ => .keep) (ρ .rev)) (L (ρ .rev)) = []
      rw [ovr_neg _ _ _ _ n1]
      show L (ρ .rev) = []
      rw [h .rev]; simp [roleList, hst]
  | rev' =>
      show dApply (ovr (ρ .rev') .pop (fun _ => .keep) (ρ .rev')) (L (ρ .rev')) = r'
      rw [ovr_pos, hr']
      rfl

/-- **The `front` pop of `RTQueue.tail` is a single micro-action** on the front
stack, with the rotation state untouched. -/
theorem tail_pop_lays (q : Queue (Fin 2)) (ρ : Roles) (L : ℕ → List (Fin 2))
    (hinj : Inj ρ) (h : Lays q ρ L) (c : Fin 2) (f : List (Fin 2))
    (hfr : q.front = c :: f) :
    Lays { q with lenf := q.lenf - 1, front := f } ρ
      (fun i => dApply (ovr (ρ .front) .pop (fun _ => .keep) i) (L i)) := by
  intro ro
  cases ro with
  | front =>
      show dApply (ovr (ρ .front) .pop (fun _ => .keep) (ρ .front)) (L (ρ .front)) = f
      rw [ovr_pos, h .front]
      show q.front.tail = f
      rw [hfr]
      rfl
  | rear =>
      have n1 : ρ .rear ≠ ρ .front := inj_ne hinj (by decide)
      show dApply (ovr (ρ .front) .pop (fun _ => .keep) (ρ .rear)) (L (ρ .rear)) = q.rear
      rw [ovr_neg _ _ _ _ n1]
      exact h .rear
  | fwd =>
      have n1 : ρ .fwd ≠ ρ .front := inj_ne hinj (by decide)
      show dApply (ovr (ρ .front) .pop (fun _ => .keep) (ρ .fwd)) (L (ρ .fwd)) = _
      rw [ovr_neg _ _ _ _ n1]
      exact h .fwd
  | fwd' =>
      have n1 : ρ .fwd' ≠ ρ .front := inj_ne hinj (by decide)
      show dApply (ovr (ρ .front) .pop (fun _ => .keep) (ρ .fwd')) (L (ρ .fwd')) = _
      rw [ovr_neg _ _ _ _ n1]
      exact h .fwd'
  | rev =>
      have n1 : ρ .rev ≠ ρ .front := inj_ne hinj (by decide)
      show dApply (ovr (ρ .front) .pop (fun _ => .keep) (ρ .rev)) (L (ρ .rev)) = _
      rw [ovr_neg _ _ _ _ n1]
      exact h .rev
  | rev' =>
      have n1 : ρ .rev' ≠ ρ .front := inj_ne hinj (by decide)
      show dApply (ovr (ρ .front) .pop (fun _ => .keep) (ρ .rev')) (L (ρ .rev')) = _
      rw [ovr_neg _ _ _ _ n1]
      exact h .rev'

/-! ## 5. The duplication `f := front` is the real obstruction -/

theorem pos_actOnG_le (T : STape Γc) (a : Act Γc) : pos (actOnG blankc T a) ≤ pos T + 1 := by
  cases a with
  | none => simp [actOnG]
  | some sm =>
      obtain ⟨s, mv⟩ := sm
      show pos (T.applyAction blankc (s, mv)) ≤ pos T + 1
      rw [PalPeg.Local.pos_applyAction]
      cases mv <;> simp <;> omega

/-- **A composite of `k` micro-actions moves a head right by at most `k`** —
the dual of `CloseoutCoreEnc19.pos_actList_ge`. -/
theorem pos_actList_le (T : STape Γc) (as : List (Act Γc)) :
    pos (actList blankc T as) ≤ pos T + as.length := by
  induction as generalizing T with
  | nil => simp
  | cons a as ih =>
      rw [actList_cons]
      have h1 := pos_actOnG_le T a
      have h2 := ih (actOnG blankc T a)
      simp only [List.length_cons]
      omega

/-- **Filling an empty debris stack is not a bounded composite.** -/
theorem not_bounded_grow (K : ℕ) (l : List (Option (Fin 2))) (r r' : List Γc)
    (hK : K < l.length) :
    ¬ ∃ as : List (Act Γc), as.length ≤ K ∧ actList blankc (dTape [] r) as = dTape l r' := by
  rintro ⟨as, hlen, has⟩
  have h := pos_actList_le (dTape [] r) as
  rw [has, pos_dTape, pos_dTape] at h
  simp only [List.length_nil] at h
  omega

/-- **`front` and `f` cannot share a stack once the reversal has moved.**  The
rotation start aliases them (`rotRoles ρ .fwd = ρ .front`), which is why §3 is
free; but `SInv` makes `f = front.drop ok`, so after one `exec` step the two
roles hold lists of different lengths and one single-headed tape cannot be laid
out for both. -/
theorem front_fwd_sep (q : Queue (Fin 2)) (ρ : Roles) (L : ℕ → List (Fin 2))
    (h : Lays q ρ L) (ok : ℕ) (f f' r r' : List (Fin 2))
    (hst : q.state = .reversing ok f f' r r')
    (hsi : RTQueue.SInv q.front q.state) (hok : 0 < ok) (hne : q.front ≠ []) :
    ρ .front ≠ ρ .fwd := by
  intro he
  rw [hst] at hsi
  obtain ⟨hle, hdrop, -⟩ := hsi
  have h1 : L (ρ .front) = q.front := h .front
  have h2 : L (ρ .fwd) = f := by rw [h .fwd]; simp [roleList, hst]
  have h3 : q.front = f := by rw [← h1, he, h2]
  have h4 : f.length = q.front.length - ok := by rw [hdrop, List.length_drop]
  rw [← h3] at h4
  have h5 : q.front.length ≠ 0 := fun hz => hne (List.eq_nil_of_length_eq_zero hz)
  omega

/-- **Under `Covers`, every spare address of an idle queue is empty.** -/
theorem covers_idle_spare (q : Queue (Fin 2)) (ρ : Roles) (L : ℕ → List (Fin 2))
    (hidle : q.state = .idle) (hc : Covers q ρ L) (i : ℕ) (hi : i < 6)
    (h1 : i ≠ ρ .front) (h2 : i ≠ ρ .rear) : L i = [] := by
  rcases hc.2 i hi with hz | ⟨ro, hro⟩
  · exact hz
  · cases ro with
    | front => exact absurd hro.symm h1
    | rear => exact absurd hro.symm h2
    | fwd => rw [← hro, hc.1 .fwd]; simp [roleList, hidle]
    | fwd' => rw [← hro, hc.1 .fwd']; simp [roleList, hidle]
    | rev => rw [← hro, hc.1 .rev]; simp [roleList, hidle]
    | rev' => rw [← hro, hc.1 .rev']; simp [roleList, hidle]

/-- **Installing the `fwd` role on a clean stack costs one head move per live
cell.**  With `front_fwd_sep` and `covers_idle_spare` this says: the rotation is
free at its first instant (§3), and the cost reappears one step later as the
duplication `f := front` — on any *empty* stack it is not a bounded rewrite.
The single escape not refuted here is `ρ' .fwd = ρ .rear`, i.e. the reversal
source taking over the rear stack. -/
theorem not_bounded_install_fwd (K : ℕ) (v v' : InputView) (L L' : ℕ → List (Fin 2))
    (d d' : ℕ → List Γc) (ρ' : Roles) (a : ℕ) (ha : a = ρ' .fwd)
    (hspare : L a = []) (h' : Lays v'.far ρ' L')
    (hK : K < (roleList v'.far .fwd).length) :
    ¬ ∃ as : List (Act Γc), as.length ≤ K ∧
      actList blankc (viewTapesQ v L d (a + 2)) as = viewTapesQ v' L' d' (a + 2) := by
  have h0 : viewTapesQ v L d (a + 2) = dTape [] (d (a + 2)) := by
    show dTape ((L a).map some) (d (a + 2)) = _
    rw [hspare]
    rfl
  have h1 : viewTapesQ v' L' d' (a + 2)
      = dTape ((roleList v'.far .fwd).map some) (d' (a + 2)) := by
    show dTape ((L' a).map some) (d' (a + 2)) = _
    rw [ha, h' .fwd]
  rw [h0, h1]
  exact not_bounded_grow K _ (d (a + 2)) (d' (a + 2)) (by simpa using hK)

end PalPeg.CloseoutCoreEnc20

#print axioms PalPeg.CloseoutCoreEnc20.queueTapes6_roleList
#print axioms PalPeg.CloseoutCoreEnc20.lays_physOf
#print axioms PalPeg.CloseoutCoreEnc20.dTape_delta
#print axioms PalPeg.CloseoutCoreEnc20.dActs_length
#print axioms PalPeg.CloseoutCoreEnc20.viewTapesQ_delta
#print axioms PalPeg.CloseoutCoreEnc20.qActs_length
#print axioms PalPeg.CloseoutCoreEnc20.check_rot
#print axioms PalPeg.CloseoutCoreEnc20.rotStart_lays
#print axioms PalPeg.CloseoutCoreEnc20.rotStart_actList
#print axioms PalPeg.CloseoutCoreEnc20.exec_reversing_lays
#print axioms PalPeg.CloseoutCoreEnc20.exec_appending_lays
#print axioms PalPeg.CloseoutCoreEnc20.invalidate_lays
#print axioms PalPeg.CloseoutCoreEnc20.tail_pop_lays
#print axioms PalPeg.CloseoutCoreEnc20.pos_actList_le
#print axioms PalPeg.CloseoutCoreEnc20.not_bounded_grow
#print axioms PalPeg.CloseoutCoreEnc20.front_fwd_sep
#print axioms PalPeg.CloseoutCoreEnc20.covers_idle_spare
#print axioms PalPeg.CloseoutCoreEnc20.not_bounded_install_fwd
