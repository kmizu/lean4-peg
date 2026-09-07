import PalPeg.RTQueue
import PalPeg.TapeLib

/-!
# Running the Hood–Melville queue on the artifact's tapes

`PalPeg.RTQueue` gives a purely functional worst-case `O(1)` FIFO queue;
`PalPeg.TapeLib` gives stack/counter views over the Kim–Park artifact's
`TapeConfiguration`.  This file connects them: the queue is realised on a
**fixed set of nine tapes**, one per list-valued field of `Queue`/`RotationState`
plus one unary counter for `ok`, and every queue operation is compiled into a
**bounded list of tape actions** (`≤ 20` for `snoc`, `≤ 27` for `tail`, `2` for
`head?`), independent of the size of the queue.

## The nine tapes (`Role`)

| role     | contents                                                          |
|----------|-------------------------------------------------------------------|
| `front`  | `q.front`                                                         |
| `fdup`   | a *duplicate* of `q.front`, maintained only while the rotation is idle |
| `rear`   | `q.rear`                                                          |
| `f`      | the rotation's `f`                                                |
| `fp`     | the rotation's `f'`                                               |
| `r`      | the rotation's `r`                                                |
| `rp`     | the rotation's `r'`                                               |
| `rpdup`  | a duplicate of `r'`                                               |
| `ok`     | a unary counter holding `ok`                                      |

Two design points make the bound possible.

* **Duplicate tapes.**  `check`'s rotation branch needs a *second* copy of
  `q.front` (the rotation scans `f = front.drop ok` while `head?`/`tail` still
  work on `front` itself; one head cannot be in two places).  Copying costs
  `O(n)`, so the copy is maintained incrementally instead: `fdup` mirrors
  `front` while idle, and `rpdup` mirrors `r'` while the rotation builds the new
  front.  Starting a rotation and installing a finished one are then mere
  **renamings of tape roles** (`rotStart`, `installPerm`), costing zero actions.

* **Garbage-tolerant marked stacks** (`SStack`).  A recycled tape still holds
  the previous occupant's cells below the head, so a stack is represented as
  `l ++ mark :: junk`: the list, a bottom marker, then arbitrary garbage.
  Re-initialising a recycled tape as an *empty* stack is then one action (write
  `mark`, move right), and the marker makes emptiness testable by a one-action
  probe (`sstack_probe`).

## What is and is not claimed

Costs are counted in **tape actions** (`Run.cost`), i.e. the total number of
`TapeConfiguration.applyAction` applications; a real multitape machine performs
the actions on distinct tapes of one program in parallel, so these counts are
upper bounds on the number of machine steps as well.

The one piece of finite control that is *not* realised on tapes here is the
comparison `q.lenr ≤ q.lenf` guarding `check` (unary counters for `lenf`/`lenr`
cannot be updated in `O(1)` at a rotation, where `lenf := lenf + lenr`).  The
tape programs below take that decision as given — `checkT` branches on the same
`if` as `check`, and `checkT_encodes` assumes only the implication that
`check_spec` also assumes (`lenf < lenr → state = idle`).
-/

namespace PalPeg
namespace RTQueueTapes

open PalPeg.Tape
open PegSeparation.RealTimeTM
open PalPeg.RTQueue

universe u

variable {k : ℕ}

/-! ## 1. Garbage-tolerant marked stacks -/

/-- A tape is *framed* when its head sits on a blank cell with only blanks to the
right, i.e. it is in stack shape (whatever lies to the left). -/
def Frame (blank : Fin k) (tp : TapeConfiguration k) : Prop :=
  tp.focus = blank ∧ Blanks blank tp.right

/-- A stack holding `l` (top first) above a bottom marker `mark`, above arbitrary
garbage left over from a previous occupant of the tape. -/
def SStack (blank mark : Fin k) (tp : TapeConfiguration k) (l : List (Fin k)) : Prop :=
  ∃ J, StackView blank tp (l ++ mark :: J)

/-- The intermediate state after a `pop`: the head sits on the popped cell. -/
def SStackTop (blank mark : Fin k) (tp : TapeConfiguration k) (a : Fin k)
    (l : List (Fin k)) : Prop :=
  ∃ J, StackTopView blank tp a (l ++ mark :: J)

theorem SStack.frame {blank mark : Fin k} {tp : TapeConfiguration k} {l : List (Fin k)}
    (h : SStack blank mark tp l) : Frame blank tp := by
  obtain ⟨J, hv⟩ := h
  exact ⟨hv.focus_blank, hv.right_blanks⟩

/-- `push a` = write `a`, move right: one action. -/
theorem sstack_push {blank mark : Fin k} {tp : TapeConfiguration k} {l : List (Fin k)}
    (h : SStack blank mark tp l) (a : Fin k) :
    SStack blank mark (step blank tp a .right) (a :: l) := by
  obtain ⟨J, hv⟩ := h
  exact ⟨J, push_spec hv a⟩

/-- `pop` step 1 = write blank, move left. -/
theorem sstack_pop {blank mark : Fin k} {tp : TapeConfiguration k} {a : Fin k}
    {l : List (Fin k)} (h : SStack blank mark tp (a :: l)) :
    SStackTop blank mark (step blank tp blank .left) a l := by
  obtain ⟨J, hv⟩ := h
  exact ⟨J, pop_spec hv⟩

/-- `pop` step 2 = erase: write blank, stay. -/
theorem sstacktop_erase {blank mark : Fin k} {tp : TapeConfiguration k} {a : Fin k}
    {l : List (Fin k)} (h : SStackTop blank mark tp a l) :
    SStack blank mark (step blank tp blank .stay) l := by
  obtain ⟨J, hv⟩ := h
  exact ⟨J, pop_erase hv⟩

/-- `peek` step 2 = restore: write the symbol back, move right. -/
theorem sstacktop_restore {blank mark : Fin k} {tp : TapeConfiguration k} {a : Fin k}
    {l : List (Fin k)} (h : SStackTop blank mark tp a l) :
    SStack blank mark (step blank tp a .right) (a :: l) := by
  obtain ⟨J, hv⟩ := h
  exact ⟨J, peek_restore hv⟩

/-- Two actions pop one cell. -/
theorem sstack_pop2 {blank mark : Fin k} {tp : TapeConfiguration k} {a : Fin k}
    {l : List (Fin k)} (h : SStack blank mark tp (a :: l)) :
    SStack blank mark (step blank (step blank tp blank .left) blank .stay) l :=
  sstacktop_erase (sstack_pop h)

/-- Two actions read the top and put it back. -/
theorem sstack_peek2 {blank mark : Fin k} {tp : TapeConfiguration k} {a : Fin k}
    {l : List (Fin k)} (h : SStack blank mark tp (a :: l)) :
    SStack blank mark (step blank (step blank tp blank .left) a .right) (a :: l) :=
  sstacktop_restore (sstack_pop h)

/-- **Recycling**: one action turns any framed tape into a fresh empty stack, the
old contents becoming garbage below the new marker. -/
theorem sstack_fresh {blank mark : Fin k} {tp : TapeConfiguration k}
    (h : Frame blank tp) : SStack blank mark (step blank tp mark .right) [] := by
  refine ⟨tp.left, ?_⟩
  rw [step_right]
  refine ⟨rfl, ?_, ?_⟩
  · exact h.2.headD
  · exact h.2.tail

/-- The one-action probe reads the top of the stack, or the marker if empty. -/
theorem sstack_probe {blank mark : Fin k} {tp : TapeConfiguration k} {l : List (Fin k)}
    (h : SStack blank mark tp l) :
    read (step blank tp blank .left) = l.head?.getD mark := by
  obtain ⟨J, hv⟩ := h
  cases l with
  | nil => simpa using read_after_pop (a := mark) (l := J) hv
  | cons a l => simpa using read_after_pop (a := a) (l := l ++ mark :: J) hv

/-! ## 2. Unary counters as marked stacks of blanks -/

/-- A unary counter: `n` blanks stacked above the marker. -/
def GCount (blank mark : Fin k) (tp : TapeConfiguration k) (n : ℕ) : Prop :=
  SStack blank mark tp (List.replicate n blank)

theorem gcount_inc {blank mark : Fin k} {tp : TapeConfiguration k} {n : ℕ}
    (h : GCount blank mark tp n) :
    GCount blank mark (step blank tp blank .right) (n + 1) := by
  rw [GCount, List.replicate_succ]
  exact sstack_push h blank

theorem gcount_dec {blank mark : Fin k} {tp : TapeConfiguration k} {n : ℕ}
    (h : GCount blank mark tp (n + 1)) :
    GCount blank mark (step blank (step blank tp blank .left) blank .stay) n := by
  rw [GCount, List.replicate_succ] at h
  exact sstack_pop2 h

/-- Decrementing a zero counter: the probe reads the marker, which is written
back.  Two actions, and the value stays `0`. -/
theorem gcount_dec_zero {blank mark : Fin k} {tp : TapeConfiguration k}
    (h : GCount blank mark tp 0) :
    GCount blank mark (step blank (step blank tp blank .left) mark .right) 0 := by
  obtain ⟨J, hv⟩ := h
  rw [List.replicate_zero, List.nil_append] at hv
  exact ⟨J, by simpa using peek_restore (pop_spec hv)⟩

/-- The probe decides whether the counter is zero (given `mark ≠ blank`). -/
theorem gcount_probe {blank mark : Fin k} {tp : TapeConfiguration k} {n : ℕ}
    (h : GCount blank mark tp n) :
    read (step blank tp blank .left) = if n = 0 then mark else blank := by
  have := sstack_probe h
  cases n with
  | zero => simpa using this
  | succ m => simpa [List.replicate_succ] using this

theorem gcount_isZero_iff {blank mark : Fin k} {tp : TapeConfiguration k} {n : ℕ}
    (hne : mark ≠ blank) (h : GCount blank mark tp n) :
    read (step blank tp blank .left) = mark ↔ n = 0 := by
  rw [gcount_probe h]
  cases n with
  | zero => simp
  | succ m => simp [Ne.symm hne]

/-! ## 3. The nine tapes, actions, and cost accounting -/

/-- The nine tape roles. -/
inductive Role
  | front | fdup | rear | f | fp | r | rp | rpdup | ok
  deriving DecidableEq, Repr

/-- The tapes of the machine, indexed by role. -/
abbrev QT (k : ℕ) := Role → TapeConfiguration k

/-- One tape action: which tape, what to write, where to move. -/
structure Act (k : ℕ) where
  role : Role
  write : Fin k
  move : Move

/-- Apply one action. -/
def act (blank : Fin k) (qt : QT k) (ρ : Role) (w : Fin k) (m : Move) : QT k :=
  fun ρ' => if ρ' = ρ then step blank (qt ρ) w m else qt ρ'

@[simp] theorem act_apply (blank : Fin k) (qt : QT k) (ρ ρ' : Role) (w : Fin k) (m : Move) :
    act blank qt ρ w m ρ' = if ρ' = ρ then step blank (qt ρ) w m else qt ρ' := rfl

/-- Run a program: a list of tape actions, applied in order. -/
def run (blank : Fin k) (qt : QT k) : List (Act k) → QT k
  | [] => qt
  | a :: p => run blank (act blank qt a.role a.write a.move) p

@[simp] theorem run_nil (blank : Fin k) (qt : QT k) : run blank qt [] = qt := rfl

@[simp] theorem run_cons (blank : Fin k) (qt : QT k) (ρ : Role) (w : Fin k) (m : Move)
    (p : List (Act k)) :
    run blank qt (⟨ρ, w, m⟩ :: p) = run blank (act blank qt ρ w m) p := rfl

/-- A machine state together with the number of tape actions performed so far. -/
structure Run (k : ℕ) where
  qt : QT k
  cost : ℕ

/-- Perform a program, charging one unit per action. -/
def Run.acts (blank : Fin k) (R : Run k) (p : List (Act k)) : Run k :=
  ⟨run blank R.qt p, R.cost + p.length⟩

/-- Rename the tape roles: a finite-control operation, costing nothing. -/
def Run.perm (R : Run k) (σ : QT k → QT k) : Run k := ⟨σ R.qt, R.cost⟩

@[simp] theorem Run.acts_cost (blank : Fin k) (R : Run k) (p : List (Act k)) :
    (R.acts blank p).cost = R.cost + p.length := rfl

@[simp] theorem Run.acts_qt (blank : Fin k) (R : Run k) (p : List (Act k)) :
    (R.acts blank p).qt = run blank R.qt p := rfl

@[simp] theorem Run.perm_cost (R : Run k) (σ : QT k → QT k) : (R.perm σ).cost = R.cost := rfl

@[simp] theorem Run.perm_qt (R : Run k) (σ : QT k → QT k) : (R.perm σ).qt = σ R.qt := rfl


/-! ## 4. What each tape holds -/

/-- The rotation's `f`. -/
def stF : RotationState (Fin k) → List (Fin k)
  | .reversing _ f _ _ _ => f
  | _ => []

/-- The rotation's `f'`. -/
def stFp : RotationState (Fin k) → List (Fin k)
  | .reversing _ _ f' _ _ => f'
  | .appending _ f' _ => f'
  | _ => []

/-- The rotation's `r`. -/
def stR : RotationState (Fin k) → List (Fin k)
  | .reversing _ _ _ r _ => r
  | _ => []

/-- The rotation's `r'`; at `done` it is the finished new front. -/
def stRp : RotationState (Fin k) → List (Fin k)
  | .reversing _ _ _ _ r' => r'
  | .appending _ _ r' => r'
  | .done nf => nf
  | _ => []

/-- The rotation's `ok`. -/
def stOk : RotationState (Fin k) → ℕ
  | .reversing ok _ _ _ _ => ok
  | .appending ok _ _ => ok
  | _ => 0

/-- The `fp` tape: a genuine stack, except at the transient `done`, where the
invalid suffix of `f'` is left behind as garbage and only the frame matters. -/
def FpEnc (blank mark : Fin k) (qt : QT k) : RotationState (Fin k) → Prop
  | .done _ => Frame blank (qt .fp)
  | s => SStack blank mark (qt .fp) (stFp s)

/-- The five rotation tapes and the `ok` counter encode the rotation state. -/
def SEnc (blank mark : Fin k) (qt : QT k) (s : RotationState (Fin k)) : Prop :=
  SStack blank mark (qt .f) (stF s) ∧ FpEnc blank mark qt s ∧
    SStack blank mark (qt .r) (stR s) ∧ SStack blank mark (qt .rp) (stRp s) ∧
    SStack blank mark (qt .rpdup) (stRp s) ∧ GCount blank mark (qt .ok) (stOk s)

/-- The duplicate front is maintained only while the rotation is idle; during a
rotation the physical tape that held it plays the role of `f`. -/
def qFdup (q : Queue (Fin k)) : List (Fin k) :=
  match q.state with
  | .idle => q.front
  | _ => []

/-- **The encoding**: the tapes `qt` represent the queue `q`. -/
structure Encodes (blank mark : Fin k) (qt : QT k) (q : Queue (Fin k)) : Prop where
  front : SStack blank mark (qt .front) q.front
  fdup : SStack blank mark (qt .fdup) (qFdup q)
  rear : SStack blank mark (qt .rear) q.rear
  state : SEnc blank mark qt q.state

/-! ## 5. The programs -/

/-- One rotation step, `≤ 8` actions.  Reversing: pop `f`, push onto `f'`, pop
`r`, push onto `r'` and its duplicate, increment `ok`.  Appending: pop `f'`,
push onto `r'` and its duplicate, decrement `ok`.  The remaining cases of `exec`
are pure finite-control moves. -/
def execProg (blank : Fin k) : RotationState (Fin k) → List (Act k)
  | .reversing _ (x :: _) _ (y :: _) _ =>
      [⟨.f, blank, .left⟩, ⟨.f, blank, .stay⟩, ⟨.fp, x, .right⟩,
        ⟨.r, blank, .left⟩, ⟨.r, blank, .stay⟩, ⟨.rp, y, .right⟩,
        ⟨.rpdup, y, .right⟩, ⟨.ok, blank, .right⟩]
  | .reversing _ [] _ [y] _ =>
      [⟨.r, blank, .left⟩, ⟨.r, blank, .stay⟩, ⟨.rp, y, .right⟩, ⟨.rpdup, y, .right⟩]
  | .appending (_ + 1) (x :: _) _ =>
      [⟨.fp, blank, .left⟩, ⟨.fp, blank, .stay⟩, ⟨.rp, x, .right⟩,
        ⟨.rpdup, x, .right⟩, ⟨.ok, blank, .left⟩, ⟨.ok, blank, .stay⟩]
  | _ => []

/-- `invalidate`, `≤ 4` actions. -/
def invProg (blank mark : Fin k) : RotationState (Fin k) → List (Act k)
  | .reversing 0 _ _ _ _ => [⟨.ok, blank, .left⟩, ⟨.ok, mark, .right⟩]
  | .reversing (_ + 1) _ _ _ _ => [⟨.ok, blank, .left⟩, ⟨.ok, blank, .stay⟩]
  | .appending 0 _ (_ :: _) =>
      [⟨.rp, blank, .left⟩, ⟨.rp, blank, .stay⟩, ⟨.rpdup, blank, .left⟩,
        ⟨.rpdup, blank, .stay⟩]
  | .appending (_ + 1) _ _ => [⟨.ok, blank, .left⟩, ⟨.ok, blank, .stay⟩]
  | _ => []

/-- Installing a finished rotation: re-initialise the three tapes about to be
recycled (`3` actions), then rename roles. -/
def installProg (_blank mark : Fin k) : List (Act k) :=
  [⟨.front, mark, .right⟩, ⟨.fdup, mark, .right⟩, ⟨.fp, mark, .right⟩]

/-- The role renaming that installs the new front: the tape that was building
`r'` becomes the front, its duplicate becomes the front duplicate, and the two
old front tapes take over the `r'` roles. -/
def installPerm (qt : QT k) : QT k := fun ρ =>
  match ρ with
  | .front => qt .rp
  | .fdup => qt .rpdup
  | .rp => qt .front
  | .rpdup => qt .fdup
  | ρ => qt ρ

/-- The role renaming that starts a rotation: the duplicate front becomes `f`,
the rear becomes `r`, and the (empty) tapes they leave behind take their places.
**Zero actions.** -/
def rotStart (qt : QT k) : QT k := fun ρ =>
  match ρ with
  | .f => qt .fdup
  | .fdup => qt .f
  | .r => qt .rear
  | .rear => qt .r
  | ρ => qt ρ

/-- The queue that `check` rotates into. -/
def rotQ (q : Queue (Fin k)) : Queue (Fin k) :=
  { lenf := q.lenf + q.lenr, front := q.front,
    state := .reversing 0 q.front [] q.rear [], lenr := 0, rear := [] }

/-! ## 6. One rotation step on the tapes -/

theorem execProg_length (blank : Fin k) (s : RotationState (Fin k)) :
    (execProg blank s).length ≤ 8 := by
  match s with
  | .idle => simp [execProg]
  | .done _ => simp [execProg]
  | .reversing _ [] _ [] _ => simp [execProg]
  | .reversing _ [] _ [_] _ => simp [execProg]
  | .reversing _ [] _ (_ :: _ :: _) _ => simp [execProg]
  | .reversing _ (_ :: _) _ [] _ => simp [execProg]
  | .reversing _ (_ :: _) _ (_ :: _) _ => simp [execProg]
  | .appending 0 _ _ => simp [execProg]
  | .appending (_ + 1) [] _ => simp [execProg]
  | .appending (_ + 1) (_ :: _) _ => simp [execProg]

theorem invProg_length (blank mark : Fin k) (s : RotationState (Fin k)) :
    (invProg blank mark s).length ≤ 4 := by
  match s with
  | .idle => simp [invProg]
  | .done _ => simp [invProg]
  | .reversing 0 _ _ _ _ => simp [invProg]
  | .reversing (_ + 1) _ _ _ _ => simp [invProg]
  | .appending 0 _ [] => simp [invProg]
  | .appending 0 _ (_ :: _) => simp [invProg]
  | .appending (_ + 1) _ _ => simp [invProg]

theorem installProg_length (blank mark : Fin k) : (installProg blank mark).length = 3 := rfl

/-- The rotation program never touches the front, duplicate-front or rear tape. -/
theorem exec_keeps (blank : Fin k) (qt : QT k) (s : RotationState (Fin k)) :
    run blank qt (execProg blank s) .front = qt .front ∧
      run blank qt (execProg blank s) .fdup = qt .fdup ∧
      run blank qt (execProg blank s) .rear = qt .rear := by
  match s with
  | .idle => exact ⟨rfl, rfl, rfl⟩
  | .done _ => exact ⟨rfl, rfl, rfl⟩
  | .reversing _ [] _ [] _ => exact ⟨rfl, rfl, rfl⟩
  | .reversing _ [] _ [_] _ => exact ⟨rfl, rfl, rfl⟩
  | .reversing _ [] _ (_ :: _ :: _) _ => exact ⟨rfl, rfl, rfl⟩
  | .reversing _ (_ :: _) _ [] _ => exact ⟨rfl, rfl, rfl⟩
  | .reversing _ (_ :: _) _ (_ :: _) _ => exact ⟨rfl, rfl, rfl⟩
  | .appending 0 _ _ => exact ⟨rfl, rfl, rfl⟩
  | .appending (_ + 1) [] _ => exact ⟨rfl, rfl, rfl⟩
  | .appending (_ + 1) (_ :: _) _ => exact ⟨rfl, rfl, rfl⟩

/-- **One rotation step is correct on the tapes.** -/
theorem exec_enc {blank mark : Fin k} {qt : QT k} {s : RotationState (Fin k)}
    (h : SEnc blank mark qt s) :
    SEnc blank mark (run blank qt (execProg blank s)) (exec s) := by
  match s with
  | .idle => exact h
  | .done _ => exact h
  | .reversing _ [] _ [] _ => exact h
  | .reversing _ [] _ [y] _ =>
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
      exact ⟨h1, h2, sstack_pop2 h3, sstack_push h4 y, sstack_push h5 y, h6⟩
  | .reversing _ [] _ (_ :: _ :: _) _ => exact h
  | .reversing _ (_ :: _) _ [] _ => exact h
  | .reversing _ (x :: _) _ (y :: _) _ =>
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
      exact ⟨sstack_pop2 h1, sstack_push h2 x, sstack_pop2 h3, sstack_push h4 y,
        sstack_push h5 y, gcount_inc h6⟩
  | .appending 0 _ _ =>
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
      exact ⟨h1, SStack.frame h2, h3, h4, h5, h6⟩
  | .appending (_ + 1) [] _ => exact h
  | .appending (_ + 1) (x :: _) _ =>
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
      exact ⟨h1, sstack_pop2 h2, h3, sstack_push h4 x, sstack_push h5 x, gcount_dec h6⟩

/-- The `invalidate` program never touches the front, duplicate-front or rear tape. -/
theorem inv_keeps (blank mark : Fin k) (qt : QT k) (s : RotationState (Fin k)) :
    run blank qt (invProg blank mark s) .front = qt .front ∧
      run blank qt (invProg blank mark s) .fdup = qt .fdup ∧
      run blank qt (invProg blank mark s) .rear = qt .rear := by
  match s with
  | .idle => exact ⟨rfl, rfl, rfl⟩
  | .done _ => exact ⟨rfl, rfl, rfl⟩
  | .reversing 0 _ _ _ _ => exact ⟨rfl, rfl, rfl⟩
  | .reversing (_ + 1) _ _ _ _ => exact ⟨rfl, rfl, rfl⟩
  | .appending 0 _ [] => exact ⟨rfl, rfl, rfl⟩
  | .appending 0 _ (_ :: _) => exact ⟨rfl, rfl, rfl⟩
  | .appending (_ + 1) _ _ => exact ⟨rfl, rfl, rfl⟩

/-- **`invalidate` is correct on the tapes.** -/
theorem inv_enc {blank mark : Fin k} {qt : QT k} {s : RotationState (Fin k)}
    (h : SEnc blank mark qt s) :
    SEnc blank mark (run blank qt (invProg blank mark s)) (invalidate s) := by
  match s with
  | .idle => exact h
  | .done _ => exact h
  | .reversing 0 _ _ _ _ =>
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
      exact ⟨h1, h2, h3, h4, h5, gcount_dec_zero h6⟩
  | .reversing (_ + 1) _ _ _ _ =>
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
      exact ⟨h1, h2, h3, h4, h5, gcount_dec h6⟩
  | .appending 0 _ [] => exact h
  | .appending 0 _ (_ :: _) =>
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
      exact ⟨h1, SStack.frame h2, h3, sstack_pop2 h4, sstack_pop2 h5, h6⟩
  | .appending (_ + 1) _ _ =>
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
      exact ⟨h1, h2, h3, h4, h5, gcount_dec h6⟩


/-! ## 7. Installing a rotation, starting one, and `exec2` / `check` -/

theorem qFdup_eq_front {q : Queue (Fin k)} (h : q.state = RotationState.idle) :
    qFdup q = q.front := by
  simp only [qFdup, h]

theorem qFdup_eq_nil {q : Queue (Fin k)} (h : q.state ≠ RotationState.idle) :
    qFdup q = [] := by
  cases hq : q.state with
  | idle => exact absurd hq h
  | reversing _ _ _ _ _ => simp only [qFdup, hq]
  | appending _ _ _ => simp only [qFdup, hq]
  | done _ => simp only [qFdup, hq]

theorem qFdup_mk_idle {q : Queue (Fin k)} {n : ℕ} {fr : List (Fin k)}
    {s : RotationState (Fin k)} (h : s = .idle) :
    qFdup { q with lenf := n, front := fr, state := s } = fr := by
  rw [h]; rfl

theorem qFdup_mk_ne {q : Queue (Fin k)} {n : ℕ} {fr : List (Fin k)}
    {s : RotationState (Fin k)} (h : s ≠ .idle) :
    qFdup { q with lenf := n, front := fr, state := s } = [] :=
  qFdup_eq_nil h

theorem exec_idle_of {s : RotationState (Fin k)} (h : exec s = .idle) : s = .idle := by
  match s with
  | .idle => rfl
  | .done _ => rw [exec_done] at h; simp at h
  | .reversing _ [] _ [] _ => rw [exec_rev_nil_nil] at h; simp at h
  | .reversing _ [] _ [_] _ => rw [exec_rev_nil] at h; simp at h
  | .reversing _ [] _ (_ :: _ :: _) _ => rw [exec_rev_nil_two] at h; simp at h
  | .reversing _ (_ :: _) _ [] _ => rw [exec_rev_cons_nil] at h; simp at h
  | .reversing _ (_ :: _) _ (_ :: _) _ => rw [exec_rev_cons] at h; simp at h
  | .appending 0 _ _ => rw [exec_app_zero] at h; simp at h
  | .appending (_ + 1) [] _ => rw [exec_app_succ_nil] at h; simp at h
  | .appending (_ + 1) (_ :: _) _ => rw [exec_app_succ] at h; simp at h

theorem invalidate_ne_idle {s : RotationState (Fin k)} (h : s ≠ .idle) :
    invalidate s ≠ .idle := by
  intro hc
  apply h
  cases s with
  | idle => rfl
  | done nf =>
      exact absurd (show RotationState.done nf = RotationState.idle from hc) (by simp)
  | reversing ok f f' r r' =>
      exact absurd
        (show RotationState.reversing (ok - 1) f f' r r' = RotationState.idle from hc) (by simp)
  | appending ok f' r' =>
      cases ok with
      | zero =>
          cases r' with
          | nil =>
              exact absurd (show RotationState.appending 0 f' ([] : List (Fin k))
                = RotationState.idle from hc) (by simp)
          | cons x r' =>
              exact absurd (show RotationState.done r' = RotationState.idle from hc) (by simp)
      | succ n =>
          exact absurd (show RotationState.appending n f' r' = RotationState.idle from hc)
            (by simp)

/-- **Installing a finished rotation.**  Three actions re-initialise the tapes
that are recycled; the rest is a renaming of roles. -/
theorem install_enc {blank mark : Fin k} {qt : QT k} {q : Queue (Fin k)}
    {nf : List (Fin k)}
    (hf : SStack blank mark (qt .front) q.front)
    (hd : SStack blank mark (qt .fdup) (qFdup q))
    (hr : SStack blank mark (qt .rear) q.rear)
    (hs : SEnc blank mark qt (.done nf)) :
    Encodes blank mark (installPerm (run blank qt (installProg blank mark)))
      { q with front := nf, state := .idle } := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hs
  exact ⟨h4, h5, hr,
    ⟨h1, sstack_fresh h2, h3, sstack_fresh hf.frame, sstack_fresh hd.frame, h6⟩⟩

/-- **Starting a rotation costs no tape actions**: the duplicate front takes over
the role of `f`, the rear takes over the role of `r`. -/
theorem rot_enc {blank mark : Fin k} {qt : QT k} {q : Queue (Fin k)}
    (h : Encodes blank mark qt q) (hi : q.state = RotationState.idle) :
    Encodes blank mark (rotStart qt) (rotQ q) := by
  have hfd : SStack blank mark (qt .fdup) q.front := by
    rw [← qFdup_eq_front hi]; exact h.fdup
  have hs : SEnc blank mark qt RotationState.idle := hi ▸ h.state
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hs
  exact ⟨h.front, h1, h3, ⟨hfd, h2, h.rear, h4, h5, h6⟩⟩

/-- Install the new front when the rotation has finished. -/
def installIf (blank mark : Fin k) (s : RotationState (Fin k)) (R : Run k) : Run k :=
  match s with
  | .done _ => Run.perm (Run.acts blank R (installProg blank mark)) installPerm
  | _ => R

/-- Two rotation steps, installing the new front if the rotation completes. -/
def exec2T (blank mark : Fin k) (q : Queue (Fin k)) (R : Run k) : Run k :=
  installIf blank mark (exec (exec q.state))
    (Run.acts blank (Run.acts blank R (execProg blank q.state)) (execProg blank (exec q.state)))

theorem installIf_not_done (blank mark : Fin k) (s : RotationState (Fin k)) (R : Run k)
    (h : NotDone s) : installIf blank mark s R = R := by
  cases s with
  | done _ => exact absurd h (by simp [NotDone])
  | idle => rfl
  | reversing _ _ _ _ _ => rfl
  | appending _ _ _ => rfl

/-- **`exec2` on the tapes.** -/
theorem exec2T_encodes {blank mark : Fin k} {q : Queue (Fin k)} {R : Run k}
    (h : Encodes blank mark R.qt q) :
    Encodes blank mark (exec2T blank mark q R).qt (exec2 q) := by
  have hS : SEnc blank mark (run blank (run blank R.qt (execProg blank q.state))
      (execProg blank (exec q.state))) (exec (exec q.state)) := exec_enc (exec_enc h.state)
  obtain ⟨kf1, kd1, kr1⟩ := exec_keeps blank R.qt q.state
  obtain ⟨kf2, kd2, kr2⟩ := exec_keeps blank (run blank R.qt (execProg blank q.state))
    (exec q.state)
  have hf : SStack blank mark
      (run blank (run blank R.qt (execProg blank q.state))
        (execProg blank (exec q.state)) .front) q.front := by
    rw [kf2, kf1]; exact h.front
  have hd : SStack blank mark
      (run blank (run blank R.qt (execProg blank q.state))
        (execProg blank (exec q.state)) .fdup) (qFdup q) := by
    rw [kd2, kd1]; exact h.fdup
  have hr : SStack blank mark
      (run blank (run blank R.qt (execProg blank q.state))
        (execProg blank (exec q.state)) .rear) q.rear := by
    rw [kr2, kr1]; exact h.rear
  by_cases hdc : ∃ nf, exec (exec q.state) = RotationState.done nf
  · obtain ⟨nf, hn⟩ := hdc
    have e1 : exec2 q = { q with front := nf, state := .idle } := exec2_eq_of_done hn
    have e2 : exec2T blank mark q R
        = Run.perm (Run.acts blank (Run.acts blank (Run.acts blank R (execProg blank q.state))
            (execProg blank (exec q.state))) (installProg blank mark)) installPerm := by
      unfold exec2T; rw [hn]; rfl
    rw [e1, e2]
    exact install_enc hf hd hr (hn ▸ hS)
  · have hnd : NotDone (exec (exec q.state)) := by
      cases hx : exec (exec q.state) with
      | done nf => exact absurd ⟨nf, hx⟩ hdc
      | idle => trivial
      | reversing _ _ _ _ _ => trivial
      | appending _ _ _ => trivial
    have e1 : exec2 q = { q with state := exec (exec q.state) } :=
      exec2_eq_of_not_done rfl hnd
    have e2 : exec2T blank mark q R
        = Run.acts blank (Run.acts blank R (execProg blank q.state))
            (execProg blank (exec q.state)) := by
      unfold exec2T; exact installIf_not_done blank mark _ _ hnd
    have e3 : qFdup { q with state := exec (exec q.state) } = qFdup q := by
      by_cases hi : q.state = RotationState.idle
      · have h3 : exec (exec q.state) = RotationState.idle := by rw [hi]; rfl
        rw [qFdup_eq_front (q := { q with state := exec (exec q.state) }) h3,
          qFdup_eq_front hi]
      · rw [qFdup_eq_nil (q := { q with state := exec (exec q.state) })
          (fun hc => hi (exec_idle_of (exec_idle_of hc))), qFdup_eq_nil hi]
    rw [e1, e2]
    refine ⟨hf, ?_, hr, hS⟩
    rw [e3]
    exact hd

/-- `check` on the tapes: the rotation branch is a pure renaming of roles. -/
def checkT (blank mark : Fin k) (q : Queue (Fin k)) (R : Run k) : Run k :=
  if q.lenr ≤ q.lenf then exec2T blank mark q R
  else exec2T blank mark (rotQ q) (Run.perm R rotStart)

/-- **`check` on the tapes.**  The hypothesis is exactly the one `check_spec`
uses: if the rear has outgrown the front, no rotation can be in progress. -/
theorem checkT_encodes {blank mark : Fin k} {q : Queue (Fin k)} {R : Run k}
    (h : Encodes blank mark R.qt q)
    (hrot : q.lenf < q.lenr → q.state = RotationState.idle) :
    Encodes blank mark (checkT blank mark q R).qt (check q) := by
  unfold checkT check
  split_ifs with hc
  · exact exec2T_encodes h
  · exact exec2T_encodes (R := Run.perm R rotStart) (rot_enc h (hrot (Nat.lt_of_not_le hc)))

/-! ## 8. `snoc` -/

/-- `snoc`: push onto the rear tape, then `check`. -/
def snocT (blank mark : Fin k) (q : Queue (Fin k)) (a : Fin k) (R : Run k) : Run k :=
  checkT blank mark { q with lenr := q.lenr + 1, rear := a :: q.rear }
    (Run.acts blank R [⟨.rear, a, .right⟩])

/-- **`snoc` on the tapes.** -/
theorem snocT_encodes {blank mark : Fin k} {q : Queue (Fin k)} {a : Fin k} {R : Run k}
    (h : Encodes blank mark R.qt q) (hq : Inv q) :
    Encodes blank mark (snocT blank mark q a R).qt (snoc q a) := by
  have hp := snoc_pinv hq a
  exact checkT_encodes (R := Run.acts blank R [⟨.rear, a, .right⟩])
    ⟨h.front, h.fdup, sstack_push h.rear a, h.state⟩ (fun hlt => hp.rot hlt)


/-! ## 9. `tail` -/

/-- Pop the front tape; while idle, pop its duplicate too. -/
def tailFrontProg (blank : Fin k) (s : RotationState (Fin k)) : List (Act k) :=
  match s with
  | .idle =>
      [⟨.front, blank, .left⟩, ⟨.front, blank, .stay⟩,
        ⟨.fdup, blank, .left⟩, ⟨.fdup, blank, .stay⟩]
  | _ => [⟨.front, blank, .left⟩, ⟨.front, blank, .stay⟩]

theorem tailFrontProg_length (blank : Fin k) (s : RotationState (Fin k)) :
    (tailFrontProg blank s).length ≤ 4 := by
  cases s <;> simp [tailFrontProg]

theorem tailFront_front (blank : Fin k) (qt : QT k) (s : RotationState (Fin k)) :
    run blank qt (tailFrontProg blank s) .front
      = step blank (step blank (qt .front) blank .left) blank .stay := by
  cases s <;> rfl

theorem tailFront_rear (blank : Fin k) (qt : QT k) (s : RotationState (Fin k)) :
    run blank qt (tailFrontProg blank s) .rear = qt .rear := by
  cases s <;> rfl

theorem tailFront_fdup_idle (blank : Fin k) (qt : QT k) :
    run blank qt (tailFrontProg blank RotationState.idle) .fdup
      = step blank (step blank (qt .fdup) blank .left) blank .stay := rfl

theorem tailFront_fdup_ne (blank : Fin k) (qt : QT k) {s : RotationState (Fin k)}
    (h : s ≠ .idle) : run blank qt (tailFrontProg blank s) .fdup = qt .fdup := by
  cases s with
  | idle => exact absurd rfl h
  | reversing _ _ _ _ _ => rfl
  | appending _ _ _ => rfl
  | done _ => rfl

theorem tailFront_senc {blank mark : Fin k} {qt : QT k} {s s' : RotationState (Fin k)}
    (h : SEnc blank mark qt s') :
    SEnc blank mark (run blank qt (tailFrontProg blank s)) s' := by
  cases s with
  | idle => exact h
  | reversing _ _ _ _ _ => exact h
  | appending _ _ _ => exact h
  | done _ => exact h

/-- `tail`: pop the front (and its duplicate while idle), run `invalidate`,
then `check`. -/
def tailT (blank mark : Fin k) (q : Queue (Fin k)) (R : Run k) : Run k :=
  match q.front with
  | [] => R
  | _ :: f =>
      checkT blank mark
        { q with lenf := q.lenf - 1, front := f, state := invalidate q.state }
        (Run.acts blank (Run.acts blank R (tailFrontProg blank q.state))
          (invProg blank mark q.state))

/-- **`tail` on the tapes.** -/
theorem tailT_encodes {blank mark : Fin k} {q : Queue (Fin k)} {R : Run k}
    (h : Encodes blank mark R.qt q) (hq : Inv q) :
    Encodes blank mark (tailT blank mark q R).qt (RTQueue.tail q) := by
  cases hfr : q.front with
  | nil =>
      have e1 : RTQueue.tail q = q := by unfold RTQueue.tail; rw [hfr]
      have e2 : tailT blank mark q R = R := by unfold tailT; rw [hfr]
      rw [e1, e2]; exact h
  | cons x f =>
      have e1 : RTQueue.tail q
          = check { q with lenf := q.lenf - 1, front := f, state := invalidate q.state } := by
        unfold RTQueue.tail; rw [hfr]
      have e2 : tailT blank mark q R
          = checkT blank mark
              { q with lenf := q.lenf - 1, front := f, state := invalidate q.state }
              (Run.acts blank (Run.acts blank R (tailFrontProg blank q.state))
                (invProg blank mark q.state)) := by
        unfold tailT; rw [hfr]
      rw [e1, e2]
      obtain ⟨ki1, ki2, ki3⟩ := inv_keeps blank mark
        (run blank R.qt (tailFrontProg blank q.state)) q.state
      refine checkT_encodes ?_ ?_
      · refine ⟨?_, ?_, ?_, ?_⟩
        · show SStack blank mark _ f
          rw [Run.acts_qt, Run.acts_qt, ki1, tailFront_front]
          exact sstack_pop2 (hfr ▸ h.front)
        · show SStack blank mark _ (qFdup _)
          rw [Run.acts_qt, Run.acts_qt, ki2]
          by_cases hi : q.state = RotationState.idle
          · have hidle : invalidate q.state = RotationState.idle := by rw [hi]; rfl
            rw [qFdup_mk_idle hidle, hi, tailFront_fdup_idle]
            have hfd : SStack blank mark (R.qt .fdup) (x :: f) := by
              rw [← hfr, ← qFdup_eq_front hi]; exact h.fdup
            exact sstack_pop2 hfd
          · rw [qFdup_mk_ne (invalidate_ne_idle hi), tailFront_fdup_ne blank R.qt hi,
              ← qFdup_eq_nil hi]
            exact h.fdup
        · show SStack blank mark _ q.rear
          rw [Run.acts_qt, Run.acts_qt, ki3, tailFront_rear]
          exact h.rear
        · exact inv_enc (tailFront_senc h.state)
      · intro hlt
        show invalidate q.state = RotationState.idle
        have hle := hq.le
        have hpl := hq.pot_len
        obtain ⟨P, hP⟩ := frontList_eq_append hq.sinv hq.nd
        have hlenf : 1 ≤ q.lenf := by
          rw [hq.lenf_eq, hP, hfr]; simp
        have hlt' : q.lenf - 1 < q.lenr := hlt
        have hrem : rem q.state = 0 := by omega
        rw [eq_idle_of_rem_zero hq.nd hrem]
        exact inv_idle

/-! ## 10. `head?` -/

/-- Probe the front tape (one action). -/
def headProbe (blank : Fin k) : List (Act k) := [⟨.front, blank, .left⟩]

/-- `head?`: probe the front tape, then write the symbol read back.  Two
actions, and the tapes are left exactly as they were. -/
def headT (blank : Fin k) (R : Run k) : Run k :=
  Run.acts blank (Run.acts blank R (headProbe blank))
    [⟨.front, read (run blank R.qt (headProbe blank) .front), .right⟩]

/-- **The probe reads the head of the queue** (the marker if the queue is
empty, so with `mark ≠ blank` and marker-free data the test is exact). -/
theorem headT_read {blank mark : Fin k} {qt : QT k} {q : Queue (Fin k)}
    (h : Encodes blank mark qt q) :
    read (run blank qt (headProbe blank) .front) = (head? q).getD mark :=
  sstack_probe h.front

/-- `head?` restores the tapes. -/
theorem headT_encodes {blank mark : Fin k} {q : Queue (Fin k)} {R : Run k}
    (h : Encodes blank mark R.qt q) : Encodes blank mark (headT blank R).qt q := by
  refine ⟨?_, h.fdup, h.rear, h.state⟩
  show SStack blank mark ((headT blank R).qt Role.front) q.front
  simp only [headT, Run.acts_qt]
  rw [headT_read h]
  cases hfr : q.front with
  | nil =>
      have h0 : (head? q).getD mark = mark := by rw [head?, hfr]; rfl
      rw [h0]
      have h0' : SStack blank mark (R.qt .front) [] := hfr ▸ h.front
      exact gcount_dec_zero (show GCount blank mark (R.qt .front) 0 from h0')
  | cons x l =>
      have h0 : (head? q).getD mark = x := by rw [head?, hfr]; rfl
      rw [h0]
      exact sstack_peek2 (hfr ▸ h.front)

theorem headT_cost (blank : Fin k) (R : Run k) : (headT blank R).cost = R.cost + 2 := by
  show R.cost + 1 + 1 = R.cost + 2
  omega

/-! ## 11. Action-count bounds -/

theorem installIf_cost (blank mark : Fin k) (s : RotationState (Fin k)) (R : Run k) :
    (installIf blank mark s R).cost ≤ R.cost + 3 := by
  cases s with
  | done _ =>
      show (Run.acts blank R (installProg blank mark)).cost ≤ R.cost + 3
      rw [Run.acts_cost, installProg_length]
  | idle => exact Nat.le_add_right _ _
  | reversing _ _ _ _ _ => exact Nat.le_add_right _ _
  | appending _ _ _ => exact Nat.le_add_right _ _

theorem exec2T_cost (blank mark : Fin k) (q : Queue (Fin k)) (R : Run k) :
    (exec2T blank mark q R).cost ≤ R.cost + 19 := by
  have h1 := execProg_length blank q.state
  have h2 := execProg_length blank (exec q.state)
  have h3 := installIf_cost blank mark (exec (exec q.state))
    (Run.acts blank (Run.acts blank R (execProg blank q.state))
      (execProg blank (exec q.state)))
  rw [Run.acts_cost, Run.acts_cost] at h3
  show (installIf blank mark (exec (exec q.state)) _).cost ≤ R.cost + 19
  omega

theorem checkT_cost (blank mark : Fin k) (q : Queue (Fin k)) (R : Run k) :
    (checkT blank mark q R).cost ≤ R.cost + 19 := by
  unfold checkT
  split_ifs with hc
  · exact exec2T_cost blank mark q R
  · exact exec2T_cost blank mark (rotQ q) (Run.perm R rotStart)

/-- **`snoc` costs at most 20 tape actions.** -/
theorem snocT_cost (blank mark : Fin k) (q : Queue (Fin k)) (a : Fin k) (R : Run k) :
    (snocT blank mark q a R).cost ≤ R.cost + 20 := by
  have h := checkT_cost blank mark { q with lenr := q.lenr + 1, rear := a :: q.rear }
    (Run.acts blank R [⟨.rear, a, .right⟩])
  rw [Run.acts_cost] at h
  show (checkT blank mark _ _).cost ≤ R.cost + 20
  simpa using Nat.le_trans h (by simp)

/-- **`tail` costs at most 27 tape actions.** -/
theorem tailT_cost (blank mark : Fin k) (q : Queue (Fin k)) (R : Run k) :
    (tailT blank mark q R).cost ≤ R.cost + 27 := by
  cases hfr : q.front with
  | nil =>
      have e2 : tailT blank mark q R = R := by unfold tailT; rw [hfr]
      rw [e2]; exact Nat.le_add_right _ _
  | cons x f =>
      have e2 : tailT blank mark q R
          = checkT blank mark
              { q with lenf := q.lenf - 1, front := f, state := invalidate q.state }
              (Run.acts blank (Run.acts blank R (tailFrontProg blank q.state))
                (invProg blank mark q.state)) := by
        unfold tailT; rw [hfr]
      have h1 := tailFrontProg_length blank q.state
      have h2 := invProg_length blank mark q.state
      have h3 := checkT_cost blank mark
        { q with lenf := q.lenf - 1, front := f, state := invalidate q.state }
        (Run.acts blank (Run.acts blank R (tailFrontProg blank q.state))
          (invProg blank mark q.state))
      rw [Run.acts_cost, Run.acts_cost] at h3
      rw [e2]
      omega

/-! ## 12. Sequences of operations -/

/-- A queue operation. -/
inductive Op (k : ℕ)
  | snoc (a : Fin k)
  | tail

/-- The abstract effect. -/
def Op.applyQ (q : Queue (Fin k)) : Op k → Queue (Fin k)
  | .snoc a => RTQueue.snoc q a
  | .tail => RTQueue.tail q

/-- The effect on the tapes. -/
def Op.applyT (blank mark : Fin k) (q : Queue (Fin k)) (R : Run k) : Op k → Run k
  | .snoc a => snocT blank mark q a R
  | .tail => tailT blank mark q R

/-- The effect on the FIFO contents. -/
def Op.applyL (l : List (Fin k)) : Op k → List (Fin k)
  | .snoc a => l ++ [a]
  | .tail => l.tail

def runOps (blank mark : Fin k) :
    List (Op k) → Queue (Fin k) → Run k → Queue (Fin k) × Run k
  | [], q, R => (q, R)
  | o :: os, q, R => runOps blank mark os (Op.applyQ q o) (Op.applyT blank mark q R o)

/-- **Main theorem.**  Any sequence of `snoc`/`tail` operations can be run on the
tapes: the encoding is maintained throughout, the total number of tape actions
is at most `27` per operation, and the tapes hold exactly the FIFO contents. -/
theorem queue_on_tapes (blank mark : Fin k) (ops : List (Op k)) (q : Queue (Fin k))
    (R : Run k) (hq : Inv q) (h : Encodes blank mark R.qt q) :
    Inv (runOps blank mark ops q R).1 ∧
      Encodes blank mark (runOps blank mark ops q R).2.qt (runOps blank mark ops q R).1 ∧
      (runOps blank mark ops q R).2.cost ≤ R.cost + 27 * ops.length ∧
      toList (runOps blank mark ops q R).1 = ops.foldl Op.applyL (toList q) := by
  induction ops generalizing q R with
  | nil =>
      refine ⟨hq, h, ?_, ?_⟩
      · show R.cost ≤ R.cost + 27 * 0
        omega
      · show toList q = List.foldl Op.applyL (toList q) []
        rfl
  | cons o os ih =>
      cases o with
      | snoc a =>
          obtain ⟨i1, i2, i3, i4⟩ :=
            ih (q := RTQueue.snoc q a) (R := snocT blank mark q a R) (inv_snoc hq a)
              (snocT_encodes h hq)
          have hc := snocT_cost blank mark q a R
          refine ⟨i1, i2, ?_, ?_⟩
          · show (runOps blank mark os (RTQueue.snoc q a) (snocT blank mark q a R)).2.cost
              ≤ R.cost + 27 * (os.length + 1)
            omega
          · show toList (runOps blank mark os (RTQueue.snoc q a) (snocT blank mark q a R)).1
              = List.foldl Op.applyL (toList q) (Op.snoc a :: os)
            rw [i4, toList_snoc hq]
            rfl
      | tail =>
          obtain ⟨i1, i2, i3, i4⟩ :=
            ih (q := RTQueue.tail q) (R := tailT blank mark q R) (inv_tail hq)
              (tailT_encodes h hq)
          have hc := tailT_cost blank mark q R
          refine ⟨i1, i2, ?_, ?_⟩
          · show (runOps blank mark os (RTQueue.tail q) (tailT blank mark q R)).2.cost
              ≤ R.cost + 27 * (os.length + 1)
            omega
          · show toList (runOps blank mark os (RTQueue.tail q) (tailT blank mark q R)).1
              = List.foldl Op.applyL (toList q) (Op.tail :: os)
            rw [i4, toList_tail hq]
            rfl

/-! ## 13. Initial tapes -/

/-- Every tape starts as an empty marked stack. -/
def initQT (blank mark : Fin k) : QT k := fun _ => ⟨[mark], blank, []⟩

theorem initQT_encodes (blank mark : Fin k) :
    Encodes blank mark (initQT blank mark) (empty : Queue (Fin k)) := by
  have hst : SStack blank mark (⟨[mark], blank, []⟩ : TapeConfiguration k) [] :=
    ⟨[], rfl, rfl, blanks_nil blank⟩
  exact ⟨hst, hst, hst, ⟨hst, hst, hst, hst, hst, hst⟩⟩

/-- **Corollary.**  Starting from blank tapes, any sequence of `n` queue
operations is realised in at most `27 * n` tape actions, and the tapes then
encode exactly the FIFO list produced by those operations. -/
theorem queue_on_tapes_empty (blank mark : Fin k) (ops : List (Op k)) :
    Encodes blank mark (runOps blank mark ops empty ⟨initQT blank mark, 0⟩).2.qt
        (runOps blank mark ops empty ⟨initQT blank mark, 0⟩).1 ∧
      (runOps blank mark ops empty ⟨initQT blank mark, 0⟩).2.cost ≤ 27 * ops.length ∧
      toList (runOps blank mark ops empty ⟨initQT blank mark, 0⟩).1
        = ops.foldl Op.applyL [] := by
  obtain ⟨_, h2, h3, h4⟩ :=
    queue_on_tapes blank mark ops empty ⟨initQT blank mark, 0⟩ inv_empty
      (initQT_encodes blank mark)
  refine ⟨h2, ?_, ?_⟩
  · simpa using h3
  · simpa [toList_empty] using h4

end RTQueueTapes
end PalPeg

