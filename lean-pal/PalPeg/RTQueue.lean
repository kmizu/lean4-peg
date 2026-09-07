import Mathlib.Data.List.Basic
import Mathlib.Tactic.Common

/-!
# Hood–Melville real-time queue

A purely functional FIFO queue with *worst-case* `O(1)` per operation, following
Okasaki, *Purely Functional Data Structures*, §8.2.1 (the "real-time queue"
obtained by global rebuilding / incremental rotation, due to Hood and Melville).

Lean has no laziness, so the banker's/lazy-rotation real-time queue is not
available; Hood–Melville does the rotation **eagerly but incrementally**, a
constant number of steps per operation, which is what is formalised here.

## Cost

`exec` is a single pattern match on `RotationState`, i.e. it reduces to one of
finitely many constructor cases and performs `O(1)` work; likewise `invalidate`.
Per queue operation:

* `snoc q a` = `check` on a queue with one extra rear cell: **exactly 2 `exec`**
  (via `exec2`), plus `O(1)` list/ℕ operations.
* `tail q`  = **1 `invalidate` + exactly 2 `exec`** (via `check`/`exec2`).
* `head? q` = **0 `exec`**: one `List.head?`.

So every operation performs at most two `exec` steps, each of bounded size:
worst-case `O(1)`.
-/

namespace PalPeg
namespace RTQueue

universe u

/-- The state of the incremental rotation. -/
inductive RotationState (α : Type u) where
  /-- No rotation in progress. -/
  | idle : RotationState α
  /-- Reversing phase: `ok` valid elements, `f`/`r` still to reverse into `f'`/`r'`. -/
  | reversing (ok : ℕ) (f f' r r' : List α) : RotationState α
  /-- Appending phase: the first `ok` cells of `f'` are still valid; `r'` is built up. -/
  | appending (ok : ℕ) (f' r' : List α) : RotationState α
  /-- The rotation finished with new front `f`. -/
  | done (f : List α) : RotationState α

/-- A Hood–Melville queue. -/
structure Queue (α : Type u) where
  lenf : ℕ
  front : List α
  state : RotationState α
  lenr : ℕ
  rear : List α

variable {α : Type u}

/-- One step of the incremental rotation. Single pattern match: `O(1)`. -/
def exec : RotationState α → RotationState α
  | .reversing ok (x :: f) f' (y :: r) r' => .reversing (ok + 1) f (x :: f') r (y :: r')
  | .reversing ok [] f' [y] r' => .appending ok f' (y :: r')
  | .appending 0 _ r' => .done r'
  | .appending (ok + 1) (x :: f') r' => .appending ok f' (x :: r')
  | s => s

/-- Record that one element of the old front has been dequeued. `O(1)`. -/
def invalidate : RotationState α → RotationState α
  | .reversing ok f f' r r' => .reversing (ok - 1) f f' r r'
  | .appending 0 _ (_ :: r') => .done r'
  | .appending (ok + 1) f' r' => .appending ok f' r'
  | s => s

/-- Two rotation steps, installing the new front when the rotation completes. -/
def exec2 (q : Queue α) : Queue α :=
  match exec (exec q.state) with
  | .done newf => { q with front := newf, state := .idle }
  | s => { q with state := s }

/-- Restore `lenr ≤ lenf`, starting a rotation if needed, then take two steps. -/
def check (q : Queue α) : Queue α :=
  if q.lenr ≤ q.lenf then exec2 q
  else exec2 { lenf := q.lenf + q.lenr, front := q.front,
               state := .reversing 0 q.front [] q.rear [], lenr := 0, rear := [] }

/-- The empty queue. -/
def empty : Queue α :=
  { lenf := 0, front := [], state := .idle, lenr := 0, rear := [] }

/-- Enqueue at the rear. -/
def snoc (q : Queue α) (a : α) : Queue α :=
  check { q with lenr := q.lenr + 1, rear := a :: q.rear }

/-- The first element, if any. -/
def head? (q : Queue α) : Option α := q.front.head?

/-- Dequeue at the front (identity on the empty queue). -/
def tail (q : Queue α) : Queue α :=
  match q.front with
  | [] => q
  | _ :: f => check { q with lenf := q.lenf - 1, front := f, state := invalidate q.state }

/-! ## Abstract contents -/

/-- The abstract *front* part of the queue: the elements the rotation state and
the stored front together stand for. -/
def frontList : RotationState α → List α → List α
  | .idle, f => f
  | .reversing _ _ _ r r', f => f ++ (r.reverse ++ r')
  | .appending ok f' r', _ => (f'.take ok).reverse ++ r'
  | .done nf, _ => nf

/-- The abstract FIFO contents, front to back. -/
def toList (q : Queue α) : List α := frontList q.state q.front ++ q.rear.reverse

/-! ## Sanity checks -/

private def mk (l : List ℕ) : Queue ℕ := l.foldl snoc empty

example : toList (empty : Queue ℕ) = [] := rfl
example : toList (mk [1, 2, 3]) = [1, 2, 3] := by rfl
example : toList (mk [1, 2, 3, 4, 5, 6, 7]) = [1, 2, 3, 4, 5, 6, 7] := by rfl
example : toList (tail (mk [1, 2, 3, 4, 5])) = [2, 3, 4, 5] := by rfl
example : toList (tail (tail (mk [1, 2, 3, 4, 5]))) = [3, 4, 5] := by rfl
example : head? (mk [1, 2, 3]) = some 1 := by rfl
example : head? (empty : Queue ℕ) = none := rfl
example : toList (snoc (tail (tail (mk [1, 2, 3, 4, 5, 6]))) 9) = [3, 4, 5, 6, 9] := by rfl
example : toList (tail (tail (tail (tail (tail (tail (mk [1,2,3,4,5,6]))))))) = [] := by rfl


/-! ## List helpers -/

private lemma take_succ_eq {L : List α} {n : ℕ} (h : n < L.length) :
    L.take (n + 1) = L.take n ++ [L[n]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h]
  rfl

private lemma drop_succ_eq {L : List α} {n : ℕ} (h : n < L.length) :
    L.drop n = L[n] :: L.drop (n + 1) := List.drop_eq_getElem_cons h

private lemma lt_of_drop_cons {L : List α} {n : ℕ} {x : α} {t : List α}
    (h : L.drop n = x :: t) : n < L.length := by
  by_contra hc
  rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt hc)] at h
  exact absurd h (by simp)

private lemma take_eq_self_of_drop_nil {L : List α} {n : ℕ} (h : L.drop n = []) :
    L.take n = L := by
  have := List.take_append_drop n L
  rw [h, List.append_nil] at this
  exact this

private lemma take_of_take_succ {L A : List α} {n : ℕ} {x : α}
    (h : L.take (n + 1) = A ++ [x]) (hA : A.length = n) : L.take n = A := by
  have h1 : L.take n = (L.take (n + 1)).take n := by
    rw [List.take_take]; congr 1; omega
  rw [h1, h, ← hA, List.take_left]

/-! ## Reduction lemmas for `exec` / `invalidate` -/

@[simp] lemma exec_idle : exec (.idle : RotationState α) = .idle := rfl
@[simp] lemma exec_done (nf : List α) : exec (.done nf) = .done nf := rfl
@[simp] lemma exec_rev_cons (ok : ℕ) (x : α) (f f' : List α) (y : α) (r r' : List α) :
    exec (.reversing ok (x :: f) f' (y :: r) r') = .reversing (ok + 1) f (x :: f') r (y :: r') :=
  rfl
@[simp] lemma exec_rev_nil (ok : ℕ) (f' : List α) (y : α) (r' : List α) :
    exec (.reversing ok [] f' [y] r') = .appending ok f' (y :: r') := rfl
lemma exec_rev_nil_nil (ok : ℕ) (f' r' : List α) :
    exec (.reversing ok [] f' [] r') = .reversing ok [] f' [] r' := rfl
lemma exec_rev_nil_two (ok : ℕ) (f' : List α) (y z : α) (r r' : List α) :
    exec (.reversing ok [] f' (y :: z :: r) r') = .reversing ok [] f' (y :: z :: r) r' := rfl
lemma exec_rev_cons_nil (ok : ℕ) (x : α) (f f' r' : List α) :
    exec (.reversing ok (x :: f) f' [] r') = .reversing ok (x :: f) f' [] r' := rfl
@[simp] lemma exec_app_zero (f' r' : List α) : exec (.appending 0 f' r') = .done r' := rfl
@[simp] lemma exec_app_succ (ok : ℕ) (x : α) (f' r' : List α) :
    exec (.appending (ok + 1) (x :: f') r') = .appending ok f' (x :: r') := rfl
lemma exec_app_succ_nil (ok : ℕ) (r' : List α) :
    exec (.appending (ok + 1) [] r') = .appending (ok + 1) [] r' := rfl

@[simp] lemma inv_idle : invalidate (.idle : RotationState α) = .idle := rfl
@[simp] lemma inv_rev (ok : ℕ) (f f' r r' : List α) :
    invalidate (.reversing ok f f' r r') = .reversing (ok - 1) f f' r r' := rfl
@[simp] lemma inv_app_zero (f' : List α) (x : α) (r' : List α) :
    invalidate (.appending 0 f' (x :: r')) = .done r' := rfl
@[simp] lemma inv_app_succ (ok : ℕ) (f' r' : List α) :
    invalidate (.appending (ok + 1) f' r') = .appending ok f' r' := rfl

/-! ## The invariant -/

/-- The rotation state is not a (transient) `done`. -/
def NotDone : RotationState α → Prop
  | .done _ => False
  | _ => True

/-- Remaining number of `exec` steps before the rotation produces `done`. -/
def rem : RotationState α → ℕ
  | .idle => 0
  | .done _ => 0
  | .reversing ok f _ _ _ => ok + 2 * f.length + 2
  | .appending ok _ _ => ok + 1

/-- Structural invariant of the rotation state relative to the stored front. -/
def SInv : List α → RotationState α → Prop
  | _, .idle => True
  | _, .done _ => True
  | front, .reversing ok f f' r _r' =>
      ok ≤ front.length ∧ f = front.drop ok ∧ r.length = f.length + 1 ∧
        f'.take ok = (front.take ok).reverse
  | front, .appending ok f' r' =>
      ok ≤ front.length ∧ f'.take ok = (front.take ok).reverse ∧
        ∃ P, r' = front.drop ok ++ P

/-- Okasaki's queue invariant. -/
structure Inv (q : Queue α) : Prop where
  lenf_eq : q.lenf = (frontList q.state q.front).length
  lenr_eq : q.lenr = q.rear.length
  le : q.lenr ≤ q.lenf
  sinv : SInv q.front q.state
  nd : NotDone q.state
  /-- Potential bound guaranteeing the rotation ends before `front` is exhausted. -/
  pot_front : rem q.state ≤ 2 * q.front.length
  /-- Potential bound guaranteeing the rotation ends before the next one starts. -/
  pot_len : rem q.state + 2 * q.lenr ≤ 2 * q.lenf

/-- Precondition of `check`: `Inv` with one unit of slack. -/
structure PInv (q : Queue α) : Prop where
  lenf_eq : q.lenf = (frontList q.state q.front).length
  lenr_eq : q.lenr = q.rear.length
  le : q.lenr ≤ q.lenf + 1
  sinv : SInv q.front q.state
  rot : q.lenf < q.lenr → q.state = .idle
  pot_front : rem q.state ≤ 2 * q.front.length + 2
  pot_len : rem q.state + 2 * q.lenr ≤ 2 * q.lenf + 2

lemma eq_idle_of_rem_zero {s : RotationState α} (hnd : NotDone s) (h : rem s = 0) :
    s = .idle := by
  cases s with
  | idle => rfl
  | done nf => exact absurd hnd (by simp [NotDone])
  | reversing ok f f' r r' => simp [rem] at h
  | appending ok f' r' => simp [rem] at h

/-- The abstract front always begins with the stored front. -/
lemma frontList_eq_append {front : List α} {s : RotationState α}
    (h : SInv front s) (hnd : NotDone s) : ∃ P, frontList s front = front ++ P := by
  cases s with
  | idle => exact ⟨[], by simp [frontList]⟩
  | done nf => exact absurd hnd (by simp [NotDone])
  | reversing ok f f' r r' => exact ⟨r.reverse ++ r', by simp [frontList]⟩
  | appending ok f' r' =>
    obtain ⟨_, h2, P, h3⟩ := h
    refine ⟨P, ?_⟩
    rw [frontList, h2, List.reverse_reverse, h3, ← List.append_assoc, List.take_append_drop]


/-! ## `exec` preserves the abstract contents and the structural invariant -/

lemma exec_frontList {front : List α} {s : RotationState α} (h : SInv front s) :
    frontList (exec s) front = frontList s front := by
  cases s with
  | idle => rfl
  | done nf => rfl
  | reversing ok f f' r r' =>
    cases f with
    | nil =>
      cases r with
      | nil => rw [exec_rev_nil_nil]
      | cons y r =>
        cases r with
        | nil =>
          obtain ⟨_, h2, _, h4⟩ := h
          have htake : front.take ok = front := take_eq_self_of_drop_nil h2.symm
          rw [exec_rev_nil]
          simp [frontList, h4, htake]
        | cons z r => rw [exec_rev_nil_two]
    | cons x f =>
      cases r with
      | nil => rw [exec_rev_cons_nil]
      | cons y r => simp [frontList]
  | appending ok f' r' =>
    cases ok with
    | zero => simp [frontList]
    | succ ok =>
      cases f' with
      | nil => rw [exec_app_succ_nil]
      | cons x f' => simp [frontList]

lemma exec_sinv {front : List α} {s : RotationState α} (h : SInv front s) :
    SInv front (exec s) := by
  cases s with
  | idle => exact h
  | done nf => exact h
  | reversing ok f f' r r' =>
    cases f with
    | nil =>
      cases r with
      | nil => rw [exec_rev_nil_nil]; exact h
      | cons y r =>
        cases r with
        | nil =>
          obtain ⟨h1, h2, _, h4⟩ := h
          rw [exec_rev_nil]
          exact ⟨h1, h4, ⟨y :: r', by rw [← h2]; simp⟩⟩
        | cons z r => rw [exec_rev_nil_two]; exact h
    | cons x f =>
      cases r with
      | nil => rw [exec_rev_cons_nil]; exact h
      | cons y r =>
        obtain ⟨h1, h2, h3, h4⟩ := h
        have hlt : ok < front.length := lt_of_drop_cons h2.symm
        have hdrop : front.drop ok = front[ok] :: front.drop (ok + 1) := drop_succ_eq hlt
        rw [hdrop] at h2
        have hx : x = front[ok] := (List.cons.injEq _ _ _ _ ▸ h2).1
        have hf : f = front.drop (ok + 1) := (List.cons.injEq _ _ _ _ ▸ h2).2
        rw [exec_rev_cons]
        refine ⟨by omega, hf, by simp at h3 ⊢; omega, ?_⟩
        rw [take_succ_eq hlt, List.reverse_append, List.take_succ_cons, h4, hx]
        simp
  | appending ok f' r' =>
    cases ok with
    | zero => rw [exec_app_zero]; trivial
    | succ ok =>
      cases f' with
      | nil =>
        exfalso
        obtain ⟨h1, h2, _⟩ := h
        have := congrArg List.length h2
        simp at this
        omega
      | cons x f' =>
        obtain ⟨h1, h2, P, h3⟩ := h
        have hlt : ok < front.length := by omega
        have hts := take_succ_eq hlt
        rw [hts] at h2
        simp only [List.take_succ_cons, List.reverse_append, List.reverse_cons,
          List.reverse_nil, List.nil_append, List.cons_append] at h2
        have hx : x = front[ok] := (List.cons.injEq _ _ _ _ ▸ h2).1
        have hf' : f'.take ok = (front.take ok).reverse := (List.cons.injEq _ _ _ _ ▸ h2).2
        rw [exec_app_succ]
        refine ⟨by omega, hf', ⟨P, ?_⟩⟩
        rw [drop_succ_eq hlt, ← hx, List.cons_append, ← h3]

lemma exec_rem {front : List α} {s : RotationState α} (h : SInv front s) :
    rem (exec s) ≤ rem s - 1 := by
  cases s with
  | idle => simp [rem]
  | done nf => simp [rem]
  | reversing ok f f' r r' =>
    cases f with
    | nil =>
      cases r with
      | nil => exfalso; obtain ⟨_, _, h3, _⟩ := h; simp at h3
      | cons y r =>
        cases r with
        | nil => rw [exec_rev_nil]; simp [rem]
        | cons z r => exfalso; obtain ⟨_, _, h3, _⟩ := h; simp at h3
    | cons x f =>
      cases r with
      | nil => exfalso; obtain ⟨_, _, h3, _⟩ := h; simp at h3
      | cons y r => rw [exec_rev_cons]; simp [rem]; omega
  | appending ok f' r' =>
    cases ok with
    | zero => simp [rem]
    | succ ok =>
      cases f' with
      | nil =>
        exfalso
        obtain ⟨h1, h2, _⟩ := h
        have := congrArg List.length h2
        simp at this
        omega
      | cons x f' => rw [exec_app_succ]; simp [rem]


/-! ## `invalidate` -/

lemma invalidate_spec {front f : List α} {x : α} {s : RotationState α}
    (hf : front = x :: f) (hs : SInv front s) (hnd : NotDone s)
    (hrem : rem s ≤ 2 * front.length) :
    SInv f (invalidate s) ∧ frontList (invalidate s) f = (frontList s front).tail ∧
      rem (invalidate s) ≤ rem s - 1 := by
  subst hf
  cases s with
  | done nf => exact absurd hnd (by simp [NotDone])
  | idle => exact ⟨trivial, by simp [frontList], by simp [rem]⟩
  | reversing ok fl f' r r' =>
    obtain ⟨h1, h2, h3, h4⟩ := hs
    have hlen : fl.length = f.length + 1 - ok := by
      rw [h2]; simp
    have hok : 2 ≤ ok := by
      simp only [rem, List.length_cons] at hrem
      simp only [List.length_cons] at h1
      omega
    obtain ⟨k, rfl⟩ : ∃ k, ok = k + 1 := ⟨ok - 1, by omega⟩
    have hkf : k ≤ f.length := by simp at h1; omega
    have h2' : fl = f.drop k := by rw [h2]; simp
    have h4' : f'.take k = (f.take k).reverse := by
      refine take_of_take_succ (A := (f.take k).reverse) (x := x) ?_ ?_
      · rw [h4]; simp
      · simp; omega
    refine ⟨⟨by omega, by simpa using h2', by simpa using h3, by simpa using h4'⟩, ?_, ?_⟩
    · simp [frontList]
    · simp only [inv_rev, rem]; omega
  | appending ok f' r' =>
    obtain ⟨h1, h2, P, h3⟩ := hs
    cases ok with
    | zero =>
      simp only [List.drop_zero] at h3
      subst h3
      refine ⟨trivial, ?_, by simp [rem]⟩
      simp [frontList]
    | succ k =>
      have hkf : k ≤ f.length := by simp at h1; omega
      have h4' : f'.take k = (f.take k).reverse := by
        refine take_of_take_succ (A := (f.take k).reverse) (x := x) ?_ ?_
        · rw [h2]; simp
        · simp; omega
      refine ⟨⟨by omega, h4', ⟨P, by simpa using h3⟩⟩, ?_, by simp [rem]⟩
      rw [inv_app_succ]
      simp only [frontList, h4', h2, List.reverse_reverse, List.take_succ_cons]
      simp


/-! ## `exec2` and `check` -/

lemma exec2_eq_of_not_done {q : Queue α} {s : RotationState α}
    (hs : exec (exec q.state) = s) (h : NotDone s) :
    exec2 q = { q with state := s } := by
  unfold exec2; rw [hs]
  cases s with
  | done nf => exact absurd h (by simp [NotDone])
  | idle => rfl
  | reversing ok f f' r r' => rfl
  | appending ok f' r' => rfl

lemma exec2_eq_of_done {q : Queue α} {nf : List α}
    (hs : exec (exec q.state) = .done nf) :
    exec2 q = { q with front := nf, state := .idle } := by
  unfold exec2; rw [hs]

lemma exec2_spec {q : Queue α}
    (h1 : q.lenf = (frontList q.state q.front).length)
    (h2 : q.lenr = q.rear.length)
    (h3 : q.lenr ≤ q.lenf)
    (h4 : SInv q.front q.state)
    (h5 : rem q.state ≤ 2 * q.front.length + 2)
    (h6 : rem q.state + 2 * q.lenr ≤ 2 * q.lenf + 2) :
    Inv (exec2 q) ∧ toList (exec2 q) = toList q := by
  have hS1 : SInv q.front (exec q.state) := exec_sinv h4
  have hS2 : SInv q.front (exec (exec q.state)) := exec_sinv hS1
  have hF : frontList (exec (exec q.state)) q.front = frontList q.state q.front := by
    rw [exec_frontList hS1, exec_frontList h4]
  have hR1 := exec_rem h4
  have hR2 := exec_rem hS1
  by_cases hd : ∃ nf, exec (exec q.state) = .done nf
  · obtain ⟨nf, hs⟩ := hd
    rw [hs] at hF
    simp only [frontList] at hF
    rw [exec2_eq_of_done hs]
    refine ⟨⟨?_, h2, h3, trivial, trivial, ?_, ?_⟩, ?_⟩
    · simpa [frontList, hF] using h1
    · simp [rem]
    · simp only [rem]; omega
    · simp [toList, frontList, hF]
  · have hnd : NotDone (exec (exec q.state)) := by
      cases hs : exec (exec q.state) with
      | done nf => exact absurd ⟨nf, hs⟩ hd
      | idle => trivial
      | reversing ok f f' r r' => trivial
      | appending ok f' r' => trivial
    rw [exec2_eq_of_not_done rfl hnd]
    refine ⟨⟨?_, h2, h3, hS2, hnd, ?_, ?_⟩, ?_⟩
    · show q.lenf = (frontList (exec (exec q.state)) q.front).length
      rw [hF]; exact h1
    · show rem (exec (exec q.state)) ≤ 2 * q.front.length
      omega
    · show rem (exec (exec q.state)) + 2 * q.lenr ≤ 2 * q.lenf
      omega
    · show frontList (exec (exec q.state)) q.front ++ q.rear.reverse = toList q
      rw [hF]; rfl

lemma check_spec {q : Queue α} (h : PInv q) : Inv (check q) ∧ toList (check q) = toList q := by
  unfold check
  split_ifs with hc
  · exact exec2_spec h.lenf_eq h.lenr_eq hc h.sinv h.pot_front h.pot_len
  · have hlt : q.lenf < q.lenr := Nat.lt_of_not_le hc
    have hidle : q.state = RotationState.idle := h.rot hlt
    have hlenf : q.lenf = q.front.length := by
      rw [h.lenf_eq, hidle]; rfl
    have hlenr : q.lenr = q.rear.length := h.lenr_eq
    have hle := h.le
    have hrear : q.rear.length = q.front.length + 1 := by omega
    have key := exec2_spec (q := (⟨q.lenf + q.lenr, q.front,
        RotationState.reversing 0 q.front [] q.rear [], 0, []⟩ : Queue α))
      (by show q.lenf + q.lenr = (q.front ++ (q.rear.reverse ++ [])).length
          simp; omega)
      rfl (Nat.zero_le _)
      (show SInv q.front (RotationState.reversing 0 q.front [] q.rear []) from
        ⟨Nat.zero_le _, rfl, by simpa using hrear, rfl⟩)
      (by show 0 + 2 * q.front.length + 2 ≤ 2 * q.front.length + 2; omega)
      (by show 0 + 2 * q.front.length + 2 + 2 * 0 ≤ 2 * (q.lenf + q.lenr) + 2; omega)
    refine ⟨key.1, ?_⟩
    rw [key.2]
    show q.front ++ (q.rear.reverse ++ []) ++ List.reverse [] = toList q
    rw [toList, hidle]
    simp [frontList]


/-! ## Main theorems -/

theorem toList_empty : toList (empty : Queue α) = [] := rfl

theorem inv_empty : Inv (empty : Queue α) :=
  ⟨rfl, rfl, Nat.le_refl _, trivial, trivial, by simp [rem, empty], by simp [rem, empty]⟩

lemma snoc_pinv {q : Queue α} (hq : Inv q) (a : α) :
    PInv { q with lenr := q.lenr + 1, rear := a :: q.rear } := by
  have hle := hq.le
  have hp := hq.pot_len
  have hpf := hq.pot_front
  refine ⟨hq.lenf_eq, by simp [hq.lenr_eq], by simpa using Nat.succ_le_succ hle, hq.sinv,
    ?_, ?_, ?_⟩
  · intro hlt
    replace hlt : q.lenf < q.lenr + 1 := hlt
    show q.state = RotationState.idle
    exact eq_idle_of_rem_zero hq.nd (by omega)
  · show rem q.state ≤ 2 * q.front.length + 2
    omega
  · show rem q.state + 2 * (q.lenr + 1) ≤ 2 * q.lenf + 2
    omega

theorem toList_snoc {q : Queue α} (hq : Inv q) (a : α) :
    toList (snoc q a) = toList q ++ [a] := by
  rw [snoc, (check_spec (snoc_pinv hq a)).2]
  show frontList q.state q.front ++ (a :: q.rear).reverse = toList q ++ [a]
  simp [toList]

theorem inv_snoc {q : Queue α} (hq : Inv q) (a : α) : Inv (snoc q a) :=
  (check_spec (snoc_pinv hq a)).1

/-- Both facts about `tail` at once. -/
lemma tail_spec {q : Queue α} (hq : Inv q) :
    Inv (tail q) ∧ toList (tail q) = (toList q).tail := by
  obtain ⟨P, hP⟩ := frontList_eq_append hq.sinv hq.nd
  cases hfront : q.front with
  | nil =>
    have hrem0 : rem q.state = 0 := by
      have := hq.pot_front; rw [hfront] at this; simpa using this
    have hidle : q.state = RotationState.idle := eq_idle_of_rem_zero hq.nd hrem0
    have h0 : q.lenf = 0 := by rw [hq.lenf_eq, hidle, hfront]; rfl
    have h1 : q.rear = [] := by
      have h2 := hq.lenr_eq; have h3 := hq.le
      exact List.eq_nil_of_length_eq_zero (by omega)
    have hempty : toList q = [] := by rw [toList, hidle, hfront, h1]; rfl
    have ht : tail q = q := by unfold tail; rw [hfront]
    rw [ht, hempty]
    exact ⟨hq, rfl⟩
  | cons x f =>
    obtain ⟨hsi, hfl, hrm⟩ := invalidate_spec hfront hq.sinv hq.nd hq.pot_front
    have hPf : frontList q.state q.front = x :: (f ++ P) := by rw [hP, hfront]; rfl
    have hlenf1 : 1 ≤ q.lenf := by rw [hq.lenf_eq, hPf]; simp
    have hpl := hq.pot_len
    have hpf := hq.pot_front
    have hle := hq.le
    have hflen : q.front.length = f.length + 1 := by rw [hfront]; simp
    have hq' : PInv { q with lenf := q.lenf - 1, front := f, state := invalidate q.state } := by
      refine ⟨?_, hq.lenr_eq, ?_, hsi, ?_, ?_, ?_⟩
      · show q.lenf - 1 = (frontList (invalidate q.state) f).length
        rw [hfl, hq.lenf_eq]; simp
      · show q.lenr ≤ q.lenf - 1 + 1
        omega
      · intro hlt
        replace hlt : q.lenf - 1 < q.lenr := hlt
        show invalidate q.state = RotationState.idle
        have hst : q.state = RotationState.idle :=
          eq_idle_of_rem_zero hq.nd (by omega)
        rw [hst]; rfl
      · show rem (invalidate q.state) ≤ 2 * f.length + 2
        omega
      · show rem (invalidate q.state) + 2 * q.lenr ≤ 2 * (q.lenf - 1) + 2
        omega
    have hkey := check_spec hq'
    have ht : tail q
        = check { q with lenf := q.lenf - 1, front := f, state := invalidate q.state } := by
      unfold tail; rw [hfront]
    rw [ht]
    refine ⟨hkey.1, ?_⟩
    rw [hkey.2]
    show frontList (invalidate q.state) f ++ q.rear.reverse = (toList q).tail
    rw [hfl, toList, hPf]
    simp

theorem inv_tail {q : Queue α} (hq : Inv q) : Inv (tail q) := (tail_spec hq).1

theorem toList_tail {q : Queue α} (hq : Inv q) : toList (tail q) = (toList q).tail :=
  (tail_spec hq).2

theorem head?_eq {q : Queue α} (hq : Inv q) : head? q = (toList q).head? := by
  obtain ⟨P, hP⟩ := frontList_eq_append hq.sinv hq.nd
  cases hfront : q.front with
  | nil =>
    have hrem0 : rem q.state = 0 := by
      have := hq.pot_front; rw [hfront] at this; simpa using this
    have hidle : q.state = RotationState.idle := eq_idle_of_rem_zero hq.nd hrem0
    have h0 : q.lenf = 0 := by rw [hq.lenf_eq, hidle, hfront]; rfl
    have h1 : q.rear = [] := by
      have h2 := hq.lenr_eq; have h3 := hq.le
      exact List.eq_nil_of_length_eq_zero (by omega)
    rw [head?, hfront, toList, hidle, hfront, h1]; rfl
  | cons x f =>
    rw [head?, toList, hP, hfront]
    simp

/-! ## Adequacy: building a queue from a list -/

theorem inv_foldl_snoc (l : List α) (q : Queue α) (hq : Inv q) : Inv (l.foldl snoc q) := by
  induction l generalizing q with
  | nil => exact hq
  | cons a l ih => exact ih _ (inv_snoc hq a)

theorem toList_foldl_snoc (l : List α) (q : Queue α) (hq : Inv q) :
    toList (l.foldl snoc q) = toList q ++ l := by
  induction l generalizing q with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons, ih _ (inv_snoc hq a), toList_snoc hq]
    simp

/-- Enqueueing a whole list yields exactly that list. -/
theorem toList_ofList (l : List α) : toList (l.foldl snoc (empty : Queue α)) = l := by
  rw [toList_foldl_snoc l _ inv_empty, toList_empty, List.nil_append]

end RTQueue
end PalPeg
