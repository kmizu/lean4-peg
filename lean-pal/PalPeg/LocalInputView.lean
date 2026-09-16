import PalPeg.GalilScaffoldInputHead
import PalPeg.RTQueue

/-!
# Local refinement of the non-local head copies (`InputView`)

Two operations of the Galil scaffold are *non-local* as written:

* `FppControl.beginFallback` sets `walker := p`, i.e. copies a whole
  `GalilScaffoldPlace.Place` in one step;
* `initVM` / `replayStartVM` set `left := right`, `center := right`
  (resp. `right := center`, `left := center`), i.e. copy a whole
  `GalilScaffoldInputHead.PlaceHead` in one step.

This module removes the content copy.  Every cursor owns its **own maintained
copy of the input**, fed one symbol per arrival.  Copying a head then degenerates
to *repositioning* a head on an already-identical tape, which costs one local
tick per cell of distance (`reposition_reaches`), and no content is ever moved.

## Reuse

The suffix of the copy that the cursor has not visited yet is stored in the
**Hood-Melville real-time queue** of `PalPeg.RTQueue` (`Queue`, `snoc`, `tail`,
`head?`, `toList`, `Inv`), which already comes with its FIFO specification
(`toList_snoc`, `toList_tail`, `head?_eq`, `inv_snoc`, `inv_tail`) and, on tapes,
with the real-time bound of `PalPeg.RTQueueTapes.queue_on_tapes_empty`
(any `n` queue operations cost `<= 31 * n` tape actions).  So `arrive` is a single
`snoc` and `stepRight` is a single `head?`/`tail`: each is `O(1)` micro-steps.

A plain stack `near` holds the cells that a left move has pushed back, so that a
left move never has to cons onto the queue.

The abstraction `absHead` lands in `GalilScaffoldInputHead.PlaceHead`, whose
`left`/`read` are reused verbatim; the missing right move (`moveRightH`,
`rightPH`) is defined here and shown inverse to the existing `moveLeft`/`left`.
-/

set_option autoImplicit false

namespace PalPeg.LocalInputView

open PalPeg.GalilScaffoldInputHead

/-! ## 1. The missing right move on the abstract head -/

/-- Right move of the zipper `Head`, inverse of `moveLeft`. -/
def moveRightH (h : Head) : Head := match h.right with
  | [] => h
  | a :: tail => ⟨a, h.focus :: h.left, tail, h.incoming⟩

/-- Right move of `PlaceHead`, inverse of `GalilScaffoldInputHead.left`:
the gap toggles, and only a gap-to-letter step moves the zipper. -/
def rightPH (p : PlaceHead) : PlaceHead :=
  ⟨if p.gap then moveRightH p.head else p.head, !p.gap⟩

theorem moveLeft_moveRightH (h : Head) (hr : h.right ≠ []) :
    moveLeft (moveRightH h) = h := by
  rcases h with ⟨f, l, r, q⟩
  cases r with
  | nil => exact absurd rfl hr
  | cons a t => rfl

theorem left_rightPH (p : PlaceHead) (hr : p.gap = true → p.head.right ≠ []) :
    left (rightPH p) = p := by
  rcases p with ⟨h, g⟩
  cases g
  · rfl
  · show (⟨moveLeft (moveRightH h), true⟩ : PlaceHead) = ⟨h, true⟩
    rw [moveLeft_moveRightH h (hr rfl)]

/-- One arrival delivered to the abstract head: the first pending symbol is
appended at the far right of the stored content. -/
def arriveH (h : Head) : Head := match h.incoming with
  | [] => h
  | a :: q => ⟨h.focus, h.left, h.right ++ [some a], q⟩

def arrivePH (p : PlaceHead) : PlaceHead := ⟨arriveH p.head, p.gap⟩

/-- The whole content a head stands for, position forgotten. -/
def flatten (p : PlaceHead) : List (Option (Fin 2)) :=
  p.head.left.reverse ++ p.head.focus :: p.head.right

/-! ## 2. The view -/

/-- A cursor's own maintained copy of the input.

* `back`  : cells strictly left of the focus, nearest first (a stack tape);
* `focus` : the cell under the head;
* `near`  : cells right of the focus that a left move pushed back (a stack tape);
* `far`   : the never-yet-visited suffix, in a Hood-Melville real-time queue;
* `gap`   : the half-step flag of `PlaceHead`.

Arrivals `snoc` onto `far` (far right end), right moves `tail` it (near left
end); both are `O(1)`.  No operation ever copies content. -/
structure InputView where
  back : List (Option (Fin 2))
  focus : Option (Fin 2)
  near : List (Option (Fin 2))
  far : RTQueue.Queue (Fin 2)
  gap : Bool

/-- The queue part of the stored content, as cells. -/
def farList (v : InputView) : List (Option (Fin 2)) :=
  (RTQueue.toList v.far).map some

/-- All stored content right of the focus. -/
def absRight (v : InputView) : List (Option (Fin 2)) := v.near ++ farList v

/-- Well-formedness: the queue satisfies the Hood-Melville invariant. -/
def WF (v : InputView) : Prop := RTQueue.Inv v.far

/-- The abstract head a view represents, given the still-pending arrivals `q`. -/
def absHead (v : InputView) (q : List (Fin 2)) : PlaceHead :=
  ⟨⟨v.focus, v.back, absRight v, q⟩, v.gap⟩

/-- The whole stored content of a view. -/
def cells (v : InputView) : List (Option (Fin 2)) :=
  v.back.reverse ++ v.focus :: absRight v

/-- The head's position: the number of cells to its left. -/
def pos (v : InputView) : ℕ := v.back.length

theorem flatten_absHead (v : InputView) (q : List (Fin 2)) :
    flatten (absHead v q) = cells v := rfl

theorem length_cells (v : InputView) :
    (cells v).length = pos v + 1 + (absRight v).length := by
  simp [cells, pos]; omega

/-! ## 3. Operations -/

/-- One arrival: a single `snoc` on the real-time queue. `O(1)`. -/
def arrive (a : Fin 2) (v : InputView) : InputView :=
  { v with far := RTQueue.snoc v.far a }

/-- One cell to the right. `O(1)`: pop the pushed-back stack, else `head?`/`tail`
the queue. -/
def stepRight (v : InputView) : InputView :=
  match v.near with
  | c :: rest => { v with focus := c, back := v.focus :: v.back, near := rest }
  | [] =>
      match RTQueue.head? v.far with
      | some a =>
          { v with focus := some a, back := v.focus :: v.back, far := RTQueue.tail v.far }
      | none => v

/-- One cell to the left. `O(1)`: pop `back`, push onto `near`. -/
def stepLeft (v : InputView) : InputView :=
  match v.back with
  | c :: rest => { v with focus := c, back := rest, near := v.focus :: v.near }
  | [] => v

/-- The view counterpart of `GalilScaffoldInputHead.left`. -/
def moveLeftV (v : InputView) : InputView :=
  if v.gap then { v with gap := false } else { stepLeft v with gap := true }

/-- The view counterpart of `rightPH`. -/
def moveRight (v : InputView) : InputView :=
  if v.gap then { stepRight v with gap := false } else { v with gap := true }

/-! ## 4. Queue lemmas -/

theorem farList_snoc {v : InputView} (hw : WF v) (a : Fin 2) :
    farList { v with far := RTQueue.snoc v.far a } = farList v ++ [some a] := by
  show (RTQueue.toList (RTQueue.snoc v.far a)).map some = _
  rw [RTQueue.toList_snoc hw]
  simp [farList]

theorem farList_arrive {v : InputView} (hw : WF v) (a : Fin 2) :
    farList (arrive a v) = farList v ++ [some a] := farList_snoc hw a

theorem absRight_arrive {v : InputView} (hw : WF v) (a : Fin 2) :
    absRight (arrive a v) = absRight v ++ [some a] := by
  show (arrive a v).near ++ farList (arrive a v) = (v.near ++ farList v) ++ [some a]
  rw [show (arrive a v).near = v.near from rfl, farList_arrive hw a, ← List.append_assoc]

theorem WF_arrive {v : InputView} (hw : WF v) (a : Fin 2) : WF (arrive a v) :=
  RTQueue.inv_snoc hw a

theorem farList_nil_of_head_none {v : InputView} (hw : WF v)
    (h : RTQueue.head? v.far = none) : farList v = [] := by
  have h' : (RTQueue.toList v.far).head? = none := by
    rw [← RTQueue.head?_eq hw]; exact h
  cases hl : RTQueue.toList v.far with
  | nil => simp [farList, hl]
  | cons b r => rw [hl] at h'; simp at h'

theorem farList_of_head_some {v : InputView} (hw : WF v) {a : Fin 2}
    (h : RTQueue.head? v.far = some a) :
    farList v = some a :: farList { v with far := RTQueue.tail v.far } := by
  have h' : (RTQueue.toList v.far).head? = some a := by
    rw [← RTQueue.head?_eq hw]; exact h
  have ht : RTQueue.toList (RTQueue.tail v.far) = (RTQueue.toList v.far).tail :=
    RTQueue.toList_tail hw
  cases hl : RTQueue.toList v.far with
  | nil => rw [hl] at h'; simp at h'
  | cons b r =>
      rw [hl] at h'
      have hba : b = a := by simpa using h'
      subst hba
      simp [farList, hl, ht]

/-! ## 5. `absHead` transport -/

/-- An arrival on the view is exactly one arrival on the abstract head:
the symbol leaves `incoming` and lands at the far right of the content. -/
theorem absHead_arrive {v : InputView} (hw : WF v) (a : Fin 2) (q : List (Fin 2)) :
    absHead (arrive a v) q = arrivePH (absHead v (a :: q)) := by
  show (⟨⟨v.focus, v.back, absRight (arrive a v), q⟩, v.gap⟩ : PlaceHead)
      = ⟨⟨v.focus, v.back, absRight v ++ [some a], q⟩, v.gap⟩
  rw [absRight_arrive hw]

theorem absRight_stepRight {v : InputView} (hw : WF v) {c : Option (Fin 2)}
    {r : List (Option (Fin 2))} (h : absRight v = c :: r) :
    (stepRight v).focus = c ∧ (stepRight v).back = v.focus :: v.back ∧
      absRight (stepRight v) = r ∧ WF (stepRight v) ∧ (stepRight v).gap = v.gap := by
  cases hn : v.near with
  | cons c0 rest =>
      rw [absRight, hn] at h
      have hc1 : c0 = c := (List.cons.inj h).1
      have hc2 : rest ++ farList v = r := (List.cons.inj h).2
      subst hc1
      refine ⟨by simp [stepRight, hn], by simp [stepRight, hn], ?_, ?_, by simp [stepRight, hn]⟩
      · simpa [stepRight, hn, absRight, farList] using hc2
      · simpa [WF, stepRight, hn] using hw
  | nil =>
      cases hq : RTQueue.head? v.far with
      | none =>
          have he : absRight v = [] := by
            simp [absRight, hn, farList_nil_of_head_none hw hq]
          rw [he] at h; exact absurd h (by simp)
      | some a =>
          have hf := farList_of_head_some hw hq
          rw [absRight, hn, List.nil_append, hf] at h
          have hc1 : some a = c := (List.cons.inj h).1
          have hc2 : farList { v with far := RTQueue.tail v.far } = r := (List.cons.inj h).2
          subst hc1
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · simp [stepRight, hn, hq]
          · simp [stepRight, hn, hq]
          · simpa [stepRight, hn, hq, absRight, farList] using hc2
          · simpa [WF, stepRight, hn, hq] using RTQueue.inv_tail hw
          · simp [stepRight, hn, hq]

theorem stepRight_nil {v : InputView} (hw : WF v) (h : absRight v = []) :
    stepRight v = v := by
  have hn : v.near = [] := by
    cases hn : v.near with
    | nil => rfl
    | cons c r => rw [absRight, hn] at h; simp at h
  have hfl : farList v = [] := by simpa [absRight, hn] using h
  cases hq : RTQueue.head? v.far with
  | none => simp [stepRight, hn, hq]
  | some a => rw [farList_of_head_some hw hq] at hfl; simp at hfl

/-- `moveRight` on the view realizes `rightPH` on the abstract head. -/
theorem absHead_moveRight {v : InputView} (hw : WF v) (q : List (Fin 2)) :
    absHead (moveRight v) q = rightPH (absHead v q) := by
  cases hg : v.gap
  · simp [moveRight, rightPH, absHead, hg, absRight, farList]
  · cases hr : absRight v with
    | nil =>
        have hs := stepRight_nil hw hr
        have hr' : v.near ++ (RTQueue.toList v.far).map some = [] := hr
        simp [moveRight, rightPH, absHead, hg, hs, moveRightH, absRight, farList, hr']
    | cons c r =>
        obtain ⟨h1, h2, h3, _, _⟩ := absRight_stepRight hw hr
        have h3' : (stepRight v).near ++ (RTQueue.toList (stepRight v).far).map some = r := h3
        have hr' : v.near ++ (RTQueue.toList v.far).map some = c :: r := hr
        simp [moveRight, rightPH, absHead, hg, moveRightH, h1, h2, absRight, farList, h3', hr']

/-- `moveLeftV` on the view realizes `GalilScaffoldInputHead.left`. -/
theorem absHead_moveLeft (v : InputView) (q : List (Fin 2)) :
    absHead (moveLeftV v) q = left (absHead v q) := by
  cases hg : v.gap
  · cases hb : v.back with
    | nil => simp [moveLeftV, left, absHead, hg, hb, moveLeft, stepLeft, absRight, farList]
    | cons c r =>
        simp [moveLeftV, left, absHead, hg, hb, moveLeft, stepLeft, absRight, farList]
  · simp [moveLeftV, left, absHead, hg, absRight, farList]

/-! ## 6. Content is never moved -/

theorem cells_arrive {v : InputView} (hw : WF v) (a : Fin 2) :
    cells (arrive a v) = cells v ++ [some a] := by
  show v.back.reverse ++ v.focus :: absRight (arrive a v)
      = (v.back.reverse ++ v.focus :: absRight v) ++ [some a]
  rw [absRight_arrive hw]
  simp

theorem cells_stepRight {v : InputView} (hw : WF v) : cells (stepRight v) = cells v := by
  cases hr : absRight v with
  | nil => rw [stepRight_nil hw hr]
  | cons c r =>
      obtain ⟨h1, h2, h3, _, _⟩ := absRight_stepRight hw hr
      simp [cells, h1, h2, h3, hr]

theorem cells_stepLeft (v : InputView) : cells (stepLeft v) = cells v := by
  cases hb : v.back with
  | nil => simp [stepLeft, hb]
  | cons c r => simp [cells, stepLeft, hb, absRight, farList]

theorem pos_stepLeft {v : InputView} (h : 0 < pos v) : pos (stepLeft v) + 1 = pos v := by
  cases hb : v.back with
  | nil => rw [pos, hb] at h; simp at h
  | cons c r => simp [pos, stepLeft, hb]

theorem pos_stepRight {v : InputView} (hw : WF v) (h : 0 < (absRight v).length) :
    pos (stepRight v) = pos v + 1 := by
  cases hr : absRight v with
  | nil => rw [hr] at h; simp at h
  | cons c r =>
      obtain ⟨_, h2, _, _, _⟩ := absRight_stepRight hw hr
      simp [pos, h2]

theorem WF_stepLeft {v : InputView} (hw : WF v) : WF (stepLeft v) := by
  cases hb : v.back with
  | nil => simpa [stepLeft, hb] using hw
  | cons c r => simpa [WF, stepLeft, hb] using hw

theorem WF_stepRight {v : InputView} (hw : WF v) : WF (stepRight v) := by
  cases hr : absRight v with
  | nil => rw [stepRight_nil hw hr]; exact hw
  | cons c r => exact (absRight_stepRight hw hr).2.2.2.1

theorem gap_stepLeft (v : InputView) : (stepLeft v).gap = v.gap := by
  cases hb : v.back <;> simp [stepLeft, hb]

theorem gap_stepRight {v : InputView} (hw : WF v) : (stepRight v).gap = v.gap := by
  cases hr : absRight v with
  | nil => rw [stepRight_nil hw hr]
  | cons c r => exact (absRight_stepRight hw hr).2.2.2.2

/-! ## 7. Repositioning: a head copy at distance `d` costs `d` local ticks -/

def repDist (a b : ℕ) : ℕ := (a - b) + (b - a)

/-- One micro-step of repositioning toward `target`. -/
def repositionStep (target : ℕ) (v : InputView) : InputView :=
  if pos v < target then stepRight v else if target < pos v then stepLeft v else v

/-- `n` micro-steps of repositioning. -/
def reposition (target : ℕ) : ℕ → InputView → InputView
  | 0, v => v
  | n + 1, v => reposition target n (repositionStep target v)

/-- **Main theorem.**  A view whose stored content reaches `target` arrives at
`target` after exactly `repDist (pos v) target` local micro-steps, with its
content, gap and well-formedness untouched.  So replacing `left := right` by
"reposition my own copy" costs one tick per cell of distance and copies nothing. -/
theorem reposition_reaches (target : ℕ) :
    ∀ (n : ℕ) (v : InputView), WF v → repDist (pos v) target = n →
      target ≤ pos v + (absRight v).length →
      pos (reposition target n v) = target ∧
        cells (reposition target n v) = cells v ∧
        WF (reposition target n v) ∧
        (reposition target n v).gap = v.gap := by
  intro n
  induction n with
  | zero =>
      intro v hw hd _
      have hp : pos v = target := by unfold repDist at hd; omega
      exact ⟨hp, rfl, hw, rfl⟩
  | succ n ih =>
      intro v hw hd hcap
      have hne : pos v ≠ target := by unfold repDist at hd; omega
      rcases Nat.lt_or_ge (pos v) target with hlt | hge
      · have hlen : 0 < (absRight v).length := by omega
        have hstep : repositionStep target v = stepRight v := by
          simp [repositionStep, hlt]
        have hp := pos_stepRight hw hlen
        have hc := cells_stepRight hw
        have hw' := WF_stepRight hw
        have hg := gap_stepRight hw
        have hcap' : target ≤ pos (stepRight v) + (absRight (stepRight v)).length := by
          have h1 := length_cells v
          have h2 := length_cells (stepRight v)
          rw [hc] at h2
          omega
        have hd' : repDist (pos (stepRight v)) target = n := by
          unfold repDist at hd ⊢; omega
        obtain ⟨i1, i2, i3, i4⟩ := ih (stepRight v) hw' hd' hcap'
        refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [reposition, hstep]
        · exact i1
        · rw [i2, hc]
        · exact i3
        · rw [i4, hg]
      · have hgt : target < pos v := by omega
        have hpos : 0 < pos v := by omega
        have hstep : repositionStep target v = stepLeft v := by
          have h1 : ¬ (pos v < target) := by omega
          simp [repositionStep, h1, hgt]
        have hp := pos_stepLeft hpos
        have hc := cells_stepLeft v
        have hw' := WF_stepLeft hw
        have hg := gap_stepLeft v
        have hcap' : target ≤ pos (stepLeft v) + (absRight (stepLeft v)).length := by
          have h1 := length_cells v
          have h2 := length_cells (stepLeft v)
          rw [hc] at h2
          omega
        have hd' : repDist (pos (stepLeft v)) target = n := by
          unfold repDist at hd ⊢; omega
        obtain ⟨i1, i2, i3, i4⟩ := ih (stepLeft v) hw' hd' hcap'
        refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [reposition, hstep]
        · exact i1
        · rw [i2, hc]
        · exact i3
        · rw [i4, hg]

/-! ## 8. Two views fed the same arrivals -/

/-- Feed a whole batch of arrivals, one `snoc` each. -/
def feed (l : List (Fin 2)) (v : InputView) : InputView :=
  l.foldl (fun w a => arrive a w) v

theorem WF_feed (l : List (Fin 2)) {v : InputView} (hw : WF v) : WF (feed l v) := by
  induction l generalizing v with
  | nil => exact hw
  | cons a t ih => exact ih (WF_arrive hw a)

theorem cells_feed (l : List (Fin 2)) {v : InputView} (hw : WF v) :
    cells (feed l v) = cells v ++ l.map some := by
  induction l generalizing v with
  | nil => simp [feed]
  | cons a t ih =>
      show cells (feed t (arrive a v)) = _
      rw [ih (WF_arrive hw a), cells_arrive hw a]
      simp

/-- **Two views fed the same arrivals hold the same content.**  Hence their
abstract heads differ only in where the head stands (position and gap) and in
which arrivals are still pending -- never in content.  This is what makes
"copy the head" a repositioning job. -/
theorem two_views_same_content {v₁ v₂ : InputView} (hw₁ : WF v₁) (hw₂ : WF v₂)
    (h : cells v₁ = cells v₂) (l : List (Fin 2)) :
    cells (feed l v₁) = cells (feed l v₂) := by
  rw [cells_feed l hw₁, cells_feed l hw₂, h]

/-- The same statement at the level of the abstract heads: only the split point
(position/gap) and the pending arrivals may differ. -/
theorem two_views_absHead {v₁ v₂ : InputView} (hw₁ : WF v₁) (hw₂ : WF v₂)
    (h : cells v₁ = cells v₂) (l : List (Fin 2)) (q₁ q₂ : List (Fin 2)) :
    flatten (absHead (feed l v₁) q₁) = flatten (absHead (feed l v₂) q₂) := by
  rw [flatten_absHead, flatten_absHead]
  exact two_views_same_content hw₁ hw₂ h l

/-! ## 9. A fresh view -/

def emptyView : InputView := ⟨[], none, [], RTQueue.empty, false⟩

theorem WF_emptyView : WF emptyView := RTQueue.inv_empty

/-- A view built from scratch by `n` arrivals holds exactly those `n` symbols
after the sentinel, and costs `n` queue operations, i.e. `<= 31 * n` tape actions
by `PalPeg.RTQueueTapes.queue_on_tapes_empty`. -/
theorem cells_feed_emptyView (l : List (Fin 2)) :
    cells (feed l emptyView) = none :: l.map some := by
  rw [cells_feed l WF_emptyView]
  simp [cells, emptyView, absRight, farList, RTQueue.toList_empty]

#print axioms absHead_arrive
#print axioms absHead_moveRight
#print axioms absHead_moveLeft
#print axioms left_rightPH
#print axioms reposition_reaches
#print axioms two_views_same_content
#print axioms two_views_absHead
#print axioms cells_feed_emptyView

end PalPeg.LocalInputView
