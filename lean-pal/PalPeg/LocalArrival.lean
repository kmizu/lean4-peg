import PalPeg.LocalInputView
import PalPeg.LocalState
import PalPeg.GalilScaffoldInputTrace
import PalPeg.GalilScaffoldChainVerifier

/-!
# Arrivals made abstraction-invisible (`absHead'`)

`PalPeg.LocalTracking` records (gap 1 of its docstring) that the abstract
`GalilScaffoldTop.Tick` has **no arrival rule**: the `compare` phase only ever
*pops* from a head's `incoming` FIFO, never grows it.  Hence an arrival at the
local level must be invisible to the abstraction, which is exactly the right
disjunct of the oracle `O4b`.

The abstraction `PalPeg.LocalInputView.absHead` of the local cursor does *not*
have that property: it puts the queue part `farList v` of the cursor's own copy
into the abstract `right` **stack** and the still-undelivered symbols `q` into
the abstract `incoming`, so `arrive` moves a symbol from `incoming` into `right`
— a visible change.

This file gives the **corrected** abstraction

```
absHead' v pending = ⟨⟨v.focus, v.back, v.near, RTQueue.toList v.far ++ pending⟩, v.gap⟩
```

which keeps the not-yet-visited suffix `far` in the abstract `incoming`, next to
the not-yet-arrived `pending`.  An arrival then only moves the boundary *inside*
`incoming`, which is invisible:

* `absHead'_arrive` — `absHead' (arrive a v) q = absHead' v (a :: q)`;
* `absHead'_moveRight_near` / `absHead'_moveRight_far` — the local right move
  still realizes the abstract `GalilScaffoldChainVerifier.right`, the second one
  being precisely the case where the abstract pop from `incoming` is the local
  pop from the queue `far`;
* `canRight_absHead'` — the availability condition, which now also fires when
  the symbol the abstract machine wants has *not yet arrived*
  (`far = []`, `q ≠ []`);
* `Ahead` and `moveRight_ok` — the (necessary) side condition that the local
  head never needs a not-yet-arrived symbol, under which the realization holds
  unconditionally.

Finally `abs'`/`absState'` restate `PalPeg.LocalState.abs`/`absState` with
`absHead'`, `feed'` is the arrival that also pops `pending`, and
`absState'_feed'` is the **stutter disjunct of `O4b`**:
`absState' (feed' x) = absState' x`.

`PalPeg.LocalState` is not edited; `abs'` is defined alongside `abs`.
-/

set_option autoImplicit false

namespace PalPeg.LocalArrival

open PalPeg.GalilScaffoldInputHead
open PalPeg.GalilScaffoldChainInputSupply (GalilVM)
open PalPeg.LocalInputView (InputView WF arrive moveRight stepRight farList absRight)
open PalPeg.GalilScaffoldChainVerifier (canRight right headRight)

/-! ## 1. The corrected abstraction -/

/-- **The corrected abstraction of a local cursor.**

Unlike `PalPeg.LocalInputView.absHead`, the never-yet-visited suffix `far` is
put into the abstract `incoming` FIFO, *in front of* the symbols `pending` that
have not arrived yet.  The abstract `right` stack holds only the cells a left
move has pushed back (`near`). -/
def absHead' (v : InputView) (pending : List (Fin 2)) : PlaceHead :=
  ⟨⟨v.focus, v.back, v.near, RTQueue.toList v.far ++ pending⟩, v.gap⟩

@[simp] theorem absHead'_gap (v : InputView) (q : List (Fin 2)) :
    (absHead' v q).gap = v.gap := rfl

@[simp] theorem absHead'_focus (v : InputView) (q : List (Fin 2)) :
    (absHead' v q).head.focus = v.focus := rfl

@[simp] theorem absHead'_left (v : InputView) (q : List (Fin 2)) :
    (absHead' v q).head.left = v.back := rfl

@[simp] theorem absHead'_right (v : InputView) (q : List (Fin 2)) :
    (absHead' v q).head.right = v.near := rfl

@[simp] theorem absHead'_incoming (v : InputView) (q : List (Fin 2)) :
    (absHead' v q).head.incoming = RTQueue.toList v.far ++ q := rfl

/-! ## 2. An arrival is invisible -/

/-- **Arrivals are abstraction-invisible.**  A local `arrive` only moves the
boundary between "arrived but unvisited" (`far`) and "not yet arrived" (`q`)
*inside* the abstract `incoming` FIFO. -/
theorem absHead'_arrive {v : InputView} (hw : WF v) (a : Fin 2) (q : List (Fin 2)) :
    absHead' (arrive a v) q = absHead' v (a :: q) := by
  have h : RTQueue.toList (RTQueue.snoc v.far a) = RTQueue.toList v.far ++ [a] :=
    RTQueue.toList_snoc hw a
  show (⟨⟨v.focus, v.back, v.near, RTQueue.toList (RTQueue.snoc v.far a) ++ q⟩, v.gap⟩ :
      PlaceHead) = ⟨⟨v.focus, v.back, v.near, RTQueue.toList v.far ++ (a :: q)⟩, v.gap⟩
  rw [h]
  simp

/-! ## 3. The right move still realizes the abstract one -/

/-- A half-step (`gap = false`) is a pure gap toggle on both sides. -/
theorem absHead'_moveRight_gap {v : InputView} (hg : v.gap = false) (q : List (Fin 2)) :
    absHead' (moveRight v) q = right (absHead' v q) := by
  rcases v with ⟨back, focus, near, far, gap⟩
  cases gap
  · rfl
  · exact absurd hg (by simp)

/-- A full step whose cell is in the pushed-back stack: the abstract pop from
`right` is the local pop from `near`. -/
theorem absHead'_moveRight_near {v : InputView} (hn : v.near ≠ []) (q : List (Fin 2)) :
    absHead' (moveRight v) q = right (absHead' v q) := by
  rcases v with ⟨back, focus, near, far, gap⟩
  cases gap
  · rfl
  · cases near with
    | nil => exact absurd rfl hn
    | cons c rest => rfl

/-- A full step whose cell is still in the queue: **the abstract pop from
`incoming` is the local pop from `far`.** -/
theorem absHead'_moveRight_far {v : InputView} (hw : WF v) (hn : v.near = [])
    (hf : RTQueue.toList v.far ≠ []) (q : List (Fin 2)) :
    absHead' (moveRight v) q = right (absHead' v q) := by
  rcases v with ⟨back, focus, near, far, gap⟩
  have hn' : near = [] := hn
  subst hn'
  have hw' : RTQueue.Inv far := hw
  have hf' : RTQueue.toList far ≠ [] := hf
  cases gap
  · rfl
  · obtain ⟨a, rest, hl⟩ : ∃ a rest, RTQueue.toList far = a :: rest := by
      cases hh : RTQueue.toList far with
      | nil => exact absurd hh hf'
      | cons a r => exact ⟨a, r, rfl⟩
    have hh : RTQueue.head? far = some a := by rw [RTQueue.head?_eq hw', hl]; rfl
    have ht : RTQueue.toList (RTQueue.tail far) = rest := by
      rw [RTQueue.toList_tail hw', hl]; rfl
    have hm : moveRight (⟨back, focus, [], far, true⟩ : InputView)
        = ⟨focus :: back, some a, [], RTQueue.tail far, false⟩ := by
      simp [PalPeg.LocalInputView.moveRight, PalPeg.LocalInputView.stepRight, hh]
    have hrr : right (absHead' (⟨back, focus, [], far, true⟩ : InputView) q)
        = (⟨⟨some a, focus :: back, [], rest ++ q⟩, false⟩ : PlaceHead) := by
      simp [right, absHead', headRight, PalPeg.GalilScaffoldInputTrace.moveRight, hl]
    rw [hm, hrr]
    show (⟨⟨some a, focus :: back, [], RTQueue.toList (RTQueue.tail far) ++ q⟩, false⟩ :
      PlaceHead) = _
    rw [ht]

/-! ## 4. Availability -/

/-- **The availability condition.**  The abstract machine may want to move right
while the symbol has *not yet arrived* (`far = []` but `q ≠ []`): that is the
last disjunct, and it is exactly what `Ahead` below has to exclude. -/
theorem canRight_absHead' (v : InputView) (q : List (Fin 2)) :
    canRight (absHead' v q) ↔
      (v.gap = false ∨ v.near ≠ [] ∨ RTQueue.toList v.far ≠ [] ∨ q ≠ []) := by
  have h : (RTQueue.toList v.far ++ q) ≠ [] ↔ (RTQueue.toList v.far ≠ [] ∨ q ≠ []) := by
    cases hl : RTQueue.toList v.far with
    | nil => simp
    | cons b r => simp
  show (v.gap = false ∨ v.near ≠ [] ∨ (RTQueue.toList v.far ++ q) ≠ []) ↔ _
  rw [h]

/-- **The local head never needs a not-yet-arrived symbol.**  If the local
cursor is about to take a full right step (`gap = true`) and has nothing pushed
back (`near = []`), then the cell it needs has already arrived (`far ≠ []`) —
unless nothing is pending at all. -/
def Ahead (v : InputView) (q : List (Fin 2)) : Prop :=
  v.gap = true → v.near = [] → RTQueue.toList v.far ≠ [] ∨ q = []

/-- **The realization theorem.**  Under `Ahead`, every right move the abstract
machine is allowed to take is realized by the local `moveRight`. -/
theorem moveRight_ok {v : InputView} (hw : WF v) {q : List (Fin 2)}
    (ha : Ahead v q) (hc : canRight (absHead' v q)) :
    absHead' (moveRight v) q = right (absHead' v q) := by
  cases hg : v.gap
  · exact absHead'_moveRight_gap hg q
  · by_cases hn : v.near = []
    · have hfar : RTQueue.toList v.far ≠ [] := by
        rcases ha hg hn with h | hq
        · exact h
        · rcases (canRight_absHead' v q).1 hc with h1 | h1 | h1 | h1
          · rw [hg] at h1; exact absurd h1 (by simp)
          · exact absurd hn h1
          · exact h1
          · exact absurd hq h1
      exact absHead'_moveRight_far hw hn hfar q
    · exact absHead'_moveRight_near hn q

/-! ## 5. The corrected state abstraction and the stutter disjunct of `O4b` -/

open PalPeg.LocalState (GalilVML)

variable {P : ℕ}

/-- `PalPeg.LocalState.abs`, restated with `absHead'` on the three input heads.
`PalPeg.LocalState` itself is left untouched. -/
def abs' (x : GalilVML P) : GalilVM :=
  { PalPeg.LocalState.abs x with
    left := absHead' x.left x.pending
    center := absHead' x.center x.pending
    right := absHead' x.right x.pending }

/-- The corrected abstraction onto a full scaffold state. -/
def absState' (x : GalilVML P) : PalPeg.GalilScaffoldTop.State GalilVM := ⟨x.ctl, abs' x⟩

@[simp] theorem absState'_ctl (x : GalilVML P) : (absState' x).ctl = x.ctl := rfl
@[simp] theorem absState'_vm (x : GalilVML P) : (absState' x).vm = abs' x := rfl

/-- One arrival at the local level, on all five cursors.  Definitionally the
`PalPeg.LocalTracking.feedL` of the tracking skeleton (repeated here so that this
file does not have to import it). -/
def feedL (a : Fin 2) (x : GalilVML P) : GalilVML P :=
  { x with
    left := arrive a x.left,
    center := arrive a x.center,
    right := arrive a x.right,
    walkerView := arrive a x.walkerView,
    fppWalker := arrive a x.fppWalker }

/-- One arrival at the local level **that also pops `pending`**: the letter
leaves the still-undelivered list and is `snoc`-ed onto every cursor's queue. -/
def feedL' (a : Fin 2) (rest : List (Fin 2)) (x : GalilVML P) : GalilVML P :=
  { feedL a x with pending := rest }

/-- `feed'`, dispatching on the pending list. -/
def feedPending (l : List (Fin 2)) (x : GalilVML P) : GalilVML P :=
  match l with
  | [] => x
  | a :: rest => feedL' a rest x

/-- The arrival step of the local machine: deliver the first pending letter (if
any) to all five cursors, and drop it from `pending`. -/
def feed' (x : GalilVML P) : GalilVML P := feedPending x.pending x

theorem feed'_cons {x : GalilVML P} {a : Fin 2} {rest : List (Fin 2)}
    (hp : x.pending = a :: rest) : feed' x = feedL' a rest x := by
  show feedPending x.pending x = _
  rw [hp]
  rfl

theorem feed'_nil {x : GalilVML P} (hp : x.pending = []) : feed' x = x := by
  show feedPending x.pending x = _
  rw [hp]
  rfl

/-- **The stutter disjunct of `O4b`, for `abs'`.**  Delivering a pending letter
to all five cursors does not move the corrected abstraction at all. -/
theorem abs'_feedL' {x : GalilVML P} (hw : PalPeg.LocalState.ViewsWF x) (a : Fin 2)
    (rest : List (Fin 2)) (hp : x.pending = a :: rest) :
    abs' (feedL' a rest x) = abs' x := by
  obtain ⟨hwl, hwc, hwr, -, -⟩ := hw
  have hl : absHead' (arrive a x.left) rest = absHead' x.left x.pending := by
    rw [absHead'_arrive hwl, hp]
  have hc : absHead' (arrive a x.center) rest = absHead' x.center x.pending := by
    rw [absHead'_arrive hwc, hp]
  have hr : absHead' (arrive a x.right) rest = absHead' x.right x.pending := by
    rw [absHead'_arrive hwr, hp]
  show { PalPeg.LocalState.abs (feedL' a rest x) with
      left := absHead' (arrive a x.left) rest
      center := absHead' (arrive a x.center) rest
      right := absHead' (arrive a x.right) rest } = abs' x
  rw [hl, hc, hr]
  rfl

/-- **`O4b`'s stutter disjunct.**  `absState' (feed' x) = absState' x`. -/
theorem absState'_feed' {x : GalilVML P} (hw : PalPeg.LocalState.ViewsWF x) :
    absState' (feed' x) = absState' x := by
  cases hp : x.pending with
  | nil => rw [feed'_nil hp]
  | cons a rest =>
      rw [feed'_cons hp]
      show (⟨(feedL' a rest x).ctl, abs' (feedL' a rest x)⟩ :
        PalPeg.GalilScaffoldTop.State GalilVM) = ⟨x.ctl, abs' x⟩
      rw [abs'_feedL' hw a rest hp]
      rfl

#print axioms absHead'_arrive
#print axioms absHead'_moveRight_near
#print axioms absHead'_moveRight_far
#print axioms canRight_absHead'
#print axioms moveRight_ok
#print axioms abs'_feedL'
#print axioms absState'_feed'

end PalPeg.LocalArrival
