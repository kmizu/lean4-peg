import PalPeg.CloseoutCoreEnc16

/-!
# Closeout, step 2r: the cursor queue as a bounded composite, and why the old layout cannot be one

`CloseoutCoreEnc17` discharges `shiftPick` at every address **except** the two
moving cursor blocks, which it names `rest`/`hrest`; `CloseoutCoreEnc13`
obstacle 4 is the same gap.  The moving datum is `LocalInputView.moveRight`,
which rewrites the `left`/`center` cursors laid out by
`CloseoutCoreEnc.viewTapes` (and, in the repaired form, by
`CloseoutCoreEnc7.queueTapes6`/`viewTapes8`).  Nothing here is about the whole
machine, so

**無条件 PAL ∈ PEG は未完.**

## What is established (unconditional)

* **§1 (the length monotonicity of a composite).**  `wideLen_actOnG` /
  `wideLen_actList`: `left.length + 1 + right.length` never decreases along an
  `actList`.  This is the only fact needed for §2.
* **§2 (the old layout is *not* a composite, at all).**
  `not_pop_stackTape` and `not_pop_listTape`: for **no** list of `Act Γc`
  whatsoever — bounded or not — does `actList` carry `stackTape (a :: l)` to
  `stackTape l`, nor `listTape (a :: b :: l)` to `listTape (b :: l)`.  Both layouts
  normalise the dead half of the tape away (`right = []`, resp. `left = []`),
  and a Turing head can only *grow* the written region.  So the `rest` of
  `CloseoutCoreEnc17` is not merely unproved on `viewTapes`: on that layout it
  is **false**, and the layout must change.  `not_pop_viewTapes1` states this in
  the form `CloseoutCoreEnc17.hrest` would need.
* **§3 (the repaired stack tape).**  `dTape l r` keeps the popped cells as
  *debris* `r` to the right of the head instead of erasing them.
  `dTape_nil_debris` identifies `dTape l []` with
  `CloseoutCoreEnc3.stackTape l`, so the repair only adds trailing junk.
  `pop_dTape` is **one** micro-action and `push_dTape` is **two**
  (`popActs_length`, `pushActs_length`), both unconditional equalities.
* **§4 (the repaired cursor).**  `viewTapesD v d` is the `tView = 4` layout of
  one cursor on `dTape`s.  `moveRight_actList` is the goal: at every one of the
  four addresses, `LocalInputView.moveRight` is `actList` of `moveActs`, a list
  of length `≤ 2` (`moveActs_length`, `moveRight_actList_bounded`), **whenever
  the real-time queue is not popped** — i.e. on the half-step (`gap = false`)
  and on the pushed-back branch (`near ≠ []`).

## What is *not* established, one line each

1. **The `far` branch is open**: when `near = []` the move runs
   `RTQueue.tail`, whose `check`/`exec2` may *start* a rotation
   (`.reversing 0 front [] rear []`), which assigns whole lists to the `f`/`r`
   stacks and, at `.done`, to `front`; on tapes that is a **role permutation**
   of the six stacks of `CloseoutCoreEnc7.queueTapes6`, not a bounded rewrite of
   any one of them, so it needs the `rolesOfQ` treatment of
   `CloseoutCoreEnc14`/`16` transported from the counter bank to the queue bank.
2. **`shiftVm_tapeActK'` is not built**: discharging `CloseoutCoreEnc17`'s
   `rest`/`hrest` needs `CloseoutCoreEnc.encTapes` itself rebuilt on
   `viewTapesD` (an edit to an existing file), which is out of scope here.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutCoreEnc18

open PalPeg PalPeg.Program
open PalPeg.Local (pos)
open PalPeg.CloseoutCoreStep (Γc blankc)
open PalPeg.CloseoutCoreEnc (cellSym listTape viewTapes)
open PalPeg.CloseoutCoreEnc3 (stackTape)
open PalPeg.CloseoutCoreEnc12 (Act actList actOnG actList_cons)
open PalPeg.LocalInputView (InputView stepRight moveRight)

/-! ## 1. A composite never shrinks the written region -/

/-- The written width of a tape: everything the head has ever had under it. -/
def wideLen (T : STape Γc) : ℕ := T.left.length + 1 + T.right.length

theorem wideLen_actOnG (T : STape Γc) (a : Act Γc) :
    wideLen T ≤ wideLen (actOnG blankc T a) := by
  cases a with
  | none => exact Nat.le_refl _
  | some sm =>
      obtain ⟨s, mv⟩ := sm
      obtain ⟨L, f, R⟩ := T
      cases mv with
      | stay => exact Nat.le_refl _
      | right =>
          cases R with
          | nil =>
              show wideLen ⟨L, f, []⟩ ≤ wideLen (⟨s :: L, blankc, []⟩ : STape Γc)
              simp only [wideLen, List.length_cons, List.length_nil]
              omega
          | cons n r =>
              show wideLen ⟨L, f, n :: r⟩ ≤ wideLen (⟨s :: L, n, r⟩ : STape Γc)
              simp only [wideLen, List.length_cons]
              omega
      | left =>
          cases L with
          | nil =>
              show wideLen ⟨[], f, R⟩ ≤ wideLen (⟨[], s, R⟩ : STape Γc)
              exact Nat.le_refl _
          | cons n l =>
              show wideLen ⟨n :: l, f, R⟩ ≤ wideLen (⟨l, n, s :: R⟩ : STape Γc)
              simp only [wideLen, List.length_cons]
              omega

/-- **A composite step never shrinks the written region.** -/
theorem wideLen_actList (T : STape Γc) (as : List (Act Γc)) :
    wideLen T ≤ wideLen (actList blankc T as) := by
  induction as generalizing T with
  | nil => exact Nat.le_refl _
  | cons a as ih =>
      rw [actList_cons]
      exact le_trans (wideLen_actOnG T a) (ih _)

/-! ## 2. The old layout is not a composite -/

theorem wideLen_stackTape (l : List (Option (Fin 2))) :
    wideLen (stackTape l) = l.length + 1 := by
  cases l with
  | nil => rfl
  | cons a t =>
      show (t.map cellSym ++ [blankc]).length + 1 + ([] : List Γc).length = (a :: t).length + 1
      simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]

/-- `listTape` parks the head at the **left** end, so its written width is the
length of the list (and `1` on the empty list, which is why the pop of a
one-element `listTape` is the single write `blankc` and the obstruction below
needs two elements). -/
theorem wideLen_listTape_cons (a : Option (Fin 2)) (l : List (Option (Fin 2))) :
    wideLen (listTape (a :: l)) = l.length + 1 := by
  show ([] : List Γc).length + 1 + (l.map cellSym).length = l.length + 1
  simp only [List.length_map, List.length_nil]
  omega

/-- **A `stackTape` pop is not a composite of micro-actions**, for *any* list of
micro-actions: the layout erases the popped cell, and a head cannot erase. -/
theorem not_pop_stackTape (a : Option (Fin 2)) (l : List (Option (Fin 2))) :
    ¬ ∃ as : List (Act Γc), actList blankc (stackTape (a :: l)) as = stackTape l := by
  rintro ⟨as, has⟩
  have h := wideLen_actList (stackTape (a :: l)) as
  rw [has, wideLen_stackTape, wideLen_stackTape] at h
  simp at h

/-- The same for the `near` layout of `CloseoutCoreEnc.viewTapes`. -/
theorem not_pop_listTape (a b : Option (Fin 2)) (l : List (Option (Fin 2))) :
    ¬ ∃ as : List (Act Γc),
      actList blankc (listTape (a :: b :: l)) as = listTape (b :: l) := by
  rintro ⟨as, has⟩
  have h := wideLen_actList (listTape (a :: b :: l)) as
  rw [has, wideLen_listTape_cons, wideLen_listTape_cons] at h
  simp at h

/-- **`CloseoutCoreEnc17.hrest` is false on `viewTapes`**, at cursor address `1`:
a right move off a nonempty `near` has no micro-action list at all. -/
theorem not_pop_viewTapes1 (v : InputView) (c b : Option (Fin 2))
    (rest : List (Option (Fin 2))) (hg : v.gap = true) (hn : v.near = c :: b :: rest) :
    ¬ ∃ as : List (Act Γc), actList blankc (viewTapes v 1) as = viewTapes (moveRight v) 1 := by
  have h0 : viewTapes v 1 = listTape (c :: b :: rest) := by
    show listTape v.near = _
    rw [hn]
  have h1 : viewTapes (moveRight v) 1 = listTape (b :: rest) := by
    show listTape (moveRight v).near = _
    have hnear : (moveRight v).near = b :: rest := by
      unfold moveRight
      rw [hg]
      show (stepRight v).near = b :: rest
      unfold stepRight
      rw [hn]
    rw [hnear]
  rw [h0, h1]
  exact not_pop_listTape c b rest

/-! ## 3. The repaired stack tape: keep the debris -/

/-- **A stack tape that does not erase**: the live stack `l` to the left of and
under the head, the dead cells `r` still standing to its right. -/
def dTape (l : List (Option (Fin 2))) (r : List Γc) : STape Γc :=
  match l with
  | [] => ⟨[], blankc, r⟩
  | a :: rest => ⟨rest.map cellSym ++ [blankc], cellSym a, r⟩

/-- With no debris this is exactly `CloseoutCoreEnc3.stackTape`. -/
theorem dTape_nil_debris (l : List (Option (Fin 2))) : dTape l [] = stackTape l := by
  cases l <;> rfl

@[simp] theorem pos_dTape (l : List (Option (Fin 2))) (r : List Γc) :
    pos (dTape l r) = l.length := by
  cases l with
  | nil => rfl
  | cons a t => simp [pos, dTape]

/-- The symbol the head of a `dTape` is standing on. -/
def topSym : List (Option (Fin 2)) → Γc
  | [] => blankc
  | a :: _ => cellSym a

/-- **A pop is one micro-action.** -/
def popActs : List (Act Γc) := [some (blankc, PegSeparation.RealTimeTM.Move.left)]

theorem popActs_length : popActs.length = 1 := rfl

theorem pop_dTape (a : Option (Fin 2)) (l : List (Option (Fin 2))) (r : List Γc) :
    actList blankc (dTape (a :: l) r) popActs = dTape l (blankc :: r) := by
  cases l with
  | nil => rfl
  | cons b t => rfl

/-- **A push is two micro-actions**, and it eats one cell of debris. -/
def pushActs (l : List (Option (Fin 2))) (b : Option (Fin 2)) : List (Act Γc) :=
  [some (topSym l, PegSeparation.RealTimeTM.Move.right), some (cellSym b, PegSeparation.RealTimeTM.Move.stay)]

theorem pushActs_length (l : List (Option (Fin 2))) (b : Option (Fin 2)) :
    (pushActs l b).length = 2 := rfl

theorem push_dTape (l : List (Option (Fin 2))) (r : List Γc) (b : Option (Fin 2)) :
    actList blankc (dTape l r) (pushActs l b) = dTape (b :: l) r.tail := by
  cases l with
  | nil => cases r <;> rfl
  | cons a t => cases r <;> rfl

/-- The identity is the empty composite. -/
theorem keep_dTape (l : List (Option (Fin 2))) (r : List Γc) :
    actList blankc (dTape l r) [] = dTape l r := rfl

/-! ## 4. The repaired cursor, and `moveRight` -/

/-- **The `tView = 4` tapes of one cursor, repaired**: `back` carrying `focus` on
the head, `near`, and the two stacks of the real-time queue, each with its own
debris. -/
def viewTapesD (v : InputView) (d : ℕ → List Γc) : ℕ → STape Γc
  | 0 => dTape (v.focus :: v.back) (d 0)
  | 1 => dTape v.near (d 1)
  | 2 => dTape (v.far.front.map some) (d 2)
  | _ => dTape (v.far.rear.map some) (d 3)

/-- **The micro-action list of `moveRight` at each of the four addresses**, on
the branches that do not touch the real-time queue. -/
def moveActs (v : InputView) : ℕ → List (Act Γc)
  | 0 => if v.gap then pushActs (v.focus :: v.back) v.near.headI else []
  | 1 => if v.gap then popActs else []
  | _ => []

theorem moveActs_length (v : InputView) (i : ℕ) : (moveActs v i).length ≤ 2 := by
  match i with
  | 0 =>
      show (if v.gap then pushActs (v.focus :: v.back) v.near.headI else []).length ≤ 2
      split
      · simp [pushActs]
      · simp
  | 1 =>
      show (if v.gap then popActs else []).length ≤ 2
      split
      · simp [popActs]
      · simp
  | (k + 2) => exact Nat.zero_le _

/-- The debris after the move: address `0` consumed one cell, address `1` grew
one, the queue tapes are untouched. -/
def moveDebris (v : InputView) (d : ℕ → List Γc) : ℕ → List Γc
  | 0 => if v.gap then (d 0).tail else d 0
  | 1 => if v.gap then blankc :: d 1 else d 1
  | i => d i

/-- **`LocalInputView.moveRight` is a bounded composite at every cursor
address**, on the two branches that leave `far` alone: the half-step
(`gap = false`) and the pushed-back branch (`near = c :: rest`). -/
theorem moveRight_actList (v : InputView) (d : ℕ → List Γc)
    (hnear : v.gap = true → v.near ≠ []) (i : ℕ) :
    viewTapesD (moveRight v) (moveDebris v d) i
      = actList blankc (viewTapesD v d i) (moveActs v i) := by
  cases hg : v.gap with
  | false =>
      have hv : moveRight v = { v with gap := true } := by
        unfold moveRight
        rw [hg]
        rfl
      match i with
      | 0 =>
          show dTape ((moveRight v).focus :: (moveRight v).back) (moveDebris v d 0)
            = actList blankc (dTape (v.focus :: v.back) (d 0)) (moveActs v 0)
          have ha : moveActs v 0 = [] := by
            show (if v.gap then pushActs (v.focus :: v.back) v.near.headI else []) = []
            rw [hg]
            rfl
          have hd : moveDebris v d 0 = d 0 := by
            show (if v.gap then (d 0).tail else d 0) = d 0
            rw [hg]
            rfl
          rw [ha, hd, hv]
          rfl
      | 1 =>
          show dTape (moveRight v).near (moveDebris v d 1)
            = actList blankc (dTape v.near (d 1)) (moveActs v 1)
          have ha : moveActs v 1 = [] := by
            show (if v.gap then popActs else []) = []
            rw [hg]
            rfl
          have hd : moveDebris v d 1 = d 1 := by
            show (if v.gap then blankc :: d 1 else d 1) = d 1
            rw [hg]
            rfl
          rw [ha, hd, hv]
          rfl
      | 2 =>
          show dTape ((moveRight v).far.front.map some) (moveDebris v d 2)
            = actList blankc (dTape (v.far.front.map some) (d 2)) (moveActs v 2)
          rw [hv]
          rfl
      | (k + 3) =>
          show dTape ((moveRight v).far.rear.map some) (moveDebris v d 3)
            = actList blankc (dTape (v.far.rear.map some) (d 3)) (moveActs v (k + 3))
          rw [hv]
          rfl
  | true =>
      obtain ⟨c, rest, hn⟩ : ∃ c rest, v.near = c :: rest := by
        cases hnn : v.near with
        | nil => exact absurd hnn (hnear hg)
        | cons c rest => exact ⟨c, rest, rfl⟩
      have hv : moveRight v =
          { v with focus := c, back := v.focus :: v.back, near := rest, gap := false } := by
        unfold moveRight
        rw [hg]
        show ({ stepRight v with gap := false } : InputView) = _
        unfold stepRight
        rw [hn]
      have hhi : v.near.headI = c := by rw [hn]; rfl
      match i with
      | 0 =>
          show dTape ((moveRight v).focus :: (moveRight v).back) (moveDebris v d 0)
            = actList blankc (dTape (v.focus :: v.back) (d 0)) (moveActs v 0)
          have ha : moveActs v 0 = pushActs (v.focus :: v.back) c := by
            show (if v.gap then pushActs (v.focus :: v.back) v.near.headI else []) = _
            rw [hg, hhi]
            rfl
          have hd : moveDebris v d 0 = (d 0).tail := by
            show (if v.gap then (d 0).tail else d 0) = _
            rw [hg]
            rfl
          rw [ha, hd, hv]
          exact (push_dTape (v.focus :: v.back) (d 0) c).symm
      | 1 =>
          show dTape (moveRight v).near (moveDebris v d 1)
            = actList blankc (dTape v.near (d 1)) (moveActs v 1)
          have ha : moveActs v 1 = popActs := by
            show (if v.gap then popActs else []) = _
            rw [hg]
            rfl
          have hd : moveDebris v d 1 = blankc :: d 1 := by
            show (if v.gap then blankc :: d 1 else d 1) = _
            rw [hg]
            rfl
          rw [ha, hd, hv, hn]
          exact (pop_dTape c rest (d 1)).symm
      | 2 =>
          show dTape ((moveRight v).far.front.map some) (moveDebris v d 2)
            = actList blankc (dTape (v.far.front.map some) (d 2)) (moveActs v 2)
          rw [hv]
          rfl
      | (k + 3) =>
          show dTape ((moveRight v).far.rear.map some) (moveDebris v d 3)
            = actList blankc (dTape (v.far.rear.map some) (d 3)) (moveActs v (k + 3))
          rw [hv]
          rfl

/-- **The bounded form**, as `CloseoutCoreEnc17.hrest` would consume it: a
single list-valued datum of length `≤ 2 ≤ 4` realising the move at every
address of one cursor block. -/
theorem moveRight_actList_bounded (v : InputView) (d : ℕ → List Γc)
    (hnear : v.gap = true → v.near ≠ []) :
    ∃ acts : ℕ → List (Act Γc),
      (∀ i, (acts i).length ≤ 2) ∧
      ∀ i, viewTapesD (moveRight v) (moveDebris v d) i
        = actList blankc (viewTapesD v d i) (acts i) :=
  ⟨moveActs v, moveActs_length v, moveRight_actList v d hnear⟩

end PalPeg.CloseoutCoreEnc18

#print axioms PalPeg.CloseoutCoreEnc18.wideLen_actList
#print axioms PalPeg.CloseoutCoreEnc18.not_pop_stackTape
#print axioms PalPeg.CloseoutCoreEnc18.not_pop_listTape
#print axioms PalPeg.CloseoutCoreEnc18.not_pop_viewTapes1
#print axioms PalPeg.CloseoutCoreEnc18.pop_dTape
#print axioms PalPeg.CloseoutCoreEnc18.push_dTape
#print axioms PalPeg.CloseoutCoreEnc18.moveActs_length
#print axioms PalPeg.CloseoutCoreEnc18.moveRight_actList
#print axioms PalPeg.CloseoutCoreEnc18.moveRight_actList_bounded
