import PalPeg.CloseoutCoreEnc14

/-!
# Closeout, step 2o: the layout transport of the two branch budgets

`CloseoutCoreEnc14` §3 proves `chooseVm_tapeActList` / `shiftVm_tapeActList` on
the **raw** layout `CloseoutCoreEnc.encTapes`, and lists as its missing fact 1
that these do not yet reach `CloseoutCoreEnc8.padTapesN`, the layout over which
the `CloseoutCoreEnc13` §5 residual `TapeActK` is stated.  This file supplies
the two commutation laws that close that gap (`shift1` and `padRN` versus
`actList`), transports the two branches to `padTapesN` at the slot address, and
records exactly what the radius-`K` margin costs.  Nothing here is about the
whole machine, so

**無条件 PAL ∈ PEG は未完.**

## What is established (unconditional)

* **§1 (how one micro-action moves the head and the reservoir).**
  `pos_pred_le_actOnG` (`pos T - 1 ≤ pos (actOnG b T a)`) and `wlen_actOnG`
  (the stored width is conserved while the head has a stored cell to its right).
* **§2 (the two commutation laws).**  `shift1_actList`: the sentinel shift
  commutes with a composite provided the composite cannot walk off the left edge
  (`as.length ≤ pos T`) — the single-action law `shift1_actOnG` needs exactly
  `0 < pos T`, and `shift1_actOnG_left_edge` shows the hypothesis is **not**
  removable.  `padRN_actList`: the right reservoir commutes with a composite
  provided the composite stays inside the **stored** width of the unpadded tape
  (`pos T + as.length ≤ wlen T`), with `padRN_actOnG` needing `T.right ≠ []`;
  `padRN_actOnG_right_edge` shows that hypothesis is not removable either —
  a right move at the right edge leaves the two reservoirs off by one cell, so
  *the reservoir `n` cannot supply its own room*.
* **§3 (the transport).**  `chooseVm_padTapesN_slot` and
  `shiftVm_padTapesN_slot`: at the address `CloseoutCoreEnc14.slotIdx j`, the
  `padTapesN` tape of the successor of either branch is
  `actList blankc (padTapesN n rep m (slotIdx j)) as` for a list of length `≤ 2`
  — the `TapeActK.tape` shape of `CloseoutCoreEnc13` §5 — under exactly the two
  head invariants §2 asks for, `2 ≤ pos (m.vm.phys j)` and
  `pos (m.vm.phys j) + 2 ≤ wlen (m.vm.phys j)`, and for **every** `n`.
* **§4 (the margin, exactly).**  `pos_padTapesN_slot`: the head of the laid-out
  slot sits at `pos (m.vm.phys j) + 1`, so `margin_padTapesN_slot` gives
  `K ≤ pos (padTapesN n rep m (slotIdx j))` from `K ≤ pos (m.vm.phys j) + 1`.
  This is sharp: `pos_padRN` and `pos_shift1` show the reservoir is on the
  **right** and the sentinel is a single cell, so obstruction 3 of
  `CloseoutCoreEnc13` cannot be discharged from `n` at all.
* **§5 (which other addresses are fixed).**  `chooseVm_encTapes_view`: the six
  cursor blocks `i < nViews * tView` are untouched by `chooseSelect`.

## What is *not* established, one line each

1. **The `TapeActK` instance is still out of reach**, because the residual
   quantifies over *every* `i` and the bank is not the only thing the two
   branches move: `LocalTick3.bankTick` also applies `mirOp` to `radiusMir`,
   `lowerMir`, `lengthMir` (addresses `nViews * tView + P + 0 … 6`) and
   `shiftVm`/`shiftMid` advance `left`, `center` and the chain, so the analogue
   of §5 for `shiftPick` and for the mirror block is *false as stated* and needs
   its own micro-action list per block.
2. **Both head invariants of §3 and the margin of §4 must come from the counter
   layout**, i.e. from `LocalCounter.SegCtr (m.vm.phys j) v` with `v` large
   enough (and from a stored right segment), not from `n`: neither the left
   sentinel nor the right reservoir can produce them.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutCoreEnc15

open PalPeg PalPeg.Program
open PalPeg.Local (pos)
open PalPeg.CloseoutCoreStep (Γc blankc nViews tView)
open PalPeg.CloseoutCoreEnc (segSym mapTape encTapes)
open PalPeg.CloseoutCoreEnc3 (shift1 pos_shift1)
open PalPeg.CloseoutCoreEnc5 (wlen)
open PalPeg.CloseoutCoreEnc8 (padRN pos_padRN wlen_padRN padTapesN)
open PalPeg.CloseoutCoreEnc12 (Act actOnG actList actList_cons)
open PalPeg.CloseoutCoreEnc14 (slotIdx padTapesN_slotIdx)
open PalPeg.LocalReplayParked (Mirrored1)
open PalPeg.LocalChain (ChainL)
open PalPeg.GalilScaffoldChainInputSupply (ChainVM)

variable {Γ : Type}

/-! ## 1. How one micro-action moves the head and the reservoir -/

/-- A left move costs at most one cell of left margin. -/
theorem pos_pred_le_actOnG (b : Γ) (T : STape Γ) (a : Act Γ) :
    pos T - 1 ≤ pos (actOnG b T a) := by
  cases a with
  | none => simp [actOnG]
  | some sm =>
      obtain ⟨s, mv⟩ := sm
      obtain ⟨L, f, R⟩ := T
      cases mv with
      | stay => simp [actOnG, STape.applyAction, pos]
      | right => cases R <;> (simp only [actOnG, STape.applyAction, pos, List.length_cons]; omega)
      | left => cases L <;> simp [actOnG, STape.applyAction, pos]

/-- **The stored width is conserved** while the head still has a stored cell to
its right. -/
theorem wlen_actOnG (b : Γ) (T : STape Γ) (a : Act Γ) (h : T.right ≠ []) :
    wlen (actOnG b T a) = wlen T := by
  obtain ⟨L, f, R⟩ := T
  cases a with
  | none => rfl
  | some sm =>
      obtain ⟨s, mv⟩ := sm
      cases mv with
      | stay => rfl
      | right =>
          cases R with
          | nil => exact absurd rfl h
          | cons r R =>
              simp only [actOnG, STape.applyAction, wlen, pos, List.length_cons]
              omega
      | left =>
          cases L with
          | nil => simp [actOnG, STape.applyAction, wlen, pos]
          | cons l L =>
              simp only [actOnG, STape.applyAction, wlen, pos, List.length_cons]
              omega

theorem right_ne_nil_of_pos_lt_wlen {T : STape Γ} (h : pos T < wlen T) : T.right ≠ [] := by
  intro hr
  rw [wlen, hr] at h
  simp at h

/-! ## 2. The two commutation laws -/

/-- **The sentinel shift commutes with one micro-action**, away from the left
edge. -/
theorem shift1_actOnG (b : Γ) (T : STape Γ) (a : Act Γ) (h : 0 < pos T) :
    shift1 b (actOnG b T a) = actOnG b (shift1 b T) a := by
  obtain ⟨L, f, R⟩ := T
  cases a with
  | none => rfl
  | some sm =>
      obtain ⟨s, mv⟩ := sm
      cases mv with
      | stay => rfl
      | right => cases R <;> rfl
      | left =>
          cases L with
          | nil => simp [pos] at h
          | cons l L => rfl

/-- The hypothesis of `shift1_actOnG` is **not** removable: at the left edge the
sentinel is consumed by the move. -/
theorem shift1_actOnG_left_edge (b s f : Γ) (R : List Γ) :
    shift1 b (actOnG b (⟨[], f, R⟩ : STape Γ) (some (s, .left)))
      ≠ actOnG b (shift1 b (⟨[], f, R⟩ : STape Γ)) (some (s, .left)) := by
  intro hcon
  have h : ([b] : List Γ) = [] := congrArg STape.left hcon
  simp at h

/-- **The sentinel shift commutes with a composite** that cannot walk off the
left edge. -/
theorem shift1_actList (b : Γ) (T : STape Γ) (as : List (Act Γ))
    (h : as.length ≤ pos T) :
    shift1 b (actList b T as) = actList b (shift1 b T) as := by
  induction as generalizing T with
  | nil => rfl
  | cons a as ih =>
      simp only [List.length_cons] at h
      have hp : 0 < pos T := by omega
      have hnext : as.length ≤ pos (actOnG b T a) := by
        have := pos_pred_le_actOnG b T a
        omega
      rw [actList_cons, ih _ hnext, shift1_actOnG b T a hp, actList_cons]

/-- **The right reservoir commutes with one micro-action** that does not need a
fresh cell. -/
theorem padRN_actOnG (b : Γ) (n : ℕ) (T : STape Γ) (a : Act Γ) (h : T.right ≠ []) :
    padRN b n (actOnG b T a) = actOnG b (padRN b n T) a := by
  obtain ⟨L, f, R⟩ := T
  cases a with
  | none => rfl
  | some sm =>
      obtain ⟨s, mv⟩ := sm
      cases mv with
      | stay => rfl
      | right =>
          cases R with
          | nil => exact absurd rfl h
          | cons r R => rfl
      | left => cases L <;> rfl

/-- The hypothesis of `padRN_actOnG` is **not** removable: a right move at the
right edge leaves the two reservoirs off by one cell, so the reservoir cannot
supply its own room. -/
theorem padRN_actOnG_right_edge (b s f : Γ) (L : List Γ) (n : ℕ) :
    padRN b (n + 1) (actOnG b (⟨L, f, []⟩ : STape Γ) (some (s, .right)))
      ≠ actOnG b (padRN b (n + 1) (⟨L, f, []⟩ : STape Γ)) (some (s, .right)) := by
  intro hcon
  have h : List.replicate (n + 1) b = List.replicate n b := congrArg STape.right hcon
  have := congrArg List.length h
  simp at this

/-- **The right reservoir commutes with a composite** that stays inside the
stored width. -/
theorem padRN_actList (b : Γ) (n : ℕ) (T : STape Γ) (as : List (Act Γ))
    (h : pos T + as.length ≤ wlen T) :
    padRN b n (actList b T as) = actList b (padRN b n T) as := by
  induction as generalizing T with
  | nil => rfl
  | cons a as ih =>
      simp only [List.length_cons] at h
      have hlt : pos T < wlen T := by omega
      have hr : T.right ≠ [] := right_ne_nil_of_pos_lt_wlen hlt
      have hw : wlen (actOnG b T a) = wlen T := wlen_actOnG b T a hr
      have hp : pos (actOnG b T a) ≤ pos T + 1 :=
        PalPeg.CloseoutCoreEnc13.pos_actOnG_le b T a
      have hnext : pos (actOnG b T a) + as.length ≤ wlen (actOnG b T a) := by omega
      rw [actList_cons, ih _ hnext, padRN_actOnG b n T a hr, actList_cons]

@[simp] theorem pos_shift1' (b : Γ) (T : STape Γ) : pos (shift1 b T) = pos T + 1 :=
  pos_shift1 b T

@[simp] theorem wlen_shift1 (b : Γ) (T : STape Γ) : wlen (shift1 b T) = wlen T + 1 := by
  simp only [wlen, shift1, pos, List.length_append, List.length_cons, List.length_nil]
  omega

/-- **The full layout transport of a composite at one address.** -/
theorem padTapesN_actList (b : Γ) (n : ℕ) (T : STape Γ) (as : List (Act Γ))
    (hleft : as.length ≤ pos T) (hright : pos T + as.length ≤ wlen T) :
    padRN b n (shift1 b (actList b T as))
      = actList b (padRN b n (shift1 b T)) as := by
  rw [shift1_actList b T as hleft]
  refine padRN_actList b n (shift1 b T) as ?_
  rw [pos_shift1', wlen_shift1]
  omega

/-! ## 3. The two branches, transported to `padTapesN` -/

variable {P : ℕ}

open PalPeg.GalilScaffoldController (Control)

theorem mapTape_wlen (t : STape PalPeg.LocalCounter.Seg) :
    wlen (mapTape segSym t) = wlen t := by
  simp [wlen, mapTape, pos]

/-- **`chooseSelect` at the slot's address, on the layout the residual uses.** -/
theorem chooseVm_padTapesN_slot (n : ℕ) (rep : ChainVM → ChainL) (c : Control)
    (m : Mirrored1 P) (j : Fin P) (hleft : 2 ≤ pos (m.vm.phys j))
    (hright : pos (m.vm.phys j) + 2 ≤ wlen (m.vm.phys j)) :
    ∃ as : List (Act Γc), as.length ≤ 2 ∧
      padTapesN n rep ⟨PalPeg.LocalTick3.chooseVm c m.vm, m.mirL⟩ (slotIdx j : ℕ)
        = actList blankc (padTapesN n rep m (slotIdx j : ℕ)) as := by
  obtain ⟨as, has, h⟩ := PalPeg.CloseoutCoreEnc14.chooseVm_tapeActList rep c m j
  refine ⟨as, has, ?_⟩
  have hpos : pos (encTapes rep m (slotIdx j : ℕ)) = pos (m.vm.phys j) := by
    rw [PalPeg.CloseoutCoreEnc14.encTapes_slotIdx]
    exact PalPeg.CloseoutCoreEnc14.mapTape_pos _
  have hwl : wlen (encTapes rep m (slotIdx j : ℕ)) = wlen (m.vm.phys j) := by
    rw [PalPeg.CloseoutCoreEnc14.encTapes_slotIdx]
    exact mapTape_wlen _
  rw [PalPeg.CloseoutCoreEnc8.padTapesN, PalPeg.CloseoutCoreEnc8.padTapesN,
    PalPeg.CloseoutCoreEnc3.encTapes1, PalPeg.CloseoutCoreEnc3.encTapes1, h]
  exact padTapesN_actList blankc n _ as (by omega) (by omega)

/-- **`shiftPick`'s bank half at the slot's address**, on the same layout. -/
theorem shiftVm_padTapesN_slot (n : ℕ) (rep : ChainVM → ChainL)
    (w : PalPeg.GalilScaffoldChainWatch.State) (m : Mirrored1 P) (j : Fin P)
    (hleft : 2 ≤ pos (m.vm.phys j))
    (hright : pos (m.vm.phys j) + 2 ≤ wlen (m.vm.phys j)) :
    ∃ as : List (Act Γc), as.length ≤ 2 ∧
      padTapesN n rep ⟨PalPeg.LocalTick3.shiftVm w m.vm, m.mirL⟩ (slotIdx j : ℕ)
        = actList blankc (padTapesN n rep m (slotIdx j : ℕ)) as := by
  obtain ⟨as, has, h⟩ := PalPeg.CloseoutCoreEnc14.shiftVm_tapeActList rep w m j
  refine ⟨as, has, ?_⟩
  have hpos : pos (encTapes rep m (slotIdx j : ℕ)) = pos (m.vm.phys j) := by
    rw [PalPeg.CloseoutCoreEnc14.encTapes_slotIdx]
    exact PalPeg.CloseoutCoreEnc14.mapTape_pos _
  have hwl : wlen (encTapes rep m (slotIdx j : ℕ)) = wlen (m.vm.phys j) := by
    rw [PalPeg.CloseoutCoreEnc14.encTapes_slotIdx]
    exact mapTape_wlen _
  rw [PalPeg.CloseoutCoreEnc8.padTapesN, PalPeg.CloseoutCoreEnc8.padTapesN,
    PalPeg.CloseoutCoreEnc3.encTapes1, PalPeg.CloseoutCoreEnc3.encTapes1, h]
  exact padTapesN_actList blankc n _ as (by omega) (by omega)

/-! ## 4. The margin at the slot's address, exactly -/

/-- **The head of the laid-out slot**: one sentinel to the left of the counter's
own head, and the reservoir adds nothing. -/
theorem pos_padTapesN_slot (n : ℕ) (rep : ChainVM → ChainL) (m : Mirrored1 P) (j : Fin P) :
    pos (padTapesN n rep m (slotIdx j : ℕ)) = pos (m.vm.phys j) + 1 := by
  rw [padTapesN_slotIdx, pos_padRN, pos_shift1, PalPeg.CloseoutCoreEnc14.mapTape_pos]

/-- **The radius-`K` margin at the slot's address** is exactly the counter's own
left margin plus the single sentinel. -/
theorem margin_padTapesN_slot (K n : ℕ) (rep : ChainVM → ChainL) (m : Mirrored1 P)
    (j : Fin P) (h : K ≤ pos (m.vm.phys j) + 1) :
    K ≤ pos (padTapesN n rep m (slotIdx j : ℕ)) := by
  rw [pos_padTapesN_slot]; exact h

/-! ## 5. Which other addresses `chooseSelect` fixes -/

/-- **The six cursor blocks are untouched by `chooseSelect`.** -/
theorem chooseVm_encTapes_view (rep : ChainVM → ChainL) (c : Control) (m : Mirrored1 P)
    (i : ℕ) (hi : i < nViews * tView) :
    encTapes rep ⟨PalPeg.LocalTick3.chooseVm c m.vm, m.mirL⟩ i = encTapes rep m i := by
  have h6 : nViews * tView = 6 * tView := by unfold nViews; ring
  rw [h6] at hi
  have e1 : (PalPeg.LocalTick3.chooseVm c m.vm).left = m.vm.left := rfl
  have e2 : (PalPeg.LocalTick3.chooseVm c m.vm).center = m.vm.center := rfl
  have e3 : (PalPeg.LocalTick3.chooseVm c m.vm).right = m.vm.right := rfl
  have e4 : (PalPeg.LocalTick3.chooseVm c m.vm).walkerView = m.vm.walkerView := rfl
  have e5 : (PalPeg.LocalTick3.chooseVm c m.vm).fppWalker = m.vm.fppWalker := rfl
  by_cases c1 : i < tView
  · simp only [encTapes, if_pos c1, e1]
  by_cases c2 : i < 2 * tView
  · simp only [encTapes, if_neg c1, if_pos c2, e2]
  by_cases c3 : i < 3 * tView
  · simp only [encTapes, if_neg c1, if_neg c2, if_pos c3, e3]
  by_cases c4 : i < 4 * tView
  · simp only [encTapes, if_neg c1, if_neg c2, if_neg c3, if_pos c4, e4]
  by_cases c5 : i < 5 * tView
  · simp only [encTapes, if_neg c1, if_neg c2, if_neg c3, if_neg c4, if_pos c5, e5]
  · have c6 : i < 6 * tView := hi
    simp only [encTapes, if_neg c1, if_neg c2, if_neg c3, if_neg c4, if_neg c5, if_pos c6]

#print axioms wlen_actOnG
#print axioms shift1_actList
#print axioms shift1_actOnG_left_edge
#print axioms padRN_actList
#print axioms padRN_actOnG_right_edge
#print axioms padTapesN_actList
#print axioms chooseVm_padTapesN_slot
#print axioms shiftVm_padTapesN_slot
#print axioms pos_padTapesN_slot
#print axioms margin_padTapesN_slot
#print axioms chooseVm_encTapes_view

end PalPeg.CloseoutCoreEnc15
