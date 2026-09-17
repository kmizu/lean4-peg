import PalPeg.CloseoutCoreEnc13

/-!
# Closeout, step 2n: the slot alphabet inside the core alphabet, and the address of a slot

`CloseoutCoreEnc13` lists as its **missing fact 1** the embedding of the slot
alphabet `Seg = Fin 3` into the core alphabet `Γc`, together with the index of
bank slot `j` in `Fin (tL P tChain)`, "without which §1's action lists cannot be
transported into a `TapeActK`".  This file supplies both, and transports §2's
two branch budgets (`chooseVm_phys_actList`, `shiftVm_phys_actList`) and §3's
sign read (`segCtr_rd_pred`) across them.  Nothing here is about the whole
machine, so

**無条件 PAL ∈ PEG は未完.**

## What is established (unconditional)

* **§1 (the embedding).**  `embAct` recodes one `CloseoutCoreEnc12.Act Seg` into
  one `Act Γc` along `CloseoutCoreEnc.segSym` (which is injective and
  blank-preserving).  `mapTape_actOnG` and `mapTape_actList` say the recoding is
  a *simulation on the nose*: `mapTape segSym` commutes with `actOnG`/`actList`
  with **no** side condition — in particular the left-edge branch of
  `STape.applyAction` is preserved, because `mapTape` does not change which of
  `left`/`right` is empty.
* **§2 (the address).**  `slotIdx j : Fin (tL P tChain)` is
  `nViews * tView + j` (`= 24 + j`), the place where `CloseoutCoreEnc.encTapes`
  puts `mapTape segSym (m.vm.phys j)`; `encTapes_slotIdx` is that identity, and
  `encTapes1_slotIdx` / `padTapesN_slotIdx` push it through the sentinel shift
  and the right reservoir.  `slotIdx_inj` and `slotIdx_ne_view` record that the
  bank occupies `P` distinct indices, disjoint from the six cursor blocks.
* **§3 (the transport of the two branches).**  `chooseVm_tapeActList` and
  `shiftVm_tapeActList`: for the successor state of either branch, the tape at
  address `slotIdx j` of the **raw** layout `encTapes` is
  `actList blankc (encTapes rep m (slotIdx j)) as` for a list `as : List (Act Γc)`
  of length `≤ 2`, namely the `embAct`-image of the slot list of
  `CloseoutCoreEnc13` §2.  This is the `Γc`-side statement the `TapeActK` field
  `tape` asks for, at the layout the `Kc = 1` files already use.
* **§4 (the sign cell, named in `Γc`).**  `segCtr_rd_pred_enc`: under
  `LocalCounter.SegCtr t v` the cell one step left of the head of
  `mapTape segSym t` is `segSym sep` when `v = 0` and `segSym mark` when
  `v > 0`, and `segSym_sep_ne_mark` separates the two — so §3 of `Enc13` names a
  cell of the **core** alphabet, as missing fact 1 asked.

## What is *not* established, one line each

1. **The `TapeActK` instance itself.**  §3 lands on `encTapes`, not on
   `padTapesN`: `actList` does **not** commute with `CloseoutCoreEnc3.shift1`
   when a left move happens at the left edge (`⟨[], w, R⟩` vs `⟨[b], w, R⟩`),
   nor with `CloseoutCoreEnc8.padRN` when a right move consumes a reservoir
   cell, so `chooseVm_tapeActK` / `shiftVm_tapeActK` need the head invariants
   `0 < pos` and `pos + 2 ≤ wlen` for the slot tape — i.e. the very margin of
   `CloseoutCoreEnc13` obstruction 3 — plus the same transport for the *other*
   `tL P tChain - P` addresses, which the two branches leave fixed only if the
   cursors and buffers are untouched (not proved here).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutCoreEnc14

open PalPeg PalPeg.Program
open PalPeg.Local (pos rd)
open PalPeg.CloseoutCoreStep (Γc blankc tL nViews tView)
open PalPeg.CloseoutCoreEnc (tChain segSym segSym_inj mapTape encTapes)
open PalPeg.CloseoutCoreEnc12 (Act actOnG actList actList_cons)
open PalPeg.LocalCounter (Seg)
open PalPeg.LocalState (GalilVML)
open PalPeg.LocalReplayParked (Mirrored1)
open PalPeg.LocalChain (ChainL)
open PalPeg.GalilScaffoldChainInputSupply (ChainVM)

/-! ## 1. The slot alphabet inside the core alphabet -/

/-- **The embedding of one slot micro-action into the core alphabet.** -/
def embAct (a : Act Seg) : Act Γc :=
  match a with
  | none => none
  | some (s, mv) => some (segSym s, mv)

/-- The embedding of a composite. -/
def embActs (as : List (Act Seg)) : List (Act Γc) := as.map embAct

@[simp] theorem embActs_length (as : List (Act Seg)) : (embActs as).length = as.length := by
  simp [embActs]

@[simp] theorem embActs_nil : embActs [] = [] := rfl

theorem embActs_cons (a : Act Seg) (as : List (Act Seg)) :
    embActs (a :: as) = embAct a :: embActs as := rfl

/-- **The recoding is a simulation on the nose, for one micro-action.**  No side
condition: `mapTape` preserves which of `left`/`right` is empty, so even the
left-edge branch of `STape.applyAction` is matched. -/
theorem mapTape_actOnG (T : STape Seg) (a : Act Seg) :
    mapTape segSym (actOnG PalPeg.LocalCounter.blank T a)
      = actOnG blankc (mapTape segSym T) (embAct a) := by
  obtain ⟨L, f, R⟩ := T
  cases a with
  | none => rfl
  | some sm =>
      obtain ⟨s, mv⟩ := sm
      cases mv with
      | stay => rfl
      | right =>
          cases R with
          | nil => rfl
          | cons n R => rfl
      | left =>
          cases L with
          | nil => rfl
          | cons n L => rfl

/-- **The recoding is a simulation on the nose, for a composite.** -/
theorem mapTape_actList (T : STape Seg) (as : List (Act Seg)) :
    mapTape segSym (actList PalPeg.LocalCounter.blank T as)
      = actList blankc (mapTape segSym T) (embActs as) := by
  induction as generalizing T with
  | nil => rfl
  | cons a as ih =>
      rw [actList_cons, ih, embActs_cons, actList_cons, mapTape_actOnG]

/-! ## 2. The address of a bank slot -/

variable {P : ℕ}

theorem slotIdx_lt (j : Fin P) : nViews * tView + (j : ℕ) < tL P tChain := by
  have hj := j.isLt
  have h : 0 < tChain := by
    unfold PalPeg.CloseoutCoreEnc.tChain
    positivity
  unfold tL
  have h2 : 0 < PalPeg.CloseoutCoreStep.tMir := by
    unfold PalPeg.CloseoutCoreStep.tMir; omega
  omega

/-- **The address of bank slot `j`** in the core's tape family. -/
def slotIdx (j : Fin P) : Fin (tL P tChain) := ⟨nViews * tView + (j : ℕ), slotIdx_lt j⟩

theorem slotIdx_val (j : Fin P) : (slotIdx j : ℕ) = nViews * tView + (j : ℕ) := rfl

theorem slotIdx_inj : Function.Injective (slotIdx (P := P)) := by
  intro a b h
  have : nViews * tView + (a : ℕ) = nViews * tView + (b : ℕ) := congrArg Fin.val h
  exact Fin.ext (by omega)

/-- The bank block starts after the six cursor blocks. -/
theorem slotIdx_ne_view (j : Fin P) : nViews * tView ≤ (slotIdx j : ℕ) := by
  rw [slotIdx_val]; omega

/-- **The layout puts the slot tape at its address.** -/
theorem encTapes_slotIdx (rep : ChainVM → ChainL) (m : Mirrored1 P) (j : Fin P) :
    encTapes rep m (slotIdx j : ℕ) = mapTape segSym (m.vm.phys j) := by
  have h1 : ¬ (nViews * tView + (j : ℕ) < tView) := by unfold nViews tView; omega
  have h2 : ¬ (nViews * tView + (j : ℕ) < 2 * tView) := by unfold nViews tView; omega
  have h3 : ¬ (nViews * tView + (j : ℕ) < 3 * tView) := by unfold nViews tView; omega
  have h4 : ¬ (nViews * tView + (j : ℕ) < 4 * tView) := by unfold nViews tView; omega
  have h5 : ¬ (nViews * tView + (j : ℕ) < 5 * tView) := by unfold nViews tView; omega
  have h6 : ¬ (nViews * tView + (j : ℕ) < 6 * tView) := by unfold nViews tView; omega
  have h7 : nViews * tView + (j : ℕ) - nViews * tView = (j : ℕ) := by omega
  simp only [encTapes, slotIdx_val, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5,
    if_neg h6, h7, dif_pos j.isLt]

/-- The same, through the sentinel shift. -/
theorem encTapes1_slotIdx (rep : ChainVM → ChainL) (m : Mirrored1 P) (j : Fin P) :
    PalPeg.CloseoutCoreEnc3.encTapes1 rep m (slotIdx j : ℕ)
      = PalPeg.CloseoutCoreEnc3.shift1 blankc (mapTape segSym (m.vm.phys j)) := by
  rw [PalPeg.CloseoutCoreEnc3.encTapes1, encTapes_slotIdx]

/-- The same, through the right reservoir. -/
theorem padTapesN_slotIdx (n : ℕ) (rep : ChainVM → ChainL) (m : Mirrored1 P) (j : Fin P) :
    PalPeg.CloseoutCoreEnc8.padTapesN n rep m (slotIdx j : ℕ)
      = PalPeg.CloseoutCoreEnc8.padRN blankc n
          (PalPeg.CloseoutCoreEnc3.shift1 blankc (mapTape segSym (m.vm.phys j))) := by
  rw [PalPeg.CloseoutCoreEnc8.padTapesN, encTapes1_slotIdx]

/-! ## 3. The two branches, transported to `Γc` -/

open PalPeg.GalilScaffoldController (Control)

/-- **`chooseSelect` at the slot's address, in the core alphabet.** -/
theorem chooseVm_tapeActList (rep : ChainVM → ChainL) (c : Control) (m : Mirrored1 P)
    (j : Fin P) :
    ∃ as : List (Act Γc), as.length ≤ 2 ∧
      encTapes rep ⟨PalPeg.LocalTick3.chooseVm c m.vm, m.mirL⟩ (slotIdx j : ℕ)
        = actList blankc (encTapes rep m (slotIdx j : ℕ)) as := by
  obtain ⟨as, has, h⟩ :=
    PalPeg.CloseoutCoreEnc13.chooseVm_phys_actList (P := P) c m.vm j
  refine ⟨embActs as, by simpa using has, ?_⟩
  rw [encTapes_slotIdx, encTapes_slotIdx]
  show mapTape segSym ((PalPeg.LocalTick3.chooseVm c m.vm).phys j) = _
  rw [h, mapTape_actList]

/-- **`shiftPick`'s bank half at the slot's address, in the core alphabet.** -/
theorem shiftVm_tapeActList (rep : ChainVM → ChainL)
    (w : PalPeg.GalilScaffoldChainWatch.State) (m : Mirrored1 P) (j : Fin P) :
    ∃ as : List (Act Γc), as.length ≤ 2 ∧
      encTapes rep ⟨PalPeg.LocalTick3.shiftVm w m.vm, m.mirL⟩ (slotIdx j : ℕ)
        = actList blankc (encTapes rep m (slotIdx j : ℕ)) as := by
  obtain ⟨as, has, h⟩ :=
    PalPeg.CloseoutCoreEnc13.shiftVm_phys_actList (P := P) w m.vm j
  refine ⟨embActs as, by simpa using has, ?_⟩
  rw [encTapes_slotIdx, encTapes_slotIdx]
  show mapTape segSym ((PalPeg.LocalTick3.shiftVm w m.vm).phys j) = _
  rw [h, mapTape_actList]

/-! ## 4. The sign cell, named in `Γc` -/

theorem segSym_sep_ne_mark :
    segSym PalPeg.LocalCounter.sep ≠ segSym PalPeg.LocalCounter.mark := by
  intro h
  exact PalPeg.LocalCounter.sep_ne_mark (segSym_inj h)

theorem mapTape_pos (T : STape Seg) : pos (mapTape segSym T) = pos T := by
  simp [mapTape, pos]

theorem mapTape_rd (T : STape Seg) (p : ℕ) :
    rd blankc (mapTape segSym T) p = segSym (rd PalPeg.LocalCounter.blank T p) := by
  have hb : blankc = segSym PalPeg.LocalCounter.blank := rfl
  obtain ⟨L, f, R⟩ := T
  show ((L.map segSym).reverse ++ segSym f :: R.map segSym).getD p blankc
      = segSym ((L.reverse ++ f :: R).getD p PalPeg.LocalCounter.blank)
  have hl : (L.map segSym).reverse ++ segSym f :: R.map segSym
      = (L.reverse ++ f :: R).map segSym := by
    simp [List.map_append, List.map_reverse]
  rw [hl, hb]
  exact PalPeg.CloseoutCoreEnc.getD_map segSym _ _ p

/-- **The sign cell of a laid-out counter, in the core alphabet.** -/
theorem segCtr_rd_pred_enc {t : STape Seg} {v : ℕ} (h : PalPeg.LocalCounter.SegCtr t v) :
    rd blankc (mapTape segSym t) (pos (mapTape segSym t) - 1)
      = if v = 0 then segSym PalPeg.LocalCounter.sep else segSym PalPeg.LocalCounter.mark := by
  rw [mapTape_pos, mapTape_rd, PalPeg.CloseoutCoreEnc13.segCtr_rd_pred h]
  by_cases hv : v = 0 <;> simp [hv]

#print axioms mapTape_actList
#print axioms encTapes_slotIdx
#print axioms chooseVm_tapeActList
#print axioms shiftVm_tapeActList
#print axioms segCtr_rd_pred_enc

end PalPeg.CloseoutCoreEnc14
