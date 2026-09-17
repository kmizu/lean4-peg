import PalPeg.CloseoutCoreEnc15

/-!
# Closeout, step 2p: `chooseSelect` is a composite residual at **every** address

`CloseoutCoreEnc15` transports `LocalTick3.chooseVm` to `padTapesN` at the slot
addresses (`chooseVm_padTapesN_slot`) and shows the six cursor blocks are fixed
(`chooseVm_encTapes_view`), but lists as its missing fact 1 that the `TapeActK`
residual of `CloseoutCoreEnc13` §5 quantifies over *every* index `i`, and that
the three mirror banks (`radiusMir`, `lowerMir`, `lengthMir`, at the addresses
`nViews * tView + P + 0 … 6`) also move.  This file closes that gap **for
`chooseVm`**: it makes the per-address micro-action list an explicit function of
the encoded control (the roles table is a component of `QL`), proves the tape
law at every address, and assembles the `TapeActK` instance.  Nothing here is
about the whole machine, so

**無条件 PAL ∈ PEG は未完.**

## What is established (unconditional)

* **§1 (the roles table is readable from the encoded control).**  `rolesOfQ`
  projects the tenth component of `QL`, and `rolesOfQ_encPadN` says it is
  `m.vm.roles` on the nose — so a *function of `q`* may branch on which logical
  counter owns a slot, which is what `TapeActK.acts` needs.
* **§2 (the slot list, explicitly).**  `opAt` names the at-most-one action a
  bank tick performs on slot `j`, `bankStep_opAt` replaces the existential of
  `CloseoutCoreEnc13.bankStep_actList` by this function, and
  `chooseVm_phys_chooseSlotActs` gives `chooseVm`'s slot list
  `chooseSlotActs R j` (length `≤ 2`) as a function of the roles table alone.
* **§3 (the mirror block).**  `encTapes_mirIdx` names the seven mirror addresses,
  and `chooseVm_radiusMir` / `lowerMir` / `lengthMir` compute them: `radiusMir`
  is one `resetSeg`, `lengthMir` one `push`, `lowerMir` is fixed.
* **§4 (every address).**  `chooseActs` is the total micro-action list, of length
  `≤ 2` everywhere (`chooseActs_length`), and `chooseVm_encTapes_all` proves
  `encTapes rep (chooseVm …) i = actList blankc (encTapes rep m i) (chooseActs …
  i)` for **all** `i` — unconditionally, no head invariant needed.
  `chooseVm_padTapesN_all` is the same on the laid-out family, under the two
  layout invariants `CloseoutCoreEnc15` §2 asks for, stated uniformly over the
  addresses.
* **§5 (the instance).**  `chooseVm_tapeActK` builds
  `CloseoutCoreEnc13.TapeActK` for `chooseVm` at any radius `2 ≤ K`, taking the
  finite-control component (`nq` together with its law `hctl`) as data.

## What is *not* established, one line each

1. **The control component is a hypothesis**: `chooseVm_tapeActK` receives `nq`
   and `hctl`, because `qOfL` of `chooseVm c m.vm` changes the clamped control,
   the roles-independent counter summaries and `pol` in a way no lemma here
   computes; only the tape half of the residual is discharged.
2. **The two head invariants (and hence the margin) are assumed**, as
   `CloseoutCoreEnc15` missing fact 2 says: they must come from the counter
   layout `LocalCounter.SegCtr` at each address, not from the reservoir `n`.
3. **`shiftVm` is not covered**: `shiftPick` also advances the `left`, `center`
   and chain cursors, so §4's view-fixity input (`CloseoutCoreEnc15` §5) fails
   for it and it needs its own per-block list.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutCoreEnc16

open PalPeg PalPeg.Program
open PalPeg.Local (pos)
open PalPeg.CloseoutCoreStep (Γc blankc tL QL nViews tView qOfL)
open PalPeg.CloseoutCoreEnc (QChain tChain segSym mapTape encTapes)
open PalPeg.CloseoutCoreEnc5 (wlen)
open PalPeg.CloseoutCoreEnc8 (padTapesN encPadN)
open PalPeg.CloseoutCoreEnc12 (Act actList actList_cons)
open PalPeg.CloseoutCoreEnc13 (opActs op_apply_eq_actList actList_append TapeActK)
open PalPeg.CloseoutCoreEnc14 (embAct embActs embActs_length slotIdx slotIdx_val mapTape_actList)
open PalPeg.LocalCounter (Seg)
open PalPeg.LocalState (GalilVML Ctr)
open PalPeg.LocalTick3 (Op bankStep bankTick mirOp chooseOps1 chooseOps2 chooseVm)
open PalPeg.LocalReplayParked (Mirrored1)
open PalPeg.LocalChain (ChainL)
open PalPeg.GalilScaffoldChainInputSupply (ChainVM)
open PalPeg.GalilScaffoldController (Control Mode)
open PalPeg.LocalSysConcrete (Starved)

variable {P : ℕ}

/-! ## 1. The roles table, read off the encoded control -/

/-- **The roles component of `QL`.** -/
def rolesOfQ {delay Lp Lf : ℕ} {QC : Type} (q : QL delay Lp Lf P QC) : Ctr → Fin P :=
  q.2.2.2.2.2.2.2.2.2.1

@[simp] theorem rolesOfQ_qOfL (delay Lp Lf : ℕ) {QC : Type} (encChain : ChainVM → QC)
    (m : Mirrored1 P) : rolesOfQ (qOfL delay Lp Lf encChain m) = m.vm.roles := rfl

@[simp] theorem rolesOfQ_encPadN (n delay Lp Lf : ℕ) (rep : ChainVM → ChainL)
    (m : Mirrored1 P) : rolesOfQ (encPadN n delay Lp Lf rep m).1 = m.vm.roles := rfl

/-! ## 2. The slot list, as a function of the roles table -/

/-- The micro-action list a bank tick performs on slot `j`. -/
noncomputable def opAt (f : Ctr → Op) (R : Ctr → Fin P) (j : Fin P) : List (Act Seg) := by
  classical
  exact if h : ∃ c, R c = j then opActs (f (Classical.choose h)) else []

theorem opAt_length (f : Ctr → Op) (R : Ctr → Fin P) (j : Fin P) : (opAt f R j).length ≤ 1 := by
  classical
  unfold opAt
  by_cases h : ∃ c, R c = j
  · simp only [dif_pos h]; exact PalPeg.CloseoutCoreEnc13.opActs_length _
  · simp [dif_neg h]

/-- **`CloseoutCoreEnc13.bankStep_actList`, with the list named.** -/
theorem bankStep_opAt (f : Ctr → Op) (x : GalilVML P) (j : Fin P) :
    bankStep f x j = actList PalPeg.LocalCounter.blank (x.phys j) (opAt f x.roles j) := by
  classical
  by_cases h : ∃ c, x.roles c = j
  · have h1 : bankStep f x j = (f (Classical.choose h)).apply (x.phys j) := by
      simp only [bankStep, dif_pos h]
    rw [h1, op_apply_eq_actList]
    unfold opAt
    simp only [dif_pos h]
  · have h1 : bankStep f x j = x.phys j := by simp only [bankStep, dif_neg h]
    rw [h1]
    unfold opAt
    simp only [dif_neg h]
    rfl

/-- **The slot list of `chooseSelect`**, a function of the roles table. -/
noncomputable def chooseSlotActs (R : Ctr → Fin P) (j : Fin P) : List (Act Γc) :=
  embActs (opAt chooseOps1 R j ++ opAt chooseOps2 R j)

theorem chooseSlotActs_length (R : Ctr → Fin P) (j : Fin P) :
    (chooseSlotActs R j).length ≤ 2 := by
  unfold chooseSlotActs
  rw [embActs_length, List.length_append]
  have := opAt_length chooseOps1 R j
  have := opAt_length chooseOps2 R j
  omega

theorem chooseVm_phys_chooseSlotActs (c : Control) (x : GalilVML P) (j : Fin P) :
    mapTape segSym ((chooseVm c x).phys j)
      = actList blankc (mapTape segSym (x.phys j)) (chooseSlotActs x.roles j) := by
  have h0 : (chooseVm c x).phys j = bankStep chooseOps2 (bankTick chooseOps1 x) j := rfl
  have hr : (bankTick chooseOps1 x).roles = x.roles := rfl
  have h1 : bankStep chooseOps2 (bankTick chooseOps1 x) j
      = actList PalPeg.LocalCounter.blank ((bankTick chooseOps1 x).phys j)
        (opAt chooseOps2 x.roles j) := by
    rw [← hr]; exact bankStep_opAt _ _ j
  have h2 : (bankTick chooseOps1 x).phys j
      = actList PalPeg.LocalCounter.blank (x.phys j) (opAt chooseOps1 x.roles j) :=
    bankStep_opAt _ _ j
  rw [h0, h1, h2, ← actList_append]
  unfold chooseSlotActs
  rw [mapTape_actList]

/-! ## 3. The mirror block -/

/-- **The seven mirror addresses of the layout.** -/
theorem encTapes_mirIdx (rep : ChainVM → ChainL) (m : Mirrored1 P) (k : ℕ)
    (hk : k < 7) :
    encTapes rep m (nViews * tView + P + k)
      = (if k = 0 then mapTape segSym m.vm.radiusMir.src
         else if k = 1 then mapTape segSym (m.vm.radiusMir.mir 0)
         else if k = 2 then mapTape segSym (m.vm.radiusMir.mir 1)
         else if k = 3 then mapTape segSym m.vm.lowerMir.src
         else if k = 4 then mapTape segSym (m.vm.lowerMir.mir 0)
         else if k = 5 then mapTape segSym m.vm.lengthMir.src
         else mapTape segSym (m.vm.lengthMir.mir 0)) := by
  have h1 : ¬ (nViews * tView + P + k < tView) := by unfold nViews tView; omega
  have h2 : ¬ (nViews * tView + P + k < 2 * tView) := by unfold nViews tView; omega
  have h3 : ¬ (nViews * tView + P + k < 3 * tView) := by unfold nViews tView; omega
  have h4 : ¬ (nViews * tView + P + k < 4 * tView) := by unfold nViews tView; omega
  have h5 : ¬ (nViews * tView + P + k < 5 * tView) := by unfold nViews tView; omega
  have h6 : ¬ (nViews * tView + P + k < 6 * tView) := by unfold nViews tView; omega
  have hd : ¬ (nViews * tView + P + k - nViews * tView < P) := by omega
  have hj : nViews * tView + P + k - nViews * tView - P = k := by omega
  simp only [encTapes, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6,
    dif_neg hd, hj]
  interval_cases k <;> simp

/-- One counter op, recoded into the core alphabet, is a composite. -/
theorem mir_act (o : Op) (t : STape Seg) :
    mapTape segSym (o.apply t) = actList blankc (mapTape segSym t) (embActs (opActs o)) := by
  rw [op_apply_eq_actList, mapTape_actList]

/-- **`chooseSelect` resets the radius mirror bank**: one micro-action on each of
its three tapes. -/
theorem chooseVm_radiusMir_src (c : Control) (x : GalilVML P) :
    (chooseVm c x).radiusMir.src = Op.reset.apply x.radiusMir.src := rfl

theorem chooseVm_radiusMir_mir0 (c : Control) (x : GalilVML P) :
    (chooseVm c x).radiusMir.mir 0 = Op.reset.apply (x.radiusMir.mir 0) := rfl

theorem chooseVm_radiusMir_mir1 (c : Control) (x : GalilVML P) :
    (chooseVm c x).radiusMir.mir 1 = Op.reset.apply (x.radiusMir.mir 1) := rfl

/-- **`chooseSelect` leaves the lower mirror bank fixed.** -/
theorem chooseVm_lowerMir_src (c : Control) (x : GalilVML P) :
    (chooseVm c x).lowerMir.src = x.lowerMir.src := rfl

theorem chooseVm_lowerMir_mir0 (c : Control) (x : GalilVML P) :
    (chooseVm c x).lowerMir.mir 0 = x.lowerMir.mir 0 := rfl

/-- **`chooseSelect` pushes on the length mirror bank.** -/
theorem chooseVm_lengthMir_src (c : Control) (x : GalilVML P) :
    (chooseVm c x).lengthMir.src = Op.push.apply (Op.reset.apply x.lengthMir.src) := rfl

theorem chooseVm_lengthMir_mir0 (c : Control) (x : GalilVML P) :
    (chooseVm c x).lengthMir.mir 0 = Op.push.apply (Op.reset.apply (x.lengthMir.mir 0)) := rfl

/-- Two counter ops, recoded, are a composite of two micro-actions. -/
theorem mir_act2 (o1 o2 : Op) (t : STape Seg) :
    mapTape segSym (o2.apply (o1.apply t))
      = actList blankc (mapTape segSym t) (embActs (opActs o1 ++ opActs o2)) := by
  rw [op_apply_eq_actList o2, op_apply_eq_actList o1, ← actList_append, mapTape_actList]

/-- **The addresses past the mirror block are fixed by `chooseSelect`.** -/
theorem chooseVm_encTapes_tail (rep : ChainVM → ChainL) (c : Control) (m : Mirrored1 P)
    (i : ℕ) (hge : nViews * tView + P ≤ i) (hk : 7 ≤ i - nViews * tView - P) :
    encTapes rep ⟨chooseVm c m.vm, m.mirL⟩ i = encTapes rep m i := by
  have hv : nViews * tView = 24 := by unfold nViews tView; omega
  have h1 : ¬ (i < tView) := by unfold tView; omega
  have h2 : ¬ (i < 2 * tView) := by unfold tView; omega
  have h3 : ¬ (i < 3 * tView) := by unfold tView; omega
  have h4 : ¬ (i < 4 * tView) := by unfold tView; omega
  have h5 : ¬ (i < 5 * tView) := by unfold tView; omega
  have h6 : ¬ (i < 6 * tView) := by unfold tView; omega
  have hd : ¬ (i - nViews * tView < P) := by omega
  have hn0 : ¬ (i - nViews * tView - P = 0) := by omega
  have hn1 : ¬ (i - nViews * tView - P = 1) := by omega
  have hn2 : ¬ (i - nViews * tView - P = 2) := by omega
  have hn3 : ¬ (i - nViews * tView - P = 3) := by omega
  have hn4 : ¬ (i - nViews * tView - P = 4) := by omega
  have hn5 : ¬ (i - nViews * tView - P = 5) := by omega
  have hn6 : ¬ (i - nViews * tView - P = 6) := by omega
  simp only [encTapes, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6,
    dif_neg hd, if_neg hn0, if_neg hn1, if_neg hn2, if_neg hn3, if_neg hn4, if_neg hn5,
    if_neg hn6]
  rfl

/-! ## 4. The micro-action list at every address -/

/-- **The total micro-action list of `chooseSelect`**, a function of the roles
table alone. -/
noncomputable def chooseActs (R : Ctr → Fin P) (i : ℕ) : List (Act Γc) :=
  if i < nViews * tView then []
  else if h : i - nViews * tView < P then chooseSlotActs R ⟨_, h⟩
  else
    if i - nViews * tView - P ≤ 2 then embActs (opActs Op.reset)
    else if i - nViews * tView - P = 5 ∨ i - nViews * tView - P = 6 then
      embActs (opActs Op.reset ++ opActs Op.push)
    else []

theorem chooseActs_length (R : Ctr → Fin P) (i : ℕ) : (chooseActs R i).length ≤ 2 := by
  unfold chooseActs
  split
  · simp
  · split
    · exact chooseSlotActs_length _ _
    · split
      · simp [embActs, opActs]
      · split <;> simp [embActs, opActs]

theorem chooseActs_view (R : Ctr → Fin P) (i : ℕ) (hi : i < nViews * tView) :
    chooseActs R i = [] := by
  unfold chooseActs; rw [if_pos hi]

theorem chooseActs_slot (R : Ctr → Fin P) (j : Fin P) :
    chooseActs R (slotIdx j : ℕ) = chooseSlotActs R j := by
  have h1 : ¬ ((slotIdx j : ℕ) < nViews * tView) := by rw [slotIdx_val]; omega
  have h2 : (slotIdx j : ℕ) - nViews * tView < P := by rw [slotIdx_val]; simp only [Nat.add_sub_cancel_left]; exact j.isLt
  have h3 : (slotIdx j : ℕ) - nViews * tView = (j : ℕ) := by rw [slotIdx_val]; omega
  unfold chooseActs
  rw [if_neg h1, dif_pos h2]
  congr 1
  exact Fin.ext h3

theorem chooseActs_mir (R : Ctr → Fin P) (k : ℕ) :
    chooseActs R (nViews * tView + P + k)
      = (if k ≤ 2 then embActs (opActs Op.reset)
         else if k = 5 ∨ k = 6 then embActs (opActs Op.reset ++ opActs Op.push)
         else []) := by
  have h1 : ¬ (nViews * tView + P + k < nViews * tView) := by omega
  have h2 : ¬ (nViews * tView + P + k - nViews * tView < P) := by omega
  have h3 : nViews * tView + P + k - nViews * tView - P = k := by omega
  unfold chooseActs
  rw [if_neg h1, dif_neg h2, h3]

/-- **The mirror block, address by address.** -/
theorem chooseVm_encTapes_mir (rep : ChainVM → ChainL) (c : Control) (m : Mirrored1 P)
    (k : ℕ) (hk : k < 7) :
    encTapes rep ⟨chooseVm c m.vm, m.mirL⟩ (nViews * tView + P + k)
      = actList blankc (encTapes rep m (nViews * tView + P + k))
          (chooseActs m.vm.roles (nViews * tView + P + k)) := by
  rw [encTapes_mirIdx rep ⟨chooseVm c m.vm, m.mirL⟩ k hk, encTapes_mirIdx rep m k hk,
    chooseActs_mir]
  interval_cases k
  · show mapTape segSym ((chooseVm c m.vm).radiusMir.src)
        = actList blankc (mapTape segSym m.vm.radiusMir.src) (embActs (opActs Op.reset))
    rw [chooseVm_radiusMir_src]; exact mir_act _ _
  · show mapTape segSym ((chooseVm c m.vm).radiusMir.mir 0)
        = actList blankc (mapTape segSym (m.vm.radiusMir.mir 0)) (embActs (opActs Op.reset))
    rw [chooseVm_radiusMir_mir0]; exact mir_act _ _
  · show mapTape segSym ((chooseVm c m.vm).radiusMir.mir 1)
        = actList blankc (mapTape segSym (m.vm.radiusMir.mir 1)) (embActs (opActs Op.reset))
    rw [chooseVm_radiusMir_mir1]; exact mir_act _ _
  · show mapTape segSym ((chooseVm c m.vm).lowerMir.src)
        = actList blankc (mapTape segSym m.vm.lowerMir.src) []
    rw [chooseVm_lowerMir_src]; rfl
  · show mapTape segSym ((chooseVm c m.vm).lowerMir.mir 0)
        = actList blankc (mapTape segSym (m.vm.lowerMir.mir 0)) []
    rw [chooseVm_lowerMir_mir0]; rfl
  · show mapTape segSym ((chooseVm c m.vm).lengthMir.src)
        = actList blankc (mapTape segSym m.vm.lengthMir.src)
            (embActs (opActs Op.reset ++ opActs Op.push))
    rw [chooseVm_lengthMir_src]; exact mir_act2 _ _ _
  · show mapTape segSym ((chooseVm c m.vm).lengthMir.mir 0)
        = actList blankc (mapTape segSym (m.vm.lengthMir.mir 0))
            (embActs (opActs Op.reset ++ opActs Op.push))
    rw [chooseVm_lengthMir_mir0]; exact mir_act2 _ _ _

/-- **`chooseSelect` is a composite of at most two micro-actions at *every*
address of the raw layout.** -/
theorem chooseVm_encTapes_all (rep : ChainVM → ChainL) (c : Control) (m : Mirrored1 P)
    (i : ℕ) :
    encTapes rep ⟨chooseVm c m.vm, m.mirL⟩ i
      = actList blankc (encTapes rep m i) (chooseActs m.vm.roles i) := by
  by_cases hview : i < nViews * tView
  · rw [chooseActs_view _ _ hview]
    exact PalPeg.CloseoutCoreEnc15.chooseVm_encTapes_view rep c m i
      (by unfold nViews at hview ⊢; omega)
  by_cases hslot : i - nViews * tView < P
  · have hj : i = (slotIdx (P := P) ⟨i - nViews * tView, hslot⟩ : ℕ) := by
      rw [slotIdx_val]
      show i = nViews * tView + (i - nViews * tView)
      omega
    rw [hj, chooseActs_slot, PalPeg.CloseoutCoreEnc14.encTapes_slotIdx,
      PalPeg.CloseoutCoreEnc14.encTapes_slotIdx]
    exact chooseVm_phys_chooseSlotActs c m.vm _
  · have hge : nViews * tView + P ≤ i := by omega
    by_cases hk : i - nViews * tView - P < 7
    · have hi : i = nViews * tView + P + (i - nViews * tView - P) := by omega
      rw [hi]
      exact chooseVm_encTapes_mir rep c m _ hk
    · have h7 : 7 ≤ i - nViews * tView - P := by omega
      have hz : chooseActs m.vm.roles i = [] := by
        unfold chooseActs
        rw [if_neg hview, dif_neg hslot, if_neg (by omega : ¬ (i - nViews * tView - P ≤ 2)),
          if_neg (by omega : ¬ (i - nViews * tView - P = 5 ∨ i - nViews * tView - P = 6))]
      rw [hz]
      exact chooseVm_encTapes_tail rep c m i hge h7

/-- **The same on the laid-out family**, under the two head invariants of
`CloseoutCoreEnc15` §2, stated uniformly over the addresses. -/
theorem chooseVm_padTapesN_all (n : ℕ) (rep : ChainVM → ChainL) (c : Control)
    (m : Mirrored1 P)
    (hleft : ∀ i, 2 ≤ pos (encTapes rep m i))
    (hright : ∀ i, pos (encTapes rep m i) + 2 ≤ wlen (encTapes rep m i)) (i : ℕ) :
    padTapesN n rep ⟨chooseVm c m.vm, m.mirL⟩ i
      = actList blankc (padTapesN n rep m i) (chooseActs m.vm.roles i) := by
  have hlen := chooseActs_length m.vm.roles i
  have h1 := hleft i
  have h2 := hright i
  rw [PalPeg.CloseoutCoreEnc8.padTapesN, PalPeg.CloseoutCoreEnc8.padTapesN,
    PalPeg.CloseoutCoreEnc3.encTapes1, PalPeg.CloseoutCoreEnc3.encTapes1,
    chooseVm_encTapes_all rep c m i]
  exact PalPeg.CloseoutCoreEnc15.padTapesN_actList blankc n _ _ (by omega) (by omega)

/-! ## 5. The `TapeActK` instance -/

open PalPeg.CloseoutCoreEnc13 (rwOfK)

/-- **`chooseSelect` as a radius-`K` composite residual at every address.**  The
tape half is discharged here; the finite-control half is the datum `nq` together
with its law `hctl`. -/
noncomputable def chooseVm_tapeActK (K n delay Lp Lf : ℕ) (rep : ChainVM → ChainL)
    (c : Control) (md : Mode) (sc : Mirrored1 P → Prop) (hK : 2 ≤ K)
    (nq : QL delay Lp Lf P QChain → (Fin (tL P tChain) → Local.Window Γc K) →
      QL delay Lp Lf P QChain)
    (hctl : ∀ m : Mirrored1 P, m.vm.ctl.mode = md → ¬ Starved m.vm → sc m →
      (encPadN n delay Lp Lf rep ⟨chooseVm c m.vm, m.mirL⟩).1
        = nq (encPadN n delay Lp Lf rep m).1 (rwOfK K (encPadN n delay Lp Lf rep) m))
    (hleft : ∀ (m : Mirrored1 P) (i : ℕ), 2 ≤ pos (encTapes rep m i))
    (hright : ∀ (m : Mirrored1 P) (i : ℕ),
      pos (encTapes rep m i) + 2 ≤ wlen (encTapes rep m i)) :
    TapeActK (P := P) K n delay Lp Lf rep (fun m => ⟨chooseVm c m.vm, m.mirL⟩) md sc where
  nq := nq
  acts := fun q _ i => chooseActs (rolesOfQ q) i
  len_le := fun q ws i => le_trans (chooseActs_length _ i) hK
  ctl := hctl
  tape := fun m i hmd hs hsc => by
    have h := chooseVm_padTapesN_all n rep c m (hleft m) (hright m) i
    rw [h, rolesOfQ_encPadN]

#print axioms bankStep_opAt
#print axioms chooseVm_phys_chooseSlotActs
#print axioms encTapes_mirIdx
#print axioms chooseVm_encTapes_tail
#print axioms chooseVm_encTapes_mir
#print axioms chooseVm_encTapes_all
#print axioms chooseVm_padTapesN_all
#print axioms chooseVm_tapeActK

end PalPeg.CloseoutCoreEnc16
