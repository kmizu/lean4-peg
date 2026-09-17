import PalPeg.CloseoutCoreEnc16

/-!
# Closeout, step 2q: `shiftPick` as a composite residual at every address

`CloseoutCoreEnc16` closes the `TapeActK` residual of `CloseoutCoreEnc13` §5 for
`chooseSelect` at **every** address, and lists as its missing fact 3 that
`shiftPick` is *not* covered, because `LocalTick3.shiftVm` (and its intermediate
`shiftMid`) also advance the `left` and `center` cursors and the chain, so the
view-fixity input `CloseoutCoreEnc15` §5 fails for it.  This file does for
`shiftVm` everything that can be done address-wise without a cursor model: the
bank block, the whole mirror block, the two double buffers and the four fixed
cursor blocks are computed unconditionally, and the two moving regions (the
`left`/`center` blocks and the chain block) are isolated into a single named
datum `rest`.  Nothing here is about the whole machine, so

**無条件 PAL ∈ PEG は未完.**

## What is established (unconditional)

* **§1 (the bank block).**  `shiftVm_roles`, `shiftSlotActs` and
  `shiftVm_phys_shiftSlotActs`: `shiftPick`'s two bank ticks give an explicit
  per-slot list of length `≤ 2`, a function of the roles table alone — the
  `CloseoutCoreEnc16` §2 treatment of `chooseSelect`, transported to
  `shiftOps1`/`shiftOps2` via `CloseoutCoreEnc16.bankStep_opAt`.
* **§2 (the mirror block, computed).**  `shiftVm_radiusMir_*` /
  `shiftVm_lowerMir_*` / `shiftVm_lengthMir_*`: the radius bank takes a single
  `pop` on each of its three tapes (`shiftOps1 .radius = .pop`,
  `shiftOps2 .radius = .keep`), the lower bank is fixed, and the length bank
  takes **two** `pop`s (`shiftOps1 .length = shiftOps2 .length = .pop`).
  `shiftVm_encTapes_mir` turns this into the `actList` law at the seven mirror
  addresses.
* **§3 (the four fixed cursor blocks and the two buffers).**
  `shiftVm_encTapes_viewFixed`: `right`, `walkerView`, `fppWalker` and the
  parked mirror `mirL` (the blocks `2 * tView ≤ i < nViews * tView`) are
  untouched; `shiftVm_encTapes_buf`: so are `dpBuf` and `fppBuf` (the addresses
  `nViews * tView + P + k` with `7 ≤ k < tMir + tBuf`).
* **§4 (every address, modulo one datum).**  `shiftActs rest R` is the total
  micro-action list: it is the computed list on the bank, mirror, fixed-cursor
  and buffer addresses, and the supplied `rest i` on the moving ones.
  `shiftActs_length` bounds it by `4 = CloseoutCoreEnc12.microCount .shiftPick`
  when `rest` is bounded by `4` (the computed part never exceeds `2`), and
  `shiftVm_encTapes_all` / `shiftVm_padTapesN_all` prove the composite law at
  every `i` from the single hypothesis `hrest`, which mentions only the moving
  region `RestAddr`.
* **§5 (the instance).**  `shiftVm_tapeActK` builds `CloseoutCoreEnc13.TapeActK`
  for `shiftPick` at any radius `4 ≤ K`, taking the finite control (`nq`,
  `hctl`) and the moving region (`rest`, `hrest`) as data — exactly the two
  places where this file has nothing to compute.

## What is *not* established, one line each

1. **The moving region is a hypothesis**: `LocalInputView.moveRight` rewrites a
   real-time queue (`viewTapes` tapes `2`/`3` of the `left` and `center` blocks)
   and `encTapes` reads the chain through the *uninterpreted* representation
   `rep`, so neither `left`/`center` nor `chainTapes (rep (.watch (chainShiftOne
   w)))` is a bounded composite of `CloseoutCoreEnc12.Act`s of the old tape by
   anything proved here; `rest`/`hrest` name precisely that gap.
2. **The control component and the two head invariants are hypotheses**, exactly
   as in `CloseoutCoreEnc16` missing facts 1–2.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutCoreEnc17

open PalPeg PalPeg.Program
open PalPeg.Local (pos)
open PalPeg.CloseoutCoreStep (Γc blankc tL QL nViews tView tMir tBuf qOfL)
open PalPeg.CloseoutCoreEnc (QChain tChain segSym mapTape encTapes)
open PalPeg.CloseoutCoreEnc5 (wlen)
open PalPeg.CloseoutCoreEnc8 (padTapesN encPadN)
open PalPeg.CloseoutCoreEnc12 (Act actList)
open PalPeg.CloseoutCoreEnc13 (opActs op_apply_eq_actList actList_append TapeActK)
open PalPeg.CloseoutCoreEnc14 (embActs embActs_length slotIdx slotIdx_val mapTape_actList)
open PalPeg.CloseoutCoreEnc16 (rolesOfQ rolesOfQ_encPadN opAt opAt_length bankStep_opAt
  mir_act mir_act2 encTapes_mirIdx)
open PalPeg.LocalCounter (Seg)
open PalPeg.LocalState (GalilVML Ctr)
open PalPeg.LocalTick3 (Op bankStep bankTick shiftOps1 shiftOps2 shiftMid shiftVm)
open PalPeg.LocalReplayParked (Mirrored1)
open PalPeg.LocalChain (ChainL)
open PalPeg.GalilScaffoldChainInputSupply (ChainVM)
open PalPeg.GalilScaffoldController (Mode)
open PalPeg.LocalSysConcrete (Starved)

variable {P : ℕ}

/-! ## 1. The bank block -/

theorem shiftVm_roles (w : PalPeg.GalilScaffoldChainWatch.State) (x : GalilVML P) :
    (shiftVm w x).roles = x.roles := rfl

/-- **The slot list of `shiftPick`**, a function of the roles table. -/
noncomputable def shiftSlotActs (R : Ctr → Fin P) (j : Fin P) : List (Act Γc) :=
  embActs (opAt shiftOps1 R j ++ opAt shiftOps2 R j)

theorem shiftSlotActs_length (R : Ctr → Fin P) (j : Fin P) :
    (shiftSlotActs R j).length ≤ 2 := by
  unfold shiftSlotActs
  rw [embActs_length, List.length_append]
  have := opAt_length shiftOps1 R j
  have := opAt_length shiftOps2 R j
  omega

theorem shiftVm_phys_shiftSlotActs (w : PalPeg.GalilScaffoldChainWatch.State)
    (x : GalilVML P) (j : Fin P) :
    mapTape segSym ((shiftVm w x).phys j)
      = actList blankc (mapTape segSym (x.phys j)) (shiftSlotActs x.roles j) := by
  have h0 : (shiftVm w x).phys j = bankStep shiftOps2 (shiftMid w x) j := rfl
  have hr : (shiftMid w x).roles = x.roles := rfl
  have h1 : bankStep shiftOps2 (shiftMid w x) j
      = actList PalPeg.LocalCounter.blank ((shiftMid w x).phys j)
        (opAt shiftOps2 x.roles j) := by
    rw [← hr]; exact bankStep_opAt _ _ j
  have h2 : (shiftMid w x).phys j
      = actList PalPeg.LocalCounter.blank (x.phys j) (opAt shiftOps1 x.roles j) :=
    bankStep_opAt _ _ j
  rw [h0, h1, h2, ← actList_append]
  unfold shiftSlotActs
  rw [mapTape_actList]

/-! ## 2. The mirror block -/

theorem shiftVm_radiusMir_src (w : PalPeg.GalilScaffoldChainWatch.State) (x : GalilVML P) :
    (shiftVm w x).radiusMir.src = Op.pop.apply x.radiusMir.src := rfl

theorem shiftVm_radiusMir_mir0 (w : PalPeg.GalilScaffoldChainWatch.State) (x : GalilVML P) :
    (shiftVm w x).radiusMir.mir 0 = Op.pop.apply (x.radiusMir.mir 0) := rfl

theorem shiftVm_radiusMir_mir1 (w : PalPeg.GalilScaffoldChainWatch.State) (x : GalilVML P) :
    (shiftVm w x).radiusMir.mir 1 = Op.pop.apply (x.radiusMir.mir 1) := rfl

theorem shiftVm_lowerMir_src (w : PalPeg.GalilScaffoldChainWatch.State) (x : GalilVML P) :
    (shiftVm w x).lowerMir.src = x.lowerMir.src := rfl

theorem shiftVm_lowerMir_mir0 (w : PalPeg.GalilScaffoldChainWatch.State) (x : GalilVML P) :
    (shiftVm w x).lowerMir.mir 0 = x.lowerMir.mir 0 := rfl

theorem shiftVm_lengthMir_src (w : PalPeg.GalilScaffoldChainWatch.State) (x : GalilVML P) :
    (shiftVm w x).lengthMir.src = Op.pop.apply (Op.pop.apply x.lengthMir.src) := rfl

theorem shiftVm_lengthMir_mir0 (w : PalPeg.GalilScaffoldChainWatch.State) (x : GalilVML P) :
    (shiftVm w x).lengthMir.mir 0 = Op.pop.apply (Op.pop.apply (x.lengthMir.mir 0)) := rfl

/-- The micro-action list of the mirror address `nViews * tView + P + k`. -/
def shiftMirActs (k : ℕ) : List (Act Γc) :=
  if k ≤ 2 then embActs (opActs Op.pop)
  else if k = 5 ∨ k = 6 then embActs (opActs Op.pop ++ opActs Op.pop)
  else []

theorem shiftMirActs_length (k : ℕ) : (shiftMirActs k).length ≤ 2 := by
  unfold shiftMirActs
  split
  · simp [embActs, opActs]
  · split <;> simp [embActs, opActs]

/-- **The mirror block, address by address.** -/
theorem shiftVm_encTapes_mir (rep : ChainVM → ChainL)
    (w : PalPeg.GalilScaffoldChainWatch.State) (m : Mirrored1 P) (k : ℕ) (hk : k < 7) :
    encTapes rep ⟨shiftVm w m.vm, m.mirL⟩ (nViews * tView + P + k)
      = actList blankc (encTapes rep m (nViews * tView + P + k)) (shiftMirActs k) := by
  rw [encTapes_mirIdx rep ⟨shiftVm w m.vm, m.mirL⟩ k hk, encTapes_mirIdx rep m k hk]
  unfold shiftMirActs
  interval_cases k
  · show mapTape segSym ((shiftVm w m.vm).radiusMir.src)
        = actList blankc (mapTape segSym m.vm.radiusMir.src) _
    rw [if_pos (by omega : (0:ℕ) ≤ 2), shiftVm_radiusMir_src]; exact mir_act _ _
  · show mapTape segSym ((shiftVm w m.vm).radiusMir.mir 0)
        = actList blankc (mapTape segSym (m.vm.radiusMir.mir 0)) _
    rw [if_pos (by omega : (1:ℕ) ≤ 2), shiftVm_radiusMir_mir0]; exact mir_act _ _
  · show mapTape segSym ((shiftVm w m.vm).radiusMir.mir 1)
        = actList blankc (mapTape segSym (m.vm.radiusMir.mir 1)) _
    rw [if_pos (by omega : (2:ℕ) ≤ 2), shiftVm_radiusMir_mir1]; exact mir_act _ _
  · show mapTape segSym ((shiftVm w m.vm).lowerMir.src)
        = actList blankc (mapTape segSym m.vm.lowerMir.src) _
    rw [if_neg (by omega : ¬ ((3:ℕ) ≤ 2)), if_neg (by omega : ¬ ((3:ℕ) = 5 ∨ (3:ℕ) = 6)),
      shiftVm_lowerMir_src]
    rfl
  · show mapTape segSym ((shiftVm w m.vm).lowerMir.mir 0)
        = actList blankc (mapTape segSym (m.vm.lowerMir.mir 0)) _
    rw [if_neg (by omega : ¬ ((4:ℕ) ≤ 2)), if_neg (by omega : ¬ ((4:ℕ) = 5 ∨ (4:ℕ) = 6)),
      shiftVm_lowerMir_mir0]
    rfl
  · show mapTape segSym ((shiftVm w m.vm).lengthMir.src)
        = actList blankc (mapTape segSym m.vm.lengthMir.src) _
    rw [if_neg (by omega : ¬ ((5:ℕ) ≤ 2)), if_pos (by omega : ((5:ℕ) = 5 ∨ (5:ℕ) = 6)),
      shiftVm_lengthMir_src]
    exact mir_act2 _ _ _
  · show mapTape segSym ((shiftVm w m.vm).lengthMir.mir 0)
        = actList blankc (mapTape segSym (m.vm.lengthMir.mir 0)) _
    rw [if_neg (by omega : ¬ ((6:ℕ) ≤ 2)), if_pos (by omega : ((6:ℕ) = 5 ∨ (6:ℕ) = 6)),
      shiftVm_lengthMir_mir0]
    exact mir_act2 _ _ _

/-! ## 3. The fixed cursor blocks and the two buffers -/

/-- **The four cursor blocks `shiftPick` does not move.** -/
theorem shiftVm_encTapes_viewFixed (rep : ChainVM → ChainL)
    (w : PalPeg.GalilScaffoldChainWatch.State) (m : Mirrored1 P) (i : ℕ)
    (hlo : 2 * tView ≤ i) (hi : i < nViews * tView) :
    encTapes rep ⟨shiftVm w m.vm, m.mirL⟩ i = encTapes rep m i := by
  have h6 : nViews * tView = 6 * tView := by unfold nViews; ring
  rw [h6] at hi
  have e3 : (shiftVm w m.vm).right = m.vm.right := rfl
  have e4 : (shiftVm w m.vm).walkerView = m.vm.walkerView := rfl
  have e5 : (shiftVm w m.vm).fppWalker = m.vm.fppWalker := rfl
  have c1 : ¬ (i < tView) := by unfold tView at hlo ⊢; omega
  have c2 : ¬ (i < 2 * tView) := by omega
  by_cases c3 : i < 3 * tView
  · simp only [encTapes, if_neg c1, if_neg c2, if_pos c3, e3]
  by_cases c4 : i < 4 * tView
  · simp only [encTapes, if_neg c1, if_neg c2, if_neg c3, if_pos c4, e4]
  by_cases c5 : i < 5 * tView
  · simp only [encTapes, if_neg c1, if_neg c2, if_neg c3, if_neg c4, if_pos c5, e5]
  · have c6 : i < 6 * tView := hi
    simp only [encTapes, if_neg c1, if_neg c2, if_neg c3, if_neg c4, if_neg c5, if_pos c6]

/-- **The two double buffers are untouched by `shiftPick`.** -/
theorem shiftVm_encTapes_buf (rep : ChainVM → ChainL)
    (w : PalPeg.GalilScaffoldChainWatch.State) (m : Mirrored1 P) (i : ℕ)
    (hge : nViews * tView + P ≤ i) (hk : 7 ≤ i - nViews * tView - P)
    (hb : i - nViews * tView - P < tMir + tBuf) :
    encTapes rep ⟨shiftVm w m.vm, m.mirL⟩ i = encTapes rep m i := by
  have hnv : nViews * tView = 24 := by unfold nViews tView; omega
  have htv : tView = 4 := rfl
  have h1 : ¬ (i < tView) := by omega
  have h2 : ¬ (i < 2 * tView) := by omega
  have h3 : ¬ (i < 3 * tView) := by omega
  have h4 : ¬ (i < 4 * tView) := by omega
  have h5 : ¬ (i < 5 * tView) := by omega
  have h6 : ¬ (i < 6 * tView) := by omega
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
  have ed : (shiftVm w m.vm).dpBuf = m.vm.dpBuf := rfl
  have ef : (shiftVm w m.vm).fppBuf = m.vm.fppBuf := rfl
  by_cases hc : i - nViews * tView - P < tMir + (2 * 12 + 1)
  · simp only [if_pos hc, ed]
  · simp only [if_neg hc, if_pos hb, ef]

/-! ## 4. The micro-action list at every address -/

/-- **The moving region of `shiftPick`**: the `left` and `center` cursor blocks,
and the chain block. -/
def RestAddr (P i : ℕ) : Prop :=
  i < 2 * tView ∨ nViews * tView + P + (tMir + tBuf) ≤ i

/-- **The total micro-action list of `shiftPick`**, computed everywhere except on
`RestAddr`, where it is the supplied datum. -/
noncomputable def shiftActs (rest : ℕ → List (Act Γc)) (R : Ctr → Fin P) (i : ℕ) :
    List (Act Γc) :=
  if i < 2 * tView then rest i
  else if i < nViews * tView then []
  else if h : i - nViews * tView < P then shiftSlotActs R ⟨_, h⟩
  else if i < nViews * tView + P + (tMir + tBuf) then shiftMirActs (i - nViews * tView - P)
  else rest i

theorem shiftActs_length (rest : ℕ → List (Act Γc)) (hrl : ∀ i, (rest i).length ≤ 4)
    (R : Ctr → Fin P) (i : ℕ) : (shiftActs rest R i).length ≤ 4 := by
  unfold shiftActs
  split
  · exact hrl i
  · split
    · simp
    · split
      · exact le_trans (shiftSlotActs_length _ _) (by omega)
      · split
        · exact le_trans (shiftMirActs_length _) (by omega)
        · exact hrl i

/-- **`shiftPick` is a composite at *every* address of the raw layout**, given
the composite law on the moving region. -/
theorem shiftVm_encTapes_all (rep : ChainVM → ChainL)
    (w : PalPeg.GalilScaffoldChainWatch.State) (m : Mirrored1 P) (rest : ℕ → List (Act Γc))
    (hrest : ∀ i, RestAddr P i →
      encTapes rep ⟨shiftVm w m.vm, m.mirL⟩ i
        = actList blankc (encTapes rep m i) (rest i))
    (i : ℕ) :
    encTapes rep ⟨shiftVm w m.vm, m.mirL⟩ i
      = actList blankc (encTapes rep m i) (shiftActs rest m.vm.roles i) := by
  unfold shiftActs
  by_cases h0 : i < 2 * tView
  · rw [if_pos h0]; exact hrest i (Or.inl h0)
  rw [if_neg h0]
  by_cases hview : i < nViews * tView
  · rw [if_pos hview]
    exact shiftVm_encTapes_viewFixed rep w m i (by omega) hview
  rw [if_neg hview]
  by_cases hslot : i - nViews * tView < P
  · rw [dif_pos hslot]
    have key : ∀ (j : Fin P), (slotIdx (P := P) j : ℕ) = i →
        encTapes rep ⟨shiftVm w m.vm, m.mirL⟩ i
          = actList blankc (encTapes rep m i) (shiftSlotActs m.vm.roles j) := by
      intro j hij
      rw [← hij, PalPeg.CloseoutCoreEnc14.encTapes_slotIdx,
        PalPeg.CloseoutCoreEnc14.encTapes_slotIdx]
      exact shiftVm_phys_shiftSlotActs w m.vm _
    exact key ⟨i - nViews * tView, hslot⟩
      (by rw [slotIdx_val]; show nViews * tView + (i - nViews * tView) = i; omega)
  rw [dif_neg hslot]
  have hge : nViews * tView + P ≤ i := by omega
  by_cases hb : i < nViews * tView + P + (tMir + tBuf)
  · rw [if_pos hb]
    by_cases hk : i - nViews * tView - P < 7
    · have hi : i = nViews * tView + P + (i - nViews * tView - P) := by omega
      calc encTapes rep ⟨shiftVm w m.vm, m.mirL⟩ i
          = encTapes rep ⟨shiftVm w m.vm, m.mirL⟩ (nViews * tView + P + (i - nViews * tView - P)) := by
            rw [← hi]
        _ = actList blankc (encTapes rep m (nViews * tView + P + (i - nViews * tView - P)))
              (shiftMirActs (i - nViews * tView - P)) := shiftVm_encTapes_mir rep w m _ hk
        _ = actList blankc (encTapes rep m i) (shiftMirActs (i - nViews * tView - P)) := by
            rw [← hi]
    · have h7 : 7 ≤ i - nViews * tView - P := by omega
      have hz : shiftMirActs (i - nViews * tView - P) = [] := by
        unfold shiftMirActs
        rw [if_neg (by omega), if_neg (by omega)]
      rw [hz]
      exact shiftVm_encTapes_buf rep w m i hge h7 (by omega)
  · rw [if_neg hb]
    exact hrest i (Or.inr (by omega))

/-- **The same on the laid-out family**, under the two head invariants of
`CloseoutCoreEnc15` §2 with the radius-`4` margin. -/
theorem shiftVm_padTapesN_all (n : ℕ) (rep : ChainVM → ChainL)
    (w : PalPeg.GalilScaffoldChainWatch.State) (m : Mirrored1 P) (rest : ℕ → List (Act Γc))
    (hrl : ∀ i, (rest i).length ≤ 4)
    (hrest : ∀ i, RestAddr P i →
      encTapes rep ⟨shiftVm w m.vm, m.mirL⟩ i
        = actList blankc (encTapes rep m i) (rest i))
    (hleft : ∀ i, 4 ≤ pos (encTapes rep m i))
    (hright : ∀ i, pos (encTapes rep m i) + 4 ≤ wlen (encTapes rep m i)) (i : ℕ) :
    padTapesN n rep ⟨shiftVm w m.vm, m.mirL⟩ i
      = actList blankc (padTapesN n rep m i) (shiftActs rest m.vm.roles i) := by
  have hlen := shiftActs_length rest hrl m.vm.roles i
  have h1 := hleft i
  have h2 := hright i
  rw [PalPeg.CloseoutCoreEnc8.padTapesN, PalPeg.CloseoutCoreEnc8.padTapesN,
    PalPeg.CloseoutCoreEnc3.encTapes1, PalPeg.CloseoutCoreEnc3.encTapes1,
    shiftVm_encTapes_all rep w m rest hrest i]
  exact PalPeg.CloseoutCoreEnc15.padTapesN_actList blankc n _ _ (by omega) (by omega)

/-! ## 5. The `TapeActK` instance -/

open PalPeg.CloseoutCoreEnc13 (rwOfK)

/-- **`shiftPick` as a radius-`K` composite residual at every address.**  The
bank, mirror, fixed-cursor and buffer halves are discharged here; the finite
control (`nq`, `hctl`) and the moving region (`rest`, `hrest`) are data. -/
noncomputable def shiftVm_tapeActK (K n delay Lp Lf : ℕ) (rep : ChainVM → ChainL)
    (w : PalPeg.GalilScaffoldChainWatch.State) (md : Mode) (sc : Mirrored1 P → Prop)
    (hK : 4 ≤ K)
    (nq : QL delay Lp Lf P QChain → (Fin (tL P tChain) → Local.Window Γc K) →
      QL delay Lp Lf P QChain)
    (hctl : ∀ m : Mirrored1 P, m.vm.ctl.mode = md → ¬ Starved m.vm → sc m →
      (encPadN n delay Lp Lf rep ⟨shiftVm w m.vm, m.mirL⟩).1
        = nq (encPadN n delay Lp Lf rep m).1 (rwOfK K (encPadN n delay Lp Lf rep) m))
    (rest : ℕ → List (Act Γc)) (hrl : ∀ i, (rest i).length ≤ 4)
    (hrest : ∀ (m : Mirrored1 P) (i : ℕ), RestAddr P i →
      encTapes rep ⟨shiftVm w m.vm, m.mirL⟩ i
        = actList blankc (encTapes rep m i) (rest i))
    (hleft : ∀ (m : Mirrored1 P) (i : ℕ), 4 ≤ pos (encTapes rep m i))
    (hright : ∀ (m : Mirrored1 P) (i : ℕ),
      pos (encTapes rep m i) + 4 ≤ wlen (encTapes rep m i)) :
    TapeActK (P := P) K n delay Lp Lf rep (fun m => ⟨shiftVm w m.vm, m.mirL⟩) md sc where
  nq := nq
  acts := fun q _ i => shiftActs rest (rolesOfQ q) i
  len_le := fun q ws i => le_trans (shiftActs_length rest hrl _ i) hK
  ctl := hctl
  tape := fun m i hmd hs hsc => by
    have h := shiftVm_padTapesN_all n rep w m rest hrl (hrest m) (hleft m) (hright m) i
    rw [h, rolesOfQ_encPadN]

#print axioms shiftVm_phys_shiftSlotActs
#print axioms shiftVm_encTapes_mir
#print axioms shiftVm_encTapes_viewFixed
#print axioms shiftVm_encTapes_buf
#print axioms shiftVm_encTapes_all
#print axioms shiftVm_padTapesN_all
#print axioms shiftVm_tapeActK

end PalPeg.CloseoutCoreEnc17
