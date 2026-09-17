import PalPeg.CloseoutCoreEnc17
import PalPeg.CloseoutCoreEnc18

/-!
# Closeout, step 2s: the debris layout of the whole core, and `shiftPick` on it

`CloseoutCoreEnc17` discharges `shiftPick` at every address **except** the two
moving cursor blocks (`rest`/`hrest`), and `CloseoutCoreEnc18` shows that on the
*current* layout `CloseoutCoreEnc.viewTapes` that residual is not merely
unproved but **false** (a head cannot erase), while on the debris layout
`viewTapesD` the half-step and the pushed-back branch of
`LocalInputView.moveRight` *are* bounded composites.  This file carries the
repair through the whole core: it defines the layout `encTapesD` — literally
`CloseoutCoreEnc.encTapes` with its six cursor blocks moved onto `viewTapesD` —
transports every non-cursor fact of `CloseoutCoreEnc16`/`17` to it for free, and
builds the `shiftPick` instance on it.  Nothing here is about the whole machine,
so

**無条件 PAL ∈ PEG は未完.**

## What is established (unconditional)

* **§1 (the layout).**  `encTapesD rep dbg m` agrees with `encTapes rep m`
  address by address outside the six cursor blocks (`encTapesD_tail`), and each
  cursor block is `CloseoutCoreEnc18.viewTapesD` with its own debris column
  `dbg m b`.  So the bank, mirror, buffer and chain halves of the old layout are
  **unchanged**, and every fact about them transports by `rfl`.
* **§2 (the tail, transported).**  `shiftVm_encTapes_tailAll`: at every address
  `≥ nViews * tView` the `shiftPick` step is `CloseoutCoreEnc17.shiftActs`,
  taking only the chain residual `restC` as data — this is the
  `CloseoutCoreEnc17` §4 proof with its two cursor cases removed, so it needs no
  `hrest` below `2 * tView`.
* **§3 (the moving cursors).**  `moveActs2`/`moveDebris2` iterate
  `CloseoutCoreEnc18.moveActs`/`moveDebris`, and `moveRight2_actList` proves the
  **two** right moves `shiftPick` performs on `left` are one composite of length
  `≤ 4` at each of the four addresses of that cursor; `center`'s single move is
  `CloseoutCoreEnc18.moveRight_actList` directly.
* **§4 (every address).**  `shiftActsD` is the total micro-action list and
  `shiftVm_encTapesD_all` / `shiftVm_padTapesND_all` prove the composite law at
  **every** address of the debris layout, with the chain block as the only
  remaining datum.
* **§5 (the instance).**  `TapeActKD` is `CloseoutCoreEnc13.TapeActK` on
  `padTapesND`, and `shiftVm_tapeActK'` builds it for `shiftPick` at any radius
  `4 ≤ K`.
* **§6 (why the `far` branch is not a bounded rewrite here).**  `pos_actList_ge`
  and `not_bounded_clear_dTape`: an `actList` of length `≤ K` moves a head left
  by at most `K`, so clearing a `dTape` of live length `> K` is impossible.
  `not_bounded_rot_rear` instantiates this at the rear stack of a cursor: the
  rotation `RTQueue.check` starts with `rear := []`, which on address `3` of
  `viewTapesD` is exactly such a clearing.  So item 2 of the plan —
  `moveRight_actList_rot` on the four-tape cursor — is **false**; the rotation
  needs the six queue stacks of `CloseoutCoreEnc7.queueTapes6` with a role
  table, i.e. `tView ≥ 8`.

## What is *not* established, one line each

1. **The chain block is still a datum**: `encTapes` reads the chain through the
   uninterpreted `rep`, so `restC`/`hrestC` (addresses
   `≥ nViews * tView + P + (tMir + tBuf)`) is carried, unproved, from
   `CloseoutCoreEnc17`.
2. **The `far` branch of `moveRight` is excluded by hypothesis**: `hL`, `hL2`,
   `hC` assume `near ≠ []` on a full step, i.e. the cursor never dequeues the
   real-time queue during a shift; §6 shows this cannot be dropped on a
   four-tape cursor.
3. **`acts` is supplied**: `LocalInputView.InputView.gap` is *not* a component of
   `CloseoutCoreStep.QL` and not laid out on any tape, so `moveActs` is not
   known to be a function of the encoded state; `shiftVm_tapeActK'` takes the
   `acts` field and its defining equation `hacts` as data, exactly as
   `CloseoutCoreEnc17.shiftVm_tapeActK` takes `nq`/`hctl`.
4. **The debris discipline is a hypothesis**: `hd0`/`hd1`/`hdF` say the layout's
   debris columns follow `moveDebris`; nothing here constructs them.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutCoreEnc19

open PalPeg PalPeg.Program
open PalPeg.Local (pos Window)
open PalPeg.CloseoutCoreStep (Γc blankc tL QL nViews tView tMir tBuf qOfL)
open PalPeg.CloseoutCoreEnc (QChain tChain qChainOf encTapes)
open PalPeg.CloseoutCoreEnc3 (shift1)
open PalPeg.CloseoutCoreEnc5 (wlen)
open PalPeg.CloseoutCoreEnc8 (padRN padTapesN encPadN)
open PalPeg.CloseoutCoreEnc12 (Act actList actOnG actList_cons)
open PalPeg.CloseoutCoreEnc13 (actList_append TapeActK rwOfK)
open PalPeg.CloseoutCoreEnc16 (rolesOfQ)
open PalPeg.CloseoutCoreEnc17 (shiftActs shiftActs_length shiftSlotActs shiftMirActs
  shiftVm_phys_shiftSlotActs shiftVm_encTapes_mir shiftVm_encTapes_viewFixed
  shiftVm_encTapes_buf)
open PalPeg.CloseoutCoreEnc18 (dTape pos_dTape viewTapesD moveActs moveActs_length
  moveDebris moveRight_actList)
open PalPeg.LocalState (GalilVML Ctr)
open PalPeg.LocalInputView (InputView moveRight)
open PalPeg.LocalTick3 (shiftVm)
open PalPeg.LocalReplayParked (Mirrored1)
open PalPeg.LocalChain (ChainL)
open PalPeg.GalilScaffoldChainInputSupply (ChainVM)
open PalPeg.GalilScaffoldController (Mode)
open PalPeg.LocalSysConcrete (Starved)

variable {P : ℕ}

/-! ## 1. The debris layout of the whole core -/

/-- **`CloseoutCoreEnc.encTapes` with its cursor blocks on the debris layout.**
The six cursors of the core (`left`, `center`, `right`, `walkerView`,
`fppWalker` and the parked mirror `Mirrored1.mirL`) are laid out by
`CloseoutCoreEnc18.viewTapesD`, block `b` using the debris column `dbg m b`;
every other address is literally the old layout. -/
noncomputable def encTapesD (rep : ChainVM → ChainL)
    (dbg : Mirrored1 P → ℕ → ℕ → List Γc) (m : Mirrored1 P) : ℕ → STape Γc := fun i =>
  if i < tView then viewTapesD m.vm.left (dbg m 0) i
  else if i < 2 * tView then viewTapesD m.vm.center (dbg m 1) (i - tView)
  else if i < 3 * tView then viewTapesD m.vm.right (dbg m 2) (i - 2 * tView)
  else if i < 4 * tView then viewTapesD m.vm.walkerView (dbg m 3) (i - 3 * tView)
  else if i < 5 * tView then viewTapesD m.vm.fppWalker (dbg m 4) (i - 4 * tView)
  else if i < 6 * tView then viewTapesD m.mirL (dbg m 5) (i - 5 * tView)
  else encTapes rep m i

theorem nViews_tView : nViews * tView = 6 * tView := rfl

/-- **Outside the cursor blocks the repair changes nothing**, so every fact of
`CloseoutCoreEnc14`/`16`/`17` about the bank, the mirror banks, the two double
buffers and the chain transports to `encTapesD` unchanged. -/
theorem encTapesD_tail (rep : ChainVM → ChainL) (dbg : Mirrored1 P → ℕ → ℕ → List Γc)
    (m : Mirrored1 P) (i : ℕ) (hge : nViews * tView ≤ i) :
    encTapesD rep dbg m i = encTapes rep m i := by
  have h6 : nViews * tView = 6 * tView := rfl
  rw [h6] at hge
  have htv : tView = 4 := rfl
  unfold encTapesD
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega)]

/-! ## 2. The tail of `shiftPick`, transported -/

/-- **`CloseoutCoreEnc17` §4 above the cursor blocks.**  Same statement as
`CloseoutCoreEnc17.shiftVm_encTapes_all`, but the hypothesis only mentions the
chain block, because the two cursor cases are never entered. -/
theorem shiftVm_encTapes_tailAll (rep : ChainVM → ChainL)
    (w : PalPeg.GalilScaffoldChainWatch.State) (m : Mirrored1 P)
    (restC : ℕ → List (Act Γc))
    (hrestC : ∀ i, nViews * tView + P + (tMir + tBuf) ≤ i →
      encTapes rep ⟨shiftVm w m.vm, m.mirL⟩ i
        = actList blankc (encTapes rep m i) (restC i))
    (i : ℕ) (hge : nViews * tView ≤ i) :
    encTapes rep ⟨shiftVm w m.vm, m.mirL⟩ i
      = actList blankc (encTapes rep m i) (shiftActs restC m.vm.roles i) := by
  have h6 : nViews * tView = 6 * tView := rfl
  have htv : tView = 4 := rfl
  unfold shiftActs
  rw [if_neg (by omega), if_neg (by omega)]
  by_cases hslot : i - nViews * tView < P
  · rw [dif_pos hslot]
    have key : ∀ (j : Fin P), (PalPeg.CloseoutCoreEnc14.slotIdx (P := P) j : ℕ) = i →
        encTapes rep ⟨shiftVm w m.vm, m.mirL⟩ i
          = actList blankc (encTapes rep m i) (shiftSlotActs m.vm.roles j) := by
      intro j hij
      rw [← hij, PalPeg.CloseoutCoreEnc14.encTapes_slotIdx,
        PalPeg.CloseoutCoreEnc14.encTapes_slotIdx]
      exact shiftVm_phys_shiftSlotActs w m.vm _
    exact key ⟨i - nViews * tView, hslot⟩
      (by rw [PalPeg.CloseoutCoreEnc14.slotIdx_val]
          show nViews * tView + (i - nViews * tView) = i
          omega)
  rw [dif_neg hslot]
  have hge2 : nViews * tView + P ≤ i := by omega
  by_cases hb : i < nViews * tView + P + (tMir + tBuf)
  · rw [if_pos hb]
    by_cases hk : i - nViews * tView - P < 7
    · have hi : i = nViews * tView + P + (i - nViews * tView - P) := by omega
      calc encTapes rep ⟨shiftVm w m.vm, m.mirL⟩ i
          = encTapes rep ⟨shiftVm w m.vm, m.mirL⟩
              (nViews * tView + P + (i - nViews * tView - P)) := by rw [← hi]
        _ = actList blankc
              (encTapes rep m (nViews * tView + P + (i - nViews * tView - P)))
              (shiftMirActs (i - nViews * tView - P)) := shiftVm_encTapes_mir rep w m _ hk
        _ = actList blankc (encTapes rep m i) (shiftMirActs (i - nViews * tView - P)) := by
            rw [← hi]
    · have h7 : 7 ≤ i - nViews * tView - P := by omega
      have hz : shiftMirActs (i - nViews * tView - P) = [] := by
        unfold shiftMirActs
        rw [if_neg (by omega), if_neg (by omega)]
      rw [hz]
      exact shiftVm_encTapes_buf rep w m i hge2 h7 (by omega)
  · rw [if_neg hb]
    exact hrestC i (by omega)

/-! ## 3. The two moving cursors -/

/-- The composite of two right moves. -/
def moveActs2 (v : InputView) (i : ℕ) : List (Act Γc) :=
  moveActs v i ++ moveActs (moveRight v) i

theorem moveActs2_length (v : InputView) (i : ℕ) : (moveActs2 v i).length ≤ 4 := by
  unfold moveActs2
  rw [List.length_append]
  have h1 := moveActs_length v i
  have h2 := moveActs_length (moveRight v) i
  omega

/-- The debris after two right moves. -/
def moveDebris2 (v : InputView) (d : ℕ → List Γc) : ℕ → List Γc :=
  moveDebris (moveRight v) (moveDebris v d)

/-- **The two right moves `shiftPick` performs on `left` are one composite** of
length `≤ 4` at each of the four addresses of that cursor. -/
theorem moveRight2_actList (v : InputView) (d : ℕ → List Γc)
    (h0 : v.gap = true → v.near ≠ [])
    (h1 : (moveRight v).gap = true → (moveRight v).near ≠ []) (i : ℕ) :
    viewTapesD (moveRight (moveRight v)) (moveDebris2 v d) i
      = actList blankc (viewTapesD v d i) (moveActs2 v i) := by
  unfold moveDebris2 moveActs2
  rw [moveRight_actList (moveRight v) (moveDebris v d) h1 i,
    moveRight_actList v d h0 i, actList_append]

/-! ## 4. `shiftPick` at every address of the debris layout -/

theorem shiftVm_left (w : PalPeg.GalilScaffoldChainWatch.State) (x : GalilVML P) :
    (shiftVm w x).left = moveRight (moveRight x.left) := rfl

theorem shiftVm_center (w : PalPeg.GalilScaffoldChainWatch.State) (x : GalilVML P) :
    (shiftVm w x).center = moveRight x.center := rfl

theorem shiftVm_right (w : PalPeg.GalilScaffoldChainWatch.State) (x : GalilVML P) :
    (shiftVm w x).right = x.right := rfl

theorem shiftVm_walkerView (w : PalPeg.GalilScaffoldChainWatch.State) (x : GalilVML P) :
    (shiftVm w x).walkerView = x.walkerView := rfl

theorem shiftVm_fppWalker (w : PalPeg.GalilScaffoldChainWatch.State) (x : GalilVML P) :
    (shiftVm w x).fppWalker = x.fppWalker := rfl

/-- **The total micro-action list of `shiftPick` on the debris layout.** -/
noncomputable def shiftActsD (vL vC : InputView) (restC : ℕ → List (Act Γc))
    (R : Ctr → Fin P) (i : ℕ) : List (Act Γc) :=
  if i < tView then moveActs2 vL i
  else if i < 2 * tView then moveActs vC (i - tView)
  else shiftActs restC R i

theorem shiftActsD_length (vL vC : InputView) (restC : ℕ → List (Act Γc))
    (hrl : ∀ i, (restC i).length ≤ 4) (R : Ctr → Fin P) (i : ℕ) :
    (shiftActsD vL vC restC R i).length ≤ 4 := by
  unfold shiftActsD
  split
  · exact moveActs2_length vL i
  · split
    · exact le_trans (moveActs_length vC _) (by omega)
    · exact shiftActs_length restC hrl R i

/-- **`shiftPick` is a bounded composite at *every* address of the debris
layout**, modulo the chain block. -/
theorem shiftVm_encTapesD_all (rep : ChainVM → ChainL)
    (dbg : Mirrored1 P → ℕ → ℕ → List Γc)
    (w : PalPeg.GalilScaffoldChainWatch.State) (m : Mirrored1 P)
    (restC : ℕ → List (Act Γc))
    (hL : m.vm.left.gap = true → m.vm.left.near ≠ [])
    (hL2 : (moveRight m.vm.left).gap = true → (moveRight m.vm.left).near ≠ [])
    (hC : m.vm.center.gap = true → m.vm.center.near ≠ [])
    (hd0 : dbg ⟨shiftVm w m.vm, m.mirL⟩ 0 = moveDebris2 m.vm.left (dbg m 0))
    (hd1 : dbg ⟨shiftVm w m.vm, m.mirL⟩ 1 = moveDebris m.vm.center (dbg m 1))
    (hdF : ∀ b, 2 ≤ b → b < 6 → dbg ⟨shiftVm w m.vm, m.mirL⟩ b = dbg m b)
    (hrestC : ∀ i, nViews * tView + P + (tMir + tBuf) ≤ i →
      encTapes rep ⟨shiftVm w m.vm, m.mirL⟩ i
        = actList blankc (encTapes rep m i) (restC i))
    (i : ℕ) :
    encTapesD rep dbg ⟨shiftVm w m.vm, m.mirL⟩ i
      = actList blankc (encTapesD rep dbg m i)
        (shiftActsD m.vm.left m.vm.center restC m.vm.roles i) := by
  have htv : tView = 4 := rfl
  have hzero : ∀ k : ℕ, 2 * tView ≤ k → k < 6 * tView →
      shiftActs restC m.vm.roles k = [] := by
    intro k hk1 hk2
    unfold shiftActs
    rw [if_neg (by omega), if_pos (by rw [nViews_tView]; omega)]
  unfold shiftActsD encTapesD
  by_cases c0 : i < tView
  · rw [if_pos c0, if_pos c0, if_pos c0]
    show viewTapesD (shiftVm w m.vm).left (dbg ⟨shiftVm w m.vm, m.mirL⟩ 0) i
      = actList blankc (viewTapesD m.vm.left (dbg m 0) i) (moveActs2 m.vm.left i)
    rw [shiftVm_left, hd0]
    exact moveRight2_actList m.vm.left (dbg m 0) hL hL2 i
  rw [if_neg c0, if_neg c0, if_neg c0]
  by_cases c1 : i < 2 * tView
  · rw [if_pos c1, if_pos c1, if_pos c1]
    show viewTapesD (shiftVm w m.vm).center (dbg ⟨shiftVm w m.vm, m.mirL⟩ 1) (i - tView)
      = actList blankc (viewTapesD m.vm.center (dbg m 1) (i - tView))
        (moveActs m.vm.center (i - tView))
    rw [shiftVm_center, hd1]
    exact moveRight_actList m.vm.center (dbg m 1) hC (i - tView)
  rw [if_neg c1, if_neg c1, if_neg c1]
  by_cases c2 : i < 3 * tView
  · rw [if_pos c2, if_pos c2, hzero i (by omega) (by omega)]
    show viewTapesD (shiftVm w m.vm).right (dbg ⟨shiftVm w m.vm, m.mirL⟩ 2) (i - 2 * tView)
      = actList blankc (viewTapesD m.vm.right (dbg m 2) (i - 2 * tView)) []
    rw [shiftVm_right, hdF 2 (by omega) (by omega)]
    rfl
  rw [if_neg c2, if_neg c2]
  by_cases c3 : i < 4 * tView
  · rw [if_pos c3, if_pos c3, hzero i (by omega) (by omega)]
    show viewTapesD (shiftVm w m.vm).walkerView (dbg ⟨shiftVm w m.vm, m.mirL⟩ 3)
        (i - 3 * tView)
      = actList blankc (viewTapesD m.vm.walkerView (dbg m 3) (i - 3 * tView)) []
    rw [shiftVm_walkerView, hdF 3 (by omega) (by omega)]
    rfl
  rw [if_neg c3, if_neg c3]
  by_cases c4 : i < 5 * tView
  · rw [if_pos c4, if_pos c4, hzero i (by omega) (by omega)]
    show viewTapesD (shiftVm w m.vm).fppWalker (dbg ⟨shiftVm w m.vm, m.mirL⟩ 4)
        (i - 4 * tView)
      = actList blankc (viewTapesD m.vm.fppWalker (dbg m 4) (i - 4 * tView)) []
    rw [shiftVm_fppWalker, hdF 4 (by omega) (by omega)]
    rfl
  rw [if_neg c4, if_neg c4]
  by_cases c5 : i < 6 * tView
  · rw [if_pos c5, if_pos c5, hzero i (by omega) (by omega)]
    show viewTapesD (⟨shiftVm w m.vm, m.mirL⟩ : Mirrored1 P).mirL
        (dbg ⟨shiftVm w m.vm, m.mirL⟩ 5) (i - 5 * tView)
      = actList blankc (viewTapesD m.mirL (dbg m 5) (i - 5 * tView)) []
    rw [hdF 5 (by omega) (by omega)]
    rfl
  rw [if_neg c5, if_neg c5]
  exact shiftVm_encTapes_tailAll rep w m restC hrestC i (by rw [nViews_tView]; omega)

/-! ## 5. The laid-out family and the `TapeActK` instance -/

noncomputable def encTapesD1 (rep : ChainVM → ChainL)
    (dbg : Mirrored1 P → ℕ → ℕ → List Γc) (m : Mirrored1 P) : ℕ → STape Γc :=
  fun i => shift1 blankc (encTapesD rep dbg m i)

noncomputable def padTapesND (n : ℕ) (rep : ChainVM → ChainL)
    (dbg : Mirrored1 P → ℕ → ℕ → List Γc) (m : Mirrored1 P) : ℕ → STape Γc :=
  fun i => padRN blankc n (encTapesD1 rep dbg m i)

noncomputable def encPadND (n delay Lp Lf : ℕ) (rep : ChainVM → ChainL)
    (dbg : Mirrored1 P → ℕ → ℕ → List Γc) (m : Mirrored1 P) :
    QL delay Lp Lf P QChain × (Fin (tL P tChain) → STape Γc) :=
  (qOfL delay Lp Lf (fun c => qChainOf (rep c)) m, fun j => padTapesND n rep dbg m j.val)

@[simp] theorem rolesOfQ_encPadND (n delay Lp Lf : ℕ) (rep : ChainVM → ChainL)
    (dbg : Mirrored1 P → ℕ → ℕ → List Γc) (m : Mirrored1 P) :
    rolesOfQ (encPadND n delay Lp Lf rep dbg m).1 = m.vm.roles := rfl

/-- **`CloseoutCoreEnc13.TapeActK` on the debris layout.** -/
structure TapeActKD (K n delay Lp Lf : ℕ) (rep : ChainVM → ChainL)
    (dbg : Mirrored1 P → ℕ → ℕ → List Γc)
    (f : Mirrored1 P → Mirrored1 P) (md : Mode) (sc : Mirrored1 P → Prop) where
  nq : QL delay Lp Lf P QChain → (Fin (tL P tChain) → Window Γc K) →
    QL delay Lp Lf P QChain
  acts : QL delay Lp Lf P QChain → (Fin (tL P tChain) → Window Γc K) → ℕ → List (Act Γc)
  len_le : ∀ q ws i, (acts q ws i).length ≤ K
  ctl : ∀ m : Mirrored1 P, m.vm.ctl.mode = md → ¬ Starved m.vm → sc m →
    (encPadND n delay Lp Lf rep dbg (f m)).1
      = nq (encPadND n delay Lp Lf rep dbg m).1
        (rwOfK K (encPadND n delay Lp Lf rep dbg) m)
  tape : ∀ (m : Mirrored1 P) (i : ℕ), m.vm.ctl.mode = md → ¬ Starved m.vm → sc m →
    padTapesND n rep dbg (f m) i
      = actList blankc (padTapesND n rep dbg m i)
        (acts (encPadND n delay Lp Lf rep dbg m).1
          (rwOfK K (encPadND n delay Lp Lf rep dbg) m) i)

/-- **The same composite on the laid-out family**, under the two head invariants
with the radius-`4` margin. -/
theorem shiftVm_padTapesND_all (n : ℕ) (rep : ChainVM → ChainL)
    (dbg : Mirrored1 P → ℕ → ℕ → List Γc)
    (w : PalPeg.GalilScaffoldChainWatch.State) (m : Mirrored1 P)
    (restC : ℕ → List (Act Γc)) (hrl : ∀ i, (restC i).length ≤ 4)
    (hL : m.vm.left.gap = true → m.vm.left.near ≠ [])
    (hL2 : (moveRight m.vm.left).gap = true → (moveRight m.vm.left).near ≠ [])
    (hC : m.vm.center.gap = true → m.vm.center.near ≠ [])
    (hd0 : dbg ⟨shiftVm w m.vm, m.mirL⟩ 0 = moveDebris2 m.vm.left (dbg m 0))
    (hd1 : dbg ⟨shiftVm w m.vm, m.mirL⟩ 1 = moveDebris m.vm.center (dbg m 1))
    (hdF : ∀ b, 2 ≤ b → b < 6 → dbg ⟨shiftVm w m.vm, m.mirL⟩ b = dbg m b)
    (hrestC : ∀ i, nViews * tView + P + (tMir + tBuf) ≤ i →
      encTapes rep ⟨shiftVm w m.vm, m.mirL⟩ i
        = actList blankc (encTapes rep m i) (restC i))
    (hleft : ∀ i, 4 ≤ pos (encTapesD rep dbg m i))
    (hright : ∀ i, pos (encTapesD rep dbg m i) + 4 ≤ wlen (encTapesD rep dbg m i))
    (i : ℕ) :
    padTapesND n rep dbg ⟨shiftVm w m.vm, m.mirL⟩ i
      = actList blankc (padTapesND n rep dbg m i)
        (shiftActsD m.vm.left m.vm.center restC m.vm.roles i) := by
  have hlen := shiftActsD_length m.vm.left m.vm.center restC hrl m.vm.roles i
  have h1 := hleft i
  have h2 := hright i
  rw [padTapesND, padTapesND, encTapesD1, encTapesD1,
    shiftVm_encTapesD_all rep dbg w m restC hL hL2 hC hd0 hd1 hdF hrestC i]
  exact PalPeg.CloseoutCoreEnc15.padTapesN_actList blankc n _ _ (by omega) (by omega)

/-- **`shiftPick` as a radius-`K` composite residual at every address of the
debris layout.**  Compared with `CloseoutCoreEnc17.shiftVm_tapeActK`, the two
moving cursor blocks are now *proved*; what remains as data is the finite
control (`nq`, `hctl`), the chain block (`restC`, `hrestC`), the `acts`
projection (`acts`, `hacts`; `InputView.gap` is not in `QL`), the debris
discipline (`hd0`/`hd1`/`hdF`) and the `near ≠ []` side conditions. -/
noncomputable def shiftVm_tapeActK' (K n delay Lp Lf : ℕ) (rep : ChainVM → ChainL)
    (dbg : Mirrored1 P → ℕ → ℕ → List Γc)
    (w : PalPeg.GalilScaffoldChainWatch.State) (md : Mode) (sc : Mirrored1 P → Prop)
    (hK : 4 ≤ K)
    (nq : QL delay Lp Lf P QChain → (Fin (tL P tChain) → Window Γc K) →
      QL delay Lp Lf P QChain)
    (hctl : ∀ m : Mirrored1 P, m.vm.ctl.mode = md → ¬ Starved m.vm → sc m →
      (encPadND n delay Lp Lf rep dbg ⟨shiftVm w m.vm, m.mirL⟩).1
        = nq (encPadND n delay Lp Lf rep dbg m).1
          (rwOfK K (encPadND n delay Lp Lf rep dbg) m))
    (acts : QL delay Lp Lf P QChain → (Fin (tL P tChain) → Window Γc K) → ℕ →
      List (Act Γc))
    (hlen : ∀ q ws i, (acts q ws i).length ≤ K)
    (restC : Mirrored1 P → ℕ → List (Act Γc)) (hrl : ∀ m i, (restC m i).length ≤ 4)
    (hacts : ∀ (m : Mirrored1 P) (i : ℕ),
      acts (encPadND n delay Lp Lf rep dbg m).1
          (rwOfK K (encPadND n delay Lp Lf rep dbg) m) i
        = shiftActsD m.vm.left m.vm.center (restC m) m.vm.roles i)
    (hL : ∀ m : Mirrored1 P, m.vm.left.gap = true → m.vm.left.near ≠ [])
    (hL2 : ∀ m : Mirrored1 P,
      (moveRight m.vm.left).gap = true → (moveRight m.vm.left).near ≠ [])
    (hC : ∀ m : Mirrored1 P, m.vm.center.gap = true → m.vm.center.near ≠ [])
    (hd0 : ∀ m : Mirrored1 P,
      dbg ⟨shiftVm w m.vm, m.mirL⟩ 0 = moveDebris2 m.vm.left (dbg m 0))
    (hd1 : ∀ m : Mirrored1 P,
      dbg ⟨shiftVm w m.vm, m.mirL⟩ 1 = moveDebris m.vm.center (dbg m 1))
    (hdF : ∀ (m : Mirrored1 P) (b : ℕ), 2 ≤ b → b < 6 →
      dbg ⟨shiftVm w m.vm, m.mirL⟩ b = dbg m b)
    (hrestC : ∀ (m : Mirrored1 P) (i : ℕ), nViews * tView + P + (tMir + tBuf) ≤ i →
      encTapes rep ⟨shiftVm w m.vm, m.mirL⟩ i
        = actList blankc (encTapes rep m i) (restC m i))
    (hleft : ∀ (m : Mirrored1 P) (i : ℕ), 4 ≤ pos (encTapesD rep dbg m i))
    (hright : ∀ (m : Mirrored1 P) (i : ℕ),
      pos (encTapesD rep dbg m i) + 4 ≤ wlen (encTapesD rep dbg m i)) :
    TapeActKD (P := P) K n delay Lp Lf rep dbg (fun m => ⟨shiftVm w m.vm, m.mirL⟩) md sc where
  nq := nq
  acts := acts
  len_le := hlen
  ctl := hctl
  tape := fun m i hmd hs hsc => by
    rw [hacts m i]
    exact shiftVm_padTapesND_all n rep dbg w m (restC m) (hrl m) (hL m) (hL2 m) (hC m)
      (hd0 m) (hd1 m) (hdF m) (hrestC m) (hleft m) (hright m) i

/-! ## 6. Why the rotation branch is not a bounded rewrite on four tapes -/

theorem pos_actOnG_ge (T : STape Γc) (a : Act Γc) : pos T ≤ pos (actOnG blankc T a) + 1 := by
  cases a with
  | none => simp [actOnG]
  | some sm =>
      obtain ⟨s, mv⟩ := sm
      show pos T ≤ pos (T.applyAction blankc (s, mv)) + 1
      rw [PalPeg.Local.pos_applyAction]
      cases mv <;> simp <;> omega

/-- **A composite of `k` micro-actions moves a head left by at most `k`.** -/
theorem pos_actList_ge (T : STape Γc) (as : List (Act Γc)) :
    pos T ≤ pos (actList blankc T as) + as.length := by
  induction as generalizing T with
  | nil => simp
  | cons a as ih =>
      rw [actList_cons]
      have h1 := pos_actOnG_ge T a
      have h2 := ih (actOnG blankc T a)
      simp only [List.length_cons]
      omega

/-- **Clearing a debris stack is not a bounded composite.**  `dTape l r` has its
head `l.length` cells from the left edge and `dTape [] r'` has it at `0`, so any
realisation costs at least `l.length` micro-actions. -/
theorem not_bounded_clear_dTape (K : ℕ) (l : List (Option (Fin 2))) (r r' : List Γc)
    (hK : K < l.length) :
    ¬ ∃ as : List (Act Γc), as.length ≤ K ∧
      actList blankc (dTape l r) as = dTape [] r' := by
  rintro ⟨as, hlen, has⟩
  have h := pos_actList_ge (dTape l r) as
  rw [has, pos_dTape, pos_dTape] at h
  simp only [List.length_nil] at h
  omega

/-- **The `far` branch of `moveRight` has no bounded realisation on the
four-tape cursor.**  When `near = []` and the queue needs a rotation,
`RTQueue.check` sets `rear := []`; on address `3` of
`CloseoutCoreEnc18.viewTapesD` that is exactly a clearing of a `dTape` whose
live part is the old `rear`.  So `moveRight_actList_rot` is **false** at radius
`K` for every queue with more than `K` rear cells: the rotation must be carried
by the six queue stacks of `CloseoutCoreEnc7.queueTapes6` and a role table, not
by a bounded rewrite of these four tapes. -/
theorem not_bounded_rot_rear (K : ℕ) (v v' : InputView) (d d' : ℕ → List Γc)
    (hrear : K < v.far.rear.length) (hclear : v'.far.rear = []) :
    ¬ ∃ as : List (Act Γc), as.length ≤ K ∧
      actList blankc (viewTapesD v d 3) as = viewTapesD v' d' 3 := by
  have h0 : viewTapesD v d 3 = dTape (v.far.rear.map some) (d 3) := rfl
  have h1 : viewTapesD v' d' 3 = dTape [] (d' 3) := by
    show dTape (v'.far.rear.map some) (d' 3) = _
    rw [hclear]
    rfl
  rw [h0, h1]
  exact not_bounded_clear_dTape K _ (d 3) (d' 3) (by simpa using hrear)

end PalPeg.CloseoutCoreEnc19

#print axioms PalPeg.CloseoutCoreEnc19.encTapesD_tail
#print axioms PalPeg.CloseoutCoreEnc19.shiftVm_encTapes_tailAll
#print axioms PalPeg.CloseoutCoreEnc19.moveRight2_actList
#print axioms PalPeg.CloseoutCoreEnc19.shiftVm_encTapesD_all
#print axioms PalPeg.CloseoutCoreEnc19.shiftVm_padTapesND_all
#print axioms PalPeg.CloseoutCoreEnc19.shiftVm_tapeActK'
#print axioms PalPeg.CloseoutCoreEnc19.pos_actList_ge
#print axioms PalPeg.CloseoutCoreEnc19.not_bounded_clear_dTape
#print axioms PalPeg.CloseoutCoreEnc19.not_bounded_rot_rear
