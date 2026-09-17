import PalPeg.CloseoutCoreEnc22

/-!
# Closeout, step 2w: the initial layout, the chain residue, and `shiftPick` runs

`CloseoutCoreEnc22.shiftVm_tapeActKQ` realises one `shiftPick` step as a
composite of `≤ 28` micro-actions at every address of the nine-tape cursor
layout `encTapesQ`, taking as hypotheses the queue invariants, the layout data
of the two moving cursor blocks, the chain residue `restC`, and the head
margins.  This file (1) exhibits the layout data at a boot state (empty
queues), (2) isolates the chain residue as a property of the uninterpreted
chain representation `rep` alone, and (3) iterates the step along a run of
`shiftPick` steps, producing a layout *family* indexed by the step.  Nothing
here is about the whole machine, so

**無条件 PAL ∈ PEG は未完.**

## What is established (unconditional)

* **§1** `roleIdx` (the identity role table), `sRoleList_empty`, and
  `laysS_initial`: a cursor whose queue is `RTQueue.empty` is laid out by the
  all-empty family with the identity table (`SBound`, `SInj`, `LaysS`), and
  satisfies `RTQueue.Inv` (`RTQueue.inv_empty`).  `qLay_initial` packages this
  for both moving blocks of a `Mirrored1` whose `left`/`center` queues are
  empty (e.g. `LocalInputView.emptyView`).  There is no `GalilVML`-level boot
  state in the repository (`GalilBootVM.initVM0` is a `GalilVM`), so the boot
  state is characterised by `InitialQueues m`.
* **§2** `shiftVm_chain`: a `shiftPick` step rewrites the chain to
  `.watch (chainShiftOne w)`; `encTapes_chainIdx`: the chain block of
  `encTapes` is `chainTapes (rep m.vm.chain)`.  Hence the residue `restC` is
  **not a function of the step but of `rep`**: `ChainShiftBounded rep` (the
  chain tapes of `rep (.watch (chainShiftOne w))` are a `≤ 4`-composite of
  those of `rep c`, for every `c`) yields `restC`/`hrl`/`hrestC` at every
  state (`restC_of_rep`), initially and across every step alike
  (`restC_initial`, `restC_step`).  No bound on `restC` can be *derived* here
  because `rep` is uninterpreted.
* **§3** `shiftRun`, `QLay`, `qLay_step`, and **`shiftVm_tapeActKQ_run`**:
  along a run of `shiftPick` steps from any state with `QLay m0 lay0`, there
  is a layout family `lay i`/`dbg i` with `QLay` at every step, every step a
  composite of `≤ K` micro-actions (`28 ≤ K`) on `encTapesQ`, and on the padded
  family `padTapesNQ` whenever the head margins hold at that step.

## What is *not* established, one line each

1. **`ChainShiftBounded rep`** is a hypothesis: the chain block is read through
   the uninterpreted `rep`.
2. **The head margins** `hleft`/`hright` remain per-step hypotheses of the
   padded law (they are stated on the produced layout at step `i`).
3. **The layout family is chosen by `Classical.choose`** from the existential
   step theorem, so it is a function of the run, not of the state alone; the
   `TapeActK` structure (finite control `nq`/`acts`) is still not built.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutCoreEnc23

open PalPeg PalPeg.Program
open PalPeg.Local (pos)
open PalPeg.CloseoutCoreStep (Γc blankc nViews tView tMir tBuf)
open PalPeg.CloseoutCoreEnc (encTapes chainTapes)
open PalPeg.CloseoutCoreEnc5 (wlen)
open PalPeg.CloseoutCoreEnc12 (Act actList)
open PalPeg.CloseoutCoreEnc21 (SRole SRoles SInj LaysS sRoleList)
open PalPeg.CloseoutCoreEnc22
open PalPeg.LocalInputView (InputView)
open PalPeg.LocalState (GalilVML)
open PalPeg.LocalReplayParked (Mirrored1)
open PalPeg.LocalChain (ChainL)
open PalPeg.GalilScaffoldChainInputSupply (ChainVM chainShiftOne)
open PalPeg.LocalTick3 (shiftVm)
open PalPeg.RTQueue (Queue)

variable {P : ℕ}

/-! ## 1. The initial layout: empty queues, identity role table -/

/-- The identity role table. -/
def roleIdx : SRole → ℕ
  | .front => 0
  | .rear => 1
  | .fwd => 2
  | .fwd' => 3
  | .rev => 4
  | .rev' => 5
  | .shadow => 6

theorem sbound_roleIdx : SBound roleIdx := by
  intro ro; cases ro <;> simp [roleIdx]

theorem sinj_roleIdx : SInj roleIdx := by
  intro a b h
  cases a <;> cases b <;> first | rfl | (simp [roleIdx] at h)

/-- Every role of the empty queue carries the empty list. -/
theorem sRoleList_empty (ro : SRole) : sRoleList (RTQueue.empty : Queue (Fin 2)) ro = [] := by
  cases ro <;> rfl

/-- The all-empty physical family and junk. -/
def emptyFam : ℕ → List (Fin 2) := fun _ => []

theorem laysS_empty : LaysS (RTQueue.empty : Queue (Fin 2)) roleIdx emptyFam emptyFam := by
  intro ro; rw [sRoleList_empty]; rfl

/-- **The layout data at a cursor with the empty queue**: identity table, all
stacks empty, and the queue invariant. -/
theorem laysS_initial (v : InputView) (hv : v.far = RTQueue.empty) :
    SBound roleIdx ∧ SInj roleIdx ∧ LaysS v.far roleIdx emptyFam emptyFam ∧
      RTQueue.Inv v.far := by
  rw [hv]
  exact ⟨sbound_roleIdx, sinj_roleIdx, laysS_empty, RTQueue.inv_empty⟩

theorem emptyView_far : (LocalInputView.emptyView).far = RTQueue.empty := rfl

/-- The layout data of the two moving blocks, as `shiftVm_tapeActKQ` wants it. -/
structure QLay (m : Mirrored1 P) (lay : ℕ → ℕ → List (Fin 2)) : Prop where
  left : ∃ (ρ : SRoles) (J : ℕ → List (Fin 2)),
    SBound ρ ∧ SInj ρ ∧ LaysS m.vm.left.far ρ (lay 0) J
  center : ∃ (ρ : SRoles) (J : ℕ → List (Fin 2)),
    SBound ρ ∧ SInj ρ ∧ LaysS m.vm.center.far ρ (lay 1) J
  invL : RTQueue.Inv m.vm.left.far
  invC : RTQueue.Inv m.vm.center.far

/-- The boot condition on the two moving cursors: both queues empty. -/
def InitialQueues (m : Mirrored1 P) : Prop :=
  m.vm.left.far = RTQueue.empty ∧ m.vm.center.far = RTQueue.empty

/-- The initial physical family: every block, every address empty. -/
def lay0 : ℕ → ℕ → List (Fin 2) := fun _ _ => []

/-- The initial debris: none. -/
def dbg0 : ℕ → ℕ → List Γc := fun _ _ => []

theorem qLay_initial (m : Mirrored1 P) (h : InitialQueues m) : QLay m lay0 := by
  obtain ⟨hL, hC⟩ := h
  obtain ⟨hb, hinj, hlayL, hinvL⟩ := laysS_initial m.vm.left hL
  obtain ⟨_, _, hlayC, hinvC⟩ := laysS_initial m.vm.center hC
  exact ⟨⟨roleIdx, emptyFam, hb, hinj, hlayL⟩, ⟨roleIdx, emptyFam, hb, hinj, hlayC⟩, hinvL, hinvC⟩

/-! ## 2. The chain residue is a property of `rep` -/

theorem shiftVm_chain (w : PalPeg.GalilScaffoldChainWatch.State) (x : GalilVML P) :
    (shiftVm w x).chain = .watch (chainShiftOne w) := rfl

/-- The chain block of `encTapes`. -/
theorem encTapes_chainIdx (rep : ChainVM → ChainL) (m : Mirrored1 P) (i : ℕ)
    (hi : nViews * tView + P + (tMir + tBuf) ≤ i) :
    encTapes rep m i = chainTapes (rep m.vm.chain) (i - nViews * tView - P - tMir - tBuf) := by
  have hnt : nViews * tView = 24 := rfl
  have htv : tView = 4 := rfl
  have hm : tMir = 7 := rfl
  have hb : tBuf = 44 := rfl
  have c1 : ¬ i < tView := by omega
  have c2 : ¬ i < 2 * tView := by omega
  have c3 : ¬ i < 3 * tView := by omega
  have c4 : ¬ i < 4 * tView := by omega
  have c5 : ¬ i < 5 * tView := by omega
  have c6 : ¬ i < 6 * tView := by omega
  have c7 : ¬ i - nViews * tView < P := by omega
  unfold encTapes
  rw [if_neg c1, if_neg c2, if_neg c3, if_neg c4, if_neg c5, if_neg c6, dif_neg c7]
  dsimp only
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega)]

/-- **The chain contract on `rep`**: the chain tapes after a shift are a
`≤ 4`-composite of the chain tapes before, whatever the chain was. -/
def ChainShiftBounded (rep : ChainVM → ChainL) : Prop :=
  ∀ (w : PalPeg.GalilScaffoldChainWatch.State) (c : ChainVM),
    ∃ rc : ℕ → List (Act Γc), (∀ j, (rc j).length ≤ 4) ∧
      ∀ j, chainTapes (rep (.watch (chainShiftOne w))) j
        = actList blankc (chainTapes (rep c) j) (rc j)

/-- **`restC` from the contract, at every state.** -/
theorem restC_of_rep (rep : ChainVM → ChainL) (hrep : ChainShiftBounded rep)
    (w : PalPeg.GalilScaffoldChainWatch.State) (m : Mirrored1 P) :
    ∃ restC : ℕ → List (Act Γc), (∀ i, (restC i).length ≤ 4) ∧
      ∀ i, nViews * tView + P + (tMir + tBuf) ≤ i →
        encTapes rep ⟨shiftVm w m.vm, m.mirL⟩ i
          = actList blankc (encTapes rep m i) (restC i) := by
  obtain ⟨rc, hrl, hrc⟩ := hrep w m.vm.chain
  refine ⟨fun i => rc (i - nViews * tView - P - tMir - tBuf), fun i => hrl _, ?_⟩
  intro i hi
  rw [encTapes_chainIdx rep _ i hi, encTapes_chainIdx rep m i hi]
  show chainTapes (rep (shiftVm w m.vm).chain) _ = _
  rw [shiftVm_chain]
  exact hrc _

/-- `restC` at a boot state (chain `.idle`): the same contract instance. -/
theorem restC_initial (rep : ChainVM → ChainL) (hrep : ChainShiftBounded rep)
    (w : PalPeg.GalilScaffoldChainWatch.State) (m : Mirrored1 P) (hidle : m.vm.chain = .idle) :
    ∃ restC : ℕ → List (Act Γc), (∀ i, (restC i).length ≤ 4) ∧
      ∀ i, nViews * tView + P + (tMir + tBuf) ≤ i →
        encTapes rep ⟨shiftVm w m.vm, m.mirL⟩ i
          = actList blankc (encTapes rep m i) (restC i) :=
  restC_of_rep rep hrep w m

/-- `restC` after a step: the residue of the *next* step is again `≤ 4`, since
the contract is state-independent. -/
theorem restC_step (rep : ChainVM → ChainL) (hrep : ChainShiftBounded rep)
    (w w' : PalPeg.GalilScaffoldChainWatch.State) (m : Mirrored1 P) :
    ∃ restC : ℕ → List (Act Γc), (∀ i, (restC i).length ≤ 4) ∧
      ∀ i, nViews * tView + P + (tMir + tBuf) ≤ i →
        encTapes rep ⟨shiftVm w' (shiftVm w m.vm), m.mirL⟩ i
          = actList blankc (encTapes rep ⟨shiftVm w m.vm, m.mirL⟩ i) (restC i) :=
  restC_of_rep rep hrep w' ⟨shiftVm w m.vm, m.mirL⟩

/-! ## 3. Runs of `shiftPick` steps -/

/-- A run of `shiftPick` steps driven by the watch states `ws`. -/
noncomputable def shiftRun (ws : ℕ → PalPeg.GalilScaffoldChainWatch.State) (m0 : Mirrored1 P) :
    ℕ → Mirrored1 P
  | 0 => m0
  | i + 1 => ⟨shiftVm (ws i) (shiftRun ws m0 i).vm, (shiftRun ws m0 i).mirL⟩

theorem shiftRun_zero (ws : ℕ → PalPeg.GalilScaffoldChainWatch.State) (m0 : Mirrored1 P) :
    shiftRun ws m0 0 = m0 := rfl

theorem shiftRun_succ (ws : ℕ → PalPeg.GalilScaffoldChainWatch.State) (m0 : Mirrored1 P)
    (i : ℕ) :
    shiftRun ws m0 (i + 1) = ⟨shiftVm (ws i) (shiftRun ws m0 i).vm, (shiftRun ws m0 i).mirL⟩ :=
  rfl

/-- A physical layout: family and debris. -/
abbrev Lay : Type := (ℕ → ℕ → List (Fin 2)) × (ℕ → ℕ → List Γc)

/-- **One step, with `QLay` carried.** -/
theorem qLay_step (rep : ChainVM → ChainL) (hrep : ChainShiftBounded rep)
    (w : PalPeg.GalilScaffoldChainWatch.State) (m : Mirrored1 P) (p : Lay)
    (h : QLay m p.1) :
    ∃ p' : Lay, QLay (⟨shiftVm w m.vm, m.mirL⟩ : Mirrored1 P) p'.1 ∧
      ∃ acts : ℕ → List (Act Γc), (∀ i, (acts i).length ≤ 28) ∧
        ∀ i, encTapesQ rep p'.1 p'.2 ⟨shiftVm w m.vm, m.mirL⟩ i
          = actList blankc (encTapesQ rep p.1 p.2 m i) (acts i) := by
  obtain ⟨restC, hrl, hrestC⟩ := restC_of_rep rep hrep w m
  obtain ⟨ρL, JL, hbL, hinjL, hlayL⟩ := h.left
  obtain ⟨ρC, JC, hbC, hinjC, hlayC⟩ := h.center
  obtain ⟨lay', dbg', acts, _, hlayL', hlayC', hlen, hall⟩ :=
    shiftVm_encTapesQ_all rep p.1 p.2 w m restC hrl ρL ρC JL JC hbL hinjL hlayL h.invL
      hbC hinjC hlayC h.invC hrestC
  refine ⟨(lay', dbg'), ⟨hlayL', hlayC', ?_, ?_⟩, acts, hlen, hall⟩
  · show RTQueue.Inv (shiftVm w m.vm).left.far
    rw [PalPeg.CloseoutCoreEnc19.shiftVm_left]
    exact inv_moveRight _ (inv_moveRight _ h.invL)
  · show RTQueue.Inv (shiftVm w m.vm).center.far
    rw [PalPeg.CloseoutCoreEnc19.shiftVm_center]
    exact inv_moveRight _ h.invC

/-- The layout family along a run, chosen step by step. -/
noncomputable def laySeq (rep : ChainVM → ChainL) (hrep : ChainShiftBounded rep)
    (ws : ℕ → PalPeg.GalilScaffoldChainWatch.State) (m0 : Mirrored1 P) (p0 : Lay)
    (h0 : QLay m0 p0.1) : (i : ℕ) → {p : Lay // QLay (shiftRun ws m0 i) p.1}
  | 0 => ⟨p0, h0⟩
  | i + 1 =>
      ⟨Classical.choose (qLay_step rep hrep (ws i) (shiftRun ws m0 i) (laySeq rep hrep ws m0 p0 h0 i).1
          (laySeq rep hrep ws m0 p0 h0 i).2),
       (Classical.choose_spec (qLay_step rep hrep (ws i) (shiftRun ws m0 i)
          (laySeq rep hrep ws m0 p0 h0 i).1 (laySeq rep hrep ws m0 p0 h0 i).2)).1⟩

/-- **`shiftPick` runs as radius-`K` composites on the nine-tape cursor
layout, for every `28 ≤ K`**: from any state with `QLay m0 lay0` (in
particular a boot state, `qLay_initial`), there is a layout family `lay i`/
`dbg i` along the run such that `QLay` holds at every step, each step is a
composite of `≤ K` micro-actions at every address of `encTapesQ`, and of the
padded family `padTapesNQ` whenever the head margins hold at that step. -/
theorem shiftVm_tapeActKQ_run (K n : ℕ) (hK : 28 ≤ K) (rep : ChainVM → ChainL)
    (hrep : ChainShiftBounded rep) (ws : ℕ → PalPeg.GalilScaffoldChainWatch.State)
    (m0 : Mirrored1 P) (lay0 : ℕ → ℕ → List (Fin 2)) (dbg0 : ℕ → ℕ → List Γc)
    (h0 : QLay m0 lay0) :
    ∃ (lay : ℕ → ℕ → ℕ → List (Fin 2)) (dbg : ℕ → ℕ → ℕ → List Γc)
      (acts : ℕ → ℕ → List (Act Γc)),
      lay 0 = lay0 ∧ dbg 0 = dbg0 ∧
      (∀ i, QLay (shiftRun ws m0 i) (lay i)) ∧
      (∀ i j, (acts i j).length ≤ K) ∧
      (∀ i j, encTapesQ rep (lay (i + 1)) (dbg (i + 1)) (shiftRun ws m0 (i + 1)) j
        = actList blankc (encTapesQ rep (lay i) (dbg i) (shiftRun ws m0 i) j) (acts i j)) ∧
      (∀ i, (∀ j, K ≤ pos (encTapesQ rep (lay i) (dbg i) (shiftRun ws m0 i) j)) →
        (∀ j, pos (encTapesQ rep (lay i) (dbg i) (shiftRun ws m0 i) j) + K
          ≤ wlen (encTapesQ rep (lay i) (dbg i) (shiftRun ws m0 i) j)) →
        ∀ j, padTapesNQ n rep (lay (i + 1)) (dbg (i + 1)) (shiftRun ws m0 (i + 1)) j
          = actList blankc (padTapesNQ n rep (lay i) (dbg i) (shiftRun ws m0 i) j) (acts i j)) := by
  let seq := laySeq rep hrep ws m0 (lay0, dbg0) h0
  let spec := fun i => (Classical.choose_spec (qLay_step rep hrep (ws i) (shiftRun ws m0 i)
    (seq i).1 (seq i).2)).2
  refine ⟨fun i => (seq i).1.1, fun i => (seq i).1.2,
    fun i => Classical.choose (spec i), rfl, rfl, fun i => (seq i).2, ?_, ?_, ?_⟩
  · intro i j
    exact le_trans ((Classical.choose_spec (spec i)).1 j) hK
  · intro i j
    exact (Classical.choose_spec (spec i)).2 j
  · intro i hleft hright j
    have h1 := (Classical.choose_spec (spec i)).1 j
    have h2 : K ≤ pos (encTapesQ rep (seq i).1.1 (seq i).1.2 (shiftRun ws m0 i) j) := hleft j
    have h3 : pos (encTapesQ rep (seq i).1.1 (seq i).1.2 (shiftRun ws m0 i) j) + K
        ≤ wlen (encTapesQ rep (seq i).1.1 (seq i).1.2 (shiftRun ws m0 i) j) := hright j
    have hstep : encTapesQ rep (seq (i + 1)).1.1 (seq (i + 1)).1.2 (shiftRun ws m0 (i + 1)) j
        = actList blankc (encTapesQ rep (seq i).1.1 (seq i).1.2 (shiftRun ws m0 i) j)
          (Classical.choose (spec i) j) :=
      (Classical.choose_spec (spec i)).2 j
    show padTapesNQ n rep (seq (i + 1)).1.1 (seq (i + 1)).1.2 (shiftRun ws m0 (i + 1)) j
      = actList blankc (padTapesNQ n rep (seq i).1.1 (seq i).1.2 (shiftRun ws m0 i) j)
          (Classical.choose (spec i) j)
    unfold padTapesNQ
    rw [hstep]
    exact PalPeg.CloseoutCoreEnc15.padTapesN_actList blankc n _ _ (by omega) (by omega)

end PalPeg.CloseoutCoreEnc23

#print axioms PalPeg.CloseoutCoreEnc23.laysS_initial
#print axioms PalPeg.CloseoutCoreEnc23.qLay_initial
#print axioms PalPeg.CloseoutCoreEnc23.encTapes_chainIdx
#print axioms PalPeg.CloseoutCoreEnc23.restC_of_rep
#print axioms PalPeg.CloseoutCoreEnc23.restC_initial
#print axioms PalPeg.CloseoutCoreEnc23.restC_step
#print axioms PalPeg.CloseoutCoreEnc23.qLay_step
#print axioms PalPeg.CloseoutCoreEnc23.shiftVm_tapeActKQ_run
