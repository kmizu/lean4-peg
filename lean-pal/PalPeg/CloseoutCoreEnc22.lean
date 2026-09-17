import PalPeg.CloseoutCoreEnc21

/-!
# Closeout, step 2v: `shiftPick` on the seven-role shadow layout (`tViewQ = 9`)

`CloseoutCoreEnc21` realises every Hood–Melville sub-step (`SStep`) of the
cursor queue as a `Delta` family of `≤ 2` micro-actions per address of the
eight-plus-tape cursor `viewTapesQ`, and decomposes `RTQueue.tail` into a chain
of sub-steps under the HM invariant `hrot`.  `CloseoutCoreEnc19` assembles the
whole core on the debris layout `encTapesD` but excludes the `far` branch of
`LocalInputView.moveRight` by the side condition `near ≠ []`.  This file joins
the two: the cursor blocks of the core are laid out by `viewTapesQ` (width
`tViewQ = 9`: `back`+`focus`, `near`, seven role stacks), and one `shiftVm`
step is a composite of `≤ 28` micro-actions at **every** address, with **no**
`near ≠ []` side condition.  Nothing here is about the whole machine, so

**無条件 PAL ∈ PEG は未完.**

## What is established (unconditional)

* **§1** `Chain n` / `ChainLe n`: sub-step chains with an explicit length.
  `tail_chainLe`: `RTQueue.tail` is a chain of `≤ 6` sub-steps (`tailPop`,
  `inval`, optional `rotStart`, `exec`, `exec`, optional `install`) under
  `hrot`; `tail_hrot`: `hrot` **follows from `RTQueue.Inv`** (the queue's own
  invariant, `PalPeg.RTQueue.Inv`; this is the derivation inside
  `RTQueue.tail_spec`), so `tail_chainLe_inv` needs only `Inv`.
* **§2** `SBound ρ` (`∀ ro, ρ ro < 7`): the role table stays inside the block.
  `sstep_laysB` / `moveRightS_actListB` are `CloseoutCoreEnc21.sstep_lays` /
  `moveRightS_actList` with the bound carried through (the new table is always
  `ρ`, `rotRolesS ρ` or `doneRolesS ρ`).
* **§3** `chain_actList`: a chain of `n` sub-steps on `v.far` is a composite of
  `≤ 2n` micro-actions at every address of `viewTapesQ`, and the result is laid
  out again with a bounded injective table.
* **§4** `moveRightQ_actList`: **every** branch of `LocalInputView.moveRight`
  (half-step, pushed-back `near`, empty queue, and the `far` dequeue) is a
  composite of `≤ 14` micro-actions at every address (`2` for the head push
  plus `2 · 6` for the `tail` chain).  `inv_moveRight`: `Inv` is preserved.
* **§5** `encTapesQ`: `CloseoutCoreEnc19.encTapesD` with the six cursor blocks
  widened to `tViewQ = 9` and laid out by `viewTapesQ` (the tail is
  `encTapes` shifted by `offQ = 30`).  `shiftVm_encTapesQ_all`: `shiftPick` is
  a composite of `≤ 28` micro-actions at every address, and
  **`shiftVm_tapeActKQ`**: the same on the padded family `padTapesNQ` at any
  radius `28 ≤ K`, i.e. the calibration `K ≤ 64` holds with `K = 28`.

## What is *not* established, one line each

1. **The layout is existential, not a function of the state**: `sstep_lays`
   chooses the new table/junk by cases, so `encTapesQ` takes the physical
   family `lay`/`dbg` as parameters and the theorem *produces* the new ones;
   the `TapeActK` structure (`f : Mirrored1 P → Mirrored1 P` with the layout a
   function of `m`) is therefore not instantiated here.
2. **Hypotheses left**: `RTQueue.Inv` of the `left`/`center` queues (this is
   `LocalInputView.WF`, which replaces `hrot`); `LaysS`/`SInj`/`SBound` of the
   two cursor blocks at the start; the chain block `restC`/`hrestC` and the
   head margins `hleft`/`hright`, exactly as in `CloseoutCoreEnc19`.
3. **The finite control is not built** (`CloseoutCoreEnc21` item 3 stands).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutCoreEnc22

open PalPeg PalPeg.Program
open PalPeg.Local (pos)
open PalPeg.CloseoutCoreStep (Γc blankc tL QL nViews tView tMir tBuf)
open PalPeg.CloseoutCoreEnc (encTapes)
open PalPeg.CloseoutCoreEnc3 (shift1)
open PalPeg.CloseoutCoreEnc5 (wlen)
open PalPeg.CloseoutCoreEnc8 (padRN)
open PalPeg.CloseoutCoreEnc12 (Act actList)
open PalPeg.CloseoutCoreEnc13 (actList_append)
open PalPeg.CloseoutCoreEnc15 (padTapesN_actList)
open PalPeg.CloseoutCoreEnc17 (shiftActs shiftActs_length)
open PalPeg.CloseoutCoreEnc18 (dTape popActs pushActs pop_dTape push_dTape pushActs_length
  popActs_length)
open PalPeg.CloseoutCoreEnc19 (shiftVm_encTapes_tailAll shiftVm_left shiftVm_center
  shiftVm_right shiftVm_walkerView shiftVm_fppWalker)
open PalPeg.CloseoutCoreEnc20 (Delta dApply viewTapesQ qActs qDebris qActs_length viewTapesQ_delta
  rotStart check_rot)
open PalPeg.CloseoutCoreEnc21
open PalPeg.LocalInputView (InputView moveRight stepRight)
open PalPeg.LocalState (GalilVML Ctr)
open PalPeg.LocalReplayParked (Mirrored1)
open PalPeg.LocalChain (ChainL)
open PalPeg.GalilScaffoldChainInputSupply (ChainVM)
open PalPeg.LocalTick3 (shiftVm)
open PalPeg.RTQueue (Queue)

variable {P : ℕ}

/-! ## 1. Chains of sub-steps with an explicit length -/

/-- A chain of exactly `n` sub-steps. -/
def Chain : ℕ → Queue (Fin 2) → Queue (Fin 2) → Prop
  | 0, q, q' => q = q'
  | n + 1, q, q'' => ∃ q', SStep q q' ∧ Chain n q' q''

/-- A chain of at most `n` sub-steps. -/
def ChainLe (n : ℕ) (q q' : Queue (Fin 2)) : Prop := ∃ k, k ≤ n ∧ Chain k q q'

theorem chain_zero (q q' : Queue (Fin 2)) : Chain 0 q q' ↔ q = q' := Iff.rfl

theorem chain_succ (n : ℕ) (q q'' : Queue (Fin 2)) :
    Chain (n + 1) q q'' ↔ ∃ q', SStep q q' ∧ Chain n q' q'' := Iff.rfl

theorem chain_trans (m n : ℕ) : ∀ (q q' q'' : Queue (Fin 2)),
    Chain m q q' → Chain n q' q'' → Chain (m + n) q q'' := by
  induction m with
  | zero =>
      intro q q' q'' h1 h2
      have e : q = q' := (chain_zero q q').mp h1
      subst e
      rw [Nat.zero_add]
      exact h2
  | succ m ih =>
      intro q q' q'' h1 h2
      obtain ⟨q1, hs, hc⟩ := (chain_succ m q q').mp h1
      have e : m + 1 + n = (m + n) + 1 := by omega
      rw [e]
      exact (chain_succ (m + n) q q'').mpr ⟨q1, hs, ih q1 q' q'' hc h2⟩

theorem chainLe_refl (n : ℕ) (q : Queue (Fin 2)) : ChainLe n q q :=
  ⟨0, Nat.zero_le n, (chain_zero q q).mpr rfl⟩

theorem chainLe_of_step {q q' : Queue (Fin 2)} (hs : SStep q q') : ChainLe 1 q q' :=
  ⟨1, le_refl 1, (chain_succ 0 q q').mpr ⟨q', hs, (chain_zero q' q').mpr rfl⟩⟩

theorem chainLe_trans' {m n k : ℕ} {q q' q'' : Queue (Fin 2)}
    (h1 : ChainLe m q q') (h2 : ChainLe n q' q'') (hk : m + n ≤ k) : ChainLe k q q'' := by
  obtain ⟨k1, hk1, c1⟩ := h1
  obtain ⟨k2, hk2, c2⟩ := h2
  exact ⟨k1 + k2, by omega, chain_trans k1 k2 q q' q'' c1 c2⟩

theorem chainLe_mono {m n : ℕ} {q q' : Queue (Fin 2)} (h : m ≤ n) (hc : ChainLe m q q') :
    ChainLe n q q' := by
  obtain ⟨k, hk, c⟩ := hc
  exact ⟨k, by omega, c⟩

theorem finish_chainLe (q : Queue (Fin 2)) : ChainLe 1 q (finish q) := by
  unfold finish
  split
  · next f hf => exact chainLe_of_step (SStep.install q f hf)
  · exact chainLe_refl 1 q

theorem exec_exec_finish_chainLe (q : Queue (Fin 2)) :
    ChainLe 3 q (finish { q with state := RTQueue.exec (RTQueue.exec q.state) }) :=
  chainLe_trans' (k := 3) (chainLe_of_step (SStep.exec q))
    (chainLe_trans' (k := 2) (chainLe_of_step (SStep.exec _)) (finish_chainLe _) (by omega))
    (by omega)

/-- **`check` is a chain of `≤ 4` sub-steps** under `RTQueue.PInv.rot`. -/
theorem check_chainLe (q : Queue (Fin 2)) (hrot : q.lenf < q.lenr → q.state = .idle) :
    ChainLe 4 q (RTQueue.check q) := by
  by_cases hle : q.lenr ≤ q.lenf
  · rw [RTQueue.check, if_pos hle, exec2_eq_finish]
    exact chainLe_mono (by omega) (exec_exec_finish_chainLe q)
  · rw [check_rot q hle, exec2_eq_finish]
    exact chainLe_trans' (k := 4)
      (chainLe_of_step (SStep.rotStart q (hrot (Nat.lt_of_not_le hle))))
      (exec_exec_finish_chainLe _) (by omega)

/-- **`tail` is a chain of `≤ 6` sub-steps** under the HM invariant. -/
theorem tail_chainLe (q : Queue (Fin 2))
    (hrot : q.lenf - 1 < q.lenr → RTQueue.invalidate q.state = .idle) :
    ChainLe 6 q (RTQueue.tail q) := by
  unfold RTQueue.tail
  split
  · exact chainLe_refl 6 q
  · next c f hfr =>
      exact chainLe_trans' (k := 6) (chainLe_of_step (SStep.tailPop q c f hfr))
        (chainLe_trans' (k := 5) (chainLe_of_step (SStep.inval _)) (check_chainLe _ hrot)
          (by omega))
        (by omega)

/-- **`hrot` follows from the queue's own invariant `RTQueue.Inv`**: this is the
derivation inside `RTQueue.tail_spec` (`rem = 0` from `pot_len`, then
`eq_idle_of_rem_zero`). -/
theorem tail_hrot (q : Queue (Fin 2)) (hq : RTQueue.Inv q) :
    q.lenf - 1 < q.lenr → RTQueue.invalidate q.state = .idle := by
  intro hlt
  have hpl := hq.pot_len
  have hst : q.state = .idle := RTQueue.eq_idle_of_rem_zero hq.nd (by omega)
  rw [hst]
  rfl

theorem tail_chainLe_inv (q : Queue (Fin 2)) (hq : RTQueue.Inv q) :
    ChainLe 6 q (RTQueue.tail q) :=
  tail_chainLe q (tail_hrot q hq)

/-! ## 2. Bounded role tables: `sstep_lays` with the bound carried through -/

/-- The seven role stacks live at addresses `2`–`8` of the block. -/
def SBound (ρ : SRoles) : Prop := ∀ ro, ρ ro < 7

theorem sbound_rotRolesS {ρ : SRoles} (hb : SBound ρ) : SBound (rotRolesS ρ) :=
  fun ro => hb (rotPerm ro)

theorem sbound_doneRolesS {ρ : SRoles} (hb : SBound ρ) : SBound (doneRolesS ρ) :=
  fun ro => hb (donePerm ro)

/-- `CloseoutCoreEnc21.sstep_lays`, with `SBound` preserved. -/
theorem sstep_laysB (q q' : Queue (Fin 2)) (hs : SStep q q') (ρ : SRoles)
    (L J : ℕ → List (Fin 2)) (hb : SBound ρ) (hinj : SInj ρ) (h : LaysS q ρ L J) :
    ∃ (ρ' : SRoles) (J' : ℕ → List (Fin 2)) (u : ℕ → Delta),
      SBound ρ' ∧ SInj ρ' ∧ LaysS q' ρ' (fun i => dApply (u i) (L i)) J' := by
  have hL : ∀ ro, L (ρ ro) = sRoleList q ro ++ J (ρ ro) := h
  cases hs with
  | snocPush a =>
      refine ⟨ρ, J, toAddr ρ (pushRearD a), hb, hinj, laysS_delta hinj h _ ?_⟩
      intro ro; cases ro <;> simp [pushRearD, dApply, sRoleList]
  | tailPop c f hfr =>
      cases hst : q.state with
      | idle =>
          refine ⟨ρ, J, toAddr ρ (tailD true), hb, hinj, laysS_delta hinj h _ ?_⟩
          intro ro; cases ro <;> simp [tailD, dApply, sRoleList, hst, hfr]
      | reversing ok f0 f' r r' =>
          refine ⟨ρ, J, toAddr ρ (tailD false), hb, hinj, laysS_delta hinj h _ ?_⟩
          intro ro; cases ro <;> simp [tailD, dApply, sRoleList, hst, hfr]
      | appending ok f' r' =>
          refine ⟨ρ, J, toAddr ρ (tailD false), hb, hinj, laysS_delta hinj h _ ?_⟩
          intro ro; cases ro <;> simp [tailD, dApply, sRoleList, hst, hfr]
      | done f0 =>
          refine ⟨ρ, J, toAddr ρ (tailD false), hb, hinj, laysS_delta hinj h _ ?_⟩
          intro ro; cases ro <;> simp [tailD, dApply, sRoleList, hst, hfr]
  | inval =>
      rcases invalidate_cases q.state with
        ⟨ok, f, f', r, r', hst⟩ | ⟨f', x, r', hst⟩ | ⟨ok, f', r', hst⟩ | he
      · refine ⟨ρ, J, toAddr ρ (fun _ => .keep), hb, hinj, laysS_delta hinj h _ ?_⟩
        intro ro; cases ro <;> simp [dApply, sRoleList, hst, RTQueue.invalidate]
      · refine ⟨ρ, ovrL (ρ .fwd') (f' ++ J (ρ .fwd')) J, toAddr ρ invalDoneD, hb, hinj,
          laysS_delta hinj h _ ?_⟩
        intro ro; cases ro <;>
          simp [invalDoneD, dApply, sRoleList, hst, RTQueue.invalidate, ovrL, sinj_iff hinj]
      · refine ⟨ρ, J, toAddr ρ (fun _ => .keep), hb, hinj, laysS_delta hinj h _ ?_⟩
        intro ro; cases ro <;> simp [dApply, sRoleList, hst, RTQueue.invalidate]
      · have hq : ({ q with state := RTQueue.invalidate q.state } : Queue (Fin 2)) = q := by
          rw [he]
        rw [hq]
        exact ⟨ρ, J, fun _ => .keep, hb, hinj, h⟩
  | rotStart hidle =>
      refine ⟨rotRolesS ρ, J, fun _ => .keep, sbound_rotRolesS hb, sinj_rotRolesS hinj, ?_⟩
      intro ro
      show L (rotRolesS ρ ro) = _
      cases ro <;> simp [rotRolesS, rotPerm, hL, sRoleList, rotStart, hidle]
  | exec =>
      rcases exec_cases q.state with
        ⟨ok, x, f, f', y, r, r', hst⟩ | ⟨ok, f', y, r', hst⟩ | ⟨f', r', hst⟩ |
        ⟨ok, x, f', r', hst⟩ | he
      · refine ⟨ρ, J, toAddr ρ (revD x y), hb, hinj, laysS_delta hinj h _ ?_⟩
        intro ro; cases ro <;> simp [revD, dApply, sRoleList, hst, RTQueue.exec]
      · refine ⟨ρ, J, toAddr ρ (appStartD y), hb, hinj, laysS_delta hinj h _ ?_⟩
        intro ro; cases ro <;> simp [appStartD, dApply, sRoleList, hst, RTQueue.exec]
      · refine ⟨ρ, ovrL (ρ .fwd') (f' ++ J (ρ .fwd')) J, toAddr ρ (fun _ => .keep), hb, hinj,
          laysS_delta hinj h _ ?_⟩
        intro ro; cases ro <;>
          simp [dApply, sRoleList, hst, RTQueue.exec, ovrL, sinj_iff hinj]
      · refine ⟨ρ, J, toAddr ρ (appD x), hb, hinj, laysS_delta hinj h _ ?_⟩
        intro ro; cases ro <;> simp [appD, dApply, sRoleList, hst, RTQueue.exec]
      · have hq : ({ q with state := RTQueue.exec q.state } : Queue (Fin 2)) = q := by
          rw [he]
        rw [hq]
        exact ⟨ρ, J, fun _ => .keep, hb, hinj, h⟩
  | install f hst =>
      refine ⟨doneRolesS ρ, ovrL (ρ .front) (q.front ++ J (ρ .front)) J, fun _ => .keep,
        sbound_doneRolesS hb, sinj_doneRolesS hinj, ?_⟩
      intro ro
      show L (doneRolesS ρ ro) = _
      cases ro <;> simp [doneRolesS, donePerm, hL, sRoleList, hst, ovrL, sinj_iff hinj]

/-- `CloseoutCoreEnc21.moveRightS_actList`, with `SBound` preserved. -/
theorem moveRightS_actListB (v : InputView) (L J : ℕ → List (Fin 2)) (d : ℕ → List Γc)
    (ρ : SRoles) (hb : SBound ρ) (hinj : SInj ρ) (h : LaysS v.far ρ L J) (q' : Queue (Fin 2))
    (hs : SStep v.far q') :
    ∃ (ρ' : SRoles) (J' : ℕ → List (Fin 2)) (u : ℕ → Delta),
      SBound ρ' ∧ SInj ρ' ∧ LaysS q' ρ' (fun i => dApply (u i) (L i)) J' ∧
      ∀ i, viewTapesQ { v with far := q' } (fun i => dApply (u i) (L i)) (qDebris u L d) i
            = actList blankc (viewTapesQ v L d i) (qActs u L i) ∧ (qActs u L i).length ≤ 2 := by
  obtain ⟨ρ', J', u, hb', hinj', hl⟩ := sstep_laysB v.far q' hs ρ L J hb hinj h
  refine ⟨ρ', J', u, hb', hinj', hl, fun i => ⟨?_, qActs_length u L i⟩⟩
  rw [viewTapesQ_far]
  exact viewTapesQ_delta v L d u i

/-! ## 3. A chain of sub-steps is a bounded composite -/

/-- **A chain of `n` sub-steps on `v.far` is a composite of `≤ 2n` micro-actions
at every address of the cursor**, and the result is laid out again. -/
theorem chain_actList (n : ℕ) : ∀ (v : InputView) (q' : Queue (Fin 2))
    (L J : ℕ → List (Fin 2)) (d : ℕ → List Γc) (ρ : SRoles),
    SBound ρ → SInj ρ → LaysS v.far ρ L J → Chain n v.far q' →
    ∃ (ρ' : SRoles) (J' L' : ℕ → List (Fin 2)) (d' : ℕ → List Γc) (acts : ℕ → List (Act Γc)),
      SBound ρ' ∧ SInj ρ' ∧ LaysS q' ρ' L' J' ∧
      ∀ i, viewTapesQ { v with far := q' } L' d' i
            = actList blankc (viewTapesQ v L d i) (acts i) ∧ (acts i).length ≤ 2 * n := by
  induction n with
  | zero =>
      intro v q' L J d ρ hb hinj h hc
      have e : v.far = q' := (chain_zero _ _).mp hc
      subst e
      refine ⟨ρ, J, L, d, fun _ => [], hb, hinj, h, fun i => ⟨?_, by simp⟩⟩
      exact viewTapesQ_far v v.far L d i
  | succ n ih =>
      intro v q'' L J d ρ hb hinj h hc
      obtain ⟨q1, hs, hc'⟩ := (chain_succ n _ _).mp hc
      obtain ⟨ρ1, J1, u, hb1, hinj1, hl1, hact1⟩ :=
        moveRightS_actListB v L J d ρ hb hinj h q1 hs
      obtain ⟨ρ', J', L', d', acts', hb', hinj', hl', hact'⟩ :=
        ih { v with far := q1 } q'' (fun i => dApply (u i) (L i)) J1 (qDebris u L d) ρ1
          hb1 hinj1 hl1 hc'
      refine ⟨ρ', J', L', d', fun i => qActs u L i ++ acts' i, hb', hinj', hl', fun i => ⟨?_, ?_⟩⟩
      · rw [actList_append, ← (hact1 i).1]
        exact (hact' i).1
      · have h1 := (hact1 i).2
        have h2 := (hact' i).2
        simp only [List.length_append]
        omega

theorem chainLe_actList (n : ℕ) (v : InputView) (q' : Queue (Fin 2))
    (L J : ℕ → List (Fin 2)) (d : ℕ → List Γc) (ρ : SRoles)
    (hb : SBound ρ) (hinj : SInj ρ) (h : LaysS v.far ρ L J) (hc : ChainLe n v.far q') :
    ∃ (ρ' : SRoles) (J' L' : ℕ → List (Fin 2)) (d' : ℕ → List Γc) (acts : ℕ → List (Act Γc)),
      SBound ρ' ∧ SInj ρ' ∧ LaysS q' ρ' L' J' ∧
      ∀ i, viewTapesQ { v with far := q' } L' d' i
            = actList blankc (viewTapesQ v L d i) (acts i) ∧ (acts i).length ≤ 2 * n := by
  obtain ⟨k, hk, c⟩ := hc
  obtain ⟨ρ', J', L', d', acts, hb', hinj', hl', hact⟩ :=
    chain_actList k v q' L J d ρ hb hinj h c
  exact ⟨ρ', J', L', d', acts, hb', hinj', hl', fun i => ⟨(hact i).1, by
    have := (hact i).2; omega⟩⟩

/-! ## 4. Every branch of `moveRight` on the cursor -/

theorem moveRight_gapFalse (v : InputView) (hg : v.gap = false) :
    moveRight v = { v with gap := true } := by
  unfold moveRight
  rw [hg]
  rfl

theorem moveRight_near (v : InputView) (c : Option (Fin 2)) (rest : List (Option (Fin 2)))
    (hg : v.gap = true) (hn : v.near = c :: rest) :
    moveRight v = { v with focus := c, back := v.focus :: v.back, near := rest, gap := false } := by
  unfold moveRight
  rw [hg]
  show ({ stepRight v with gap := false } : InputView) = _
  unfold stepRight
  rw [hn]

theorem moveRight_far_none (v : InputView) (hg : v.gap = true) (hn : v.near = [])
    (hh : RTQueue.head? v.far = none) : moveRight v = { v with gap := false } := by
  unfold moveRight
  rw [hg]
  show ({ stepRight v with gap := false } : InputView) = _
  unfold stepRight
  rw [hn]
  simp only [hh, hn]

theorem moveRight_far_some (v : InputView) (a : Fin 2) (hg : v.gap = true) (hn : v.near = [])
    (hh : RTQueue.head? v.far = some a) :
    moveRight v = { v with focus := some a, back := v.focus :: v.back,
                           far := RTQueue.tail v.far, gap := false } := by
  unfold moveRight
  rw [hg]
  show ({ stepRight v with gap := false } : InputView) = _
  unfold stepRight
  rw [hn]
  simp only [hh]

/-- **`RTQueue.Inv` is preserved by `moveRight`.** -/
theorem inv_moveRight (v : InputView) (hinv : RTQueue.Inv v.far) :
    RTQueue.Inv (moveRight v).far := by
  cases hg : v.gap with
  | false => rw [moveRight_gapFalse v hg]; exact hinv
  | true =>
      cases hn : v.near with
      | cons c rest => rw [moveRight_near v c rest hg hn]; exact hinv
      | nil =>
          cases hh : RTQueue.head? v.far with
          | none => rw [moveRight_far_none v hg hn hh]; exact hinv
          | some a => rw [moveRight_far_some v a hg hn hh]; exact RTQueue.inv_tail hinv

theorem viewTapesQ_ext (v v' : InputView) (h1 : v'.focus = v.focus) (h2 : v'.back = v.back)
    (h3 : v'.near = v.near) (L : ℕ → List (Fin 2)) (d : ℕ → List Γc) (i : ℕ) :
    viewTapesQ v' L d i = viewTapesQ v L d i := by
  match i with
  | 0 =>
      show dTape (v'.focus :: v'.back) (d 0) = dTape (v.focus :: v.back) (d 0)
      rw [h1, h2]
  | 1 =>
      show dTape v'.near (d 1) = dTape v.near (d 1)
      rw [h3]
  | (n + 2) => rfl

/-- The head push of the `far` branch: address `0` only. -/
def headActs (v : InputView) (a : Fin 2) : ℕ → List (Act Γc)
  | 0 => pushActs (v.focus :: v.back) (some a)
  | _ => []

def headDebris (d : ℕ → List Γc) : ℕ → List Γc
  | 0 => (d 0).tail
  | i => d i

theorem headActs_length (v : InputView) (a : Fin 2) (i : ℕ) : (headActs v a i).length ≤ 2 := by
  match i with
  | 0 => exact le_of_eq (pushActs_length _ _)
  | (k + 1) => exact Nat.zero_le _

theorem head_push (v : InputView) (a : Fin 2) (L : ℕ → List (Fin 2)) (d : ℕ → List Γc) (i : ℕ) :
    viewTapesQ { v with focus := some a, back := v.focus :: v.back, gap := false } L
        (headDebris d) i
      = actList blankc (viewTapesQ v L d i) (headActs v a i) := by
  match i with
  | 0 =>
      show dTape (some a :: v.focus :: v.back) ((d 0).tail)
        = actList blankc (dTape (v.focus :: v.back) (d 0)) (pushActs (v.focus :: v.back) (some a))
      exact (push_dTape (v.focus :: v.back) (d 0) (some a)).symm
  | 1 => rfl
  | (n + 2) => rfl

/-- The pushed-back branch: push at `0`, pop at `1`. -/
def nearActs (v : InputView) (c : Option (Fin 2)) : ℕ → List (Act Γc)
  | 0 => pushActs (v.focus :: v.back) c
  | 1 => popActs
  | _ => []

def nearDebris (d : ℕ → List Γc) : ℕ → List Γc
  | 0 => (d 0).tail
  | 1 => blankc :: d 1
  | i => d i

theorem nearActs_length (v : InputView) (c : Option (Fin 2)) (i : ℕ) :
    (nearActs v c i).length ≤ 2 := by
  match i with
  | 0 => exact le_of_eq (pushActs_length _ _)
  | 1 => exact le_trans (le_of_eq popActs_length) (by omega)
  | (k + 2) => exact Nat.zero_le _

theorem near_pop (v : InputView) (c : Option (Fin 2)) (rest : List (Option (Fin 2)))
    (hn : v.near = c :: rest) (L : ℕ → List (Fin 2)) (d : ℕ → List Γc) (i : ℕ) :
    viewTapesQ { v with focus := c, back := v.focus :: v.back, near := rest, gap := false } L
        (nearDebris d) i
      = actList blankc (viewTapesQ v L d i) (nearActs v c i) := by
  match i with
  | 0 =>
      show dTape (c :: v.focus :: v.back) ((d 0).tail)
        = actList blankc (dTape (v.focus :: v.back) (d 0)) (pushActs (v.focus :: v.back) c)
      exact (push_dTape (v.focus :: v.back) (d 0) c).symm
  | 1 =>
      show dTape rest (blankc :: d 1) = actList blankc (dTape v.near (d 1)) popActs
      rw [hn]
      exact (pop_dTape c rest (d 1)).symm
  | (n + 2) => rfl

/-- **Every branch of `LocalInputView.moveRight` is a composite of `≤ 14`
micro-actions at every address of the cursor**, with no `near ≠ []` side
condition: the `far` dequeue is the head push (`2`) followed by the `tail`
chain (`≤ 6` sub-steps, `≤ 2` each). -/
theorem moveRightQ_actList (v : InputView) (L J : ℕ → List (Fin 2)) (d : ℕ → List Γc)
    (ρ : SRoles) (hb : SBound ρ) (hinj : SInj ρ) (h : LaysS v.far ρ L J)
    (hinv : RTQueue.Inv v.far) :
    ∃ (ρ' : SRoles) (J' L' : ℕ → List (Fin 2)) (d' : ℕ → List Γc) (acts : ℕ → List (Act Γc)),
      SBound ρ' ∧ SInj ρ' ∧ LaysS (moveRight v).far ρ' L' J' ∧
      ∀ i, viewTapesQ (moveRight v) L' d' i
            = actList blankc (viewTapesQ v L d i) (acts i) ∧ (acts i).length ≤ 14 := by
  cases hg : v.gap with
  | false =>
      have hv := moveRight_gapFalse v hg
      refine ⟨ρ, J, L, d, fun _ => [], hb, hinj, ?_, fun i => ⟨?_, by simp⟩⟩
      · rw [hv]; exact h
      · rw [hv]
        exact viewTapesQ_ext v _ rfl rfl rfl L d i
  | true =>
      cases hn : v.near with
      | cons c rest =>
          have hv := moveRight_near v c rest hg hn
          refine ⟨ρ, J, L, nearDebris d, nearActs v c, hb, hinj, ?_, fun i =>
            ⟨?_, le_trans (nearActs_length v c i) (by omega)⟩⟩
          · rw [hv]; exact h
          · rw [hv]
            exact near_pop v c rest hn L d i
      | nil =>
          cases hh : RTQueue.head? v.far with
          | none =>
              have hv := moveRight_far_none v hg hn hh
              refine ⟨ρ, J, L, d, fun _ => [], hb, hinj, ?_, fun i => ⟨?_, by simp⟩⟩
              · rw [hv]; exact h
              · rw [hv]
                exact viewTapesQ_ext v _ rfl rfl rfl L d i
          | some a =>
              have hv := moveRight_far_some v a hg hn hh
              obtain ⟨ρ', J', L', d', acts', hb', hinj', hl', hact'⟩ :=
                chainLe_actList 6 { v with focus := some a, back := v.focus :: v.back, gap := false }
                  (RTQueue.tail v.far) L J (headDebris d) ρ hb hinj h (tail_chainLe_inv v.far hinv)
              refine ⟨ρ', J', L', d', fun i => headActs v a i ++ acts' i, hb', hinj', ?_,
                fun i => ⟨?_, ?_⟩⟩
              · rw [hv]; exact hl'
              · rw [hv, actList_append, ← head_push v a L d i]
                exact (hact' i).1
              · have h1 := headActs_length v a i
                have h2 := (hact' i).2
                simp only [List.length_append]
                omega

/-! ## 5. The whole core on the nine-tape cursor blocks -/

/-- The cursor block width: `back`+`focus`, `near`, seven role stacks. -/
def tViewQ : ℕ := 9

/-- The offset of the tail: `nViews * (tViewQ - tView) = 6 * 5`. -/
def offQ : ℕ := 30

theorem nViews_tViewQ : nViews * tViewQ = nViews * tView + offQ := by decide

/-- **`CloseoutCoreEnc19.encTapesD` with the cursor blocks on `viewTapesQ`.**
Block `b` uses the physical family `lay b` and the debris column `dbg b`; the
tail is `encTapes` shifted by `offQ`. -/
noncomputable def encTapesQ (rep : ChainVM → ChainL) (lay : ℕ → ℕ → List (Fin 2))
    (dbg : ℕ → ℕ → List Γc) (m : Mirrored1 P) : ℕ → STape Γc := fun i =>
  if i < tViewQ then viewTapesQ m.vm.left (lay 0) (dbg 0) i
  else if i < 2 * tViewQ then viewTapesQ m.vm.center (lay 1) (dbg 1) (i - tViewQ)
  else if i < 3 * tViewQ then viewTapesQ m.vm.right (lay 2) (dbg 2) (i - 2 * tViewQ)
  else if i < 4 * tViewQ then viewTapesQ m.vm.walkerView (lay 3) (dbg 3) (i - 3 * tViewQ)
  else if i < 5 * tViewQ then viewTapesQ m.vm.fppWalker (lay 4) (dbg 4) (i - 4 * tViewQ)
  else if i < 6 * tViewQ then viewTapesQ m.mirL (lay 5) (dbg 5) (i - 5 * tViewQ)
  else encTapes rep m (i - offQ)

/-- Override blocks `0` and `1`. -/
def upd2 {α : Type} (x y : α) (f : ℕ → α) : ℕ → α
  | 0 => x
  | 1 => y
  | b => f b

theorem upd2_zero {α : Type} (x y : α) (f : ℕ → α) : upd2 x y f 0 = x := rfl
theorem upd2_one {α : Type} (x y : α) (f : ℕ → α) : upd2 x y f 1 = y := rfl
theorem upd2_ge {α : Type} (x y : α) (f : ℕ → α) (b : ℕ) (hb : 2 ≤ b) : upd2 x y f b = f b := by
  match b with
  | 0 => exact absurd hb (by omega)
  | 1 => exact absurd hb (by omega)
  | (n + 2) => rfl

/-- The total micro-action list of `shiftPick` on `encTapesQ`. -/
noncomputable def shiftActsQ (aL aC restC : ℕ → List (Act Γc)) (R : Ctr → Fin P) (i : ℕ) :
    List (Act Γc) :=
  if i < tViewQ then aL i
  else if i < 2 * tViewQ then aC (i - tViewQ)
  else if i < 6 * tViewQ then []
  else shiftActs restC R (i - offQ)

theorem shiftActsQ_length (aL aC restC : ℕ → List (Act Γc)) (hL : ∀ i, (aL i).length ≤ 28)
    (hC : ∀ i, (aC i).length ≤ 14) (hrl : ∀ i, (restC i).length ≤ 4) (R : Ctr → Fin P) (i : ℕ) :
    (shiftActsQ aL aC restC R i).length ≤ 28 := by
  unfold shiftActsQ
  split
  · exact hL i
  · split
    · exact le_trans (hC _) (by omega)
    · split
      · simp
      · exact le_trans (shiftActs_length restC hrl R _) (by omega)

/-- **`shiftPick` is a composite of `≤ 28` micro-actions at every address of
`encTapesQ`**, with no `near ≠ []` side condition.  The new physical families
of the two moving blocks are produced (they are the chosen `Delta` families of
`sstep_lays`), the other four blocks are unchanged, and both moving blocks are
laid out again with bounded injective tables. -/
theorem shiftVm_encTapesQ_all (rep : ChainVM → ChainL) (lay : ℕ → ℕ → List (Fin 2))
    (dbg : ℕ → ℕ → List Γc) (w : PalPeg.GalilScaffoldChainWatch.State) (m : Mirrored1 P)
    (restC : ℕ → List (Act Γc)) (hrl : ∀ i, (restC i).length ≤ 4)
    (ρL ρC : SRoles) (JL JC : ℕ → List (Fin 2))
    (hbL : SBound ρL) (hinjL : SInj ρL) (hlayL : LaysS m.vm.left.far ρL (lay 0) JL)
    (hinvL : RTQueue.Inv m.vm.left.far)
    (hbC : SBound ρC) (hinjC : SInj ρC) (hlayC : LaysS m.vm.center.far ρC (lay 1) JC)
    (hinvC : RTQueue.Inv m.vm.center.far)
    (hrestC : ∀ i, nViews * tView + P + (tMir + tBuf) ≤ i →
      encTapes rep ⟨shiftVm w m.vm, m.mirL⟩ i
        = actList blankc (encTapes rep m i) (restC i)) :
    ∃ (lay' : ℕ → ℕ → List (Fin 2)) (dbg' : ℕ → ℕ → List Γc) (acts : ℕ → List (Act Γc)),
      (∀ b, 2 ≤ b → lay' b = lay b ∧ dbg' b = dbg b) ∧
      (∃ (ρ : SRoles) (J : ℕ → List (Fin 2)),
        SBound ρ ∧ SInj ρ ∧ LaysS (shiftVm w m.vm).left.far ρ (lay' 0) J) ∧
      (∃ (ρ : SRoles) (J : ℕ → List (Fin 2)),
        SBound ρ ∧ SInj ρ ∧ LaysS (shiftVm w m.vm).center.far ρ (lay' 1) J) ∧
      (∀ i, (acts i).length ≤ 28) ∧
      ∀ i, encTapesQ rep lay' dbg' ⟨shiftVm w m.vm, m.mirL⟩ i
        = actList blankc (encTapesQ rep lay dbg m i) (acts i) := by
  obtain ⟨ρ1, J1, L1, d1, a1, hb1, hinj1, hl1, hact1⟩ :=
    moveRightQ_actList m.vm.left (lay 0) JL (dbg 0) ρL hbL hinjL hlayL hinvL
  obtain ⟨ρ2, J2, L2, d2, a2, hb2, hinj2, hl2, hact2⟩ :=
    moveRightQ_actList (moveRight m.vm.left) L1 J1 d1 ρ1 hb1 hinj1 hl1
      (inv_moveRight _ hinvL)
  obtain ⟨ρ3, J3, L3, d3, a3, hb3, hinj3, hl3, hact3⟩ :=
    moveRightQ_actList m.vm.center (lay 1) JC (dbg 1) ρC hbC hinjC hlayC hinvC
  have hLeft : ∀ i, viewTapesQ (moveRight (moveRight m.vm.left)) L2 d2 i
      = actList blankc (viewTapesQ m.vm.left (lay 0) (dbg 0) i) (a1 i ++ a2 i) := by
    intro i
    rw [actList_append, ← (hact1 i).1]
    exact (hact2 i).1
  have hLlen : ∀ i, (a1 i ++ a2 i).length ≤ 28 := by
    intro i
    have h1 := (hact1 i).2
    have h2 := (hact2 i).2
    simp only [List.length_append]
    omega
  refine ⟨upd2 L2 L3 lay, upd2 d2 d3 dbg,
    shiftActsQ (fun i => a1 i ++ a2 i) a3 restC m.vm.roles,
    fun b hb => ⟨upd2_ge _ _ _ b hb, upd2_ge _ _ _ b hb⟩,
    ⟨ρ2, J2, hb2, hinj2, by rw [shiftVm_left, upd2_zero]; exact hl2⟩,
    ⟨ρ3, J3, hb3, hinj3, by rw [shiftVm_center, upd2_one]; exact hl3⟩,
    shiftActsQ_length _ _ _ hLlen (fun i => (hact3 i).2) hrl _, ?_⟩
  intro i
  have htq : tViewQ = 9 := rfl
  have hnt : nViews * tView = 24 := rfl
  have hoffv : offQ = 30 := rfl
  unfold shiftActsQ encTapesQ
  by_cases c0 : i < tViewQ
  · rw [if_pos c0, if_pos c0, if_pos c0]
    show viewTapesQ (shiftVm w m.vm).left (upd2 L2 L3 lay 0) (upd2 d2 d3 dbg 0) i
      = actList blankc (viewTapesQ m.vm.left (lay 0) (dbg 0) i) (a1 i ++ a2 i)
    rw [shiftVm_left, upd2_zero, upd2_zero]
    exact hLeft i
  rw [if_neg c0, if_neg c0, if_neg c0]
  by_cases c1 : i < 2 * tViewQ
  · rw [if_pos c1, if_pos c1, if_pos c1]
    show viewTapesQ (shiftVm w m.vm).center (upd2 L2 L3 lay 1) (upd2 d2 d3 dbg 1) (i - tViewQ)
      = actList blankc (viewTapesQ m.vm.center (lay 1) (dbg 1) (i - tViewQ)) (a3 (i - tViewQ))
    rw [shiftVm_center, upd2_one, upd2_one]
    exact (hact3 (i - tViewQ)).1
  rw [if_neg c1, if_neg c1, if_neg c1]
  by_cases c2 : i < 3 * tViewQ
  · rw [if_pos c2, if_pos c2, if_pos (show i < 6 * tViewQ by omega)]
    show viewTapesQ (shiftVm w m.vm).right (upd2 L2 L3 lay 2) (upd2 d2 d3 dbg 2) (i - 2 * tViewQ)
      = actList blankc (viewTapesQ m.vm.right (lay 2) (dbg 2) (i - 2 * tViewQ)) []
    rw [shiftVm_right, upd2_ge _ _ _ 2 (by omega), upd2_ge _ _ _ 2 (by omega)]
    rfl
  rw [if_neg c2, if_neg c2]
  by_cases c3 : i < 4 * tViewQ
  · rw [if_pos c3, if_pos c3, if_pos (show i < 6 * tViewQ by omega)]
    show viewTapesQ (shiftVm w m.vm).walkerView (upd2 L2 L3 lay 3) (upd2 d2 d3 dbg 3)
        (i - 3 * tViewQ)
      = actList blankc (viewTapesQ m.vm.walkerView (lay 3) (dbg 3) (i - 3 * tViewQ)) []
    rw [shiftVm_walkerView, upd2_ge _ _ _ 3 (by omega), upd2_ge _ _ _ 3 (by omega)]
    rfl
  rw [if_neg c3, if_neg c3]
  by_cases c4 : i < 5 * tViewQ
  · rw [if_pos c4, if_pos c4, if_pos (show i < 6 * tViewQ by omega)]
    show viewTapesQ (shiftVm w m.vm).fppWalker (upd2 L2 L3 lay 4) (upd2 d2 d3 dbg 4)
        (i - 4 * tViewQ)
      = actList blankc (viewTapesQ m.vm.fppWalker (lay 4) (dbg 4) (i - 4 * tViewQ)) []
    rw [shiftVm_fppWalker, upd2_ge _ _ _ 4 (by omega), upd2_ge _ _ _ 4 (by omega)]
    rfl
  rw [if_neg c4, if_neg c4]
  by_cases c5 : i < 6 * tViewQ
  · rw [if_pos c5, if_pos c5, if_pos c5]
    show viewTapesQ (⟨shiftVm w m.vm, m.mirL⟩ : Mirrored1 P).mirL (upd2 L2 L3 lay 5)
        (upd2 d2 d3 dbg 5) (i - 5 * tViewQ)
      = actList blankc (viewTapesQ m.mirL (lay 5) (dbg 5) (i - 5 * tViewQ)) []
    rw [upd2_ge _ _ _ 5 (by omega), upd2_ge _ _ _ 5 (by omega)]
    rfl
  rw [if_neg c5, if_neg c5, if_neg c5]
  exact shiftVm_encTapes_tailAll rep w m restC hrestC (i - offQ) (by omega)

/-- The laid-out family of `encTapesQ`. -/
noncomputable def padTapesNQ (n : ℕ) (rep : ChainVM → ChainL) (lay : ℕ → ℕ → List (Fin 2))
    (dbg : ℕ → ℕ → List Γc) (m : Mirrored1 P) : ℕ → STape Γc :=
  fun i => padRN blankc n (shift1 blankc (encTapesQ rep lay dbg m i))

/-- **`shiftPick` as a radius-`K` composite on the nine-tape cursor layout, for
every `28 ≤ K`.**  Compared with `CloseoutCoreEnc19.shiftVm_tapeActK'`: the
`near ≠ []` side conditions are gone; in their place are the queue invariant
`RTQueue.Inv` (= `LocalInputView.WF`, from which `hrot` is derived) and the
layout data of the two moving blocks.  The new layouts are *produced*, and the
result is laid out again, with `Inv` preserved. -/
theorem shiftVm_tapeActKQ (K n : ℕ) (hK : 28 ≤ K) (rep : ChainVM → ChainL)
    (lay : ℕ → ℕ → List (Fin 2)) (dbg : ℕ → ℕ → List Γc)
    (w : PalPeg.GalilScaffoldChainWatch.State) (m : Mirrored1 P)
    (restC : ℕ → List (Act Γc)) (hrl : ∀ i, (restC i).length ≤ 4)
    (ρL ρC : SRoles) (JL JC : ℕ → List (Fin 2))
    (hbL : SBound ρL) (hinjL : SInj ρL) (hlayL : LaysS m.vm.left.far ρL (lay 0) JL)
    (hinvL : RTQueue.Inv m.vm.left.far)
    (hbC : SBound ρC) (hinjC : SInj ρC) (hlayC : LaysS m.vm.center.far ρC (lay 1) JC)
    (hinvC : RTQueue.Inv m.vm.center.far)
    (hrestC : ∀ i, nViews * tView + P + (tMir + tBuf) ≤ i →
      encTapes rep ⟨shiftVm w m.vm, m.mirL⟩ i
        = actList blankc (encTapes rep m i) (restC i))
    (hleft : ∀ i, K ≤ pos (encTapesQ rep lay dbg m i))
    (hright : ∀ i, pos (encTapesQ rep lay dbg m i) + K ≤ wlen (encTapesQ rep lay dbg m i)) :
    ∃ (lay' : ℕ → ℕ → List (Fin 2)) (dbg' : ℕ → ℕ → List Γc) (acts : ℕ → List (Act Γc)),
      (∀ b, 2 ≤ b → lay' b = lay b ∧ dbg' b = dbg b) ∧
      (∃ (ρ : SRoles) (J : ℕ → List (Fin 2)),
        SBound ρ ∧ SInj ρ ∧ LaysS (shiftVm w m.vm).left.far ρ (lay' 0) J) ∧
      (∃ (ρ : SRoles) (J : ℕ → List (Fin 2)),
        SBound ρ ∧ SInj ρ ∧ LaysS (shiftVm w m.vm).center.far ρ (lay' 1) J) ∧
      RTQueue.Inv (shiftVm w m.vm).left.far ∧ RTQueue.Inv (shiftVm w m.vm).center.far ∧
      (∀ i, (acts i).length ≤ K) ∧
      ∀ i, padTapesNQ n rep lay' dbg' ⟨shiftVm w m.vm, m.mirL⟩ i
        = actList blankc (padTapesNQ n rep lay dbg m i) (acts i) := by
  obtain ⟨lay', dbg', acts, hkeep, hlayL', hlayC', hlen, hall⟩ :=
    shiftVm_encTapesQ_all rep lay dbg w m restC hrl ρL ρC JL JC hbL hinjL hlayL hinvL
      hbC hinjC hlayC hinvC hrestC
  refine ⟨lay', dbg', acts, hkeep, hlayL', hlayC', ?_, ?_, fun i => le_trans (hlen i) hK, ?_⟩
  · rw [shiftVm_left]
    exact inv_moveRight _ (inv_moveRight _ hinvL)
  · rw [shiftVm_center]
    exact inv_moveRight _ hinvC
  · intro i
    have h1 := hlen i
    have h2 := hleft i
    have h3 := hright i
    unfold padTapesNQ
    rw [hall i]
    exact padTapesN_actList blankc n _ _ (by omega) (by omega)

end PalPeg.CloseoutCoreEnc22

#print axioms PalPeg.CloseoutCoreEnc22.chain_trans
#print axioms PalPeg.CloseoutCoreEnc22.check_chainLe
#print axioms PalPeg.CloseoutCoreEnc22.tail_chainLe
#print axioms PalPeg.CloseoutCoreEnc22.tail_hrot
#print axioms PalPeg.CloseoutCoreEnc22.tail_chainLe_inv
#print axioms PalPeg.CloseoutCoreEnc22.sstep_laysB
#print axioms PalPeg.CloseoutCoreEnc22.moveRightS_actListB
#print axioms PalPeg.CloseoutCoreEnc22.chain_actList
#print axioms PalPeg.CloseoutCoreEnc22.inv_moveRight
#print axioms PalPeg.CloseoutCoreEnc22.moveRightQ_actList
#print axioms PalPeg.CloseoutCoreEnc22.shiftVm_encTapesQ_all
#print axioms PalPeg.CloseoutCoreEnc22.shiftVm_tapeActKQ
