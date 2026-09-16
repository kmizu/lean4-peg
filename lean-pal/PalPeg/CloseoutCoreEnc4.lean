import PalPeg.CloseoutCoreEnc3

/-!
# Closeout, step 2d: from `WinRealizes` to an actual `LocalStep`

`CloseoutCoreEnc3` closes the margin for the sentinel layout `encTapes1`, shows
that a stack layout turns a push/pop into one radius-`1` window rewrite, and
bundles the rest into `CoreResidual`.  Four of its five `NAMED` residuals are
*bridging* obligations: they ask for a single `LocalStep.next` reproducing the
tick, the arrival and the fpp quantum, and for the layout to be injective.

This file attacks the bridge itself.  It introduces the only notion of tape
equality that `LocalStep.apply` can possibly deliver — agreement of the head
position and of every absolutely indexed cell (`TEq`) — proves that
`WinRealizes` is *exactly* "is a `sweep`" up to `TEq`, and packages the
reduction: a `WinStep` (a window-local `next` that reproduces the control and,
per tape, the swept window) yields `NAMED_stepWindow` as soon as the layout is
*reduced* (no trailing blank), which is the one genuinely new residual named
here.  The same is done for the arrival half.

No `WinStep` is constructed for the concrete tick, so

**無条件 PAL ∈ PEG は未完.**

## What is established

* **§1 (`TEq`).**  `LocalStep.apply` runs `sweep`, and `sweep` moves the head
  across the left edge and back, so it can leave trailing blanks in `right`
  that the original tape did not have: the *representation* is not determined.
  `TEq` (equal `pos`, equal `rd` at every absolute index) is the invariant that
  is.  `eq_of_TEq_of_reduced` closes the gap between `TEq` and `=` for tapes
  with no trailing blank, via the list lemma `list_eq_of_getD` — so the
  representation residual is a *reducedness* side condition, nothing deeper.
* **§2 (`WinRealizes` ⇔ `sweep`).**  `sweep_of_winRealizes`: given the margin
  `Kc ≤ pos T`, a `WinRealizes T T'` *is* a sweep, up to `TEq`, with the very
  window and displacement the `WinRealizes` witness carries.
  `winRealizes_of_sweep` is the converse.  This is what makes all the
  `winRealizes_*` lemmas of `CloseoutCoreEnc`/`Enc2`/`Enc3`
  (`winRealizes_of_tapeLocal`, `winRealizes_stepLocal_phys`,
  `winRealizes_push`/`pop`, `winRealizes_shift1`) usable as *step data* rather
  than as mere descriptions.
* **§3 (the bridge).**  `RealizedTickT`/`RealizedFeedT` are the up-to-`TEq`
  intertwinings; `WinStep`/`WinFeed` are the window-local data; `toStep`
  converts them into a `LocalStep`, and `realizedTickT_of_winStep` /
  `realizedFeedT_of_winFeed` prove the up-to-`TEq` intertwining outright.
  `realizedTick_of_T` / `realizedFeed_of_T` upgrade to the real
  `RealizedTick`/`RealizedFeed` under `Reduced`, hence
  `named_stepWindow_of_winStep` and `named_feedWindow_of_winFeed` discharge
  `CloseoutCoreEnc3.NAMED_stepWindow` / `NAMED_feedWindow` from a `WinStep` /
  `WinFeed` plus reducedness.  `coreResidual_of_win` assembles a
  `CloseoutCoreEnc3.CoreResidual` — hence a `CoreLocal` term — from the two.
* **§4 (`NAMED_fppQuantum` is vacuous as stated).**
  `named_fppQuantum_trivial` proves `CloseoutCoreEnc3.NAMED_fppQuantum` for
  *every* `raw, stOf, Pw, qq, first`, by taking `g := ffpp` and
  `agreeOn_refl`.  The residual as written asks only for *some* `g` agreeing
  with `ffpp`, and `ffpp` itself qualifies; the intended content — that `g` is a
  fixed-window function — is not expressed.  `NAMED_fppQuantum'` restates it so
  that `g` must come with a `WinStep`, and `named_fppQuantum_of_prime` records
  that nothing was lost in the repair.
* **§5 (the queue budget).**  `not_NAMED_queueBudget` refutes
  `CloseoutCoreEnc3.NAMED_queueBudget` (`7 ≤ tView`) outright, since
  `tView = 4`.  The repair is the constant `tView7 = 7` and the budget `tL7`;
  `tL7_pos`, `tL7_eq`, `tL_le_tL7` and `named_queueBudget7` record it.
* **§6 (the 7-tape stack cursor, and injectivity).**  `viewTapes7` lays an
  `InputView` on `back`, `near` and the five rotation stacks, every tape a
  sentinel-shifted `stackTape`.  `margin_viewTapes7` and `reduced_viewTapes7`
  are unconditional; `viewTapes7_back`, `viewTapes7_near`, `viewTapes7_front`
  and `viewTapes7_rear` *recover* the corresponding fields from the tapes, so
  the layout is injective on everything except the finite rotation state and
  the two ℕ counters (`inj_viewTapes7_upto`).  This is the injectivity block
  that `CloseoutCoreEnc3.not_injective_listTape1` shows the cursor layout of
  `Enc2` cannot have.  `winRealizes_viewTapes7_push`/`_pop` say a push or pop on
  any of the seven is one radius-`1` rewrite, and `sweep_push`/`sweep_pop`
  present them as step data.

## What is *not* established

No `WinStep` for `tickC` and no `WinFeed` for `feedC` is built — the mode
dispatch is still not written as a window function — and `NAMED_reducedTick`,
`NAMED_reducedFeed`, `NAMED_encInjective` and `NAMED_fppQuantum'` remain open.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutCoreEnc4

open PalPeg PalPeg.Program
open PalPeg.Local (Window idx idx_val pos rd toList sweep pos_sweep rd_sweep readWin
  LocalStep)
open PalPeg.LocalCounter (Seg)
open PalPeg.LocalInputView (InputView)
open PalPeg.LocalReplayParked (Mirrored1)
open PalPeg.GalilScaffoldChainInputSupply (ChainVM)
open PalPeg.GalilScaffoldController (Control)
open PalPeg.LocalChain (ChainL)
open PalPeg.LocalSysConcrete (Steps sysC tickC feedC)
open PalPeg.LocalTrackingLatch (LX)
open PalPeg.CloseoutCoreAudit (CoreLocal)
open PalPeg.CloseoutCoreStep (Γc blankc tView nViews tMir tBuf tL QL qOfL
  AgreeOn agreeOn_refl coreLocal_of)
open PalPeg.CloseoutCoreEnc (Kc WinRealizes segSym mapTape cellSym encTapes
  QChain tChain qChainOf winRealizes_refl)
open PalPeg.CloseoutCoreEnc3 (shift1 pos_shift1 margin_shift1 winRealizes_shift1
  shift1_inj encTapes1 stackTape pos_stackTape stackTape_inj winRealizes_push
  winRealizes_pop queueTapes5 CoreResidual coreLocal_ofResidual)

/-! ## 1. The tape equality `LocalStep.apply` can deliver -/

/-- **Extensional tape equality**: same head position, same cell at every
absolute index.  This is what `pos_sweep`/`rd_sweep` — i.e. the whole `Local`
API — determines; the underlying `STape` *representation* is not, because a
sweep that crosses the left edge and comes back materializes blanks in `right`
that were implicit before. -/
def TEq (T T' : STape Γc) : Prop :=
  pos T = pos T' ∧ ∀ p : ℕ, rd blankc T p = rd blankc T' p

theorem TEq.refl (T : STape Γc) : TEq T T := ⟨rfl, fun _ => rfl⟩

theorem TEq.symm {T T' : STape Γc} (h : TEq T T') : TEq T' T :=
  ⟨h.1.symm, fun p => (h.2 p).symm⟩

theorem TEq.trans {T T' T'' : STape Γc} (h : TEq T T') (h' : TEq T' T'') : TEq T T'' :=
  ⟨h.1.trans h'.1, fun p => (h.2 p).trans (h'.2 p)⟩

theorem TEq_of_eq {T T' : STape Γc} (h : T = T') : TEq T T' := h ▸ TEq.refl T

/-- A list all of whose `getD`s are blank, and whose last cell is not blank, is
empty. -/
theorem nil_of_allBlank : ∀ l : List Γc, (∀ p : ℕ, l.getD p blankc = blankc) →
    l.getLast? ≠ some blankc → l = []
  | [], _, _ => rfl
  | a :: t, h, hl => by
      have ha : a = blankc := h 0
      cases t with
      | nil =>
          refine absurd ?_ hl
          rw [List.getLast?_singleton, ha]
      | cons c r =>
          have hsub : ∀ p : ℕ, (c :: r).getD p blankc = blankc := fun p => h (p + 1)
          have hlast : (c :: r).getLast? ≠ some blankc := by
            rw [← List.getLast?_cons_cons (a := a)]
            exact hl
          exact absurd (nil_of_allBlank (c :: r) hsub hlast) (by simp)

/-- **Two reduced lists with the same `getD` profile are equal.** -/
theorem list_eq_of_getD : ∀ l l' : List Γc, (∀ p : ℕ, l.getD p blankc = l'.getD p blankc) →
    l.getLast? ≠ some blankc → l'.getLast? ≠ some blankc → l = l'
  | [], l', h, _, hl' =>
      (nil_of_allBlank l' (fun p => (h p).symm) hl').symm
  | (a :: t), [], h, hl, _ => nil_of_allBlank (a :: t) (fun p => h p) hl
  | (a :: t), (b :: t'), h, hl, hl' => by
      have hab : a = b := h 0
      have hsub : ∀ p : ℕ, t.getD p blankc = t'.getD p blankc := fun p => h (p + 1)
      have hlt : t.getLast? ≠ some blankc := by
        cases t with
        | nil => simp
        | cons c r => rw [← List.getLast?_cons_cons (a := a)]; exact hl
      have hlt' : t'.getLast? ≠ some blankc := by
        cases t' with
        | nil => simp
        | cons c r => rw [← List.getLast?_cons_cons (a := b)]; exact hl'
      rw [hab, list_eq_of_getD t t' hsub hlt hlt']

/-- **A tape is reduced** when its right part carries no trailing blank; then
the representation is determined by `pos` and `rd`. -/
def Reduced (T : STape Γc) : Prop := T.right.getLast? ≠ some blankc

theorem reduced_of_right_nil {T : STape Γc} (h : T.right = []) : Reduced T := by
  rw [Reduced, h]; simp

/-! ### `getD` bookkeeping -/

theorem getD_lt {α : Type} (l : List α) (b : α) {p : ℕ} (h : p < l.length) :
    l.getD p b = l[p] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

theorem getD_ge {α : Type} (l : List α) (b : α) {p : ℕ} (h : l.length ≤ p) :
    l.getD p b = b := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

/-- Two lists of the same length with the same `getD` profile are equal. -/
theorem list_eq_of_len_getD (l l' : List Γc) (hlen : l.length = l'.length)
    (h : ∀ p : ℕ, l.getD p blankc = l'.getD p blankc) : l = l' := by
  refine List.ext_getElem hlen (fun i h1 h2 => ?_)
  have := h i
  rwa [getD_lt l blankc h1, getD_lt l' blankc h2] at this

theorem getD_append_add {α : Type} (X Y : List α) (b : α) (k : ℕ) :
    (X ++ Y).getD (X.length + k) b = Y.getD k b := by
  induction X with
  | nil => simp
  | cons a t ih =>
      show ((a :: t) ++ Y).getD ((a :: t).length + k) b = Y.getD k b
      rw [show (a :: t).length + k = (t.length + k) + 1 by simp; omega]
      simpa using ih

theorem getD_append_lt {α : Type} (X Y : List α) (b : α) {p : ℕ} (h : p < X.length) :
    (X ++ Y).getD p b = X.getD p b := by
  rw [getD_lt _ b (by simp; omega), getD_lt _ b h, List.getElem_append_left h]

/-- The cells strictly left of the head read off the reversed left part. -/
theorem rd_left (L : List Γc) (x : Γc) (R : List Γc) {p : ℕ} (h : p < L.length) :
    rd blankc (⟨L, x, R⟩ : STape Γc) p = L.reverse.getD p blankc := by
  rw [rd, toList]
  exact getD_append_lt _ _ _ (by simpa using h)

/-- The cells strictly right of the head read off the right part. -/
theorem rd_right (L : List Γc) (x : Γc) (R : List Γc) (k : ℕ) :
    rd blankc (⟨L, x, R⟩ : STape Γc) (L.length + 1 + k) = R.getD k blankc := by
  rw [rd, toList]
  show (L.reverse ++ x :: R).getD (L.length + 1 + k) blankc = R.getD k blankc
  rw [show L.length + 1 + k = L.reverse.length + (1 + k) by simp; omega,
    getD_append_add]
  simpa using getD_append_add [x] R blankc k

/-- **`TEq` is `=` on reduced tapes.**  The head position fixes the left part,
`rd` at the head fixes the focus, and reducedness fixes the right part — so the
representation residual of `LocalStep.apply` is exactly "no trailing blank". -/
theorem eq_of_TEq_of_reduced {T T' : STape Γc} (h : TEq T T')
    (hr : Reduced T) (hr' : Reduced T') : T = T' := by
  obtain ⟨L, x, R⟩ := T
  obtain ⟨L', x', R'⟩ := T'
  have hlen : L.length = L'.length := h.1
  have hLrev : L.reverse = L'.reverse := by
    refine list_eq_of_len_getD _ _ (by simpa using hlen) (fun p => ?_)
    by_cases hp : p < L.length
    · have hp' : p < L'.length := by omega
      rw [← rd_left L x R hp, ← rd_left L' x' R' hp']
      exact h.2 p
    · rw [getD_ge _ _ (by simpa using Nat.le_of_not_lt hp),
        getD_ge _ _ (by simp; omega)]
  have hL : L = L' := by
    have h2 := congrArg List.reverse hLrev
    simpa using h2
  subst hL
  have hx : x = x' := by
    have h2 : rd blankc (⟨L, x, R⟩ : STape Γc) L.length
        = rd blankc (⟨L, x', R'⟩ : STape Γc) L.length := h.2 L.length
    have e1 : rd blankc (⟨L, x, R⟩ : STape Γc) L.length = x :=
      PalPeg.Local.rd_pos blankc _
    have e2 : rd blankc (⟨L, x', R'⟩ : STape Γc) L.length = x' :=
      PalPeg.Local.rd_pos blankc _
    rw [← e1, h2, e2]
  have hR : R = R' := by
    refine list_eq_of_getD _ _ (fun k => ?_) hr hr'
    rw [← rd_right L x R k, ← rd_right L x' R' k]
    exact h.2 _
  rw [hx, hR]

/-! ## 2. `WinRealizes` is exactly "is a sweep", up to `TEq` -/

/-- **From a window rewrite to a sweep.**  Given the margin, the witness of a
`WinRealizes` *is* the window and displacement of a `sweep`. -/
theorem sweep_of_winRealizes {T T' : STape Γc} (hK : Kc ≤ pos T) (h : WinRealizes T T') :
    ∃ (w : Window Γc Kc) (d : ℤ), |d| ≤ (Kc : ℤ) ∧ TEq T' (sweep blankc Kc T w d) := by
  obtain ⟨w, d, hd, hpos, hcell⟩ := h
  refine ⟨w, d, hd, ?_, ?_⟩
  · have h1 : (pos T' : ℤ) = (pos (sweep blankc Kc T w d) : ℤ) := by
      rw [pos_sweep blankc Kc T w d hK hd]; exact hpos
    exact_mod_cast h1
  · intro p
    rw [hcell p, rd_sweep blankc Kc T w d hK p]

/-- **The converse**: a sweep is a window rewrite. -/
theorem winRealizes_of_sweep (T : STape Γc) (w : Window Γc Kc) (d : ℤ)
    (hK : Kc ≤ pos T) (hd : |d| ≤ (Kc : ℤ)) : WinRealizes T (sweep blankc Kc T w d) :=
  PalPeg.CloseoutCoreEnc.winRealizes_sweep T w d hK hd

/-! ## 3. The bridge: window data ⟹ `NAMED_stepWindow` -/

variable {P : ℕ}

/-- The tick intertwining, up to `TEq`. -/
def RealizedTickT {Q : Type} {t : ℕ} (enc : Mirrored1 P → Q × (Fin t → STape Γc))
    (L0 : LocalStep (Fin 2) Q Γc t Kc) (f : Mirrored1 P → Mirrored1 P) : Prop :=
  ∀ m : Mirrored1 P, (enc (f m)).1 = (L0.apply blankc (enc m) none).1 ∧
    ∀ j : Fin t, TEq ((enc (f m)).2 j) ((L0.apply blankc (enc m) none).2 j)

/-- The arrival intertwining, up to `TEq`. -/
def RealizedFeedT {Q : Type} {t : ℕ} (enc : Mirrored1 P → Q × (Fin t → STape Γc))
    (L0 : LocalStep (Fin 2) Q Γc t Kc) : Prop :=
  ∀ (a : Fin 2) (m : Mirrored1 P),
    (enc (feedC a m)).1 = (L0.apply blankc (enc m) (some a)).1 ∧
    ∀ j : Fin t, TEq ((enc (feedC a m)).2 j) ((L0.apply blankc (enc m) (some a)).2 j)

/-- **Window-local data for one tick.**  `next` is a function of the finite
control, the (absent) input symbol and the windows only; `ctl` says it computes
the new control, and `tape` that each new tape is the sweep of the old one by
the window and displacement it returns — up to `TEq`, which is all `sweep`
can ever determine. -/
structure WinStep (Q : Type) (t : ℕ) (enc : Mirrored1 P → Q × (Fin t → STape Γc))
    (f : Mirrored1 P → Mirrored1 P) where
  next : Q → Option (Fin 2) → (Fin t → Window Γc Kc) → Q × (Fin t → Window Γc Kc × ℤ)
  disp_le : ∀ (q : Q) (a : Option (Fin 2)) (ws : Fin t → Window Γc Kc) (j : Fin t),
    |((next q a ws).2 j).2| ≤ (Kc : ℤ)
  ctl : ∀ m : Mirrored1 P,
    (enc (f m)).1 = (next (enc m).1 none (fun j => readWin blankc Kc ((enc m).2 j))).1
  tape : ∀ (m : Mirrored1 P) (j : Fin t), TEq ((enc (f m)).2 j)
    (sweep blankc Kc ((enc m).2 j)
      ((next (enc m).1 none (fun j' => readWin blankc Kc ((enc m).2 j'))).2 j).1
      ((next (enc m).1 none (fun j' => readWin blankc Kc ((enc m).2 j'))).2 j).2)

/-- The `LocalStep` a `WinStep` carries. -/
def WinStep.toStep {Q : Type} {t : ℕ} {enc : Mirrored1 P → Q × (Fin t → STape Γc)}
    {f : Mirrored1 P → Mirrored1 P} (W : WinStep Q t enc f) :
    LocalStep (Fin 2) Q Γc t Kc where
  next := W.next
  disp_le := W.disp_le

/-- **A `WinStep` realizes the tick, up to `TEq`.** -/
theorem realizedTickT_of_winStep {Q : Type} {t : ℕ}
    {enc : Mirrored1 P → Q × (Fin t → STape Γc)} {f : Mirrored1 P → Mirrored1 P}
    (W : WinStep Q t enc f) : RealizedTickT enc W.toStep f :=
  fun m => ⟨W.ctl m, fun j => W.tape m j⟩

/-- Window-local data for one arrival. -/
structure WinFeed (Q : Type) (t : ℕ) (enc : Mirrored1 P → Q × (Fin t → STape Γc)) where
  next : Q → Option (Fin 2) → (Fin t → Window Γc Kc) → Q × (Fin t → Window Γc Kc × ℤ)
  disp_le : ∀ (q : Q) (a : Option (Fin 2)) (ws : Fin t → Window Γc Kc) (j : Fin t),
    |((next q a ws).2 j).2| ≤ (Kc : ℤ)
  ctl : ∀ (a : Fin 2) (m : Mirrored1 P),
    (enc (feedC a m)).1
      = (next (enc m).1 (some a) (fun j => readWin blankc Kc ((enc m).2 j))).1
  tape : ∀ (a : Fin 2) (m : Mirrored1 P) (j : Fin t), TEq ((enc (feedC a m)).2 j)
    (sweep blankc Kc ((enc m).2 j)
      ((next (enc m).1 (some a) (fun j' => readWin blankc Kc ((enc m).2 j'))).2 j).1
      ((next (enc m).1 (some a) (fun j' => readWin blankc Kc ((enc m).2 j'))).2 j).2)

def WinFeed.toStep {Q : Type} {t : ℕ} {enc : Mirrored1 P → Q × (Fin t → STape Γc)}
    (W : WinFeed Q t enc) : LocalStep (Fin 2) Q Γc t Kc where
  next := W.next
  disp_le := W.disp_le

theorem realizedFeedT_of_winFeed {Q : Type} {t : ℕ}
    {enc : Mirrored1 P → Q × (Fin t → STape Γc)} (W : WinFeed Q t enc) :
    RealizedFeedT enc W.toStep :=
  fun a m => ⟨W.ctl a m, fun j => W.tape a m j⟩

/-- **From the up-to-`TEq` intertwining to the real one**, on reduced tapes. -/
theorem realizedTick_of_T {Q : Type} {t : ℕ} {enc : Mirrored1 P → Q × (Fin t → STape Γc)}
    {L0 : LocalStep (Fin 2) Q Γc t Kc} {f : Mirrored1 P → Mirrored1 P}
    (h : RealizedTickT enc L0 f)
    (hred : ∀ (m : Mirrored1 P) (j : Fin t), Reduced ((enc (f m)).2 j))
    (hred' : ∀ (m : Mirrored1 P) (j : Fin t), Reduced ((L0.apply blankc (enc m) none).2 j)) :
    PalPeg.CloseoutCoreStep.RealizedTick enc L0 f := by
  intro m
  refine Prod.ext (h m).1 (funext fun j => ?_)
  exact eq_of_TEq_of_reduced ((h m).2 j) (hred m j) (hred' m j)

theorem realizedFeed_of_T {Q : Type} {t : ℕ} {enc : Mirrored1 P → Q × (Fin t → STape Γc)}
    {L0 : LocalStep (Fin 2) Q Γc t Kc} (h : RealizedFeedT enc L0)
    (hred : ∀ (a : Fin 2) (m : Mirrored1 P) (j : Fin t), Reduced ((enc (feedC a m)).2 j))
    (hred' : ∀ (a : Fin 2) (m : Mirrored1 P) (j : Fin t),
      Reduced ((L0.apply blankc (enc m) (some a)).2 j)) :
    PalPeg.CloseoutCoreStep.RealizedFeed enc L0 := by
  intro a m
  refine Prod.ext (h a m).1 (funext fun j => ?_)
  exact eq_of_TEq_of_reduced ((h a m).2 j) (hred a m j) (hred' a m j)

/-- The sentinel encoding of `CloseoutCoreEnc3`, as one function. -/
noncomputable def enc1 (delay Lp Lf : ℕ) (rep : ChainVM → ChainL) (m : Mirrored1 P) :
    QL delay Lp Lf P QChain × (Fin (tL P tChain) → STape Γc) :=
  (qOfL delay Lp Lf (fun c => qChainOf (rep c)) m, fun i => encTapes1 rep m i.val)

/-- **`NAMED_stepWindow` from window data plus reducedness.** -/
theorem named_stepWindow_of_winStep {delay Lp Lf : ℕ} {rep : ChainVM → ChainL}
    {f : Mirrored1 P → Mirrored1 P}
    (W : WinStep (QL delay Lp Lf P QChain) (tL P tChain) (enc1 delay Lp Lf rep) f)
    (hred : ∀ (m : Mirrored1 P) (j : Fin (tL P tChain)),
      Reduced ((enc1 delay Lp Lf rep (f m)).2 j))
    (hred' : ∀ (m : Mirrored1 P) (j : Fin (tL P tChain)),
      Reduced ((W.toStep.apply blankc (enc1 delay Lp Lf rep m) none).2 j)) :
    PalPeg.CloseoutCoreEnc3.NAMED_stepWindow (P := P) delay Lp Lf rep f :=
  ⟨W.toStep, realizedTick_of_T (realizedTickT_of_winStep W) hred hred'⟩

/-- **`NAMED_feedWindow` from window data plus reducedness.** -/
theorem named_feedWindow_of_winFeed {delay Lp Lf : ℕ} {rep : ChainVM → ChainL}
    (W : WinFeed (QL delay Lp Lf P QChain) (tL P tChain) (enc1 delay Lp Lf rep))
    (hred : ∀ (a : Fin 2) (m : Mirrored1 P) (j : Fin (tL P tChain)),
      Reduced ((enc1 delay Lp Lf rep (feedC a m)).2 j))
    (hred' : ∀ (a : Fin 2) (m : Mirrored1 P) (j : Fin (tL P tChain)),
      Reduced ((W.toStep.apply blankc (enc1 delay Lp Lf rep m) (some a)).2 j)) :
    PalPeg.CloseoutCoreEnc3.NAMED_feedWindow (P := P) delay Lp Lf rep :=
  ⟨W.toStep, realizedFeed_of_T (realizedFeedT_of_winFeed W) hred hred'⟩

/-- **The residual bundle from the two halves.**  A realized tick, a realized
arrival with the *same* `LocalStep`, and the three readouts give a
`CoreResidual` — hence, through `coreLocal_ofResidual`, a `CoreLocal` term for
the concrete core. -/
def coreResidual_of_win {M : Steps P} {repC : Control → Bool} {x0 : LX (Mirrored1 P)}
    {Q : Type} {t : ℕ} {enc : Mirrored1 P → Q × (Fin t → STape Γc)}
    (L0 : LocalStep (Fin 2) Q Γc t Kc) (q0 : Q) (repQ outQ : Q → Bool)
    (htick : PalPeg.CloseoutCoreStep.RealizedTick enc L0 (tickC M))
    (hfeed : PalPeg.CloseoutCoreStep.RealizedFeed enc L0)
    (hrep : ∀ m : Mirrored1 P, repC m.vm.ctl = repQ (enc m).1)
    (hout : ∀ m : Mirrored1 P, m.vm.ctl.output = outQ (enc m).1)
    (hinit : enc x0.core = (q0, fun _ => STape.blankTape blankc)) :
    CoreResidual M repC x0 Q t where
  L0 := L0
  q0 := q0
  repQ := repQ
  outQ := outQ
  encC := enc
  htick := htick
  hfeed := hfeed
  hrep := hrep
  hout := hout
  hinit := hinit

/-- The `CoreLocal` term the bundle yields. -/
def coreLocal_of_win {M : Steps P} {repC : Control → Bool} {x0 : LX (Mirrored1 P)}
    {Q : Type} {t : ℕ} {enc : Mirrored1 P → Q × (Fin t → STape Γc)}
    (L0 : LocalStep (Fin 2) Q Γc t Kc) (q0 : Q) (repQ outQ : Q → Bool)
    (htick : PalPeg.CloseoutCoreStep.RealizedTick enc L0 (tickC M))
    (hfeed : PalPeg.CloseoutCoreStep.RealizedFeed enc L0)
    (hrep : ∀ m : Mirrored1 P, repC m.vm.ctl = repQ (enc m).1)
    (hout : ∀ m : Mirrored1 P, m.vm.ctl.output = outQ (enc m).1)
    (hinit : enc x0.core = (q0, fun _ => STape.blankTape blankc)) :
    CoreLocal (sysC M repC) x0 Q Γc t Kc :=
  coreLocal_ofResidual (coreResidual_of_win L0 q0 repQ outQ htick hfeed hrep hout hinit)

/-- **The reducedness residuals**, named with their exact types. -/
def NAMED_reducedTick {Q : Type} {t : ℕ} (enc : Mirrored1 P → Q × (Fin t → STape Γc))
    (L0 : LocalStep (Fin 2) Q Γc t Kc) (f : Mirrored1 P → Mirrored1 P) : Prop :=
  (∀ (m : Mirrored1 P) (j : Fin t), Reduced ((enc (f m)).2 j)) ∧
    ∀ (m : Mirrored1 P) (j : Fin t), Reduced ((L0.apply blankc (enc m) none).2 j)

def NAMED_reducedFeed {Q : Type} {t : ℕ} (enc : Mirrored1 P → Q × (Fin t → STape Γc))
    (L0 : LocalStep (Fin 2) Q Γc t Kc) : Prop :=
  (∀ (a : Fin 2) (m : Mirrored1 P) (j : Fin t), Reduced ((enc (feedC a m)).2 j)) ∧
    ∀ (a : Fin 2) (m : Mirrored1 P) (j : Fin t),
      Reduced ((L0.apply blankc (enc m) (some a)).2 j)

/-! ## 4. `NAMED_fppQuantum` is vacuous as stated -/

/-- **The fpp residual of `CloseoutCoreEnc3` holds for every input**, by taking
`g := ffpp` itself.  `AgreeOn` is reflexive, and nothing in the statement forces
`g` to be window-local, so the obligation carries none of its intended content. -/
theorem named_fppQuantum_trivial (raw : List (Fin 2))
    (stOf : ℕ → PalPeg.GalilScaffoldTop.State PalPeg.GalilScaffoldChainInputSupply.GalilVM)
    (Pw : PalPeg.GalilScaffoldChainInputSupply.Shared) (qq : ℕ) (first : Fin 9) :
    PalPeg.CloseoutCoreEnc3.NAMED_fppQuantum (P := P) raw stOf Pw qq first :=
  ⟨PalPeg.LocalWF.ffpp (P := P) Pw qq first, agreeOn_refl _ _⟩

/-- **The repaired fpp residual.**  The witness must agree with `ffpp` on
reachable states *and* be realized by window data over the sentinel layout. -/
def NAMED_fppQuantum' (raw : List (Fin 2))
    (stOf : ℕ → PalPeg.GalilScaffoldTop.State PalPeg.GalilScaffoldChainInputSupply.GalilVM)
    (Pw : PalPeg.GalilScaffoldChainInputSupply.Shared) (qq : ℕ) (first : Fin 9)
    (delay Lp Lf : ℕ) (rep : ChainVM → ChainL) : Prop :=
  ∃ g : Mirrored1 P → Mirrored1 P,
    AgreeOn raw stOf (PalPeg.LocalWF.ffpp (P := P) Pw qq first) g
      PalPeg.GalilScaffoldController.Mode.fpp ∧
    Nonempty (WinStep (QL delay Lp Lf P QChain) (tL P tChain) (enc1 delay Lp Lf rep) g)

/-- The repaired form still *implies* the old one, so nothing was lost. -/
theorem named_fppQuantum_of_prime {raw : List (Fin 2)}
    {stOf : ℕ → PalPeg.GalilScaffoldTop.State PalPeg.GalilScaffoldChainInputSupply.GalilVM}
    {Pw : PalPeg.GalilScaffoldChainInputSupply.Shared} {qq : ℕ} {first : Fin 9}
    {delay Lp Lf : ℕ} {rep : ChainVM → ChainL}
    (h : NAMED_fppQuantum' (P := P) raw stOf Pw qq first delay Lp Lf rep) :
    PalPeg.CloseoutCoreEnc3.NAMED_fppQuantum (P := P) raw stOf Pw qq first := by
  obtain ⟨g, hg, _⟩ := h
  exact ⟨g, hg⟩

/-! ## 5. The queue budget -/

/-- **`NAMED_queueBudget` is false as stated**: `tView = 4`. -/
theorem not_NAMED_queueBudget : ¬ PalPeg.CloseoutCoreEnc3.NAMED_queueBudget := by
  intro h
  have h7 : 7 ≤ tView := h
  exact absurd h7 (Nat.not_le.mpr PalPeg.CloseoutCoreEnc3.tView_lt_seven)

/-- The repaired cursor budget: `back`, `near` and the five rotation stacks. -/
def tView7 : ℕ := 7

/-- The repaired tape budget. -/
def tL7 (P tChain : ℕ) : ℕ := nViews * tView7 + P + tMir + tBuf + tChain

theorem tL7_pos (P tChain : ℕ) : 0 < tL7 P tChain := by
  unfold tL7 nViews tView7 tMir tBuf; omega

theorem tL7_eq (P tChain : ℕ) : tL7 P tChain = 93 + P + tChain := by
  unfold tL7 nViews tView7 tMir tBuf; omega

theorem tL_le_tL7 (P tChain : ℕ) : tL P tChain ≤ tL7 P tChain := by
  unfold tL tL7 nViews tView7 tView tMir tBuf; omega

/-- …and the budget obligation holds for it. -/
theorem named_queueBudget7 : 7 ≤ tView7 := by decide

/-! ## 6. The seven-tape stack cursor -/

/-- **One cursor on seven sentinel-shifted stack tapes**: the visited prefix
`back` (with `focus` on top), the near list, and the five stacks the
Hood–Melville rotation touches. -/
def viewTapes7 (v : InputView) : ℕ → STape Γc
  | 0 => shift1 blankc (stackTape (v.focus :: v.back))
  | 1 => shift1 blankc (stackTape v.near)
  | (n + 2) => shift1 blankc (queueTapes5 v.far n)

/-- **The margin holds for the seven-tape cursor, unconditionally.** -/
theorem margin_viewTapes7 (v : InputView) (i : ℕ) : Kc ≤ pos (viewTapes7 v i) := by
  match i with
  | 0 => exact margin_shift1 _ _
  | 1 => exact margin_shift1 _ _
  | (n + 2) => exact margin_shift1 _ _

/-- The head of tape `0` sits at depth `back.length + 2`, so the length of the
visited prefix is visible in the geometry. -/
theorem pos_viewTapes7_zero (v : InputView) :
    pos (viewTapes7 v 0) = v.back.length + 2 := by
  show pos (shift1 blankc (stackTape (v.focus :: v.back))) = v.back.length + 2
  rw [pos_shift1, pos_stackTape]
  simp

/-- **Tape `0` recovers `focus` and `back`.** -/
theorem viewTapes7_back {v v' : InputView} (h : viewTapes7 v 0 = viewTapes7 v' 0) :
    v.focus = v'.focus ∧ v.back = v'.back := by
  have h1 : stackTape (v.focus :: v.back) = stackTape (v'.focus :: v'.back) :=
    shift1_inj blankc h
  have h2 : v.focus :: v.back = v'.focus :: v'.back := stackTape_inj h1
  exact ⟨(List.cons.injEq _ _ _ _ ▸ h2).1, (List.cons.injEq _ _ _ _ ▸ h2).2⟩

/-- **Tape `1` recovers `near`.** -/
theorem viewTapes7_near {v v' : InputView} (h : viewTapes7 v 1 = viewTapes7 v' 1) :
    v.near = v'.near := stackTape_inj (shift1_inj blankc h)

theorem map_some_inj : Function.Injective (List.map (some : Fin 2 → Option (Fin 2))) :=
  List.map_injective_iff.mpr (fun a b hab => Option.some.inj hab)

/-- **Tape `2` recovers the queue's front list.** -/
theorem viewTapes7_front {v v' : InputView} (h : viewTapes7 v 2 = viewTapes7 v' 2) :
    v.far.front = v'.far.front := by
  have h1 : stackTape (v.far.front.map some) = stackTape (v'.far.front.map some) :=
    shift1_inj blankc h
  exact map_some_inj (stackTape_inj h1)

/-- **Tape `3` recovers the queue's rear list.** -/
theorem viewTapes7_rear {v v' : InputView} (h : viewTapes7 v 3 = viewTapes7 v' 3) :
    v.far.rear = v'.far.rear := by
  have h1 : stackTape (v.far.rear.map some) = stackTape (v'.far.rear.map some) :=
    shift1_inj blankc h
  exact map_some_inj (stackTape_inj h1)

/-- **The layout determines everything but the rotation state and the two
length counters** — which are finite control and unary counters, not cursor
tapes.  This is exactly the injectivity
`CloseoutCoreEnc3.not_injective_listTape1` shows the `Enc2` cursor layout
cannot have. -/
theorem inj_viewTapes7_upto {v v' : InputView} (h : ∀ i : ℕ, viewTapes7 v i = viewTapes7 v' i) :
    v.focus = v'.focus ∧ v.back = v'.back ∧ v.near = v'.near ∧
      v.far.front = v'.far.front ∧ v.far.rear = v'.far.rear :=
  ⟨(viewTapes7_back (h 0)).1, (viewTapes7_back (h 0)).2, viewTapes7_near (h 1),
    viewTapes7_front (h 2), viewTapes7_rear (h 3)⟩

/-- **A push on a cursor stack is one radius-`1` window rewrite.** -/
theorem winRealizes_viewTapes7_push (a : Option (Fin 2)) (l : List (Option (Fin 2))) :
    WinRealizes (shift1 blankc (stackTape l)) (shift1 blankc (stackTape (a :: l))) :=
  winRealizes_shift1 (winRealizes_push a l)

/-- **…and so is a pop.** -/
theorem winRealizes_viewTapes7_pop (a : Option (Fin 2)) (l : List (Option (Fin 2))) :
    WinRealizes (shift1 blankc (stackTape (a :: l))) (shift1 blankc (stackTape l)) :=
  winRealizes_shift1 (winRealizes_pop a l)

/-- A push *is* a sweep — step data, not just a description; the margin comes
for free from the sentinel. -/
theorem sweep_push (a : Option (Fin 2)) (l : List (Option (Fin 2))) :
    ∃ (w : Window Γc Kc) (d : ℤ), |d| ≤ (Kc : ℤ) ∧
      TEq (shift1 blankc (stackTape (a :: l)))
        (sweep blankc Kc (shift1 blankc (stackTape l)) w d) :=
  sweep_of_winRealizes (margin_shift1 _ _) (winRealizes_viewTapes7_push a l)

theorem sweep_pop (a : Option (Fin 2)) (l : List (Option (Fin 2))) :
    ∃ (w : Window Γc Kc) (d : ℤ), |d| ≤ (Kc : ℤ) ∧
      TEq (shift1 blankc (stackTape l))
        (sweep blankc Kc (shift1 blankc (stackTape (a :: l))) w d) :=
  sweep_of_winRealizes (margin_shift1 _ _) (winRealizes_viewTapes7_pop a l)

/-- A stack tape has nothing to the right of the head, hence is reduced. -/
theorem reduced_stackTape (l : List (Option (Fin 2))) : Reduced (stackTape l) := by
  cases l with
  | nil => exact reduced_of_right_nil rfl
  | cons a t => exact reduced_of_right_nil rfl

theorem reduced_shift1_stackTape (l : List (Option (Fin 2))) :
    Reduced (shift1 blankc (stackTape l)) := by
  cases l with
  | nil => exact reduced_of_right_nil rfl
  | cons a t => exact reduced_of_right_nil rfl

/-- **Every tape of `queueTapes5` is a stack tape**, whichever rotation phase
the queue is in. -/
theorem exists_stackTape_queueTapes5 (q : RTQueue.Queue (Fin 2)) (n : ℕ) :
    ∃ l : List (Option (Fin 2)), queueTapes5 q n = stackTape l := by
  obtain ⟨lenf, front, state, lenr, rear⟩ := q
  match n, state with
  | 0, _ => exact ⟨front.map some, by simp [queueTapes5]⟩
  | 1, _ => exact ⟨rear.map some, by simp [queueTapes5]⟩
  | 2, .idle => exact ⟨[], by simp [queueTapes5]⟩
  | 2, .reversing a b c d e => exact ⟨b.map some, by simp [queueTapes5]⟩
  | 2, .appending a b c => exact ⟨[], by simp [queueTapes5]⟩
  | 2, .done f => exact ⟨[], by simp [queueTapes5]⟩
  | 3, .idle => exact ⟨[], by simp [queueTapes5]⟩
  | 3, .reversing a b c d e => exact ⟨c.map some, by simp [queueTapes5]⟩
  | 3, .appending a b c => exact ⟨b.map some, by simp [queueTapes5]⟩
  | 3, .done f => exact ⟨[], by simp [queueTapes5]⟩
  | (k + 4), .idle => exact ⟨[], by simp [queueTapes5]⟩
  | (k + 4), .reversing a b c d e => exact ⟨e.map some, by simp [queueTapes5]⟩
  | (k + 4), .appending a b c => exact ⟨c.map some, by simp [queueTapes5]⟩
  | (k + 4), .done f => exact ⟨f.map some, by simp [queueTapes5]⟩

theorem reduced_queueTapes5 (q : RTQueue.Queue (Fin 2)) (n : ℕ) :
    Reduced (shift1 blankc (queueTapes5 q n)) := by
  obtain ⟨l, hl⟩ := exists_stackTape_queueTapes5 q n
  rw [hl]
  exact reduced_shift1_stackTape l

/-- …hence the margin is free on them too. -/
theorem margin_queueTapes5 (q : RTQueue.Queue (Fin 2)) (n : ℕ) :
    Kc ≤ pos (shift1 blankc (queueTapes5 q n)) := margin_shift1 _ _

/-- **The seven-tape cursor is reduced, tape by tape**, so `TEq` is `=` on it:
the `Reduced` half of `NAMED_reducedTick` is already discharged for the cursor
block of the layout. -/
theorem reduced_viewTapes7 (v : InputView) (i : ℕ) : Reduced (viewTapes7 v i) := by
  match i with
  | 0 => exact reduced_shift1_stackTape _
  | 1 => exact reduced_shift1_stackTape _
  | (n + 2) => exact reduced_queueTapes5 v.far n

end PalPeg.CloseoutCoreEnc4

#print axioms PalPeg.CloseoutCoreEnc4.nil_of_allBlank
#print axioms PalPeg.CloseoutCoreEnc4.list_eq_of_getD
#print axioms PalPeg.CloseoutCoreEnc4.eq_of_TEq_of_reduced
#print axioms PalPeg.CloseoutCoreEnc4.sweep_of_winRealizes
#print axioms PalPeg.CloseoutCoreEnc4.winRealizes_of_sweep
#print axioms PalPeg.CloseoutCoreEnc4.realizedTickT_of_winStep
#print axioms PalPeg.CloseoutCoreEnc4.realizedFeedT_of_winFeed
#print axioms PalPeg.CloseoutCoreEnc4.realizedTick_of_T
#print axioms PalPeg.CloseoutCoreEnc4.realizedFeed_of_T
#print axioms PalPeg.CloseoutCoreEnc4.named_stepWindow_of_winStep
#print axioms PalPeg.CloseoutCoreEnc4.named_feedWindow_of_winFeed
#print axioms PalPeg.CloseoutCoreEnc4.coreResidual_of_win
#print axioms PalPeg.CloseoutCoreEnc4.coreLocal_of_win
#print axioms PalPeg.CloseoutCoreEnc4.named_fppQuantum_trivial
#print axioms PalPeg.CloseoutCoreEnc4.named_fppQuantum_of_prime
#print axioms PalPeg.CloseoutCoreEnc4.not_NAMED_queueBudget
#print axioms PalPeg.CloseoutCoreEnc4.tL7_pos
#print axioms PalPeg.CloseoutCoreEnc4.named_queueBudget7
#print axioms PalPeg.CloseoutCoreEnc4.margin_viewTapes7
#print axioms PalPeg.CloseoutCoreEnc4.pos_viewTapes7_zero
#print axioms PalPeg.CloseoutCoreEnc4.inj_viewTapes7_upto
#print axioms PalPeg.CloseoutCoreEnc4.winRealizes_viewTapes7_push
#print axioms PalPeg.CloseoutCoreEnc4.sweep_push
#print axioms PalPeg.CloseoutCoreEnc4.reduced_viewTapes7
