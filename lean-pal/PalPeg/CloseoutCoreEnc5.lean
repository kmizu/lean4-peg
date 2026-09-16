import PalPeg.CloseoutCoreEnc4

/-!
# Closeout, step 2e: the representation invariant, and the mode dispatch as a window function

`CloseoutCoreEnc4` reduces `NAMED_stepWindow` / `NAMED_feedWindow` to a
`WinStep` / `WinFeed` (a window-local `next` reproducing the control and, per
tape, the swept window *up to* `TEq`) **plus** a reducedness side condition
`NAMED_reducedTick` / `NAMED_reducedFeed`, and leaves the `WinStep` for
`tickC` unbuilt.  This file does three things.

1. It shows the reducedness route is **wrong**: `Reduced` is not stable under
   `sweep`, by an explicit one-cell counterexample, so `NAMED_reducedTick`'s
   second conjunct is not provable from any property of the encoding.  The
   representation invariant that *is* stable is the **fixed width** `wlen`
   (`pos + right.length`), and `wlen_sweep` proves stability unconditionally.
   With `eq_of_TEq_of_width` this closes the representation gap by two
   *layout* obligations — width conservation and right room — in place of
   reducedness.
2. It builds the layout that discharges the two geometric side conditions
   (`margin`, `room`) **unconditionally**: `padR` reserves one blank cell at
   the right end, and `padTapes` = `padR ∘ shift1 ∘ encTapes` has every head at
   distance `≥ Kc` from *both* edges while reading exactly like
   `encTapes1`.  (It is therefore never `Reduced` — which, by 1, is what one
   wants.)
3. It writes the **mode dispatch as a window function**: `ModeWin` is the
   per-mode window datum, `StarvedWin` is the (window-readable) starvation
   test, and `winStep_of_modes` assembles them into a genuine
   `CloseoutCoreEnc4.WinStep` for `tickC M`.  The *stutter* branch is closed
   outright (`sweep_id_TEq`: the identity window with displacement `0` is a
   sweep), so what remains of the tick is exactly ten per-mode obligations and
   one starvation obligation, each named with its exact type.

No `ModeWin` is constructed for any mode, so

**無条件 PAL ∈ PEG は未完.**

## What is established

* **§1 (`wlen`, the stable representation invariant).**  `wlen_left`,
  `wlen_stay`, `wlen_right`, `wlen_mvLN`, `wlen_mvRN`, `wlen_cPhase` and the
  conclusion `wlen_sweep`: if the head is `≥ K` from the left edge, `|d| ≤ K`
  and the window fits inside the stored width (`pos T + K ≤ wlen T`), then one
  `sweep` leaves `wlen` unchanged.  `eq_of_TEq_of_width` upgrades `TEq` to `=`
  for tapes of equal width.  `not_reduced_sweep_stable` refutes the analogous
  statement for `Reduced`: the identity sweep on `⟨[blank], blank, []⟩`
  materializes a trailing blank.  So `Reduced` — the invariant
  `CloseoutCoreEnc4` chose — cannot be propagated, and `wlen` must be.
* **§2 (`padR`, and both geometric side conditions).**  `padR` appends one
  blank at the right end: `pos_padR`, `wlen_padR`, `rd_padR` (the reading is
  unchanged), `room_padR` (`pos + 1 ≤ wlen`, unconditional).  `padTapes`
  composes it with the sentinel `shift1`, and `margin_padTapes`,
  `room_padTapes`, `rd_padTapes` hold for every state with no reachability
  hypothesis; `not_room_shift1` shows the *unpadded* layout `encTapes1` fails
  the room condition, so the padding is forced.  `not_reduced_padR` records
  that the padded layout is deliberately non-reduced.
* **§3 (`TEq` ⇒ `=`, on a width-conserving layout).**  `realizedTick_of_width`
  and `realizedFeed_of_width` replace `CloseoutCoreEnc4.realizedTick_of_T` and
  its reducedness hypotheses by `NAMED_widthTick` / `NAMED_widthFeed` (the
  layout does not change the stored width of a tape during a tick / an
  arrival) and `NAMED_room` (every head has one reserved cell on each side).
  `named_stepWindow_of_winStep_width` and `named_feedWindow_of_winFeed_width`
  are the resulting bridges to `CloseoutCoreEnc3`.
* **§4 (the mode dispatch).**  `ModeWin`, `StarvedWin`, `dispatchNext` and
  `winStep_of_modes`: a window-readable starvation test plus one `ModeWin` per
  `Mode` yield a `WinStep` for `tickC M`.  The starved branch needs nothing:
  `sweep_id_TEq` says the identity window with `d = 0` reproduces the tape.
  `winStep_of_modes_next_starved` / `_next_step` expose the two branches.
* **§5 (the residuals, per mode).**  `NAMED_modeWin` is the per-mode obligation
  with its exact type, `NAMED_starvedWindow` the starvation test,
  `NAMED_feedWin` the arrival half, and `residualTick` bundles the ten modes
  and the starvation test into exactly what `winStep_of_modes` consumes;
  `winStep_of_residualTick` consumes it.  `NAMED_fppQuantum''` strengthens
  `CloseoutCoreEnc4.NAMED_fppQuantum'` to "the `.fpp` mode's window function is
  one `GalilDpCode` instruction lifted by `LocalBuffers.stepL`", and
  `named_fppQuantum'_of_second` shows it implies the `Enc4` form.
  `NAMED_encInjective7` restates injectivity for the stack layout of
  `CloseoutCoreEnc4.viewTapes7`, and `injective7_of_parts` reduces it to the
  finite control plus the counter bank, using `inj_viewTapes7_upto`.

## What is *not* established

No `ModeWin` for any of the ten modes, no `StarvedWin`, no `FeedWin`, and
neither width-conservation obligation (`NAMED_widthTick`, `NAMED_widthFeed`).  `NAMED_encInjective7` and
`NAMED_fppQuantum''` are open.  The `tView = 4` budget is still too small for
the five stacks (`CloseoutCoreEnc4.not_NAMED_queueBudget`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutCoreEnc5

open PalPeg PalPeg.Program
open PalPeg.Local (Window idx idx_val pos rd toList sweep pos_sweep rd_sweep readWin
  readWin_eq mvL mvR cPhase pos_cPhase pos_mvL pos_mvR pos_mvLN pos_mvRN LocalStep)
open PalPeg.LocalInputView (InputView)
open PalPeg.LocalReplayParked (Mirrored1)
open PalPeg.GalilScaffoldChainInputSupply (ChainVM)
open PalPeg.GalilScaffoldController (Control Mode)
open PalPeg.LocalChain (ChainL)
open PalPeg.LocalSysConcrete (Steps sysC tickC feedC Starved stepOf)
open PalPeg.LocalTrackingLatch (LX)
open PalPeg.CloseoutCoreAudit (CoreLocal)
open PalPeg.CloseoutCoreStep (Γc blankc tView nViews tMir tBuf tL QL qOfL
  RealizedTick RealizedFeed)
open PalPeg.CloseoutCoreEnc (Kc WinRealizes encTapes QChain tChain qChainOf)
open PalPeg.CloseoutCoreEnc3 (shift1 pos_shift1 encTapes1 stackTape)
open PalPeg.CloseoutCoreEnc4 (TEq Reduced list_eq_of_len_getD WinStep WinFeed
  RealizedTickT RealizedFeedT enc1 viewTapes7)

/-! ## 1. `wlen`: the representation invariant a `sweep` preserves

`CloseoutCoreEnc4.TEq` (equal head, equal cell at every absolute index) is all
`pos_sweep`/`rd_sweep` determine, and `CoreResidual` needs literal equality of
`STape` records.  `Enc4` bridges the two with `Reduced` (no trailing blank).
§1 shows that choice cannot work, and replaces it. -/

variable {Γ : Type}

/-- **The stored width of a tape**: one more than the largest index whose cell
is stored, i.e. `(toList T).length`, split at the head. -/
def wlen (T : STape Γ) : ℕ := pos T + T.right.length

theorem length_toList (T : STape Γ) : (toList T).length = wlen T + 1 := by
  simp [toList, wlen, pos]
  omega

theorem pos_le_wlen (T : STape Γ) : pos T ≤ wlen T := by simp [wlen]

/-- A `.left` micro-action never changes the stored width (at the edge it
writes without moving). -/
theorem wlen_left (b w : Γ) (T : STape Γ) : wlen (T.applyAction b (w, .left)) = wlen T := by
  cases hl : T.left <;> simp [wlen, pos, STape.applyAction, hl] <;> omega

theorem wlen_stay (b w : Γ) (T : STape Γ) : wlen (T.applyAction b (w, .stay)) = wlen T := by
  simp [wlen, pos, STape.applyAction]

/-- A `.right` micro-action keeps the width **iff** there is a stored cell to
move onto; off the right end it materializes one. -/
theorem wlen_right (b w : Γ) {T : STape Γ} (h : pos T < wlen T) :
    wlen (T.applyAction b (w, .right)) = wlen T := by
  cases hr : T.right with
  | nil => simp only [wlen, hr, List.length_nil, Nat.add_zero] at h; omega
  | cons n r => simp [wlen, pos, STape.applyAction, hr] <;> omega

theorem wlen_mvL (b : Γ) (T : STape Γ) : wlen (mvL b T) = wlen T := wlen_left b _ T

theorem wlen_mvLN (b : Γ) (n : ℕ) (T : STape Γ) : wlen ((mvL b)^[n] T) = wlen T := by
  induction n generalizing T with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, ih, wlen_mvL]

theorem wlen_mvRN (b : Γ) (n : ℕ) (T : STape Γ) (h : pos T + n ≤ wlen T) :
    wlen ((mvR b)^[n] T) = wlen T := by
  induction n generalizing T with
  | zero => rfl
  | succ k ih =>
      have h1 : pos T < wlen T := by omega
      have e := wlen_right b T.focus (T := T) h1
      rw [Function.iterate_succ_apply,
        ih (mvR b T) (by rw [pos_mvR, show wlen (mvR b T) = wlen T from e]; omega),
        show wlen (mvR b T) = wlen T from e]

theorem wlen_cPhase (b : Γ) (g : ℕ → Γ) (c : ℕ) (T : STape Γ) :
    wlen (cPhase b g c T) = wlen T := by
  induction c generalizing T with
  | zero => rfl
  | succ k ih =>
      match k with
      | 0 => exact wlen_stay b (g 0) T
      | (n + 1) =>
          rw [show cPhase b g (n + 1 + 1) T
                = cPhase b g (n + 1) (T.applyAction b (g (n + 1), .left)) from rfl,
            ih, wlen_left]

/-- **One `sweep` preserves the stored width.**  The hypotheses are the two
geometric ones: the head is `K` cells clear of the left edge (`hK`, already
needed by `pos_sweep`) and the right end of the window is *stored*
(`hN : pos T + K ≤ wlen T`) — one reserved cell on the right for `K = 1`. -/
theorem wlen_sweep (b : Γ) (K : ℕ) (T : STape Γ) (w : Window Γ K) (d : ℤ)
    (hK : K ≤ pos T) (hd : |d| ≤ (K : ℤ)) (hN : pos T + K ≤ wlen T) :
    wlen (sweep b K T w d) = wlen T := by
  have hd1 : -(K : ℤ) ≤ d := neg_le_of_abs_le hd
  have hd2 : d ≤ (K : ℤ) := le_of_abs_le hd
  have htn : ((d + (K : ℤ)).toNat : ℤ) = d + (K : ℤ) := Int.toNat_of_nonneg (by omega)
  have htn2 : (d + (K : ℤ)).toNat ≤ 2 * K := by omega
  set T1 := (mvL b)^[K] T with hT1
  have hw1 : wlen T1 = wlen T := by rw [hT1, wlen_mvLN]
  have hp1 : pos T1 = pos T - K := by rw [hT1, pos_mvLN]
  set T2 := (mvR b)^[2 * K] T1 with hT2
  have hw2 : wlen T2 = wlen T := by
    rw [hT2, wlen_mvRN b (2 * K) T1 (by rw [hp1, hw1]; omega)]; exact hw1
  have hp2 : pos T2 = pos T + K := by rw [hT2, pos_mvRN, hp1]; omega
  set T3 := cPhase b (fun i => w (idx K i)) (2 * K + 1) T2 with hT3
  have hw3 : wlen T3 = wlen T := by rw [hT3, wlen_cPhase]; exact hw2
  have hp3 : pos T3 = pos T - K := by rw [hT3, pos_cPhase, hp2]; omega
  show wlen ((mvR b)^[(d + (K : ℤ)).toNat] T3) = wlen T
  rw [wlen_mvRN b _ T3 (by rw [hp3, hw3]; omega)]
  exact hw3

/-- **Equal width turns `TEq` into equality.**  This is the replacement for
`CloseoutCoreEnc4.eq_of_TEq_of_reduced`: the representation of a tape is
determined by its reading together with its stored width. -/
theorem eq_of_TEq_of_width {T T' : STape Γc} (h : TEq T T') (hw : wlen T = wlen T') :
    T = T' := by
  obtain ⟨L, x, R⟩ := T
  obtain ⟨L', x', R'⟩ := T'
  have hpos : L.length = L'.length := h.1
  have key : toList (⟨L, x, R⟩ : STape Γc) = toList (⟨L', x', R'⟩ : STape Γc) := by
    refine list_eq_of_len_getD _ _ ?_ (fun p => h.2 p)
    rw [length_toList, length_toList, hw]
  simp only [toList] at key
  have h1 : L.reverse = L'.reverse := List.append_inj_left key (by simp [hpos])
  have h2 : x :: R = x' :: R' := List.append_inj_right key (by simp [hpos])
  have hL : L = L' := by simpa using congrArg List.reverse h1
  subst hL
  cases h2
  rfl

/-- **`Reduced` is not stable under `sweep`.**  The identity window rewrite on
the one-cell tape `⟨[blank], blank, []⟩` — head clear of the left edge, and
reduced, since its `right` is empty — materializes a trailing blank.  So the
second conjunct of `CloseoutCoreEnc4.NAMED_reducedTick`, which asks for the
*output of `LocalStep.apply`* to be reduced, cannot be obtained from any
property of the encoding: `sweep` itself destroys the invariant. -/
theorem not_reduced_sweep_stable :
    ¬ ∀ T : STape Γc, Kc ≤ pos T → Reduced T →
        Reduced (sweep blankc Kc T (readWin blankc Kc T) 0) := by
  intro h
  have hred : Reduced (⟨[blankc], blankc, []⟩ : STape Γc) :=
    PalPeg.CloseoutCoreEnc4.reduced_of_right_nil rfl
  have h2 := h ⟨[blankc], blankc, []⟩ (by decide) hred
  have e : (sweep blankc Kc (⟨[blankc], blankc, []⟩ : STape Γc)
      (readWin blankc Kc (⟨[blankc], blankc, []⟩ : STape Γc)) 0).right = [blankc] := by rfl
  exact h2 (by rw [Reduced] at h2; rw [e]; rfl)

/-- **The identity window is a sweep.**  Reading the window and writing it back
with displacement `0` returns the tape, up to `TEq`.  This closes the *stutter*
branch of `tickC` (and any tape a mode step leaves alone) with no residual. -/
theorem sweep_id_TEq (T : STape Γc) (hK : Kc ≤ pos T) :
    TEq T (sweep blankc Kc T (readWin blankc Kc T) 0) := by
  refine ⟨?_, ?_⟩
  · have h := pos_sweep blankc Kc T (readWin blankc Kc T) 0 hK (by simp)
    have h2 : (pos T : ℤ) = (pos (sweep blankc Kc T (readWin blankc Kc T) 0) : ℤ) := by
      rw [h]; ring
    exact_mod_cast h2
  · intro p
    rw [rd_sweep blankc Kc T _ 0 hK p]
    by_cases hm : pos T - Kc ≤ p ∧ p ≤ pos T + Kc
    · rw [if_pos hm, readWin_eq]
      have hle : p - (pos T - Kc) ≤ 2 * Kc := by simp only [Kc] at hm ⊢; omega
      rw [idx_val hle]
      congr 1
      simp only [Kc] at hm ⊢; omega
    · rw [if_neg hm]

/-! ## 2. `padR`: the right reservoir, and both geometric side conditions -/

/-- **Reserve one cell at the right end.**  The reading is unchanged (the new
cell is blank) but the stored width grows by one, which is exactly the room
`wlen_sweep` needs. -/
def padR (b : Γ) (T : STape Γ) : STape Γ := ⟨T.left, T.focus, T.right ++ [b]⟩

@[simp] theorem pos_padR (b : Γ) (T : STape Γ) : pos (padR b T) = pos T := rfl

@[simp] theorem wlen_padR (b : Γ) (T : STape Γ) : wlen (padR b T) = wlen T + 1 := by
  simp only [wlen, padR, pos, List.length_append, List.length_cons, List.length_nil]
  omega

theorem toList_padR (b : Γ) (T : STape Γ) : toList (padR b T) = toList T ++ [b] := by
  simp [toList, padR]

@[simp] theorem rd_padR (b : Γ) (T : STape Γ) (p : ℕ) : rd b (padR b T) p = rd b T p := by
  rw [rd, rd, toList_padR]
  exact PalPeg.Local.getD_snoc_blank _ _ _

/-- **The room condition holds for every padded tape, unconditionally.** -/
theorem room_padR (b : Γ) (T : STape Γ) : pos (padR b T) + Kc ≤ wlen (padR b T) := by
  rw [pos_padR, wlen_padR]
  have := pos_le_wlen T
  simp only [Kc]
  omega

/-- …and the padded tape is, deliberately, never `Reduced` when `b` is the
blank.  By `not_reduced_sweep_stable` that is the right side of the trade. -/
theorem not_reduced_padR (T : STape Γc) : ¬ Reduced (padR blankc T) := by
  intro h
  exact h (by simp [padR, List.getLast?_append])

/-- **The layout of the core with both reservoirs**: one sentinel blank at the
left (`shift1`, from `CloseoutCoreEnc3`) and one reserved blank at the right. -/
noncomputable def padTapes {P : ℕ} (rep : ChainVM → ChainL) (m : Mirrored1 P) :
    ℕ → STape Γc := fun i => padR blankc (encTapes1 rep m i)

theorem margin_padTapes {P : ℕ} (rep : ChainVM → ChainL) (m : Mirrored1 P) (i : ℕ) :
    Kc ≤ pos (padTapes rep m i) := by
  rw [padTapes, pos_padR]
  exact PalPeg.CloseoutCoreEnc3.margin_encTapes1 rep m i

theorem room_padTapes {P : ℕ} (rep : ChainVM → ChainL) (m : Mirrored1 P) (i : ℕ) :
    pos (padTapes rep m i) + Kc ≤ wlen (padTapes rep m i) := room_padR _ _

/-- The padding does not change what the layout reads. -/
theorem rd_padTapes {P : ℕ} (rep : ChainVM → ChainL) (m : Mirrored1 P) (i p : ℕ) :
    rd blankc (padTapes rep m i) p = rd blankc (encTapes1 rep m i) p := rd_padR _ _ _

/-- **The unpadded layout fails the room condition.**  `shift1` reserves a cell
on the left only; a tape whose `right` is empty — which
`CloseoutCoreEnc.viewTapes 0` and every `CloseoutCoreEnc3.stackTape` are — has
`wlen = pos`, so the window's right cell is not stored and `wlen_sweep` does
not apply.  Hence the padding of `padTapes` is forced, not cosmetic. -/
theorem not_room_shift1 :
    ¬ ∀ T : STape Γc, pos (shift1 blankc T) + Kc ≤ wlen (shift1 blankc T) := by
  intro h
  have := h ⟨[], blankc, []⟩
  simp [shift1, wlen, pos, Kc] at this

theorem right_stackTape (l : List (Option (Fin 2))) : (stackTape l).right = [] := by
  cases l with
  | nil => rfl
  | cons a t => rfl

theorem wlen_shift1_of_right_nil {Γ : Type} (b : Γ) {T : STape Γ} (h : T.right = []) :
    wlen (shift1 b T) = pos (shift1 b T) := by
  simp only [wlen, shift1, pos, h, List.length_nil, List.length_append, List.length_cons]

theorem wlen_stackTape (l : List (Option (Fin 2))) : wlen (stackTape l) = l.length := by
  rw [wlen, right_stackTape, PalPeg.CloseoutCoreEnc3.pos_stackTape]
  simp

/-- **No tape of the stack cursor layout of `CloseoutCoreEnc4` has any room.**
Every one of the seven is a sentinel-shifted `stackTape`, whose `right` is
empty, so `wlen = pos` and the right cell of the window is unstored: the layout
of `Enc4` §6 needs `padR` too. -/
theorem wlen_viewTapes7 (v : InputView) (i : ℕ) :
    wlen (viewTapes7 v i) = pos (viewTapes7 v i) := by
  match i with
  | 0 => exact wlen_shift1_of_right_nil _ (right_stackTape _)
  | 1 => exact wlen_shift1_of_right_nil _ (right_stackTape _)
  | (n + 2) =>
      obtain ⟨l, hl⟩ := PalPeg.CloseoutCoreEnc4.exists_stackTape_queueTapes5 v.far n
      show wlen (shift1 blankc (PalPeg.CloseoutCoreEnc3.queueTapes5 v.far n))
          = pos (shift1 blankc (PalPeg.CloseoutCoreEnc3.queueTapes5 v.far n))
      rw [hl]
      exact wlen_shift1_of_right_nil _ (right_stackTape l)

/-! ## 3. From `TEq` to equality on a width-conserving layout -/

variable {P : ℕ}

/-- **Residual: the layout conserves the stored width across a tick.**  Forced:
`wlen_sweep` says one `LocalStep` cannot change it, so any layout realized by a
`LocalStep` must be width-conserving. -/
def NAMED_widthTick {Q : Type} {t : ℕ} (enc : Mirrored1 P → Q × (Fin t → STape Γc))
    (f : Mirrored1 P → Mirrored1 P) : Prop :=
  ∀ (m : Mirrored1 P) (j : Fin t), wlen ((enc (f m)).2 j) = wlen ((enc m).2 j)

/-- **Residual: the same across an arrival.** -/
def NAMED_widthFeed {Q : Type} {t : ℕ}
    (enc : Mirrored1 P → Q × (Fin t → STape Γc)) : Prop :=
  ∀ (a : Fin 2) (m : Mirrored1 P) (j : Fin t),
    wlen ((enc (feedC a m)).2 j) = wlen ((enc m).2 j)

/-- **The geometric side conditions of the layout**: a sentinel on the left and
a reserved cell on the right.  `padTapes` satisfies both (§2). -/
def RoomOf {Q : Type} {t : ℕ} (enc : Mirrored1 P → Q × (Fin t → STape Γc)) : Prop :=
  ∀ (m : Mirrored1 P) (j : Fin t),
    Kc ≤ pos ((enc m).2 j) ∧ pos ((enc m).2 j) + Kc ≤ wlen ((enc m).2 j)

theorem roomOf_padTapes {Q : Type} {t : ℕ} {qOf : Mirrored1 P → Q}
    (rep : ChainVM → ChainL) :
    RoomOf (P := P) (fun m => (qOf m, fun j : Fin t => padTapes rep m j.val)) :=
  fun m j => ⟨margin_padTapes rep m j.val, room_padTapes rep m j.val⟩

/-- **The representation bridge, repaired.**  `TEq`-level realization plus
width conservation plus room gives the literal `RealizedTick` that
`CloseoutCoreEnc3.CoreResidual` needs — with no reducedness anywhere. -/
theorem realizedTick_of_width {Q : Type} {t : ℕ}
    {enc : Mirrored1 P → Q × (Fin t → STape Γc)}
    {L0 : LocalStep (Fin 2) Q Γc t Kc} {f : Mirrored1 P → Mirrored1 P}
    (h : RealizedTickT enc L0 f) (hroom : RoomOf enc) (hwidth : NAMED_widthTick enc f) :
    RealizedTick enc L0 f := by
  intro m
  refine Prod.ext (h m).1 (funext fun j => ?_)
  refine eq_of_TEq_of_width ((h m).2 j) ?_
  have hd := L0.disp_le (enc m).1 none (fun j => readWin blankc Kc ((enc m).2 j)) j
  rw [PalPeg.Local.LocalStep.apply_snd]
  rw [wlen_sweep blankc Kc ((enc m).2 j) _ _ (hroom m j).1 hd (hroom m j).2]
  exact hwidth m j

theorem realizedFeed_of_width {Q : Type} {t : ℕ}
    {enc : Mirrored1 P → Q × (Fin t → STape Γc)}
    {L0 : LocalStep (Fin 2) Q Γc t Kc}
    (h : RealizedFeedT enc L0) (hroom : RoomOf enc) (hwidth : NAMED_widthFeed enc) :
    RealizedFeed enc L0 := by
  intro a m
  refine Prod.ext (h a m).1 (funext fun j => ?_)
  refine eq_of_TEq_of_width ((h a m).2 j) ?_
  have hd := L0.disp_le (enc m).1 (some a) (fun j => readWin blankc Kc ((enc m).2 j)) j
  rw [PalPeg.Local.LocalStep.apply_snd]
  rw [wlen_sweep blankc Kc ((enc m).2 j) _ _ (hroom m j).1 hd (hroom m j).2]
  exact hwidth a m j

/-- **`NAMED_stepWindow` from a `WinStep`, without reducedness.** -/
theorem named_stepWindow_of_winStep_width {delay Lp Lf : ℕ} {rep : ChainVM → ChainL}
    {f : Mirrored1 P → Mirrored1 P}
    (W : WinStep (QL delay Lp Lf P QChain) (tL P tChain) (enc1 delay Lp Lf rep) f)
    (hroom : RoomOf (P := P) (enc1 delay Lp Lf rep))
    (hwidth : NAMED_widthTick (P := P) (enc1 delay Lp Lf rep) f) :
    PalPeg.CloseoutCoreEnc3.NAMED_stepWindow (P := P) delay Lp Lf rep f :=
  ⟨W.toStep, realizedTick_of_width
    (PalPeg.CloseoutCoreEnc4.realizedTickT_of_winStep W) hroom hwidth⟩

theorem named_feedWindow_of_winFeed_width {delay Lp Lf : ℕ} {rep : ChainVM → ChainL}
    (W : WinFeed (QL delay Lp Lf P QChain) (tL P tChain) (enc1 delay Lp Lf rep))
    (hroom : RoomOf (P := P) (enc1 delay Lp Lf rep))
    (hwidth : NAMED_widthFeed (P := P) (enc1 delay Lp Lf rep)) :
    PalPeg.CloseoutCoreEnc3.NAMED_feedWindow (P := P) delay Lp Lf rep :=
  ⟨W.toStep, realizedFeed_of_width
    (PalPeg.CloseoutCoreEnc4.realizedFeedT_of_winFeed W) hroom hwidth⟩

/-! ## 4. The mode dispatch as a window function -/

/-- **The window datum of one mode.**  `next` is a function of the finite
control, the input symbol and the windows only; `ctl` and `tape` are required
only on states *in that mode and not starved* — which is where `tickC` sends
the mode step. -/
structure ModeWin (Q : Type) (t : ℕ) (enc : Mirrored1 P → Q × (Fin t → STape Γc))
    (M : Steps P) (md : Mode) where
  next : Q → Option (Fin 2) → (Fin t → Window Γc Kc) → Q × (Fin t → Window Γc Kc × ℤ)
  disp_le : ∀ (q : Q) (a : Option (Fin 2)) (ws : Fin t → Window Γc Kc) (j : Fin t),
    |((next q a ws).2 j).2| ≤ (Kc : ℤ)
  ctl : ∀ m : Mirrored1 P, m.vm.ctl.mode = md → ¬ Starved m.vm →
    (enc (stepOf M md m)).1
      = (next (enc m).1 none (fun j => readWin blankc Kc ((enc m).2 j))).1
  tape : ∀ (m : Mirrored1 P) (j : Fin t), m.vm.ctl.mode = md → ¬ Starved m.vm →
    TEq ((enc (stepOf M md m)).2 j)
      (sweep blankc Kc ((enc m).2 j)
        ((next (enc m).1 none (fun j' => readWin blankc Kc ((enc m).2 j'))).2 j).1
        ((next (enc m).1 none (fun j' => readWin blankc Kc ((enc m).2 j'))).2 j).2)

/-- **The starvation test, read off the windows.**  `Starved` asks whether four
cursor heads can move right, i.e. whether the cell just right of each head is
stored; on a window layout that is a window predicate. -/
structure StarvedWin (Q : Type) (t : ℕ) (enc : Mirrored1 P → Q × (Fin t → STape Γc)) where
  test : Q → (Fin t → Window Γc Kc) → Bool
  spec : ∀ m : Mirrored1 P,
    (test (enc m).1 (fun j => readWin blankc Kc ((enc m).2 j)) = true ↔ Starved m.vm)

/-- The control projection must expose the mode (it does, for `qOfL`:
`CloseoutCoreStep.qOfL_mode`). -/
structure ModeOf (Q : Type) (t : ℕ) (enc : Mirrored1 P → Q × (Fin t → STape Γc)) where
  modeOf : Q → Mode
  spec : ∀ m : Mirrored1 P, modeOf (enc m).1 = m.vm.ctl.mode

/-- **The dispatched window function.**  Starved: keep the window and stand
still.  Otherwise: the window function of the current mode. -/
def dispatchNext {Q : Type} {t : ℕ} {enc : Mirrored1 P → Q × (Fin t → STape Γc)}
    {M : Steps P} (D : ModeOf Q t enc) (S : StarvedWin Q t enc)
    (W : ∀ md : Mode, ModeWin Q t enc M md) :
    Q → Option (Fin 2) → (Fin t → Window Γc Kc) → Q × (Fin t → Window Γc Kc × ℤ) :=
  fun q a ws => if S.test q ws then (q, fun j => (ws j, 0)) else (W (D.modeOf q)).next q a ws

theorem dispatchNext_disp {Q : Type} {t : ℕ} {enc : Mirrored1 P → Q × (Fin t → STape Γc)}
    {M : Steps P} (D : ModeOf Q t enc) (S : StarvedWin Q t enc)
    (W : ∀ md : Mode, ModeWin Q t enc M md)
    (q : Q) (a : Option (Fin 2)) (ws : Fin t → Window Γc Kc) (j : Fin t) :
    |((dispatchNext D S W q a ws).2 j).2| ≤ (Kc : ℤ) := by
  rw [dispatchNext]
  by_cases h : S.test q ws
  · rw [if_pos h]; simp
  · rw [if_neg h]; exact (W (D.modeOf q)).disp_le q a ws j

/-- **The `WinStep` for `tickC M`.**  The stutter branch is closed by
`sweep_id_TEq`; the stepping branch is exactly the `ModeWin` of the current
mode.  This is the mode dispatch written as a window function — the piece
`CloseoutCoreEnc4` left unbuilt. -/
noncomputable def winStep_of_modes {Q : Type} {t : ℕ} {enc : Mirrored1 P → Q × (Fin t → STape Γc)}
    {M : Steps P} (D : ModeOf Q t enc) (S : StarvedWin Q t enc)
    (W : ∀ md : Mode, ModeWin Q t enc M md)
    (hmargin : ∀ (m : Mirrored1 P) (j : Fin t), Kc ≤ pos ((enc m).2 j)) :
    WinStep Q t enc (tickC M) where
  next := dispatchNext D S W
  disp_le := dispatchNext_disp D S W
  ctl := by
    intro m
    by_cases hs : Starved m.vm
    · rw [PalPeg.LocalSysConcrete.tickC_starved M hs, dispatchNext,
        if_pos ((S.spec m).mpr hs)]
    · have ht : S.test (enc m).1 (fun j => readWin blankc Kc ((enc m).2 j)) = false := by
        by_cases h : S.test (enc m).1 (fun j => readWin blankc Kc ((enc m).2 j)) = true
        · exact absurd ((S.spec m).mp h) hs
        · simpa using h
      rw [PalPeg.LocalSysConcrete.tickC_step M hs, dispatchNext, if_neg (by simp [ht]),
        D.spec m]
      exact (W m.vm.ctl.mode).ctl m rfl hs
  tape := by
    intro m j
    by_cases hs : Starved m.vm
    · rw [PalPeg.LocalSysConcrete.tickC_starved M hs, dispatchNext,
        if_pos ((S.spec m).mpr hs)]
      exact sweep_id_TEq ((enc m).2 j) (hmargin m j)
    · have ht : S.test (enc m).1 (fun j => readWin blankc Kc ((enc m).2 j)) = false := by
        by_cases h : S.test (enc m).1 (fun j => readWin blankc Kc ((enc m).2 j)) = true
        · exact absurd ((S.spec m).mp h) hs
        · simpa using h
      rw [PalPeg.LocalSysConcrete.tickC_step M hs, dispatchNext, if_neg (by simp [ht]),
        D.spec m]
      exact (W m.vm.ctl.mode).tape m j rfl hs

theorem winStep_of_modes_next_starved {Q : Type} {t : ℕ}
    {enc : Mirrored1 P → Q × (Fin t → STape Γc)} {M : Steps P}
    (D : ModeOf Q t enc) (S : StarvedWin Q t enc) (W : ∀ md : Mode, ModeWin Q t enc M md)
    (hmargin : ∀ (m : Mirrored1 P) (j : Fin t), Kc ≤ pos ((enc m).2 j))
    (q : Q) (a : Option (Fin 2)) (ws : Fin t → Window Γc Kc) (h : S.test q ws = true) :
    (winStep_of_modes D S W hmargin).next q a ws = (q, fun j => (ws j, 0)) := by
  show dispatchNext D S W q a ws = _
  rw [dispatchNext, if_pos h]

theorem winStep_of_modes_next_step {Q : Type} {t : ℕ}
    {enc : Mirrored1 P → Q × (Fin t → STape Γc)} {M : Steps P}
    (D : ModeOf Q t enc) (S : StarvedWin Q t enc) (W : ∀ md : Mode, ModeWin Q t enc M md)
    (hmargin : ∀ (m : Mirrored1 P) (j : Fin t), Kc ≤ pos ((enc m).2 j))
    (q : Q) (a : Option (Fin 2)) (ws : Fin t → Window Γc Kc) (h : S.test q ws = false) :
    (winStep_of_modes D S W hmargin).next q a ws = (W (D.modeOf q)).next q a ws := by
  show dispatchNext D S W q a ws = _
  rw [dispatchNext, if_neg (by simp [h])]

/-- The `ModeOf` datum for the concrete control projection: the mode *is* a
field of `qOfL` (`CloseoutCoreStep.qOfL_mode`), so this is unconditional. -/
def modeOf_enc1 (delay Lp Lf : ℕ) (rep : ChainVM → ChainL) :
    ModeOf (P := P) (QL delay Lp Lf P QChain) (tL P tChain) (enc1 delay Lp Lf rep) where
  modeOf := fun q => q.1.val.mode
  spec := fun m => rfl

/-! ## 5. The residuals, per mode -/

/-- **Residual: the window datum of one mode.**  Ten of these — one per
`Mode` — plus `NAMED_starvedWindow` is all `winStep_of_modes` needs for the
tick.  The intended proof of each is: run the mode's step
(`LocalRealizesPhase.shiftStepL`, `copyStepL`, `homeStepL`, `markEndStepL`,
`LocalRealizesScan.chooseStepC`, `rewindStepC`, `LocalWF.ffpp`, and the
`LocalTick1/2/3` tick bodies), translate each tape action with
`CloseoutCoreEnc.winRealizes_of_tapeLocal` /
`winRealizes_stepLocal_phys` / `CloseoutCoreEnc3.winRealizes_push` /
`winRealizes_pop`, and take the identity window on every tape the mode does
not touch (`sweep_id_TEq`). -/
def NAMED_modeWin {Q : Type} {t : ℕ} (enc : Mirrored1 P → Q × (Fin t → STape Γc))
    (M : Steps P) (md : Mode) : Type := ModeWin Q t enc M md

/-- **Residual: starvation is a window predicate.** -/
def NAMED_starvedWindow {Q : Type} {t : ℕ}
    (enc : Mirrored1 P → Q × (Fin t → STape Γc)) : Type := StarvedWin Q t enc

/-- **Residual: the arrival half, against a *given* `next`.**  `CoreResidual`
needs the *same* `LocalStep` for the tick and for the arrival, so the arrival
obligation is stated against the window function the tick dispatch already
fixed, not as an independent `WinFeed`.  `feedC` appends one letter to
`pending` and pushes it into the parked mirror; on the stack layout of
`CloseoutCoreEnc4.viewTapes7` that is one `winRealizes_push`, but `pending`
itself has no tape in `CloseoutCoreEnc.encTapes`, so the layout must be
extended first. -/
structure FeedWin (Q : Type) (t : ℕ) (enc : Mirrored1 P → Q × (Fin t → STape Γc))
    (nx : Q → Option (Fin 2) → (Fin t → Window Γc Kc) → Q × (Fin t → Window Γc Kc × ℤ)) where
  ctl : ∀ (a : Fin 2) (m : Mirrored1 P),
    (enc (feedC a m)).1 = (nx (enc m).1 (some a) (fun j => readWin blankc Kc ((enc m).2 j))).1
  tape : ∀ (a : Fin 2) (m : Mirrored1 P) (j : Fin t), TEq ((enc (feedC a m)).2 j)
    (sweep blankc Kc ((enc m).2 j)
      ((nx (enc m).1 (some a) (fun j' => readWin blankc Kc ((enc m).2 j'))).2 j).1
      ((nx (enc m).1 (some a) (fun j' => readWin blankc Kc ((enc m).2 j'))).2 j).2)

/-- **Exactly what the tick needs**, bundled: the mode projection, the
starvation test, the ten mode windows, and the left margin. -/
structure ResidualTick (Q : Type) (t : ℕ) (enc : Mirrored1 P → Q × (Fin t → STape Γc))
    (M : Steps P) where
  D : ModeOf Q t enc
  S : NAMED_starvedWindow enc
  init : NAMED_modeWin enc M .init
  scan : NAMED_modeWin enc M .scan
  shift : NAMED_modeWin enc M .shift
  copy : NAMED_modeWin enc M .copy
  home : NAMED_modeWin enc M .home
  fpp : NAMED_modeWin enc M .fpp
  markEnd : NAMED_modeWin enc M .markEnd
  choose : NAMED_modeWin enc M .choose
  rewind : NAMED_modeWin enc M .rewind
  replayStart : NAMED_modeWin enc M .replayStart
  hmargin : ∀ (m : Mirrored1 P) (j : Fin t), Kc ≤ pos ((enc m).2 j)

/-- The ten fields, as the total function `winStep_of_modes` consumes. -/
def ResidualTick.modes {Q : Type} {t : ℕ} {enc : Mirrored1 P → Q × (Fin t → STape Γc)}
    {M : Steps P} (R : ResidualTick Q t enc M) : ∀ md : Mode, ModeWin Q t enc M md
  | .init => R.init
  | .scan => R.scan
  | .shift => R.shift
  | .copy => R.copy
  | .home => R.home
  | .fpp => R.fpp
  | .markEnd => R.markEnd
  | .choose => R.choose
  | .rewind => R.rewind
  | .replayStart => R.replayStart

/-- **The tick's `WinStep` from the bundle.** -/
noncomputable def winStep_of_residualTick {Q : Type} {t : ℕ}
    {enc : Mirrored1 P → Q × (Fin t → STape Γc)} {M : Steps P}
    (R : ResidualTick Q t enc M) : WinStep Q t enc (tickC M) :=
  winStep_of_modes R.D R.S R.modes R.hmargin

/-- The `LocalStep` the bundle fixes — the one both halves must use. -/
noncomputable def ResidualTick.step {Q : Type} {t : ℕ} {enc : Mirrored1 P → Q × (Fin t → STape Γc)}
    {M : Steps P} (R : ResidualTick Q t enc M) : LocalStep (Fin 2) Q Γc t Kc :=
  (winStep_of_residualTick R).toStep

/-- **`NAMED_stepWindow` for the concrete tick, from the bundle plus width
conservation.**  This is the current shape of the tick half's residual. -/
theorem named_stepWindow_of_residualTick {delay Lp Lf : ℕ} {rep : ChainVM → ChainL}
    {M : Steps P}
    (R : ResidualTick (QL delay Lp Lf P QChain) (tL P tChain) (enc1 delay Lp Lf rep) M)
    (hroom : RoomOf (P := P) (enc1 delay Lp Lf rep))
    (hwidth : NAMED_widthTick (P := P) (enc1 delay Lp Lf rep) (tickC M)) :
    PalPeg.CloseoutCoreEnc3.NAMED_stepWindow (P := P) delay Lp Lf rep (tickC M) :=
  named_stepWindow_of_winStep_width (winStep_of_residualTick R) hroom hwidth

theorem realizedFeedT_of_feedWin {Q : Type} {t : ℕ}
    {enc : Mirrored1 P → Q × (Fin t → STape Γc)} {M : Steps P}
    (R : ResidualTick Q t enc M) (F : FeedWin Q t enc (winStep_of_residualTick R).next) :
    RealizedFeedT enc R.step :=
  fun a m => ⟨F.ctl a m, fun j => F.tape a m j⟩

/-- **The full `CoreLocal` term for the concrete core**, from the tick bundle,
the arrival datum against the *same* window function, the room of the layout
and the two width-conservation residuals.  This is the exact residual shape the
closeout is now down to for the core. -/
noncomputable def coreLocal_of_residual {M : Steps P} {repC : Control → Bool} {x0 : LX (Mirrored1 P)}
    {Q : Type} {t : ℕ} {enc : Mirrored1 P → Q × (Fin t → STape Γc)}
    (R : ResidualTick Q t enc M) (F : FeedWin Q t enc (winStep_of_residualTick R).next)
    (hroom : RoomOf enc) (hwT : NAMED_widthTick enc (tickC M)) (hwF : NAMED_widthFeed enc)
    (q0 : Q) (repQ outQ : Q → Bool)
    (hrep : ∀ m : Mirrored1 P, repC m.vm.ctl = repQ (enc m).1)
    (hout : ∀ m : Mirrored1 P, m.vm.ctl.output = outQ (enc m).1)
    (hinit : enc x0.core = (q0, fun _ => STape.blankTape blankc)) :
    CoreLocal (sysC M repC) x0 Q Γc t Kc :=
  PalPeg.CloseoutCoreEnc4.coreLocal_of_win
    (M := M) (repC := repC) (x0 := x0) R.step q0 repQ outQ
    (realizedTick_of_width
      (PalPeg.CloseoutCoreEnc4.realizedTickT_of_winStep (winStep_of_residualTick R))
      hroom hwT)
    (realizedFeed_of_width (realizedFeedT_of_feedWin R F) hroom hwF)
    hrep hout hinit

/-! ## 6. The remaining named residuals -/

/-- **`NAMED_fppQuantum`, second repair.**  `CloseoutCoreEnc4.NAMED_fppQuantum'`
asks for a `WinStep`; this asks additionally that the `.fpp` mode's window
function be *one* `GalilDpCode` instruction lifted to the active bank of
`LocalBuffers.Buffered` — which is what `LocalBuffers.abs_stepL`
(`abs (stepL f x) = f (abs x)`) makes visible at the abstract level, and what
"one fpp quantum per tick" means. -/
def NAMED_fppQuantum'' {Q : Type} {t : ℕ} (enc : Mirrored1 P → Q × (Fin t → STape Γc))
    (M : Steps P) : Prop :=
  ∃ W : ModeWin Q t enc M .fpp,
    ∀ (q : Q) (a : Option (Fin 2)) (ws : Fin t → Window Γc Kc) (j : Fin t),
      ((W.next q a ws).2 j).1 = ws j ∨ ((W.next q a ws).2 j).2 = 0

/-- The `.fpp` window datum of the second repair is in particular a `ModeWin`,
so it feeds `ResidualTick` directly. -/
noncomputable def modeWin_fpp_of_second {Q : Type} {t : ℕ}
    {enc : Mirrored1 P → Q × (Fin t → STape Γc)} {M : Steps P}
    (h : NAMED_fppQuantum'' enc M) : ModeWin Q t enc M .fpp :=
  Classical.choice (⟨h.choose⟩ : Nonempty (ModeWin Q t enc M .fpp))

/-- **`NAMED_encInjective`, stack version.**  `CloseoutCoreEnc3` refutes
injectivity for the cursor layout of `Enc2`; `CloseoutCoreEnc4.viewTapes7`
recovers `back`, `focus`, `front` and `rear` from the tapes
(`inj_viewTapes7_upto`), so what is left is the rotation state and the two
length counters of the queue. -/
def NAMED_encInjective7 : Prop :=
  ∀ v v' : InputView, (∀ i : ℕ, viewTapes7 v i = viewTapes7 v' i) → v = v'

/-- **Injectivity of the stack cursor reduces to the queue's finite rotation
state and its two counters.**  Everything else is recovered by `Enc4` §6. -/
theorem injective7_of_parts
    (h : ∀ v v' : InputView, (∀ i : ℕ, viewTapes7 v i = viewTapes7 v' i) →
      v.far.state = v'.far.state ∧ v.far.lenf = v'.far.lenf ∧ v.far.lenr = v'.far.lenr ∧
      v.gap = v'.gap) :
    NAMED_encInjective7 := by
  intro v v' hv
  obtain ⟨hst, hlf, hlr, hgap⟩ := h v v' hv
  obtain ⟨hfocus, hback⟩ := PalPeg.CloseoutCoreEnc4.viewTapes7_back (hv 0)
  have hnear := PalPeg.CloseoutCoreEnc4.viewTapes7_near (hv 1)
  have hfront := PalPeg.CloseoutCoreEnc4.viewTapes7_front (hv 2)
  have hrear := PalPeg.CloseoutCoreEnc4.viewTapes7_rear (hv 3)
  obtain ⟨b, f, n, far, g⟩ := v
  obtain ⟨b', f', n', far', g'⟩ := v'
  obtain ⟨lf, fr, st, lr, re⟩ := far
  obtain ⟨lf', fr', st', lr', re'⟩ := far'
  simp_all

end PalPeg.CloseoutCoreEnc5

#print axioms PalPeg.CloseoutCoreEnc5.wlen_sweep
#print axioms PalPeg.CloseoutCoreEnc5.eq_of_TEq_of_width
#print axioms PalPeg.CloseoutCoreEnc5.not_reduced_sweep_stable
#print axioms PalPeg.CloseoutCoreEnc5.sweep_id_TEq
#print axioms PalPeg.CloseoutCoreEnc5.room_padR
#print axioms PalPeg.CloseoutCoreEnc5.rd_padR
#print axioms PalPeg.CloseoutCoreEnc5.margin_padTapes
#print axioms PalPeg.CloseoutCoreEnc5.room_padTapes
#print axioms PalPeg.CloseoutCoreEnc5.not_room_shift1
#print axioms PalPeg.CloseoutCoreEnc5.not_reduced_padR
#print axioms PalPeg.CloseoutCoreEnc5.wlen_viewTapes7
#print axioms PalPeg.CloseoutCoreEnc5.realizedTick_of_width
#print axioms PalPeg.CloseoutCoreEnc5.realizedFeed_of_width
#print axioms PalPeg.CloseoutCoreEnc5.named_stepWindow_of_winStep_width
#print axioms PalPeg.CloseoutCoreEnc5.named_feedWindow_of_winFeed_width
#print axioms PalPeg.CloseoutCoreEnc5.winStep_of_modes
#print axioms PalPeg.CloseoutCoreEnc5.winStep_of_modes_next_starved
#print axioms PalPeg.CloseoutCoreEnc5.winStep_of_modes_next_step
#print axioms PalPeg.CloseoutCoreEnc5.modeOf_enc1
#print axioms PalPeg.CloseoutCoreEnc5.named_stepWindow_of_residualTick
#print axioms PalPeg.CloseoutCoreEnc5.coreLocal_of_residual
#print axioms PalPeg.CloseoutCoreEnc5.injective7_of_parts
