import PalPeg.CloseoutCoreEnc5

/-!
# Closeout, step 2g: the write-and-move quantum, starvation as a local read, the arrival tape, and two verdicts

`CloseoutCoreEnc5` reduces the core's tick to ten `NAMED_modeWin` obligations
plus `NAMED_starvedWindow`, the arrival to a `FeedWin`, and leaves
`NAMED_widthFeed` and `NAMED_encInjective7` open.  This file works on exactly
those four fronts.  Two of them end in a **refutation**, each with a repaired
residual next to it.

## What is established

* **§1 (the quantum).**  `applyAction_right_TEq_sweep`: a write-at-the-head
  followed by a right move *is* a `sweep` with displacement `1`, for the window
  `wWrite` that overwrites the head cell and copies the two neighbours.  No room
  hypothesis — `rd_sweep`/`pos_sweep` need only the left margin.  Every stack
  push in the layout is this quantum.
* **§2 (starvation is local).**  `canRight_right_iff` computes the lookahead
  conjunct of `Starved`, and `canRight_and_lookahead` collapses the pair
  `canRight p ∧ canRight (right p)` to `p.head.right ≠ [] ∨ p.head.incoming ≠ []`
  — the `gap` bit drops out.  `four_iff_three` and `starved_iff` therefore
  rewrite `Starved` as **three** local reads: one stored cell right of `left`,
  `canRight` of `center`, and `canRight` of the parked right head.
  `gap_left_iterate` and `canRight_or_canRight_left` handle the parked head:
  the gap alternates along the replay offset, so one of any two consecutive
  offsets is unconditionally non-starving (`canRight_absR_of_parity`).
  `NAMED_starvedRead` is the residual that remains, and
  `starvedWindow_of_read` turns it into `CloseoutCoreEnc5.NAMED_starvedWindow`.
* **§3 (the arrival tape, and the width verdict).**  `pendTape` lays `vm.pending`
  out with the head on the first free cell, one sentinel below and **no** right
  reservoir; `pendTape_append` shows an arrival is exactly the §1 quantum and
  `pendTape_append_TEq_sweep` turns it into step data.  Then the verdict:
  `not_widthFeed_of_feedGrow` refutes `CloseoutCoreEnc5.NAMED_widthFeed` for
  every layout whose head advances on each arrival — width conservation plus a
  head that advances forces `pos > wlen` after `wlen + 1` arrivals.  So
  `Enc5.realizedFeed_of_width` has an unsatisfiable hypothesis.  The repair is
  `NAMED_feedWidthMatch` (layout and step agree on the width, neither is
  constant) with the bridge `realizedFeed_of_widthMatch`; it is a genuine
  weakening (`feedWidthMatch_of_widthFeed`).  `pos_queueTapes5_rear_snoc` is the
  concrete growth witness: `RTQueue.snoc` pushes one cell onto a cursor's rear
  stack.
* **§4 (the mode window, tape by tape).**  `ModePerTape` /
  `modeWin_of_perTape` decompose `CloseoutCoreEnc5.ModeWin` into one control
  update plus one window action per tape, and `modeWin_of_tapeFixed` closes
  outright any mode that touches no tape (via `sweep_id_TEq`).
* **§5 (the injectivity verdict, and the repaired cursor).**
  `not_NAMED_encInjective7` **refutes** `CloseoutCoreEnc5.NAMED_encInjective7`:
  two views differing only in the `r` field of a `reversing` rotation state have
  literally the same seven tapes, because `queueTapes5` stores `front`, `rear`,
  the `reversing` `f`, `f'` and `r'` and nothing else.  The seven-tape cursor is
  one stack short.  `queueTapes6`/`viewTapes8` add it (`tView7_lt_tView8`,
  `margin_viewTapes8`), and `injective_viewTapes8` **proves** injectivity up to
  `gap`, the two length counters and the rotation phase tag `tagOf` with its
  validity counter `okOf` — all finite control or unary counters, not cursor
  tapes.  `NAMED_farControl` names that residue.

## What is *not* established

No `ModeWin` for any mode: §4 gives the decomposition and the shape residuals
(`NAMED_scanShape`, `NAMED_scanMatchWin`, `NAMED_scanBgChain`,
`NAMED_initShape`, `NAMED_initWin`, `NAMED_replayStartShape`,
`NAMED_replayStartWin`, `NAMED_restartShape`), not the data.  `NAMED_starvedRead`,
`NAMED_feedWidthMatch`, `NAMED_feedGrow` and `NAMED_farControl` are open.  Two
of `Enc5`'s residuals are now known **false** (`NAMED_widthFeed`,
`NAMED_encInjective7`), so the `Enc5` bridges that use them must be replaced by
the ones here.

**無条件 PAL ∈ PEG は未完.**
-/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutCoreEnc7

open PalPeg PalPeg.Program
open PalPeg.Local (Window idx idx_val pos rd toList sweep pos_sweep rd_sweep readWin
  readWin_eq mvL mvR LocalStep rd_applyAction pos_applyAction_right)
open PalPeg.LocalState (GalilVML)
open PalPeg.LocalInputView (InputView)
open PalPeg.LocalArrival (absHead' abs')
open PalPeg.LocalReplayParked (Mirrored1 abs'' absR physHead rval)
open PalPeg.GalilScaffoldInputHead (PlaceHead)
open PalPeg.GalilScaffoldChainVerifier (canRight)
open PalPeg.GalilScaffoldChainInputSupply (ChainVM)
open PalPeg.GalilScaffoldController (Control Mode)
open PalPeg.LocalChain (ChainL)
open PalPeg.LocalSysConcrete (Steps sysC tickC feedC Starved stepOf)
open PalPeg.CloseoutCoreStep (Γc blankc tView nViews tMir tBuf tL QL qOfL
  RealizedTick RealizedFeed)
open PalPeg.CloseoutCoreEnc (Kc cellSym encTapes QChain tChain qChainOf)
open PalPeg.CloseoutCoreEnc3 (shift1 shift1_inj stackTape stackTape_inj pos_stackTape
  encTapes1 queueTapes5)
open PalPeg.CloseoutCoreEnc4 (TEq WinStep WinFeed RealizedTickT RealizedFeedT enc1
  viewTapes7 map_some_inj)
open PalPeg.CloseoutCoreEnc5 (wlen pos_le_wlen eq_of_TEq_of_width sweep_id_TEq
  ModeWin StarvedWin ModeOf NAMED_modeWin NAMED_starvedWindow NAMED_widthFeed
  NAMED_widthTick NAMED_encInjective7 RoomOf FeedWin)

variable {P : ℕ}

/-! ## 1. The write-and-move-right quantum is a sweep

Every stack-tape push in the layout is "write the new cell at the head, then
move right".  `LocalStep` semantics only offers `sweep`, so the two must be
identified.  They are, up to `TEq`, for the window that overwrites the head
cell and copies the two neighbours. -/

/-- The window that writes `s` at the head and leaves the rest of the window
alone. -/
def wWrite (T : STape Γc) (s : Γc) : Window Γc Kc :=
  fun i => if (i : ℕ) = Kc then s else readWin blankc Kc T i

/-- **A write-and-move-right micro-action *is* a sweep with displacement `1`.**
No room hypothesis: `rd_sweep` and `pos_sweep` need only the left margin. -/
theorem applyAction_right_TEq_sweep (T : STape Γc) (s : Γc) (hK : Kc ≤ pos T) :
    TEq (T.applyAction blankc (s, PegSeparation.RealTimeTM.Move.right))
      (sweep blankc Kc T (wWrite T s) 1) := by
  have hd : |(1 : ℤ)| ≤ (Kc : ℤ) := by norm_num [Kc]
  refine ⟨?_, ?_⟩
  · have h1 := pos_sweep blankc Kc T (wWrite T s) 1 hK hd
    have h2 := pos_applyAction_right blankc s T
    omega
  · intro p
    rw [rd_applyAction, rd_sweep blankc Kc T (wWrite T s) 1 hK p]
    by_cases hm : pos T - Kc ≤ p ∧ p ≤ pos T + Kc
    · rw [if_pos hm]
      have hle : p - (pos T - Kc) ≤ 2 * Kc := by simp only [Kc] at hm ⊢; omega
      have hidx : ((idx Kc (p - (pos T - Kc))) : ℕ) = p - (pos T - Kc) := idx_val hle
      by_cases hp : p = pos T
      · have h1 : p - (pos T - Kc) = Kc := by simp only [Kc] at hK hp ⊢; omega
        rw [if_pos hp]
        show s = wWrite T s (idx Kc (p - (pos T - Kc)))
        rw [wWrite, if_pos (by rw [hidx, h1])]
      · have h1 : p - (pos T - Kc) ≠ Kc := by
          simp only [Kc] at hK hp hm ⊢; omega
        rw [if_neg hp]
        show rd blankc T p = wWrite T s (idx Kc (p - (pos T - Kc)))
        rw [wWrite, if_neg (by rw [hidx]; exact h1), readWin_eq, hidx]
        congr 1
        simp only [Kc] at hm ⊢; omega
    · rw [if_neg hm, if_neg (by intro h; exact hm ⟨by omega, by omega⟩)]

/-! ## 2. Starvation is a local read of four cursors

`Starved x` is `¬ (canRight left ∧ canRight center ∧ canRight right ∧
canRight (right left))`.  Unfolding `canRight` on `absHead'` turns each
conjunct into a read of the cursor's own `gap` bit, its `near` stack and its
`far` queue — window data.  Two simplifications happen on the way. -/

theorem canRight_iff (p : PlaceHead) :
    canRight p ↔ (p.gap = false ∨ p.head.right ≠ [] ∨ p.head.incoming ≠ []) := Iff.rfl

/-- **One cell of lookahead: the second conjunct is the complement bit.**
`GalilScaffoldChainVerifier.right` toggles the gap, so `canRight (right p)`
holds vacuously exactly when `canRight p` needs stored content. -/
theorem canRight_right_iff (p : PlaceHead) :
    canRight (PalPeg.GalilScaffoldChainVerifier.right p)
      ↔ (p.gap = true ∨ p.head.right ≠ [] ∨ p.head.incoming ≠ []) := by
  cases hg : p.gap <;>
    simp [canRight, PalPeg.GalilScaffoldChainVerifier.right, hg]

/-- **…so the pair collapses: the `left` cursor's two obligations together say
exactly "one cell is stored to the right", with the gap bit gone.** -/
theorem canRight_and_lookahead (p : PlaceHead) :
    (canRight p ∧ canRight (PalPeg.GalilScaffoldChainVerifier.right p))
      ↔ (p.head.right ≠ [] ∨ p.head.incoming ≠ []) := by
  rw [canRight_iff, canRight_right_iff]
  cases hg : p.gap <;> simp

/-- The local read: one stored cell to the right of a cursor. -/
def HasNext (v : InputView) (q : List (Fin 2)) : Prop :=
  v.near ≠ [] ∨ RTQueue.toList v.far ++ q ≠ []

theorem hasNext_iff (v : InputView) (q : List (Fin 2)) :
    HasNext v q ↔ ((absHead' v q).head.right ≠ [] ∨ (absHead' v q).head.incoming ≠ []) :=
  Iff.rfl

/-- The four conjuncts of `¬ Starved`, as three local reads. -/
theorem four_iff_three (x : GalilVML P) :
    (canRight (abs'' x).left ∧ canRight (abs'' x).center ∧ canRight (abs'' x).right ∧
        canRight (PalPeg.GalilScaffoldChainVerifier.right (abs'' x).left))
      ↔ (HasNext x.left x.pending ∧
          canRight (absHead' x.center x.pending) ∧ canRight (absR x)) := by
  constructor
  · intro h
    exact ⟨(canRight_and_lookahead _).mp ⟨h.1, h.2.2.2⟩, h.2.1, h.2.2.1⟩
  · intro h
    have h14 := (canRight_and_lookahead (absHead' x.left x.pending)).mpr h.1
    exact ⟨h14.1, h.2.1, h.2.2, h14.2⟩

/-- **Starvation, spelled out as local reads.**  The `left` cursor contributes a
gap-free condition (`canRight_and_lookahead`), the `center` cursor its own
`canRight`, and the parked right head its own. -/
theorem starved_iff (x : GalilVML P) :
    Starved x ↔ ¬ (HasNext x.left x.pending ∧
      canRight (absHead' x.center x.pending) ∧ canRight (absR x)) :=
  not_congr (four_iff_three x)

theorem not_starved_iff (x : GalilVML P) :
    ¬ Starved x ↔ (HasNext x.left x.pending ∧
      canRight (absHead' x.center x.pending) ∧ canRight (absR x)) := by
  classical
  rw [starved_iff, not_not]

/-! ### The parked right head

`absR x` is `left^[rval x] (physHead x)` while replaying.  `left` toggles the
gap on every application, and a gap-free head can always move right, so the
parity of the replay offset already decides the third conjunct. -/

theorem gap_left (p : PlaceHead) :
    (PalPeg.GalilScaffoldInputHead.left p).gap = !p.gap := rfl

theorem gap_left_iterate (n : ℕ) (p : PlaceHead) :
    (PalPeg.GalilScaffoldInputHead.left^[n] p).gap = (if n % 2 = 0 then p.gap else !p.gap) := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', gap_left, ih]
      rcases Nat.even_or_odd k with he | ho
      · have h0 : k % 2 = 0 := Nat.even_iff.mp he
        have h1 : (k + 1) % 2 = 1 := by omega
        simp [h0, h1]
      · have h0 : k % 2 = 1 := Nat.odd_iff.mp ho
        have h1 : (k + 1) % 2 = 0 := by omega
        simp [h0, h1]

theorem canRight_of_gap_false {p : PlaceHead} (h : p.gap = false) : canRight p := Or.inl h

/-- **One of any two consecutive replay offsets is never starving.**  The gap
bit alternates, and a gap position is always free to move right. -/
theorem canRight_or_canRight_left (p : PlaceHead) :
    canRight p ∨ canRight (PalPeg.GalilScaffoldInputHead.left p) := by
  cases hg : p.gap
  · exact Or.inl (canRight_of_gap_false hg)
  · exact Or.inr (canRight_of_gap_false (by rw [gap_left, hg]; rfl))

/-- **The parked right head, by parity of the replay counter.**  If the replay
offset lands the head on a gap cell, the third conjunct of `¬ Starved` holds
with no reference to stored content at all. -/
theorem canRight_absR_of_parity {x : GalilVML P} (hr : x.ctl.replaying = true)
    (h : (if rval x % 2 = 0 then (physHead x).gap else !(physHead x).gap) = false) :
    canRight (absR x) := by
  refine canRight_of_gap_false ?_
  rw [PalPeg.LocalReplayParked.absR_of_replaying hr, gap_left_iterate]
  exact h

/-- **Residual: the three local reads are a `Bool` function of the control and
the windows.**  This is `NAMED_starvedWindow` with the starvation test already
reduced to `not_starved_iff`: what is left is that each of the three reads —
`near ≠ []`/queue-nonempty for `left`, `canRight` for `center`, and the parked
`canRight` for the right head — is computable from the encoded control and the
`2 * Kc + 1` cells at each head. -/
def NAMED_starvedRead {Q : Type} {t : ℕ}
    (enc : Mirrored1 P → Q × (Fin t → STape Γc)) : Type :=
  { test : Q → (Fin t → Window Γc Kc) → Bool //
    ∀ m : Mirrored1 P,
      (test (enc m).1 (fun j => readWin blankc Kc ((enc m).2 j)) = true
        ↔ ¬ (HasNext m.vm.left m.vm.pending ∧
             canRight (absHead' m.vm.center m.vm.pending) ∧ canRight (absR m.vm))) }

/-- …and it is exactly `NAMED_starvedWindow`, by `not_starved_iff`. -/
def starvedWindow_of_read {Q : Type} {t : ℕ}
    {enc : Mirrored1 P → Q × (Fin t → STape Γc)} (R : NAMED_starvedRead enc) :
    NAMED_starvedWindow enc where
  test := R.1
  spec := fun m => by
    rw [R.2 m, starved_iff]


/-! ## 3. The arrival tape, and the verdict on `NAMED_widthFeed`

`CloseoutCoreEnc5.FeedWin` is unconditional in `m`, so the layout must carry
`vm.pending` even though the invariant keeps it empty.  §3 lays it out, shows
the append is exactly the quantum of §1, and then shows that
`CloseoutCoreEnc5.NAMED_widthFeed` — width conservation across an arrival — is
**not** an option for any layout that stores arrivals. -/

/-- The cell an arriving letter occupies. -/
def pendCell (a : Fin 2) : Γc := cellSym (some a)

/-- **The arrival tape.**  The letters that have arrived and not yet been
distributed, written left to right, with the head on the first free cell and one
sentinel blank below the bottom (so the left margin is unconditional).  There is
deliberately **no** right reservoir: the tape grows. -/
def pendTape (q : List (Fin 2)) : STape Γc :=
  ⟨(q.reverse.map pendCell) ++ [blankc], blankc, []⟩

@[simp] theorem pos_pendTape (q : List (Fin 2)) : pos (pendTape q) = q.length + 1 := by
  simp [pos, pendTape]

theorem margin_pendTape (q : List (Fin 2)) : Kc ≤ pos (pendTape q) := by
  rw [pos_pendTape]
  simp only [Kc]
  omega

@[simp] theorem wlen_pendTape (q : List (Fin 2)) : wlen (pendTape q) = q.length + 1 := by
  simp [wlen, pendTape, pos]

/-- The arrival tape has no room: the cell right of the head is unstored, which
is exactly why an arrival can widen it (`CloseoutCoreEnc5.wlen_sweep` does not
apply). -/
theorem not_room_pendTape (q : List (Fin 2)) :
    ¬ (pos (pendTape q) + Kc ≤ wlen (pendTape q)) := by
  rw [pos_pendTape, wlen_pendTape]
  simp only [Kc]
  omega

/-- **An arrival is one write-and-move-right on the arrival tape.** -/
theorem pendTape_append (q : List (Fin 2)) (a : Fin 2) :
    pendTape (q ++ [a])
      = (pendTape q).applyAction blankc (pendCell a, PegSeparation.RealTimeTM.Move.right) := by
  simp [pendTape, STape.applyAction]

/-- …hence, by §1, one *sweep* with displacement `1`: the arrival half of the
window function on this tape is completely determined. -/
theorem pendTape_append_TEq_sweep (q : List (Fin 2)) (a : Fin 2) :
    TEq (pendTape (q ++ [a]))
      (sweep blankc Kc (pendTape q) (wWrite (pendTape q) (pendCell a)) 1) := by
  rw [pendTape_append]
  exact applyAction_right_TEq_sweep _ _ (margin_pendTape q)

/-- And the width grows by exactly one. -/
theorem wlen_pendTape_append (q : List (Fin 2)) (a : Fin 2) :
    wlen (pendTape (q ++ [a])) = wlen (pendTape q) + 1 := by
  simp

/-! ### The verdict -/

/-- **Residual, isolated: the arrival moves one head one cell right.**  True of
the arrival tape (`pos_pendTape`) and of the queue rear stack of every cursor
(`pos_queueTapes5_rear_snoc`). -/
def NAMED_feedGrow {Q : Type} {t : ℕ} (enc : Mirrored1 P → Q × (Fin t → STape Γc))
    (a : Fin 2) (j : Fin t) : Prop :=
  ∀ m : Mirrored1 P, pos ((enc (feedC a m)).2 j) = pos ((enc m).2 j) + 1

/-- **`CloseoutCoreEnc5.NAMED_widthFeed` is false for every layout that stores
arrivals.**  Width conservation across an arrival plus a head that advances on
every arrival forces `pos > wlen` after `wlen + 1` arrivals, contradicting
`pos_le_wlen`.  So the width-conservation route of `Enc5` §3 closes the tick but
**not** the arrival, and `realizedFeed_of_width` has an unsatisfiable
hypothesis. -/
theorem not_widthFeed_of_feedGrow {Q : Type} {t : ℕ}
    (enc : Mirrored1 P → Q × (Fin t → STape Γc)) (j : Fin t) (a : Fin 2) (m0 : Mirrored1 P)
    (hgrow : NAMED_feedGrow enc a j) (hw : NAMED_widthFeed enc) : False := by
  have key : ∀ n : ℕ,
      pos ((enc ((feedC a)^[n] m0)).2 j) = pos ((enc m0).2 j) + n ∧
        wlen ((enc ((feedC a)^[n] m0)).2 j) = wlen ((enc m0).2 j) := by
    intro n
    induction n with
    | zero => exact ⟨by simp, by simp⟩
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact ⟨by rw [hgrow, ih.1]; omega, by rw [hw a _ j, ih.2]⟩
  obtain ⟨h1, h2⟩ := key (wlen ((enc m0).2 j) + 1)
  have h3 := pos_le_wlen ((enc ((feedC a)^[wlen ((enc m0).2 j) + 1] m0)).2 j)
  have h4 := pos_le_wlen ((enc m0).2 j)
  omega

/-- **The repaired arrival residual.**  What `eq_of_TEq_of_width` actually needs
is that the layout and the step agree on the stored width — not that either is
constant.  On the arrival tape both grow by one (`wlen_pendTape_append`, and the
sweep of `pendTape_append_TEq_sweep` grows because there is no room), so this is
satisfiable where `NAMED_widthFeed` is not. -/
def NAMED_feedWidthMatch {Q : Type} {t : ℕ} (enc : Mirrored1 P → Q × (Fin t → STape Γc))
    (L0 : LocalStep (Fin 2) Q Γc t Kc) : Prop :=
  ∀ (a : Fin 2) (m : Mirrored1 P) (j : Fin t),
    wlen ((enc (feedC a m)).2 j) = wlen ((L0.apply blankc (enc m) (some a)).2 j)

/-- **The repaired bridge**: `TEq`-level realization plus width *agreement*
gives the literal `RealizedFeed` that `CloseoutCoreEnc3.CoreResidual` needs —
with no width conservation and no room. -/
theorem realizedFeed_of_widthMatch {Q : Type} {t : ℕ}
    {enc : Mirrored1 P → Q × (Fin t → STape Γc)} {L0 : LocalStep (Fin 2) Q Γc t Kc}
    (h : RealizedFeedT enc L0) (hw : NAMED_feedWidthMatch enc L0) : RealizedFeed enc L0 := by
  intro a m
  refine Prod.ext (h a m).1 (funext fun j => ?_)
  refine eq_of_TEq_of_width ((h a m).2 j) ?_
  have hj := hw a m j
  rw [PalPeg.Local.LocalStep.apply_snd] at hj
  exact hj

/-- …and it really is a weakening: on a layout with room, `Enc5`'s
`NAMED_widthFeed` implies it. -/
theorem feedWidthMatch_of_widthFeed {Q : Type} {t : ℕ}
    {enc : Mirrored1 P → Q × (Fin t → STape Γc)} (L0 : LocalStep (Fin 2) Q Γc t Kc)
    (hroom : RoomOf enc) (hw : NAMED_widthFeed enc) : NAMED_feedWidthMatch enc L0 := by
  intro a m j
  rw [PalPeg.Local.LocalStep.apply_snd,
    PalPeg.CloseoutCoreEnc5.wlen_sweep blankc Kc ((enc m).2 j) _ _ (hroom m j).1
      (L0.disp_le (enc m).1 (some a) (fun j => readWin blankc Kc ((enc m).2 j)) j)
      (hroom m j).2]
  exact hw a m j

/-! ### The concrete growth: the queue rear stack of a cursor -/

theorem snoc_of_idle {lf lr : ℕ} {fr re : List (Fin 2)} (h : lr + 1 ≤ lf) (a : Fin 2) :
    RTQueue.snoc (⟨lf, fr, .idle, lr, re⟩ : RTQueue.Queue (Fin 2)) a
      = ⟨lf, fr, .idle, lr + 1, a :: re⟩ := by
  show RTQueue.check _ = _
  rw [RTQueue.check, if_pos (by simpa using h)]
  rfl

/-- **`LocalInputView.arrive` pushes one cell onto the rear stack tape**, so the
rear head advances by one: the concrete witness of `NAMED_feedGrow`. -/
theorem pos_queueTapes5_rear_snoc {lf lr : ℕ} {fr re : List (Fin 2)} (h : lr + 1 ≤ lf)
    (a : Fin 2) :
    pos (shift1 blankc (queueTapes5 (RTQueue.snoc (⟨lf, fr, .idle, lr, re⟩ :
        RTQueue.Queue (Fin 2)) a) 1))
      = pos (shift1 blankc (queueTapes5 (⟨lf, fr, .idle, lr, re⟩ :
          RTQueue.Queue (Fin 2)) 1)) + 1 := by
  rw [snoc_of_idle h]
  show pos (shift1 blankc (stackTape ((a :: re).map some)))
      = pos (shift1 blankc (stackTape (re.map some))) + 1
  rw [PalPeg.CloseoutCoreEnc3.pos_shift1, PalPeg.CloseoutCoreEnc3.pos_shift1,
    pos_stackTape, pos_stackTape]
  simp


/-! ## 4. The mode window, tape by tape

`CloseoutCoreEnc5.ModeWin` bundles the control update and *all* `t` tape
actions into one `next`.  Every concrete mode touches a handful of tapes and
leaves the rest alone, so the useful shape is the per-tape one. -/

/-- **The per-tape form of a mode window**: one control update, and one window
action per tape. -/
structure ModePerTape (Q : Type) (t : ℕ) (enc : Mirrored1 P → Q × (Fin t → STape Γc))
    (M : Steps P) (md : Mode) where
  ctlFun : Q → Q
  tapeFun : Fin t → Q → (Fin t → Window Γc Kc) → Window Γc Kc × ℤ
  disp : ∀ (j : Fin t) (q : Q) (ws : Fin t → Window Γc Kc), |(tapeFun j q ws).2| ≤ (Kc : ℤ)
  ctl : ∀ m : Mirrored1 P, m.vm.ctl.mode = md → ¬ Starved m.vm →
    (enc (stepOf M md m)).1 = ctlFun (enc m).1
  tape : ∀ (m : Mirrored1 P) (j : Fin t), m.vm.ctl.mode = md → ¬ Starved m.vm →
    TEq ((enc (stepOf M md m)).2 j)
      (sweep blankc Kc ((enc m).2 j)
        (tapeFun j (enc m).1 (fun j' => readWin blankc Kc ((enc m).2 j'))).1
        (tapeFun j (enc m).1 (fun j' => readWin blankc Kc ((enc m).2 j'))).2)

/-- …and it is a `ModeWin`, so `CloseoutCoreEnc5.ResidualTick` can be fed
tape by tape. -/
def modeWin_of_perTape {Q : Type} {t : ℕ} {enc : Mirrored1 P → Q × (Fin t → STape Γc)}
    {M : Steps P} {md : Mode} (R : ModePerTape Q t enc M md) : ModeWin Q t enc M md where
  next := fun q a ws => (R.ctlFun q, fun j => R.tapeFun j q ws)
  disp_le := fun q a ws j => R.disp j q ws
  ctl := R.ctl
  tape := R.tape

/-- **A mode that touches no tape closes outright.**  The identity window with
displacement `0` is a sweep (`CloseoutCoreEnc5.sweep_id_TEq`), so such a mode
needs only that its control update is a function of the encoded control. -/
def modeWin_of_tapeFixed {Q : Type} {t : ℕ} {enc : Mirrored1 P → Q × (Fin t → STape Γc)}
    {M : Steps P} {md : Mode} (ctlFun : Q → Q)
    (hctl : ∀ m : Mirrored1 P, m.vm.ctl.mode = md → ¬ Starved m.vm →
      (enc (stepOf M md m)).1 = ctlFun (enc m).1)
    (htape : ∀ (m : Mirrored1 P) (j : Fin t), m.vm.ctl.mode = md → ¬ Starved m.vm →
      (enc (stepOf M md m)).2 j = (enc m).2 j)
    (hmargin : ∀ (m : Mirrored1 P) (j : Fin t), Kc ≤ pos ((enc m).2 j)) :
    ModeWin Q t enc M md :=
  modeWin_of_perTape
    { ctlFun := ctlFun
      tapeFun := fun j q ws => (ws j, 0)
      disp := fun j q ws => by simp
      ctl := hctl
      tape := fun m j hmd hs => by
        rw [htape m j hmd hs]
        exact sweep_id_TEq ((enc m).2 j) (hmargin m j) }

/-! ### The three residuals this file is aimed at, per mode

`stepOf M md` is an arbitrary function of the abstract `Steps` record, so the
mode windows cannot be built without saying *which* concrete local step each
mode takes.  These are the shape hypotheses, with the concrete steps named. -/

/-- **Residual: the shape of a `.scan` tick.**  `LocalTick1` offers exactly two:
a matched comparison `matchVm` (two `length` units, `left` one cell left,
`right` one cell right, the radius and length mirrors pushed) or a
background-only tick `bgState` (a new chain tag and a new controller record).
The left mirror is untouched by both. -/
def NAMED_scanShape (M : Steps P) : Prop :=
  ∀ m : Mirrored1 P, m.vm.ctl.mode = .scan → ¬ Starved m.vm →
    ((∃ ch : ChainVM, (M.scan m).vm = PalPeg.LocalTick1.matchVm ch m.vm ∧
        (M.scan m).mirL = m.mirL) ∨
     (∃ (ch : ChainVM) (c : Control), (M.scan m).vm = PalPeg.LocalTick1.bgState m.vm.chain ch c m.vm ∧
        (M.scan m).mirL = m.mirL))

/-- **Residual: the matched half of a `.scan` tick, tape by tape.**  `matchVm`
is `scanStep2 ch (scanStep1 ·)`: `moveLeftV` on `left`, `moveRight` on `right`,
two `LocalCounter.push`es on the `length` role tape, and `pushAll` on the radius
and length mirrors — each a single radius-`Kc` window action (§1 for the pushes,
`CloseoutCoreEnc4.sweep_push`/`_pop` for the cursor stacks). -/
def NAMED_scanMatchWin {Q : Type} {t : ℕ} (enc : Mirrored1 P → Q × (Fin t → STape Γc))
    (M : Steps P) : Type := ModePerTape Q t enc M .scan

/-- **Residual: the background half.**  `bgState ch c` changes `chain` and `ctl`
only, so every cursor, counter, mirror and buffer tape is fixed and
`modeWin_of_tapeFixed` applies to them; what is left is the chain's own tape
block `CloseoutCoreEnc.chainTapes (rep ch)`, i.e. one window step of the local
chain. -/
def NAMED_scanBgChain {Q : Type} {t : ℕ} (enc : Mirrored1 P → Q × (Fin t → STape Γc))
    (M : Steps P) : Prop :=
  ∀ (m : Mirrored1 P) (j : Fin t) (ch : ChainVM) (c : Control),
    (M.scan m).vm = PalPeg.LocalTick1.bgState m.vm.chain ch c m.vm → (M.scan m).mirL = m.mirL →
      ∃ (w : Window Γc Kc) (d : ℤ), |d| ≤ (Kc : ℤ) ∧
        TEq ((enc (M.scan m)).2 j) (sweep blankc Kc ((enc m).2 j) w d)

/-- **Residual: the shape of an `.init` tick.**  `initVM` repositions `left` and
`center` onto the (already identical) right copy; in the local refinement that
is a `LocalInputView` reposition, one cell per tick, never a content copy. -/
def NAMED_initShape (M : Steps P) : Prop :=
  ∀ m : Mirrored1 P, m.vm.ctl.mode = .init → ¬ Starved m.vm →
    (M.init m).mirL = m.mirL ∧
    (M.init m).vm.center = m.vm.center ∧
    ((M.init m).vm.left = PalPeg.LocalInputView.moveRight m.vm.left ∨
      (M.init m).vm.left = PalPeg.LocalInputView.moveLeftV m.vm.left ∨
      (M.init m).vm.left = m.vm.left)

/-- **Residual: the `.init` window datum**, per tape. -/
def NAMED_initWin {Q : Type} {t : ℕ} (enc : Mirrored1 P → Q × (Fin t → STape Γc))
    (M : Steps P) : Type := ModePerTape Q t enc M .init

/-- **Residual: the shape of a `.replayStart` tick.**  `LocalReplayParked`'s
parked implementation: the counters are `LocalTick2.commitReplay`, the control
is installed wholesale, and `left` is *swapped* with the mirror — no content
moves, which is the whole point of the parked design. -/
def NAMED_replayStartShape (M : Steps P) : Prop :=
  ∀ m : Mirrored1 P, m.vm.ctl.mode = .replayStart → ¬ Starved m.vm →
    ∃ (entry : ℕ) (c : Control),
      M.replayStart m = PalPeg.LocalReplayParked.commitReplayParked entry c m

/-- **Residual: the `.replayStart` window datum**, per tape.  The cursor block
is a *permutation* of tapes (`left` ↔ `mirL`), which is not a window action at
all: the layout must either keep a "which copy is live" bit in the finite
control or pay the reposition.  That choice is what this residual records. -/
def NAMED_replayStartWin {Q : Type} {t : ℕ} (enc : Mirrored1 P → Q × (Fin t → STape Γc))
    (M : Steps P) : Type := ModePerTape Q t enc M .replayStart

/-- **Residual: the `.replayStart` restart family.**  `LocalTick2.commitRestart`
is the other commit in the same family (`restartVM entry`); its tape effect is
`resetSlots` on one counter and `LocalBuffers.resetL` on the DP buffer. -/
def NAMED_restartShape (M : Steps P) : Prop :=
  ∀ m : Mirrored1 P, m.vm.ctl.mode = .rewind → ¬ Starved m.vm →
    ∃ (entry : ℕ) (jL jW jD : Fin P) (bL : Bool),
      (M.rewind m).vm = PalPeg.LocalTick2.commitRestart entry jL jW jD bL m.vm ∧
        (M.rewind m).mirL = m.mirL

/-! ## 5. The verdict on `NAMED_encInjective7`, and the repaired cursor layout

`CloseoutCoreEnc4.inj_viewTapes7_upto` recovers `focus`, `back`, `near`, the
queue's `front` and its `rear` from the seven tapes, and `Enc5` leaves the
rotation state, the two counters and `gap` as the residual.  That residual is
not closable: the `reversing` constructor carries a list that **no** tape of
`queueTapes5` stores. -/

/-- **`NAMED_encInjective7` is false.**  Two views differing only in the `r`
field of a `reversing` rotation state have literally the same seven tapes:
`queueTapes5` lays out `front`, `rear`, the `reversing` `f`, the `f'` and the
`r'`, and nothing else.  So the seven-tape cursor of `Enc4` §6 is one stack
short, exactly as `Enc4`'s four-tape cursor was three short. -/
theorem not_NAMED_encInjective7 : ¬ NAMED_encInjective7 := by
  intro h
  have hv : ∀ i : ℕ,
      viewTapes7 ⟨[], none, [], ⟨0, [], .reversing 0 [] [] [0] [], 0, []⟩, false⟩ i
        = viewTapes7 ⟨[], none, [], ⟨0, [], .reversing 0 [] [] [1] [], 0, []⟩, false⟩ i := by
    intro i
    match i with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | 3 => rfl
    | 4 => rfl
    | 5 => rfl
    | (k + 6) => rfl
  have hEq := h _ _ hv
  simp only [InputView.mk.injEq, RTQueue.Queue.mk.injEq] at hEq
  have hr : (RTQueue.RotationState.reversing 0 [] [] [(0 : Fin 2)] [] :
      RTQueue.RotationState (Fin 2))
      = RTQueue.RotationState.reversing 0 [] [] [(1 : Fin 2)] [] := hEq.2.2.2.1.2.2.1
  simp at hr

/-! ### The repaired cursor: six queue stacks -/

/-- **The six stacks the rotation state actually uses**: `front`, `rear`, and
the `reversing` quadruple `f`, `f'`, `r`, `r'` (with `appending` reusing `f'`
and `r'`, and `done` reusing the last).  `queueTapes5` omitted `r`. -/
def queueTapes6 (q : RTQueue.Queue (Fin 2)) : ℕ → STape Γc
  | 0 => stackTape (q.front.map some)
  | 1 => stackTape (q.rear.map some)
  | 2 => match q.state with
      | .reversing _ f _ _ _ => stackTape (f.map some)
      | _ => stackTape []
  | 3 => match q.state with
      | .reversing _ _ f' _ _ => stackTape (f'.map some)
      | .appending _ f' _ => stackTape (f'.map some)
      | _ => stackTape []
  | 4 => match q.state with
      | .reversing _ _ _ r _ => stackTape (r.map some)
      | _ => stackTape []
  | _ => match q.state with
      | .reversing _ _ _ _ r' => stackTape (r'.map some)
      | .appending _ _ r' => stackTape (r'.map some)
      | .done f => stackTape (f.map some)
      | .idle => stackTape []

/-- The repaired cursor: `back`+`focus`, `near`, and the six queue stacks. -/
def viewTapes8 (v : InputView) : ℕ → STape Γc
  | 0 => shift1 blankc (stackTape (v.focus :: v.back))
  | 1 => shift1 blankc (stackTape v.near)
  | (n + 2) => shift1 blankc (queueTapes6 v.far n)

/-- …so the cursor costs eight tapes, one more than `CloseoutCoreEnc4.tView7`. -/
def tView8 : ℕ := 8

theorem tView7_lt_tView8 : PalPeg.CloseoutCoreEnc4.tView7 < tView8 := by decide

theorem margin_viewTapes8 (v : InputView) (i : ℕ) : Kc ≤ pos (viewTapes8 v i) := by
  match i with
  | 0 => exact PalPeg.CloseoutCoreEnc3.margin_shift1 _ _
  | 1 => exact PalPeg.CloseoutCoreEnc3.margin_shift1 _ _
  | (n + 2) => exact PalPeg.CloseoutCoreEnc3.margin_shift1 _ _

/-! ### The finite-control residue, and injectivity -/

/-- The rotation phase: finite control. -/
def tagOf : RTQueue.RotationState (Fin 2) → ℕ
  | .idle => 0
  | .reversing _ _ _ _ _ => 1
  | .appending _ _ _ => 2
  | .done _ => 3

/-- The rotation's validity counter: one unary counter tape. -/
def okOf : RTQueue.RotationState (Fin 2) → ℕ
  | .reversing ok _ _ _ _ => ok
  | .appending ok _ _ => ok
  | _ => 0

theorem stack8_eq {l l' : List (Option (Fin 2))}
    (h : shift1 blankc (stackTape l) = shift1 blankc (stackTape l')) : l = l' :=
  stackTape_inj (shift1_inj blankc h)

theorem mapsome_eq {l l' : List (Fin 2)}
    (h : shift1 blankc (stackTape (l.map some)) = shift1 blankc (stackTape (l'.map some))) :
    l = l' := map_some_inj (stack8_eq h)

theorem mapsome_iff {l l' : List (Fin 2)} :
    (shift1 blankc (stackTape (l.map some)) = shift1 blankc (stackTape (l'.map some)))
      ↔ l = l' :=
  ⟨mapsome_eq, fun h => by rw [h]⟩

/-- **Injectivity of the repaired cursor, up to the finite control.**  The eight
tapes plus `gap`, the two length counters, the rotation phase tag and its
validity counter determine the view — and every one of those five residues is
finite control or a unary counter, not a cursor tape.  This is the statement
`not_NAMED_encInjective7` shows the seven-tape layout cannot have. -/
theorem injective_viewTapes8 (v v' : InputView)
    (h : ∀ i : ℕ, viewTapes8 v i = viewTapes8 v' i)
    (hgap : v.gap = v'.gap) (hlf : v.far.lenf = v'.far.lenf) (hlr : v.far.lenr = v'.far.lenr)
    (htag : tagOf v.far.state = tagOf v'.far.state)
    (hok : okOf v.far.state = okOf v'.far.state) : v = v' := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have h5 := h 5
  have h6 := h 6
  have h7 := h 7
  obtain ⟨b, fo, n, far, g⟩ := v
  obtain ⟨b', fo', n', far', g'⟩ := v'
  obtain ⟨lf, fr, st, lr, re⟩ := far
  obtain ⟨lf', fr', st', lr', re'⟩ := far'
  have hfb : fo :: b = fo' :: b' := stack8_eq h0
  have hnear : n = n' := stack8_eq h1
  have hfront : fr = fr' := mapsome_eq h2
  have hrear : re = re' := mapsome_eq h3
  have hst : st = st' := by
    cases st <;> cases st' <;>
      simp_all [tagOf, okOf, queueTapes6, viewTapes8, mapsome_iff]
  simp_all

/-- **The residue, named.**  What the repaired layout still asks of the finite
control and the counter bank: the `gap` bit, the two queue length counters, the
rotation phase tag and its validity counter. -/
def NAMED_farControl {Q : Type} {t : ℕ}
    (enc : Mirrored1 P → Q × (Fin t → STape Γc)) (viewOf : Q → InputView) : Prop :=
  ∀ m : Mirrored1 P,
    (viewOf (enc m).1).gap = m.vm.left.gap ∧
    (viewOf (enc m).1).far.lenf = m.vm.left.far.lenf ∧
    (viewOf (enc m).1).far.lenr = m.vm.left.far.lenr ∧
    tagOf (viewOf (enc m).1).far.state = tagOf m.vm.left.far.state ∧
    okOf (viewOf (enc m).1).far.state = okOf m.vm.left.far.state

end PalPeg.CloseoutCoreEnc7

#print axioms PalPeg.CloseoutCoreEnc7.applyAction_right_TEq_sweep
#print axioms PalPeg.CloseoutCoreEnc7.canRight_right_iff
#print axioms PalPeg.CloseoutCoreEnc7.canRight_and_lookahead
#print axioms PalPeg.CloseoutCoreEnc7.four_iff_three
#print axioms PalPeg.CloseoutCoreEnc7.starved_iff
#print axioms PalPeg.CloseoutCoreEnc7.not_starved_iff
#print axioms PalPeg.CloseoutCoreEnc7.gap_left_iterate
#print axioms PalPeg.CloseoutCoreEnc7.canRight_or_canRight_left
#print axioms PalPeg.CloseoutCoreEnc7.canRight_absR_of_parity
#print axioms PalPeg.CloseoutCoreEnc7.starvedWindow_of_read
#print axioms PalPeg.CloseoutCoreEnc7.pendTape_append
#print axioms PalPeg.CloseoutCoreEnc7.pendTape_append_TEq_sweep
#print axioms PalPeg.CloseoutCoreEnc7.not_room_pendTape
#print axioms PalPeg.CloseoutCoreEnc7.wlen_pendTape_append
#print axioms PalPeg.CloseoutCoreEnc7.not_widthFeed_of_feedGrow
#print axioms PalPeg.CloseoutCoreEnc7.realizedFeed_of_widthMatch
#print axioms PalPeg.CloseoutCoreEnc7.feedWidthMatch_of_widthFeed
#print axioms PalPeg.CloseoutCoreEnc7.snoc_of_idle
#print axioms PalPeg.CloseoutCoreEnc7.pos_queueTapes5_rear_snoc
#print axioms PalPeg.CloseoutCoreEnc7.modeWin_of_perTape
#print axioms PalPeg.CloseoutCoreEnc7.modeWin_of_tapeFixed
#print axioms PalPeg.CloseoutCoreEnc7.not_NAMED_encInjective7
#print axioms PalPeg.CloseoutCoreEnc7.tView7_lt_tView8
#print axioms PalPeg.CloseoutCoreEnc7.margin_viewTapes8
#print axioms PalPeg.CloseoutCoreEnc7.injective_viewTapes8
