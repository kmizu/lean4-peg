import PalPeg.CloseoutCoreEnc5
import PalPeg.CloseoutCoreAgree

/-!
# Closeout: the phase modes as window functions on the padded layout

`CloseoutCoreEnc5` reduces the tick half of the core's `LocalStep` to ten
`NAMED_modeWin` obligations (one per `GalilScaffoldController.Mode`), a
starvation test, and two width-conservation residuals, on a layout that has
room on both sides — which `CloseoutCoreEnc5.padTapes` is, and
`CloseoutCoreEnc3.encTapes1` provably is *not*
(`CloseoutCoreEnc5.not_room_shift1`, `wlen_viewTapes7`).

This file builds the machinery that turns a *per-state* window datum into a
`ModeWin`, closes the three identity modes of the word-free `Steps P` of
`CloseoutCoreAgree.SL` outright, and reduces the seven phase modes to one
residual each, with its exact type.  It builds no new dynamics and proves no
new fact about the Galil machine, so

**無条件 PAL ∈ PEG は未完.**

## What is established

* **§1 (`ModePt` and determinacy).**  `ModePt` is the *pointwise* mode datum:
  for each state a control value and, per tape, a window and a displacement
  that reproduce the mode's step up to `TEq`.  It is what
  `CloseoutCoreEnc4.sweep_of_winRealizes` hands back from a `WinRealizes`
  (`modePt_of_winRealizes`), i.e. what the translation lemmas
  `CloseoutCoreEnc.winRealizes_of_tapeLocal`,
  `CloseoutCoreEnc2.winRealizes_stepLocal_phys`,
  `CloseoutCoreEnc3.winRealizes_push`/`winRealizes_pop` produce, tape by tape.
  `DetWin` is the one thing a `ModePt` still lacks and a `ModeWin` demands:
  that the datum be a *function of the finite control and the windows*.
  `modeWin_of_det` performs the promotion; the displacement bound comes for
  free, by clamping (`clampD`), so `DetWin` carries no side condition.

  This isolates the real content of `NAMED_modeWin`: not the existence of a
  window rewrite per tape (that is `WinRealizes`, already available) but the
  *determinacy* of the branch each mode takes — `RemPosL`, `AtLeftL`,
  `AtEndL`, `MarkSetL`, `AtFirstL`, `OnLetterL` must all be window reads.

* **§2 (the identity modes, closed).**  A mode whose step is the identity gets
  its `ModeWin` unconditionally, from `CloseoutCoreEnc5.sweep_id_TEq`
  (`modeWin_id`).  `CloseoutCoreAgree.SL` has `init = scan = replayStart = id`,
  so `modeWin_SL_init`, `modeWin_SL_scan`, `modeWin_SL_replayStart` are
  **proved**, on any layout with a left margin.  Three of the ten fields of
  `CloseoutCoreEnc5.ResidualTick` are therefore no longer residual.

* **§3 (control-only steps).**  `encTapes_ctl` / `padTapes_ctl`: the layout
  reads no field of `Control`, so a step that only rewrites `ctl` leaves every
  tape *literally* unchanged.  `modeWin_of_ctlOnly` then needs only the control
  function, and `widthMode_of_ctlOnly` gives its width conservation for free.
  This is exactly the shape of the `shift`-done branch
  (`CloseoutCoreAgree.shiftStepW`, the `¬ RemPosL` case), whose only content is
  `refreshL` — a read of the R head (`CloseoutCoreAgree.onLetterVM_iff`).

* **§4 (width conservation, per mode).**  `widthTick_of_modes` reduces
  `CloseoutCoreEnc5.NAMED_widthTick` for `tickC M` to one `WidthMode`
  obligation per mode: the starved branch is a stutter, and the stepping branch
  is the mode's own.  `widthMode_id` and `widthMode_of_ctlOnly` discharge it for
  the identity and control-only modes.  Width conservation cannot be derived
  from a `ModeWin`: `TEq` does not see the stored width, which is the whole
  point of `CloseoutCoreEnc5` §1.

* **§5 (the padded layout, concretely).**  `encPad` is
  `CloseoutCoreEnc5.padTapes` with the concrete control projection `qOfL`;
  `roomOf_encPad` and `margin_encPad` are unconditional.  `modeOf_encPad` is
  `rfl`.

* **§6 (the residual bundle).**  `residualTick_SL` assembles
  `CloseoutCoreEnc5.ResidualTick` for `CloseoutCoreAgree.SL` on `encPad` from
  the starvation test plus the **seven** phase residuals, and
  `coreLocal_SL` chains it through `CloseoutCoreEnc5.coreLocal_of_residual` to
  a `CloseoutCoreAudit.CoreLocal` term.  `widthTick_SL` does the same for the
  width residual.

* **§7 (the fpp quantum).**  `fppQuantum_of_det` builds
  `CloseoutCoreEnc5.NAMED_fppQuantum''` from a `.fpp` phase residual whose
  per-tape datum is, on every tape, either the identity window or a zero
  displacement — the window shape of *one* `GalilDpCode` instruction on the
  active bank of `LocalBuffers.Buffered` (`LocalBuffers.abs_stepL`).

## The residuals (NAMED)

Per phase mode `md ∈ {shift, copy, home, fpp, markEnd, choose, rewind}`:

```
NAMED_phaseWin enc M md : Type :=
  Σ' Pt : ModePt Q t enc M md, DetWin Q t enc M md Pt
```

plus, per mode, `WidthMode enc M md`, and globally
`CloseoutCoreEnc5.NAMED_starvedWindow enc` and the arrival datum
`CloseoutCoreEnc5.FeedWin`.  Nothing here proves any of those for the phase
steps of `SL`; they are restated with their exact types and wired to the
closeout chain.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace PalPeg.CloseoutCoreEnc6

open PalPeg PalPeg.Program
open PalPeg.Local (Window idx idx_val pos rd toList sweep pos_sweep rd_sweep readWin
  readWin_eq LocalStep)
open PalPeg.GalilScaffoldChainInputSupply (ChainVM)
open PalPeg.GalilScaffoldController (Control Mode)
open PalPeg.LocalChain (ChainL)
open PalPeg.LocalReplayParked (Mirrored1)
open PalPeg.LocalSysConcrete (Steps Starved stepOf tickC feedC)
open PalPeg.LocalTrackingLatch (LX)
open PalPeg.CloseoutCoreAudit (CoreLocal)
open PalPeg.CloseoutCoreStep (Γc blankc tView nViews tL QL qOfL)
open PalPeg.CloseoutCoreEnc (Kc WinRealizes encTapes QChain tChain qChainOf)
open PalPeg.CloseoutCoreEnc3 (encTapes1)
open PalPeg.CloseoutCoreEnc4 (TEq WinStep sweep_of_winRealizes)
open PalPeg.CloseoutCoreEnc5 (wlen padR padTapes ModeWin ModeOf StarvedWin FeedWin
  ResidualTick NAMED_widthTick NAMED_widthFeed NAMED_starvedWindow NAMED_fppQuantum''
  RoomOf sweep_id_TEq margin_padTapes room_padTapes roomOf_padTapes
  winStep_of_residualTick coreLocal_of_residual)
open PalPeg.CloseoutCoreAgree (SL)

variable {P : ℕ}

/-! ## 1. The pointwise mode datum, and the determinacy it is missing -/

/-- **The pointwise window datum of one mode.**  Exactly
`CloseoutCoreEnc5.ModeWin`, except that the datum is allowed to depend on the
*state* rather than only on the finite control and the windows.  This is what
the translation lemmas of `CloseoutCoreEnc`/`Enc2`/`Enc3` produce: they work
tape by tape, on a given pair of states. -/
structure ModePt (Q : Type) (t : ℕ) (enc : Mirrored1 P → Q × (Fin t → STape Γc))
    (M : Steps P) (md : Mode) where
  win : Mirrored1 P → Q × (Fin t → Window Γc Kc × ℤ)
  disp : ∀ (m : Mirrored1 P) (j : Fin t), |((win m).2 j).2| ≤ (Kc : ℤ)
  ctl : ∀ m : Mirrored1 P, m.vm.ctl.mode = md → ¬ Starved m.vm →
    (enc (stepOf M md m)).1 = (win m).1
  tape : ∀ (m : Mirrored1 P) (j : Fin t), m.vm.ctl.mode = md → ¬ Starved m.vm →
    TEq ((enc (stepOf M md m)).2 j)
      (sweep blankc Kc ((enc m).2 j) ((win m).2 j).1 ((win m).2 j).2)

/-- **Determinacy: the datum is a window function.**  The one gap between
`ModePt` and `CloseoutCoreEnc5.ModeWin`.  Semantically: the branch the mode
takes, and the cells it writes, are computed from the finite control and the
`2 * Kc + 1` cells under each head — no side read of the state. -/
structure DetWin (Q : Type) (t : ℕ) (enc : Mirrored1 P → Q × (Fin t → STape Γc))
    (M : Steps P) (md : Mode) (Pt : ModePt Q t enc M md) where
  nx : Q → Option (Fin 2) → (Fin t → Window Γc Kc) → Q × (Fin t → Window Γc Kc × ℤ)
  spec : ∀ m : Mirrored1 P, m.vm.ctl.mode = md → ¬ Starved m.vm →
    nx (enc m).1 none (fun j => readWin blankc Kc ((enc m).2 j)) = Pt.win m

/-- Clamp a displacement into the window budget, keeping the window. -/
noncomputable def clampD (p : Window Γc Kc × ℤ) : Window Γc Kc × ℤ :=
  if |p.2| ≤ (Kc : ℤ) then p else (p.1, 0)

theorem clampD_eq {p : Window Γc Kc × ℤ} (h : |p.2| ≤ (Kc : ℤ)) : clampD p = p := by
  rw [clampD, if_pos h]

theorem abs_clampD (p : Window Γc Kc × ℤ) : |(clampD p).2| ≤ (Kc : ℤ) := by
  rw [clampD]
  by_cases h : |p.2| ≤ (Kc : ℤ)
  · rw [if_pos h]; exact h
  · rw [if_neg h]; simp

@[simp] theorem clampD_fst (p : Window Γc Kc × ℤ) : (clampD p).1 = p.1 := by
  rw [clampD]
  by_cases h : |p.2| ≤ (Kc : ℤ)
  · rw [if_pos h]
  · rw [if_neg h]

/-- **The promotion.**  A pointwise datum plus determinacy is a `ModeWin`.  The
global displacement bound `ModeWin.disp_le` — which a `DetWin` does not carry,
since `nx` is unconstrained off the states it is specified on — is supplied by
`clampD`, which is the identity where `ModePt.disp` applies. -/
noncomputable def modeWin_of_det {Q : Type} {t : ℕ}
    {enc : Mirrored1 P → Q × (Fin t → STape Γc)} {M : Steps P} {md : Mode}
    (Pt : ModePt Q t enc M md) (D : DetWin Q t enc M md Pt) : ModeWin Q t enc M md where
  next := fun q a ws => ((D.nx q a ws).1, fun j => clampD ((D.nx q a ws).2 j))
  disp_le := fun q a ws j => abs_clampD _
  ctl := fun m hmd hs => by
    have h := D.spec m hmd hs
    show (enc (stepOf M md m)).1
        = (D.nx (enc m).1 none (fun j => readWin blankc Kc ((enc m).2 j))).1
    rw [h]
    exact Pt.ctl m hmd hs
  tape := fun m j hmd hs => by
    have h := D.spec m hmd hs
    show TEq ((enc (stepOf M md m)).2 j)
      (sweep blankc Kc ((enc m).2 j)
        (clampD ((D.nx (enc m).1 none (fun j' => readWin blankc Kc ((enc m).2 j'))).2 j)).1
        (clampD ((D.nx (enc m).1 none (fun j' => readWin blankc Kc ((enc m).2 j'))).2 j)).2)
    rw [h, clampD_eq (Pt.disp m j)]
    exact Pt.tape m j hmd hs

/-- **`NAMED_modeWin`, factored.**  The residual of one mode, as the pair
"pointwise datum + determinacy". -/
def NAMED_phaseWin {Q : Type} {t : ℕ} (enc : Mirrored1 P → Q × (Fin t → STape Γc))
    (M : Steps P) (md : Mode) : Type :=
  Σ' Pt : ModePt Q t enc M md, DetWin Q t enc M md Pt

noncomputable def modeWin_of_phaseWin {Q : Type} {t : ℕ}
    {enc : Mirrored1 P → Q × (Fin t → STape Γc)} {M : Steps P} {md : Mode}
    (R : NAMED_phaseWin enc M md) : ModeWin Q t enc M md :=
  modeWin_of_det R.1 R.2

/-- **From per-tape window rewrites to a pointwise datum.**  This is the form
in which `CloseoutCoreEnc.winRealizes_of_tapeLocal`,
`CloseoutCoreEnc2.winRealizes_stepLocal_phys` and
`CloseoutCoreEnc3.winRealizes_push`/`winRealizes_pop` are available: one
`WinRealizes` per tape, plus the control agreement.  The margin is the
left-edge condition of `CloseoutCoreEnc4.sweep_of_winRealizes`. -/
noncomputable def modePt_of_winRealizes {Q : Type} {t : ℕ}
    {enc : Mirrored1 P → Q × (Fin t → STape Γc)} {M : Steps P} {md : Mode}
    (hmargin : ∀ (m : Mirrored1 P) (j : Fin t), Kc ≤ pos ((enc m).2 j))
    (hwin : ∀ (m : Mirrored1 P) (j : Fin t), m.vm.ctl.mode = md → ¬ Starved m.vm →
      WinRealizes ((enc m).2 j) ((enc (stepOf M md m)).2 j)) :
    ModePt Q t enc M md := by
  classical
  refine
    { win := fun m =>
        ((enc (stepOf M md m)).1, fun j =>
          if h : m.vm.ctl.mode = md ∧ ¬ Starved m.vm then
            let e := sweep_of_winRealizes (hmargin m j) (hwin m j h.1 h.2)
            (e.choose, e.choose_spec.choose)
          else (readWin blankc Kc ((enc m).2 j), 0)
          )
      disp := ?_, ctl := ?_, tape := ?_ }
  · intro m j
    by_cases h : m.vm.ctl.mode = md ∧ ¬ Starved m.vm
    · simp only [dif_pos h]
      exact (sweep_of_winRealizes (hmargin m j) (hwin m j h.1 h.2)).choose_spec.choose_spec.1
    · simp only [dif_neg h]
      simp
  · intro m hmd hs; rfl
  · intro m j hmd hs
    simp only [dif_pos (⟨hmd, hs⟩ : m.vm.ctl.mode = md ∧ ¬ Starved m.vm)]
    exact (sweep_of_winRealizes (hmargin m j) (hwin m j hmd hs)).choose_spec.choose_spec.2

/-! ## 2. The identity modes, closed -/

/-- **A mode that stands still needs no residual.**  The identity window at
displacement `0` is a `sweep` (`CloseoutCoreEnc5.sweep_id_TEq`), and it is
manifestly a window function, so both halves are discharged at once. -/
noncomputable def modeWin_id {Q : Type} {t : ℕ}
    {enc : Mirrored1 P → Q × (Fin t → STape Γc)} {M : Steps P} {md : Mode}
    (hstep : ∀ m : Mirrored1 P, stepOf M md m = m)
    (hmargin : ∀ (m : Mirrored1 P) (j : Fin t), Kc ≤ pos ((enc m).2 j)) :
    ModeWin Q t enc M md where
  next := fun q a ws => (q, fun j => (ws j, 0))
  disp_le := fun q a ws j => by simp
  ctl := fun m hmd hs => by rw [hstep m]
  tape := fun m j hmd hs => by
    rw [hstep m]
    exact sweep_id_TEq ((enc m).2 j) (hmargin m j)

theorem stepOf_SL_init (qq : ℕ) (first : Fin 9) (m : Mirrored1 P) :
    stepOf (SL (P := P) qq first) .init m = m := rfl

theorem stepOf_SL_scan (qq : ℕ) (first : Fin 9) (m : Mirrored1 P) :
    stepOf (SL (P := P) qq first) .scan m = m := rfl

theorem stepOf_SL_replayStart (qq : ℕ) (first : Fin 9) (m : Mirrored1 P) :
    stepOf (SL (P := P) qq first) .replayStart m = m := rfl

noncomputable def modeWin_SL_init {Q : Type} {t : ℕ}
    {enc : Mirrored1 P → Q × (Fin t → STape Γc)} (qq : ℕ) (first : Fin 9)
    (hmargin : ∀ (m : Mirrored1 P) (j : Fin t), Kc ≤ pos ((enc m).2 j)) :
    ModeWin Q t enc (SL qq first) .init :=
  modeWin_id (stepOf_SL_init qq first) hmargin

noncomputable def modeWin_SL_scan {Q : Type} {t : ℕ}
    {enc : Mirrored1 P → Q × (Fin t → STape Γc)} (qq : ℕ) (first : Fin 9)
    (hmargin : ∀ (m : Mirrored1 P) (j : Fin t), Kc ≤ pos ((enc m).2 j)) :
    ModeWin Q t enc (SL qq first) .scan :=
  modeWin_id (stepOf_SL_scan qq first) hmargin

noncomputable def modeWin_SL_replayStart {Q : Type} {t : ℕ}
    {enc : Mirrored1 P → Q × (Fin t → STape Γc)} (qq : ℕ) (first : Fin 9)
    (hmargin : ∀ (m : Mirrored1 P) (j : Fin t), Kc ≤ pos ((enc m).2 j)) :
    ModeWin Q t enc (SL qq first) .replayStart :=
  modeWin_id (stepOf_SL_replayStart qq first) hmargin

/-! ## 3. Control-only steps: the layout is blind to `Control` -/

/-- **The layout reads no field of `Control`.**  `encTapes` dispatches on the
tape index and reads the cursors, the counter bank, the mirror banks, the two
double buffers and the chain; the controller record is finite control only.  So
rewriting `ctl` moves no tape at all. -/
theorem encTapes_ctl (rep : ChainVM → ChainL) (m : Mirrored1 P) (c : Control) (i : ℕ) :
    encTapes rep ⟨{ m.vm with ctl := c }, m.mirL⟩ i = encTapes rep m i := rfl

theorem encTapes1_ctl (rep : ChainVM → ChainL) (m : Mirrored1 P) (c : Control) (i : ℕ) :
    encTapes1 rep ⟨{ m.vm with ctl := c }, m.mirL⟩ i = encTapes1 rep m i := rfl

theorem padTapes_ctl (rep : ChainVM → ChainL) (m : Mirrored1 P) (c : Control) (i : ℕ) :
    padTapes rep ⟨{ m.vm with ctl := c }, m.mirL⟩ i = padTapes rep m i := rfl

/-- **A mode whose step only rewrites the controller.**  Then every tape datum
is the identity window, and the only content is the new control value — which
must still be a window function (`nq`), because the refresh a phase exit
performs reads the heads (`CloseoutCoreAgree.refreshL`, via
`onLetterVM_iff`). -/
noncomputable def modeWin_of_ctlOnly {Q : Type} {t : ℕ}
    {enc : Mirrored1 P → Q × (Fin t → STape Γc)} {M : Steps P} {md : Mode}
    (nq : Q → (Fin t → Window Γc Kc) → Q)
    (hctl : ∀ m : Mirrored1 P, m.vm.ctl.mode = md → ¬ Starved m.vm →
      (enc (stepOf M md m)).1
        = nq (enc m).1 (fun j => readWin blankc Kc ((enc m).2 j)))
    (htape : ∀ (m : Mirrored1 P) (j : Fin t), m.vm.ctl.mode = md → ¬ Starved m.vm →
      (enc (stepOf M md m)).2 j = (enc m).2 j)
    (hmargin : ∀ (m : Mirrored1 P) (j : Fin t), Kc ≤ pos ((enc m).2 j)) :
    ModeWin Q t enc M md where
  next := fun q a ws => (nq q ws, fun j => (ws j, 0))
  disp_le := fun q a ws j => by simp
  ctl := hctl
  tape := fun m j hmd hs => by
    rw [htape m j hmd hs]
    exact sweep_id_TEq ((enc m).2 j) (hmargin m j)

/-! ## 4. Width conservation, per mode -/

/-- **The per-mode width obligation.**  `CloseoutCoreEnc5.wlen_sweep` says one
realized `LocalStep` cannot change the stored width, so this is forced; and it
does *not* follow from a `ModeWin`, because `TEq` does not see the width
(`CloseoutCoreEnc5` §1). -/
def WidthMode {Q : Type} {t : ℕ} (enc : Mirrored1 P → Q × (Fin t → STape Γc))
    (M : Steps P) (md : Mode) : Prop :=
  ∀ (m : Mirrored1 P) (j : Fin t), m.vm.ctl.mode = md → ¬ Starved m.vm →
    wlen ((enc (stepOf M md m)).2 j) = wlen ((enc m).2 j)

/-- **`NAMED_widthTick` from the ten per-mode obligations.**  The starved
branch is a stutter. -/
theorem widthTick_of_modes {Q : Type} {t : ℕ}
    {enc : Mirrored1 P → Q × (Fin t → STape Γc)} {M : Steps P}
    (h : ∀ md : Mode, WidthMode enc M md) : NAMED_widthTick enc (tickC M) := by
  classical
  intro m j
  by_cases hs : Starved m.vm
  · rw [PalPeg.LocalSysConcrete.tickC_starved M hs]
  · rw [PalPeg.LocalSysConcrete.tickC_step M hs]
    exact h m.vm.ctl.mode m j rfl hs

theorem widthMode_id {Q : Type} {t : ℕ} {enc : Mirrored1 P → Q × (Fin t → STape Γc)}
    {M : Steps P} {md : Mode} (hstep : ∀ m : Mirrored1 P, stepOf M md m = m) :
    WidthMode enc M md := fun m j _ _ => by rw [hstep m]

theorem widthMode_of_ctlOnly {Q : Type} {t : ℕ}
    {enc : Mirrored1 P → Q × (Fin t → STape Γc)} {M : Steps P} {md : Mode}
    (htape : ∀ (m : Mirrored1 P) (j : Fin t), m.vm.ctl.mode = md → ¬ Starved m.vm →
      (enc (stepOf M md m)).2 j = (enc m).2 j) :
    WidthMode enc M md := fun m j hmd hs => by rw [htape m j hmd hs]

/-! ## 5. The padded layout, concretely -/

/-- **The core's layout with both reservoirs**, with the concrete finite
control of `CloseoutCoreStep`.  Unlike `CloseoutCoreEnc4.enc1` it satisfies the
room condition on every tape (`roomOf_encPad`). -/
noncomputable def encPad (delay Lp Lf : ℕ) (rep : ChainVM → ChainL) (m : Mirrored1 P) :
    QL delay Lp Lf P QChain × (Fin (tL P tChain) → STape Γc) :=
  (qOfL delay Lp Lf (fun c => qChainOf (rep c)) m, fun j => padTapes rep m j.val)

theorem margin_encPad (delay Lp Lf : ℕ) (rep : ChainVM → ChainL) (m : Mirrored1 P)
    (j : Fin (tL P tChain)) : Kc ≤ pos ((encPad delay Lp Lf rep m).2 j) :=
  margin_padTapes rep m j.val

theorem roomOf_encPad (delay Lp Lf : ℕ) (rep : ChainVM → ChainL) :
    RoomOf (P := P) (encPad delay Lp Lf rep) :=
  roomOf_padTapes (qOf := qOfL delay Lp Lf (fun c => qChainOf (rep c))) rep

/-- The mode projection of the concrete control, as for `CloseoutCoreEnc5`. -/
def modeOf_encPad (delay Lp Lf : ℕ) (rep : ChainVM → ChainL) :
    ModeOf (P := P) (QL delay Lp Lf P QChain) (tL P tChain) (encPad delay Lp Lf rep) where
  modeOf := fun q => q.1.val.mode
  spec := fun m => rfl

/-! ## 6. The residual bundle for the word-free `SL` -/

/-- **The seven phase residuals**, on the padded layout, with their exact
types.  `init`, `scan` and `replayStart` do not appear: `SL` makes them the
identity, and §2 closes them. -/
structure NAMED_phaseSeven (delay Lp Lf : ℕ) (rep : ChainVM → ChainL)
    (qq : ℕ) (first : Fin 9) : Type where
  shift : NAMED_phaseWin (P := P) (encPad delay Lp Lf rep) (SL qq first) .shift
  copy : NAMED_phaseWin (P := P) (encPad delay Lp Lf rep) (SL qq first) .copy
  home : NAMED_phaseWin (P := P) (encPad delay Lp Lf rep) (SL qq first) .home
  fpp : NAMED_phaseWin (P := P) (encPad delay Lp Lf rep) (SL qq first) .fpp
  markEnd : NAMED_phaseWin (P := P) (encPad delay Lp Lf rep) (SL qq first) .markEnd
  choose : NAMED_phaseWin (P := P) (encPad delay Lp Lf rep) (SL qq first) .choose
  rewind : NAMED_phaseWin (P := P) (encPad delay Lp Lf rep) (SL qq first) .rewind

/-- **The tick bundle of `CloseoutCoreEnc5`, from the seven.** -/
noncomputable def residualTick_SL {delay Lp Lf : ℕ} {rep : ChainVM → ChainL}
    {qq : ℕ} {first : Fin 9}
    (S : NAMED_starvedWindow (P := P) (encPad delay Lp Lf rep))
    (R : NAMED_phaseSeven (P := P) delay Lp Lf rep qq first) :
    ResidualTick (QL delay Lp Lf P QChain) (tL P tChain) (encPad delay Lp Lf rep)
      (SL qq first) where
  D := modeOf_encPad delay Lp Lf rep
  S := S
  init := modeWin_SL_init qq first (margin_encPad delay Lp Lf rep)
  scan := modeWin_SL_scan qq first (margin_encPad delay Lp Lf rep)
  shift := modeWin_of_phaseWin R.shift
  copy := modeWin_of_phaseWin R.copy
  home := modeWin_of_phaseWin R.home
  fpp := modeWin_of_phaseWin R.fpp
  markEnd := modeWin_of_phaseWin R.markEnd
  choose := modeWin_of_phaseWin R.choose
  rewind := modeWin_of_phaseWin R.rewind
  replayStart := modeWin_SL_replayStart qq first (margin_encPad delay Lp Lf rep)
  hmargin := margin_encPad delay Lp Lf rep

/-- **The width residual for `SL`**, from the seven phase widths: the three
identity modes are free. -/
theorem widthTick_SL {delay Lp Lf : ℕ} {rep : ChainVM → ChainL} {qq : ℕ} {first : Fin 9}
    (hshift : WidthMode (P := P) (encPad delay Lp Lf rep) (SL qq first) .shift)
    (hcopy : WidthMode (P := P) (encPad delay Lp Lf rep) (SL qq first) .copy)
    (hhome : WidthMode (P := P) (encPad delay Lp Lf rep) (SL qq first) .home)
    (hfpp : WidthMode (P := P) (encPad delay Lp Lf rep) (SL qq first) .fpp)
    (hmarkEnd : WidthMode (P := P) (encPad delay Lp Lf rep) (SL qq first) .markEnd)
    (hchoose : WidthMode (P := P) (encPad delay Lp Lf rep) (SL qq first) .choose)
    (hrewind : WidthMode (P := P) (encPad delay Lp Lf rep) (SL qq first) .rewind) :
    NAMED_widthTick (P := P) (encPad delay Lp Lf rep) (tickC (SL qq first)) := by
  refine widthTick_of_modes (fun md => ?_)
  match md with
  | .init => exact widthMode_id (stepOf_SL_init qq first)
  | .scan => exact widthMode_id (stepOf_SL_scan qq first)
  | .shift => exact hshift
  | .copy => exact hcopy
  | .home => exact hhome
  | .fpp => exact hfpp
  | .markEnd => exact hmarkEnd
  | .choose => exact hchoose
  | .rewind => exact hrewind
  | .replayStart => exact widthMode_id (stepOf_SL_replayStart qq first)

/-- **The `CoreLocal` term for the padded layout and the word-free `SL`.**  The
inputs are exactly the residuals left: the starvation window test, the seven
phase windows, the seven phase widths, the arrival datum against the *same*
window function, the arrival width, and the three finite-control readouts with
the initial configuration. -/
noncomputable def coreLocal_SL {delay Lp Lf : ℕ} {rep : ChainVM → ChainL}
    {qq : ℕ} {first : Fin 9} {repC : Control → Bool} {x0 : LX (Mirrored1 P)}
    (S : NAMED_starvedWindow (P := P) (encPad delay Lp Lf rep))
    (R : NAMED_phaseSeven (P := P) delay Lp Lf rep qq first)
    (F : FeedWin (QL delay Lp Lf P QChain) (tL P tChain) (encPad delay Lp Lf rep)
      (winStep_of_residualTick (residualTick_SL S R)).next)
    (hwT : NAMED_widthTick (P := P) (encPad delay Lp Lf rep) (tickC (SL qq first)))
    (hwF : NAMED_widthFeed (P := P) (encPad delay Lp Lf rep))
    (q0 : QL delay Lp Lf P QChain) (repQ outQ : QL delay Lp Lf P QChain → Bool)
    (hrep : ∀ m : Mirrored1 P, repC m.vm.ctl = repQ (encPad delay Lp Lf rep m).1)
    (hout : ∀ m : Mirrored1 P, m.vm.ctl.output = outQ (encPad delay Lp Lf rep m).1)
    (hinit : encPad delay Lp Lf rep x0.core = (q0, fun _ => STape.blankTape blankc)) :
    CoreLocal (PalPeg.LocalSysConcrete.sysC (SL qq first) repC) x0
      (QL delay Lp Lf P QChain) Γc (tL P tChain) Kc :=
  coreLocal_of_residual (residualTick_SL S R) F (roomOf_encPad delay Lp Lf rep)
    hwT hwF q0 repQ outQ hrep hout hinit

/-! ## 7. The fpp quantum -/

/-- **`NAMED_fppQuantum''` from a `.fpp` phase residual with a single-cell
window shape.**  "One `GalilDpCode` instruction per tick" is, on the layout,
the statement that every tape either keeps its window or does not move — which
is what `LocalBuffers.abs_stepL` (`abs (stepL f x) = f (abs x)`) exposes at the
abstract level: the instruction touches the active bank at a fixed offset and
nothing else. -/
theorem fppQuantum_of_det {Q : Type} {t : ℕ}
    {enc : Mirrored1 P → Q × (Fin t → STape Γc)} {M : Steps P}
    (R : NAMED_phaseWin enc M .fpp)
    (hq : ∀ (q : Q) (a : Option (Fin 2)) (ws : Fin t → Window Γc Kc) (j : Fin t),
      ((R.2.nx q a ws).2 j).1 = ws j ∨ ((R.2.nx q a ws).2 j).2 = 0) :
    NAMED_fppQuantum'' enc M := by
  refine ⟨modeWin_of_phaseWin R, fun q a ws j => ?_⟩
  show (clampD ((R.2.nx q a ws).2 j)).1 = ws j ∨ (clampD ((R.2.nx q a ws).2 j)).2 = 0
  rcases hq q a ws j with h | h
  · exact Or.inl (by rw [clampD_fst]; exact h)
  · exact Or.inr (by rw [clampD, if_pos (by rw [h]; simp)]; exact h)

end PalPeg.CloseoutCoreEnc6

#print axioms PalPeg.CloseoutCoreEnc6.modeWin_of_det
#print axioms PalPeg.CloseoutCoreEnc6.modePt_of_winRealizes
#print axioms PalPeg.CloseoutCoreEnc6.modeWin_id
#print axioms PalPeg.CloseoutCoreEnc6.modeWin_SL_init
#print axioms PalPeg.CloseoutCoreEnc6.modeWin_SL_scan
#print axioms PalPeg.CloseoutCoreEnc6.modeWin_SL_replayStart
#print axioms PalPeg.CloseoutCoreEnc6.encTapes_ctl
#print axioms PalPeg.CloseoutCoreEnc6.padTapes_ctl
#print axioms PalPeg.CloseoutCoreEnc6.modeWin_of_ctlOnly
#print axioms PalPeg.CloseoutCoreEnc6.widthTick_of_modes
#print axioms PalPeg.CloseoutCoreEnc6.roomOf_encPad
#print axioms PalPeg.CloseoutCoreEnc6.residualTick_SL
#print axioms PalPeg.CloseoutCoreEnc6.widthTick_SL
#print axioms PalPeg.CloseoutCoreEnc6.coreLocal_SL
#print axioms PalPeg.CloseoutCoreEnc6.fppQuantum_of_det
