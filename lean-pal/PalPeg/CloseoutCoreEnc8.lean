import PalPeg.CloseoutCoreEnc6

/-!
# Closeout: the phase modes as *branch + window* residuals, on a widened layout

`CloseoutCoreEnc6` reduces the tick half of the core's `LocalStep` to the seven
phase residuals `NAMED_phaseSeven` (each a `ModePt` plus a `DetWin`), seven
`WidthMode`s, the starvation test and the arrival datum, on the padded layout
`encPad = padR ∘ shift1 ∘ encTapes`.  It gives no way to *build* a `DetWin`
except all at once, and the padded layout reserves exactly one cell on the
right.

This file supplies the two missing pieces of machinery and applies them to the
seven phase steps of `CloseoutCoreAgree.SL`.  It builds no new dynamics and
proves no new fact about the Galil machine, so

**無条件 PAL ∈ PEG は未完.**

## What is established

* **§1 (the right reservoir, widened).**  `padRN b n` appends `n` blanks
  instead of one.  `pos_padRN`, `wlen_padRN`, `rd_padRN` (the reading is
  unchanged), `room_padRN` for every `K ≤ n`; `padTapesN`, `padTapesN_one`
  (`n = 1` *is* `CloseoutCoreEnc5.padTapes`), `margin_padTapesN`,
  `room_padTapesN`, `roomOf_padTapesN`, and the layout `encPadN` with
  `margin_encPadN`, `roomOf_encPadN`, `modeOf_encPadN`, `encPadN_one`.

  The widening is available but, for `WidthMode`, **not needed**:
  `wlen_padTapesN` shows `wlen (padTapesN n …) = wlen (encTapes1 …) + n`, so
  the width obligation of a mode is the *same* statement for every `n`
  (`widthMode_encPadN_iff_enc1`).  A right move does not eat the reservoir —
  `CloseoutCoreEnc5.wlen_sweep` keeps `wlen` fixed, and the reservoir is part
  of `wlen`.  What `n ≥ 2` would buy is only a wider window budget, and `Kc`
  is `1`.

* **§2 (`WinOn`: a window datum for one branch).**  `WinOn enc f md sc` is a
  window function reproducing `f` on the states of mode `md` that are not
  starved and satisfy `sc`.  `BranchRead` is a window-readable branch
  predicate.  Then:

  - `winOn_of_branch`: a branch read plus a `WinOn` for each side is a `WinOn`
    for the dispatching step — this is how the nested `if`s of the phase steps
    are taken apart, one branch at a time;
  - `winOn_id` / `winOn_ctlOnly`: the two closable shapes (a branch that stands
    still, a branch that only rewrites `Control` — the layout is blind to it,
    `CloseoutCoreEnc6.padTapes_ctl`);
  - `phaseWin_of_winOn`: a `WinOn` for `stepOf M md` *is* a
    `CloseoutCoreEnc6.NAMED_phaseWin`, i.e. a `ModePt` together with its
    `DetWin`.  Determinacy holds by construction: the datum is *defined* as the
    window function applied to the state's own windows.

* **§3 (the branch structure of the seven, definitionally).**  Each phase step
  of `SL` is `if ⟨local read⟩ then … else …`; `stepOf_SL_*_pos/neg` record the
  two sides for `shift`, `home`, `markEnd`, `copy`, `choose` and both levels of
  `rewind`.  The branch predicates are exactly the six named reads
  `RemPosL`, `AtLeftL`, `AtEndL`, `MarkSetL`, `AtFirstL` (and, inside the
  `shift` exit, `OnLetterL`) of `CloseoutCoreAgree` /
  `LocalRealizesPhase`.

* **§4 (`shift`, one branch closed).**  The `¬ RemPosL` branch of `shiftStepW`
  only rewrites `ctl` (`shiftDoneCtlW`), so on *any* `encTapes`-derived layout
  it moves no tape at all: `padTapesN_ctl`, `winOn_shift_done`,
  `widthMode_shift_done`.  Its whole content is that the refreshed output bit
  `refreshL` — an `OnLetterL` read plus `leftFirstVM` — is a window function of
  the control, which is the residual `ShiftDoneQ`.  Assembling: with
  `ShiftDoneQ`, a `BranchRead` for `RemPosL` and a `WinOn` for `shiftPick`,
  `phaseWin_shift` gives the `.shift` field of
  `CloseoutCoreEnc6.NAMED_phaseSeven` outright.

* **§5 (the residual bundle, on the widened layout).**  `PhasePieces` collects,
  per mode, the branch reads and the per-branch window data that are left;
  `phaseSevenN_of_pieces` turns them into a `NAMED_phaseSeven`, and
  `coreLocal_SL_N` chains everything into a `CloseoutCoreAudit.CoreLocal` on
  `encPadN`.  `fppQuantum_SL` wires the `.fpp` piece to
  `CloseoutCoreEnc6.fppQuantum_of_det`.

## The residuals (NAMED)

Per mode, with `enc := encPadN n delay Lp Lf rep` and `M := SL qq first`:

* `NAMED_branchRead enc pred md` for
  `RemPosL` (`shift`, `copy`), `AtLeftL` (`home`), `AtEndL` (`markEnd`),
  `odd ∧ MarkSetL` (`choose`), `AtFirstL` and `pair` (`rewind`);
* `NAMED_winOn enc f md sc` for the *acting* side of each branch:
  `shiftPick`, `copyPick`, `homeStartVm`/`homeStepVm`, `marksVm` both ways,
  `chooseVm`/`marksVm`, `rewindDoneVm`/`rewindPairVm`/`rewindOneVm`, and the
  whole of `ffppW`;
* `NAMED_shiftDoneQ` (the output refresh as a control-window function);
* `NAMED_widthEnc1 rep M md` per mode;
* and, unchanged from `CloseoutCoreEnc5`/`Enc6`,
  `NAMED_starvedWindow`, `FeedWin`, `NAMED_widthFeed`.

Nothing here proves any of them.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace PalPeg.CloseoutCoreEnc8

open PalPeg PalPeg.Program
open PalPeg.Local (Window pos rd toList sweep readWin LocalStep)
open PalPeg.GalilScaffoldChainInputSupply (ChainVM)
open PalPeg.GalilScaffoldController (Control Mode)
open PalPeg.LocalChain (ChainL)
open PalPeg.LocalReplayParked (Mirrored1 mirrorTick1)
open PalPeg.LocalSysConcrete (Steps Starved stepOf tickC feedC)
open PalPeg.LocalTrackingLatch (LX)
open PalPeg.CloseoutCoreAudit (CoreLocal)
open PalPeg.CloseoutCoreStep (Γc blankc tL QL qOfL)
open PalPeg.CloseoutCoreEnc (Kc encTapes QChain tChain qChainOf)
open PalPeg.CloseoutCoreEnc3 (encTapes1)
open PalPeg.CloseoutCoreEnc4 (TEq)
open PalPeg.CloseoutCoreEnc5 (wlen padR padTapes ModeWin ModeOf FeedWin ResidualTick
  NAMED_widthTick NAMED_widthFeed NAMED_starvedWindow NAMED_fppQuantum'' RoomOf
  sweep_id_TEq margin_padTapes room_padTapes winStep_of_residualTick coreLocal_of_residual)
open PalPeg.CloseoutCoreEnc6 (ModePt DetWin NAMED_phaseWin WidthMode NAMED_phaseSeven
  modeWin_of_phaseWin modeWin_SL_init modeWin_SL_scan modeWin_SL_replayStart
  widthTick_of_modes widthMode_id residualTick_SL)
open PalPeg.CloseoutCoreAgree (SL MarkSetL AtFirstL OnLetterL shiftStepW shiftDoneCtlW
  chooseStepW rewindStepW refreshL ffppW)
open PalPeg.LocalRealizesPhase (AtLeftL AtEndL RemPosL copyStepL copyPick homeStepL
  markEndStepL shiftPick)

variable {P : ℕ}

/-! ## 1. The right reservoir, widened -/

variable {Γ : Type}

/-- **Reserve `n` cells at the right end.**  `CloseoutCoreEnc5.padR` is `n = 1`. -/
def padRN (b : Γ) (n : ℕ) (T : STape Γ) : STape Γ :=
  ⟨T.left, T.focus, T.right ++ List.replicate n b⟩

@[simp] theorem padRN_zero (b : Γ) (T : STape Γ) : padRN b 0 T = T := by
  cases T; simp [padRN]

theorem padRN_one (b : Γ) (T : STape Γ) : padRN b 1 T = padR b T := by
  simp [padRN, padR]

theorem padRN_succ (b : Γ) (n : ℕ) (T : STape Γ) :
    padRN b (n + 1) T = padR b (padRN b n T) := by
  simp [padRN, padR, List.replicate_succ', List.append_assoc]

@[simp] theorem pos_padRN (b : Γ) (n : ℕ) (T : STape Γ) : pos (padRN b n T) = pos T := rfl

@[simp] theorem wlen_padRN (b : Γ) (n : ℕ) (T : STape Γ) :
    wlen (padRN b n T) = wlen T + n := by
  simp only [wlen, padRN, pos, List.length_append, List.length_replicate]
  omega

@[simp] theorem rd_padRN (b : Γ) (n : ℕ) (T : STape Γ) (p : ℕ) :
    rd b (padRN b n T) p = rd b T p := by
  induction n with
  | zero => rw [padRN_zero]
  | succ k ih => rw [padRN_succ, PalPeg.CloseoutCoreEnc5.rd_padR, ih]

/-- **The room condition, for every reservoir at least as wide as the window
budget.** -/
theorem room_padRN (b : Γ) (n K : ℕ) (T : STape Γ) (hK : K ≤ n) :
    pos (padRN b n T) + K ≤ wlen (padRN b n T) := by
  rw [pos_padRN, wlen_padRN]
  have := PalPeg.CloseoutCoreEnc5.pos_le_wlen T
  omega

/-- **The core's layout with a reservoir of `n` blanks on the right.** -/
noncomputable def padTapesN (n : ℕ) (rep : ChainVM → ChainL) (m : Mirrored1 P) :
    ℕ → STape Γc := fun i => padRN blankc n (encTapes1 rep m i)

theorem padTapesN_one (rep : ChainVM → ChainL) (m : Mirrored1 P) (i : ℕ) :
    padTapesN 1 rep m i = padTapes rep m i := by
  rw [padTapesN, padRN_one, padTapes]

theorem margin_padTapesN (n : ℕ) (rep : ChainVM → ChainL) (m : Mirrored1 P) (i : ℕ) :
    Kc ≤ pos (padTapesN n rep m i) := by
  rw [padTapesN, pos_padRN]
  exact PalPeg.CloseoutCoreEnc3.margin_encTapes1 rep m i

theorem room_padTapesN (n : ℕ) (rep : ChainVM → ChainL) (m : Mirrored1 P) (i : ℕ)
    (hn : Kc ≤ n) : pos (padTapesN n rep m i) + Kc ≤ wlen (padTapesN n rep m i) :=
  room_padRN _ _ _ _ hn

theorem wlen_padTapesN (n : ℕ) (rep : ChainVM → ChainL) (m : Mirrored1 P) (i : ℕ) :
    wlen (padTapesN n rep m i) = wlen (encTapes1 rep m i) + n := by
  rw [padTapesN, wlen_padRN]

theorem rd_padTapesN (n : ℕ) (rep : ChainVM → ChainL) (m : Mirrored1 P) (i p : ℕ) :
    rd blankc (padTapesN n rep m i) p = rd blankc (encTapes1 rep m i) p := rd_padRN _ _ _ _

/-- **The layout is blind to `Control` at every reservoir width.** -/
theorem padTapesN_ctl (n : ℕ) (rep : ChainVM → ChainL) (m : Mirrored1 P) (c : Control)
    (i : ℕ) : padTapesN n rep ⟨{ m.vm with ctl := c }, m.mirL⟩ i = padTapesN n rep m i := rfl

/-- **The widened layout.** -/
noncomputable def encPadN (n delay Lp Lf : ℕ) (rep : ChainVM → ChainL) (m : Mirrored1 P) :
    QL delay Lp Lf P QChain × (Fin (tL P tChain) → STape Γc) :=
  (qOfL delay Lp Lf (fun c => qChainOf (rep c)) m, fun j => padTapesN n rep m j.val)

theorem encPadN_one (delay Lp Lf : ℕ) (rep : ChainVM → ChainL) (m : Mirrored1 P) :
    encPadN 1 delay Lp Lf rep m
      = PalPeg.CloseoutCoreEnc6.encPad (P := P) delay Lp Lf rep m := by
  rw [encPadN, PalPeg.CloseoutCoreEnc6.encPad]
  exact Prod.ext rfl (funext fun j => padTapesN_one rep m j.val)

theorem margin_encPadN (n delay Lp Lf : ℕ) (rep : ChainVM → ChainL) (m : Mirrored1 P)
    (j : Fin (tL P tChain)) : Kc ≤ pos ((encPadN n delay Lp Lf rep m).2 j) :=
  margin_padTapesN n rep m j.val

theorem roomOf_encPadN (n delay Lp Lf : ℕ) (rep : ChainVM → ChainL) (hn : Kc ≤ n) :
    RoomOf (P := P) (encPadN n delay Lp Lf rep) :=
  fun m j => ⟨margin_padTapesN n rep m j.val, room_padTapesN n rep m j.val hn⟩

def modeOf_encPadN (n delay Lp Lf : ℕ) (rep : ChainVM → ChainL) :
    ModeOf (P := P) (QL delay Lp Lf P QChain) (tL P tChain) (encPadN n delay Lp Lf rep) where
  modeOf := fun q => q.1.val.mode
  spec := fun m => rfl

/-! ### The width obligation does not see the reservoir -/

/-- **Residual: the *unpadded* layout conserves the stored width of a mode's
step.**  The reservoir cancels (`widthMode_encPadN_iff_enc1`), so this is the
whole content of `CloseoutCoreEnc6.WidthMode` for `encPadN n`, for every `n`. -/
def NAMED_widthEnc1 (rep : ChainVM → ChainL) (M : Steps P) (md : Mode) : Prop :=
  ∀ (m : Mirrored1 P) (i : ℕ), m.vm.ctl.mode = md → ¬ Starved m.vm →
    wlen (encTapes1 rep (stepOf M md m) i) = wlen (encTapes1 rep m i)

theorem widthMode_encPadN_iff_enc1 (n delay Lp Lf : ℕ) (rep : ChainVM → ChainL)
    (M : Steps P) (md : Mode) :
    WidthMode (encPadN n delay Lp Lf rep) M md ↔
      ∀ (m : Mirrored1 P) (j : Fin (tL P tChain)), m.vm.ctl.mode = md → ¬ Starved m.vm →
        wlen (encTapes1 rep (stepOf M md m) j.val) = wlen (encTapes1 rep m j.val) := by
  constructor
  · intro h m j hmd hs
    have := h m j hmd hs
    show _ = _
    rw [show ((encPadN n delay Lp Lf rep (stepOf M md m)).2 j) =
        padTapesN n rep (stepOf M md m) j.val from rfl,
      show ((encPadN n delay Lp Lf rep m).2 j) = padTapesN n rep m j.val from rfl,
      wlen_padTapesN, wlen_padTapesN] at this
    omega
  · intro h m j hmd hs
    show wlen (padTapesN n rep (stepOf M md m) j.val) = wlen (padTapesN n rep m j.val)
    rw [wlen_padTapesN, wlen_padTapesN, h m j hmd hs]

theorem widthMode_encPadN_of_enc1 (n delay Lp Lf : ℕ) (rep : ChainVM → ChainL)
    {M : Steps P} {md : Mode} (h : NAMED_widthEnc1 rep M md) :
    WidthMode (encPadN n delay Lp Lf rep) M md :=
  (widthMode_encPadN_iff_enc1 n delay Lp Lf rep M md).mpr (fun m j hmd hs => h m j.val hmd hs)

/-! ## 2. `WinOn`: one branch of one mode, as a window function -/

/-- The windows a state presents to the step. -/
def rwOf {Q : Type} {t : ℕ} (enc : Mirrored1 P → Q × (Fin t → STape Γc))
    (m : Mirrored1 P) : Fin t → Window Γc Kc :=
  fun j => readWin blankc Kc ((enc m).2 j)

/-- **A window datum for one branch of one mode.**  It reproduces `f` — up to
`CloseoutCoreEnc4.TEq`, as `ModeWin` does — on the states of mode `md` that are
not starved and satisfy the side condition `sc`. -/
structure WinOn (Q : Type) (t : ℕ) (enc : Mirrored1 P → Q × (Fin t → STape Γc))
    (f : Mirrored1 P → Mirrored1 P) (md : Mode) (sc : Mirrored1 P → Prop) where
  nx : Q → (Fin t → Window Γc Kc) → Q × (Fin t → Window Γc Kc × ℤ)
  disp : ∀ (q : Q) (ws : Fin t → Window Γc Kc) (j : Fin t), |((nx q ws).2 j).2| ≤ (Kc : ℤ)
  ctl : ∀ m : Mirrored1 P, m.vm.ctl.mode = md → ¬ Starved m.vm → sc m →
    (enc (f m)).1 = (nx (enc m).1 (rwOf enc m)).1
  tape : ∀ (m : Mirrored1 P) (j : Fin t), m.vm.ctl.mode = md → ¬ Starved m.vm → sc m →
    TEq ((enc (f m)).2 j)
      (sweep blankc Kc ((enc m).2 j) ((nx (enc m).1 (rwOf enc m)).2 j).1
        ((nx (enc m).1 (rwOf enc m)).2 j).2)

/-- **A branch predicate that is a window read.**  The determinacy content of
`CloseoutCoreEnc6.DetWin`, isolated to one test. -/
structure BranchRead (Q : Type) (t : ℕ) (enc : Mirrored1 P → Q × (Fin t → STape Γc))
    (pred : Mirrored1 P → Prop) (md : Mode) where
  test : Q → (Fin t → Window Γc Kc) → Bool
  spec : ∀ m : Mirrored1 P, m.vm.ctl.mode = md → ¬ Starved m.vm →
    (test (enc m).1 (rwOf enc m) = true ↔ pred m)

/-- **Residual, named.** -/
def NAMED_branchRead {Q : Type} {t : ℕ} (enc : Mirrored1 P → Q × (Fin t → STape Γc))
    (pred : Mirrored1 P → Prop) (md : Mode) : Type := BranchRead Q t enc pred md

/-- **Residual, named.** -/
def NAMED_winOn {Q : Type} {t : ℕ} (enc : Mirrored1 P → Q × (Fin t → STape Γc))
    (f : Mirrored1 P → Mirrored1 P) (md : Mode) (sc : Mirrored1 P → Prop) : Type :=
  WinOn Q t enc f md sc

theorem branchRead_false {Q : Type} {t : ℕ} {enc : Mirrored1 P → Q × (Fin t → STape Γc)}
    {pred : Mirrored1 P → Prop} {md : Mode} (B : BranchRead Q t enc pred md)
    {m : Mirrored1 P} (hmd : m.vm.ctl.mode = md) (hs : ¬ Starved m.vm) (hp : ¬ pred m) :
    B.test (enc m).1 (rwOf enc m) = false := by
  by_cases h : B.test (enc m).1 (rwOf enc m) = true
  · exact absurd ((B.spec m hmd hs).mp h) hp
  · simpa using h

/-- **Taking one `if` apart.**  A window-readable branch, plus a window datum
for each side, is a window datum for the dispatching step. -/
noncomputable def winOn_of_branch {Q : Type} {t : ℕ}
    {enc : Mirrored1 P → Q × (Fin t → STape Γc)} {md : Mode} {sc : Mirrored1 P → Prop}
    (pred : Mirrored1 P → Prop) (h f g : Mirrored1 P → Mirrored1 P)
    (B : BranchRead Q t enc pred md)
    (A : WinOn Q t enc f md (fun m => sc m ∧ pred m))
    (C : WinOn Q t enc g md (fun m => sc m ∧ ¬ pred m))
    (hpos : ∀ m : Mirrored1 P, m.vm.ctl.mode = md → ¬ Starved m.vm → sc m → pred m →
      h m = f m)
    (hneg : ∀ m : Mirrored1 P, m.vm.ctl.mode = md → ¬ Starved m.vm → sc m → ¬ pred m →
      h m = g m) :
    WinOn Q t enc h md sc where
  nx := fun q ws => if B.test q ws then A.nx q ws else C.nx q ws
  disp := fun q ws j => by
    by_cases hb : B.test q ws
    · simp only [hb, if_true]; exact A.disp q ws j
    · simp only [hb, Bool.false_eq_true, if_false]; exact C.disp q ws j
  ctl := fun m hmd hs hsc => by
    by_cases hp : pred m
    · have hb := (B.spec m hmd hs).mpr hp
      rw [hpos m hmd hs hsc hp]
      simp only [hb, if_true]
      exact A.ctl m hmd hs ⟨hsc, hp⟩
    · have hb := branchRead_false B hmd hs hp
      rw [hneg m hmd hs hsc hp]
      simp only [hb, Bool.false_eq_true, if_false]
      exact C.ctl m hmd hs ⟨hsc, hp⟩
  tape := fun m j hmd hs hsc => by
    by_cases hp : pred m
    · have hb := (B.spec m hmd hs).mpr hp
      rw [hpos m hmd hs hsc hp]
      simp only [hb, if_true]
      exact A.tape m j hmd hs ⟨hsc, hp⟩
    · have hb := branchRead_false B hmd hs hp
      rw [hneg m hmd hs hsc hp]
      simp only [hb, Bool.false_eq_true, if_false]
      exact C.tape m j hmd hs ⟨hsc, hp⟩

/-- **A branch that stands still.** -/
noncomputable def winOn_id {Q : Type} {t : ℕ}
    {enc : Mirrored1 P → Q × (Fin t → STape Γc)} {md : Mode} {sc : Mirrored1 P → Prop}
    (f : Mirrored1 P → Mirrored1 P)
    (hf : ∀ m : Mirrored1 P, m.vm.ctl.mode = md → ¬ Starved m.vm → sc m → f m = m)
    (hmargin : ∀ (m : Mirrored1 P) (j : Fin t), Kc ≤ pos ((enc m).2 j)) :
    WinOn Q t enc f md sc where
  nx := fun q ws => (q, fun j => (ws j, 0))
  disp := fun q ws j => by simp
  ctl := fun m hmd hs hsc => by rw [hf m hmd hs hsc]
  tape := fun m j hmd hs hsc => by
    rw [hf m hmd hs hsc]
    exact sweep_id_TEq ((enc m).2 j) (hmargin m j)

/-- **A branch that only rewrites the finite control.**  The layout reads no
field of `Control` (`CloseoutCoreEnc6.padTapes_ctl`, `padTapesN_ctl`), so every
tape datum is the identity window and the only content is `nq`. -/
noncomputable def winOn_ctlOnly {Q : Type} {t : ℕ}
    {enc : Mirrored1 P → Q × (Fin t → STape Γc)} {md : Mode} {sc : Mirrored1 P → Prop}
    (f : Mirrored1 P → Mirrored1 P)
    (nq : Q → (Fin t → Window Γc Kc) → Q)
    (hctl : ∀ m : Mirrored1 P, m.vm.ctl.mode = md → ¬ Starved m.vm → sc m →
      (enc (f m)).1 = nq (enc m).1 (rwOf enc m))
    (htape : ∀ (m : Mirrored1 P) (j : Fin t), m.vm.ctl.mode = md → ¬ Starved m.vm → sc m →
      (enc (f m)).2 j = (enc m).2 j)
    (hmargin : ∀ (m : Mirrored1 P) (j : Fin t), Kc ≤ pos ((enc m).2 j)) :
    WinOn Q t enc f md sc where
  nx := fun q ws => (nq q ws, fun j => (ws j, 0))
  disp := fun q ws j => by simp
  ctl := hctl
  tape := fun m j hmd hs hsc => by
    rw [htape m j hmd hs hsc]
    exact sweep_id_TEq ((enc m).2 j) (hmargin m j)

/-- **A `WinOn` for the mode's own step is a `NAMED_phaseWin`.**  Determinacy
is by construction: the pointwise datum *is* the window function applied to the
state's own windows, so `DetWin.spec` is `rfl`. -/
noncomputable def phaseWin_of_winOn {Q : Type} {t : ℕ}
    {enc : Mirrored1 P → Q × (Fin t → STape Γc)} {M : Steps P} {md : Mode}
    (A : WinOn Q t enc (fun m => stepOf M md m) md (fun _ => True)) :
    NAMED_phaseWin enc M md :=
  ⟨{ win := fun m => A.nx (enc m).1 (rwOf enc m)
     disp := fun m j => A.disp _ _ j
     ctl := fun m hmd hs => A.ctl m hmd hs trivial
     tape := fun m j hmd hs => A.tape m j hmd hs trivial },
   { nx := fun q _ ws => A.nx q ws
     spec := fun m hmd hs => rfl }⟩

/-- Transporting a `WinOn` along a pointwise equality of steps. -/
noncomputable def winOn_congr {Q : Type} {t : ℕ}
    {enc : Mirrored1 P → Q × (Fin t → STape Γc)} {md : Mode} {sc : Mirrored1 P → Prop}
    {f g : Mirrored1 P → Mirrored1 P} (A : WinOn Q t enc g md sc)
    (h : ∀ m : Mirrored1 P, m.vm.ctl.mode = md → ¬ Starved m.vm → sc m → f m = g m) :
    WinOn Q t enc f md sc where
  nx := A.nx
  disp := A.disp
  ctl := fun m hmd hs hsc => by rw [h m hmd hs hsc]; exact A.ctl m hmd hs hsc
  tape := fun m j hmd hs hsc => by rw [h m hmd hs hsc]; exact A.tape m j hmd hs hsc

/-! ## 3. The branch structure of the seven phase steps of `SL` -/

theorem stepOf_SL_shift (qq : ℕ) (first : Fin 9) (m : Mirrored1 P) :
    stepOf (SL (P := P) qq first) .shift m = shiftStepW m := rfl

theorem stepOf_SL_copy (qq : ℕ) (first : Fin 9) (m : Mirrored1 P) :
    stepOf (SL (P := P) qq first) .copy m = copyStepL m := rfl

theorem stepOf_SL_home (qq : ℕ) (first : Fin 9) (m : Mirrored1 P) :
    stepOf (SL (P := P) qq first) .home m = homeStepL m := rfl

theorem stepOf_SL_markEnd (qq : ℕ) (first : Fin 9) (m : Mirrored1 P) :
    stepOf (SL (P := P) qq first) .markEnd m = markEndStepL m := rfl

theorem stepOf_SL_choose (qq : ℕ) (first : Fin 9) (m : Mirrored1 P) :
    stepOf (SL (P := P) qq first) .choose m = chooseStepW first m := rfl

theorem stepOf_SL_rewind (qq : ℕ) (first : Fin 9) (m : Mirrored1 P) :
    stepOf (SL (P := P) qq first) .rewind m = rewindStepW first m := rfl

theorem stepOf_SL_fpp (qq : ℕ) (first : Fin 9) (m : Mirrored1 P) :
    stepOf (SL (P := P) qq first) .fpp m = ffppW qq first m := rfl

section Branches

variable (qq : ℕ) (first : Fin 9)

theorem shiftStepW_pos (m : Mirrored1 P) (h : RemPosL m.vm) :
    shiftStepW m = shiftPick m.vm.chain m.vm m.mirL := by
  classical
  rw [shiftStepW, if_pos h]

theorem shiftStepW_neg (m : Mirrored1 P) (h : ¬ RemPosL m.vm) :
    shiftStepW m = ⟨{ m.vm with ctl := shiftDoneCtlW m.vm }, m.mirL⟩ := by
  classical
  rw [shiftStepW, if_neg h]

theorem copyStepL_pos (m : Mirrored1 P) (h : RemPosL m.vm) :
    copyStepL m = copyPick (GalilScaffoldPlace.read (PalPeg.LocalArrival.abs' m.vm).fpp.walker) m := by
  classical
  rw [copyStepL, if_pos h]

theorem copyStepL_neg (m : Mirrored1 P) (h : ¬ RemPosL m.vm) :
    copyStepL m
      = ⟨PalPeg.LocalTick3.copyDoneVm { m.vm.ctl with mode := .home } m.vm, m.mirL⟩ := by
  classical
  rw [copyStepL, if_neg h]

theorem homeStepL_pos (m : Mirrored1 P) (h : AtLeftL m.vm) :
    homeStepL m
      = ⟨PalPeg.LocalTick3.homeStartVm { m.vm.ctl with mode := .fpp } m.vm, m.mirL⟩ := by
  classical
  rw [homeStepL, if_pos h]

theorem homeStepL_neg (m : Mirrored1 P) (h : ¬ AtLeftL m.vm) :
    homeStepL m = ⟨PalPeg.LocalTick3.homeStepVm m.vm, m.mirL⟩ := by
  classical
  rw [homeStepL, if_neg h]

theorem markEndStepL_pos (m : Mirrored1 P) (h : AtEndL m.vm) :
    markEndStepL m = ⟨PalPeg.LocalTick3.marksVm GalilScaffoldTape.moveLeft
      { m.vm.ctl with mode := .choose, odd := false } m.vm, m.mirL⟩ := by
  classical
  rw [markEndStepL, if_pos h]

theorem markEndStepL_neg (m : Mirrored1 P) (h : ¬ AtEndL m.vm) :
    markEndStepL m
      = ⟨PalPeg.LocalTick3.marksVm GalilScaffoldTape.moveRight m.vm.ctl m.vm, m.mirL⟩ := by
  classical
  rw [markEndStepL, if_neg h]

/-- The `choose` branch read: the parity bit *and* the MARKS read. -/
def ChooseBr (first : Fin 9) (m : Mirrored1 P) : Prop :=
  m.vm.ctl.odd = true ∧ MarkSetL first (PalPeg.LocalArrival.abs' m.vm)

theorem chooseStepW_pos (m : Mirrored1 P) (h : ChooseBr first m) :
    chooseStepW first m = mirrorTick1 .stay (PalPeg.LocalTick3.chooseVm
      { m.vm.ctl with mode := .rewind, pair := false } m.vm) m := by
  classical
  rw [chooseStepW,
    if_pos (show m.vm.ctl.odd = true ∧ MarkSetL first (PalPeg.LocalArrival.abs' m.vm) from h)]

theorem chooseStepW_neg (m : Mirrored1 P) (h : ¬ ChooseBr first m) :
    chooseStepW first m = mirrorTick1 .stay
      (PalPeg.LocalTick3.marksVm GalilScaffoldTape.moveLeft
        { m.vm.ctl with odd := !m.vm.ctl.odd } m.vm) m := by
  classical
  rw [chooseStepW,
    if_neg (show ¬ (m.vm.ctl.odd = true ∧ MarkSetL first (PalPeg.LocalArrival.abs' m.vm)) from h)]

theorem rewindStepW_pos (m : Mirrored1 P)
    (h : AtFirstL first (PalPeg.LocalArrival.abs' m.vm)) :
    rewindStepW first m = mirrorTick1 .stay (PalPeg.LocalTick3.rewindDoneVm
      { m.vm.ctl with mode := .replayStart } m.vm) m := by
  classical
  rw [rewindStepW, if_pos h]

theorem rewindStepW_pair (m : Mirrored1 P)
    (h : ¬ AtFirstL first (PalPeg.LocalArrival.abs' m.vm)) (hp : m.vm.ctl.pair = true) :
    rewindStepW first m = mirrorTick1 .left (PalPeg.LocalTick3.rewindPairVm
      { m.vm.ctl with pair := false } m.vm) m := by
  classical
  rw [rewindStepW, if_neg h, if_pos hp]

theorem rewindStepW_one (m : Mirrored1 P)
    (h : ¬ AtFirstL first (PalPeg.LocalArrival.abs' m.vm)) (hp : ¬ m.vm.ctl.pair = true) :
    rewindStepW first m = mirrorTick1 .stay (PalPeg.LocalTick3.rewindOneVm
      { m.vm.ctl with pair := true } m.vm) m := by
  classical
  rw [rewindStepW, if_neg h, if_neg hp]

end Branches

/-! ## 4. `shift`: the exit branch, closed -/

variable {n delay Lp Lf : ℕ} {rep : ChainVM → ChainL}

theorem encPadN_ctl (m : Mirrored1 P) (c : Control) (j : Fin (tL P tChain)) :
    (encPadN n delay Lp Lf rep (⟨{ m.vm with ctl := c }, m.mirL⟩ : Mirrored1 P)).2 j
      = (encPadN n delay Lp Lf rep m).2 j := rfl

/-- **Residual: the output refresh is a control-window function.**  The `shift`
exit writes `refreshL` into `ctl.output`; `refreshL` is an `OnLetterL` read of
the R head plus `leftFirstVM` (`CloseoutCoreAgree.onLetterVM_iff`), so this is
the determinacy of that read on the layout. -/
def NAMED_shiftDoneQ (n delay Lp Lf : ℕ) (rep : ChainVM → ChainL) : Type :=
  { nq : QL delay Lp Lf P QChain → (Fin (tL P tChain) → Window Γc Kc) →
      QL delay Lp Lf P QChain //
    ∀ m : Mirrored1 P, m.vm.ctl.mode = .shift → ¬ Starved m.vm → ¬ RemPosL m.vm →
      (encPadN n delay Lp Lf rep
          (⟨{ m.vm with ctl := shiftDoneCtlW m.vm }, m.mirL⟩ : Mirrored1 P)).1
        = nq (encPadN n delay Lp Lf rep m).1 (rwOf (encPadN n delay Lp Lf rep) m) }

/-- **The `shift` exit branch, as a window datum.**  Its tape half is closed
outright: the step rewrites `ctl` only, and the layout is blind to `Control`. -/
noncomputable def winOn_shift_done (R : NAMED_shiftDoneQ (P := P) n delay Lp Lf rep) :
    WinOn (QL delay Lp Lf P QChain) (tL P tChain) (encPadN n delay Lp Lf rep)
      (fun m => (⟨{ m.vm with ctl := shiftDoneCtlW m.vm }, m.mirL⟩ : Mirrored1 P))
      .shift (fun m => True ∧ ¬ RemPosL m.vm) :=
  winOn_ctlOnly _ R.1
    (fun m hmd hs hsc => R.2 m hmd hs hsc.2)
    (fun m j hmd hs hsc => encPadN_ctl m _ j)
    (margin_encPadN n delay Lp Lf rep)

/-- **The `shift` mode's phase residual**, from the branch read for `RemPosL`,
a window datum for the acting branch `shiftPick`, and the exit datum. -/
noncomputable def phaseWin_shift {qq : ℕ} {first : Fin 9}
    (B : NAMED_branchRead (P := P) (encPadN n delay Lp Lf rep) (fun m => RemPosL m.vm) .shift)
    (A : NAMED_winOn (P := P) (encPadN n delay Lp Lf rep)
      (fun m => shiftPick m.vm.chain m.vm m.mirL) .shift (fun m => True ∧ RemPosL m.vm))
    (R : NAMED_shiftDoneQ (P := P) n delay Lp Lf rep) :
    NAMED_phaseWin (encPadN n delay Lp Lf rep) (SL (P := P) qq first) .shift :=
  phaseWin_of_winOn
    (winOn_of_branch (fun m => RemPosL m.vm) _ _ _ B A (winOn_shift_done R)
      (fun m hmd hs _ hp => by rw [stepOf_SL_shift, shiftStepW_pos m hp])
      (fun m hmd hs _ hp => by rw [stepOf_SL_shift, shiftStepW_neg m hp]))

/-- **The `shift` exit conserves the width.**  A control rewrite moves no
tape. -/
theorem widthEnc1_shift_done (m : Mirrored1 P) (c : Control) (i : ℕ) :
    wlen (encTapes1 rep (⟨{ m.vm with ctl := c }, m.mirL⟩ : Mirrored1 P) i)
      = wlen (encTapes1 rep m i) := rfl

/-! ## 5. The bundle, on the widened layout -/

/-- **What is left of the seven phase modes**, mode by mode: the branch reads
and the acting branches.  `shift`'s exit branch is not a field — §4 closes
it. -/
structure PhasePieces (n delay Lp Lf : ℕ) (rep : ChainVM → ChainL) (qq : ℕ)
    (first : Fin 9) : Type where
  shiftBr : NAMED_branchRead (P := P) (encPadN n delay Lp Lf rep)
    (fun m => RemPosL m.vm) .shift
  shiftPick : NAMED_winOn (P := P) (encPadN n delay Lp Lf rep)
    (fun m => shiftPick m.vm.chain m.vm m.mirL) .shift (fun m => True ∧ RemPosL m.vm)
  shiftDone : NAMED_shiftDoneQ (P := P) n delay Lp Lf rep
  copy : NAMED_phaseWin (P := P) (encPadN n delay Lp Lf rep) (SL qq first) .copy
  home : NAMED_phaseWin (P := P) (encPadN n delay Lp Lf rep) (SL qq first) .home
  fpp : NAMED_phaseWin (P := P) (encPadN n delay Lp Lf rep) (SL qq first) .fpp
  markEnd : NAMED_phaseWin (P := P) (encPadN n delay Lp Lf rep) (SL qq first) .markEnd
  choose : NAMED_phaseWin (P := P) (encPadN n delay Lp Lf rep) (SL qq first) .choose
  rewind : NAMED_phaseWin (P := P) (encPadN n delay Lp Lf rep) (SL qq first) .rewind

/-- **The seven phase residuals on the widened layout, from the pieces.** -/
structure PhaseSevenN (n delay Lp Lf : ℕ) (rep : ChainVM → ChainL) (qq : ℕ)
    (first : Fin 9) : Type where
  shift : NAMED_phaseWin (P := P) (encPadN n delay Lp Lf rep) (SL qq first) .shift
  copy : NAMED_phaseWin (P := P) (encPadN n delay Lp Lf rep) (SL qq first) .copy
  home : NAMED_phaseWin (P := P) (encPadN n delay Lp Lf rep) (SL qq first) .home
  fpp : NAMED_phaseWin (P := P) (encPadN n delay Lp Lf rep) (SL qq first) .fpp
  markEnd : NAMED_phaseWin (P := P) (encPadN n delay Lp Lf rep) (SL qq first) .markEnd
  choose : NAMED_phaseWin (P := P) (encPadN n delay Lp Lf rep) (SL qq first) .choose
  rewind : NAMED_phaseWin (P := P) (encPadN n delay Lp Lf rep) (SL qq first) .rewind

noncomputable def phaseSevenN_of_pieces {qq : ℕ} {first : Fin 9}
    (R : PhasePieces (P := P) n delay Lp Lf rep qq first) :
    PhaseSevenN (P := P) n delay Lp Lf rep qq first where
  shift := phaseWin_shift R.shiftBr R.shiftPick R.shiftDone
  copy := R.copy
  home := R.home
  fpp := R.fpp
  markEnd := R.markEnd
  choose := R.choose
  rewind := R.rewind

/-- **The tick bundle on `encPadN`**, exactly as `CloseoutCoreEnc6.residualTick_SL`
does for `encPad`. -/
noncomputable def residualTick_SL_N {qq : ℕ} {first : Fin 9}
    (S : NAMED_starvedWindow (P := P) (encPadN n delay Lp Lf rep))
    (R : PhaseSevenN (P := P) n delay Lp Lf rep qq first) :
    ResidualTick (QL delay Lp Lf P QChain) (tL P tChain) (encPadN n delay Lp Lf rep)
      (SL qq first) where
  D := modeOf_encPadN n delay Lp Lf rep
  S := S
  init := modeWin_SL_init qq first (margin_encPadN n delay Lp Lf rep)
  scan := modeWin_SL_scan qq first (margin_encPadN n delay Lp Lf rep)
  shift := modeWin_of_phaseWin R.shift
  copy := modeWin_of_phaseWin R.copy
  home := modeWin_of_phaseWin R.home
  fpp := modeWin_of_phaseWin R.fpp
  markEnd := modeWin_of_phaseWin R.markEnd
  choose := modeWin_of_phaseWin R.choose
  rewind := modeWin_of_phaseWin R.rewind
  replayStart := modeWin_SL_replayStart qq first (margin_encPadN n delay Lp Lf rep)
  hmargin := margin_encPadN n delay Lp Lf rep

/-- **The width residual on `encPadN`, from the seven unpadded widths.** -/
theorem widthTick_SL_N {qq : ℕ} {first : Fin 9}
    (hshift : NAMED_widthEnc1 (P := P) rep (SL qq first) .shift)
    (hcopy : NAMED_widthEnc1 (P := P) rep (SL qq first) .copy)
    (hhome : NAMED_widthEnc1 (P := P) rep (SL qq first) .home)
    (hfpp : NAMED_widthEnc1 (P := P) rep (SL qq first) .fpp)
    (hmarkEnd : NAMED_widthEnc1 (P := P) rep (SL qq first) .markEnd)
    (hchoose : NAMED_widthEnc1 (P := P) rep (SL qq first) .choose)
    (hrewind : NAMED_widthEnc1 (P := P) rep (SL qq first) .rewind) :
    NAMED_widthTick (P := P) (encPadN n delay Lp Lf rep) (tickC (SL qq first)) := by
  refine widthTick_of_modes (fun md => ?_)
  match md with
  | .init => exact widthMode_id (PalPeg.CloseoutCoreEnc6.stepOf_SL_init qq first)
  | .scan => exact widthMode_id (PalPeg.CloseoutCoreEnc6.stepOf_SL_scan qq first)
  | .shift => exact widthMode_encPadN_of_enc1 n delay Lp Lf rep hshift
  | .copy => exact widthMode_encPadN_of_enc1 n delay Lp Lf rep hcopy
  | .home => exact widthMode_encPadN_of_enc1 n delay Lp Lf rep hhome
  | .fpp => exact widthMode_encPadN_of_enc1 n delay Lp Lf rep hfpp
  | .markEnd => exact widthMode_encPadN_of_enc1 n delay Lp Lf rep hmarkEnd
  | .choose => exact widthMode_encPadN_of_enc1 n delay Lp Lf rep hchoose
  | .rewind => exact widthMode_encPadN_of_enc1 n delay Lp Lf rep hrewind
  | .replayStart => exact widthMode_id (PalPeg.CloseoutCoreEnc6.stepOf_SL_replayStart qq first)

/-- **The `CoreLocal` term on the widened layout.** -/
noncomputable def coreLocal_SL_N {qq : ℕ} {first : Fin 9} {repC : Control → Bool}
    {x0 : LX (Mirrored1 P)}
    (hn : Kc ≤ n)
    (S : NAMED_starvedWindow (P := P) (encPadN n delay Lp Lf rep))
    (R : PhaseSevenN (P := P) n delay Lp Lf rep qq first)
    (F : FeedWin (QL delay Lp Lf P QChain) (tL P tChain) (encPadN n delay Lp Lf rep)
      (winStep_of_residualTick (residualTick_SL_N S R)).next)
    (hwT : NAMED_widthTick (P := P) (encPadN n delay Lp Lf rep) (tickC (SL qq first)))
    (hwF : NAMED_widthFeed (P := P) (encPadN n delay Lp Lf rep))
    (q0 : QL delay Lp Lf P QChain) (repQ outQ : QL delay Lp Lf P QChain → Bool)
    (hrep : ∀ m : Mirrored1 P, repC m.vm.ctl = repQ (encPadN n delay Lp Lf rep m).1)
    (hout : ∀ m : Mirrored1 P, m.vm.ctl.output = outQ (encPadN n delay Lp Lf rep m).1)
    (hinit : encPadN n delay Lp Lf rep x0.core = (q0, fun _ => STape.blankTape blankc)) :
    CoreLocal (PalPeg.LocalSysConcrete.sysC (SL qq first) repC) x0
      (QL delay Lp Lf P QChain) Γc (tL P tChain) Kc :=
  coreLocal_of_residual (residualTick_SL_N S R) F (roomOf_encPadN n delay Lp Lf rep hn)
    hwT hwF q0 repQ outQ hrep hout hinit

/-! ## 6. The fpp quantum, from the `.fpp` piece -/

theorem fppQuantum_SL {qq : ℕ} {first : Fin 9}
    (R : PhaseSevenN (P := P) n delay Lp Lf rep qq first)
    (hq : ∀ (q : QL delay Lp Lf P QChain) (a : Option (Fin 2))
      (ws : Fin (tL P tChain) → Window Γc Kc) (j : Fin (tL P tChain)),
      ((R.fpp.2.nx q a ws).2 j).1 = ws j ∨ ((R.fpp.2.nx q a ws).2 j).2 = 0) :
    NAMED_fppQuantum'' (P := P) (encPadN n delay Lp Lf rep) (SL qq first) :=
  PalPeg.CloseoutCoreEnc6.fppQuantum_of_det R.fpp hq

end PalPeg.CloseoutCoreEnc8

#print axioms PalPeg.CloseoutCoreEnc8.rd_padRN
#print axioms PalPeg.CloseoutCoreEnc8.room_padRN
#print axioms PalPeg.CloseoutCoreEnc8.padTapesN_one
#print axioms PalPeg.CloseoutCoreEnc8.margin_padTapesN
#print axioms PalPeg.CloseoutCoreEnc8.wlen_padTapesN
#print axioms PalPeg.CloseoutCoreEnc8.encPadN_one
#print axioms PalPeg.CloseoutCoreEnc8.roomOf_encPadN
#print axioms PalPeg.CloseoutCoreEnc8.widthMode_encPadN_iff_enc1
#print axioms PalPeg.CloseoutCoreEnc8.winOn_of_branch
#print axioms PalPeg.CloseoutCoreEnc8.winOn_id
#print axioms PalPeg.CloseoutCoreEnc8.winOn_ctlOnly
#print axioms PalPeg.CloseoutCoreEnc8.phaseWin_of_winOn
#print axioms PalPeg.CloseoutCoreEnc8.shiftStepW_pos
#print axioms PalPeg.CloseoutCoreEnc8.shiftStepW_neg
#print axioms PalPeg.CloseoutCoreEnc8.homeStepL_pos
#print axioms PalPeg.CloseoutCoreEnc8.markEndStepL_pos
#print axioms PalPeg.CloseoutCoreEnc8.chooseStepW_pos
#print axioms PalPeg.CloseoutCoreEnc8.rewindStepW_pair
#print axioms PalPeg.CloseoutCoreEnc8.winOn_shift_done
#print axioms PalPeg.CloseoutCoreEnc8.phaseWin_shift
#print axioms PalPeg.CloseoutCoreEnc8.phaseSevenN_of_pieces
#print axioms PalPeg.CloseoutCoreEnc8.residualTick_SL_N
#print axioms PalPeg.CloseoutCoreEnc8.widthTick_SL_N
#print axioms PalPeg.CloseoutCoreEnc8.coreLocal_SL_N
#print axioms PalPeg.CloseoutCoreEnc8.fppQuantum_SL
