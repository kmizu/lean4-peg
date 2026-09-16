import PalPeg.CloseoutCoreEnc8

/-!
# Closeout, step 2i: the branch reads, the per-step window residuals, the widths

`CloseoutCoreEnc8` leaves the seven phase modes of `CloseoutCoreAgree.SL` on the
widened layout `encPadN` as four named residuals:

* `NAMED_branchRead enc pred md` — the branch test of a mode is a window read;
* `NAMED_winOn enc f md sc` — the acting side of a branch is a window datum;
* `NAMED_shiftDoneQ` — the output refresh is a control-window function;
* `NAMED_widthEnc1 rep M md` — a mode's step conserves the stored width.

This file takes each of them apart. It builds no `LocalStep` and proves no new
dynamics, so

**無条件 PAL ∈ PEG は未完.**

## What is established (unconditional)

* **§1 (the `BranchRead` algebra).** `branchRead_congr`, `branchRead_not`,
  `branchRead_and`, `branchRead_or`, and `branchRead_ofCtl` (a test that looks
  only at the finite control). A branch read is therefore closed under the
  propositional structure of the predicate, so only its *atoms* are residual.
* **§2 (the control atoms, closed).** `clampCtl` clamps the clock and nothing
  else, so `ctl.odd` and `ctl.pair` survive into `QL` verbatim
  (`encPadN_odd`, `encPadN_pair`). Hence `branchRead_odd` and
  `branchRead_pair` hold outright, and `branchRead_chooseBr` reduces
  `CloseoutCoreEnc8.ChooseBr` — the `choose` test — to the MARKS read alone.
* **§3 (the focus atoms, reduced to two residuals).** `readWin_focus`: with the
  margin, window cell `idx Kc 1` *is* the cell under the head. So a predicate
  that is a `Fin 9` test of the focus of a laid-out `ProgLang` tape is a branch
  read (`branchRead_ofFocus`, using `sDp` injectivity through the
  `Sum.inr ∘ Sum.inr` shape of `Γc`). The two residuals left are
  `NAMED_focusMarks` and `NAMED_focusSource`: the layout carries MARKS (tape 8
  of the fpp buffer) and SOURCE (tape 7) at the head. From them
  `branchRead_atEnd`, `branchRead_atFirst`, `branchRead_markSet` and
  `branchRead_atLeft` — four of the six branch tests of `SL` — follow.
* **§4 (`RemPosL`, split).** `RemPosL = ShiftRemaining ∨ CopyRemaining` and
  `CopyRemaining` is a walker read *and* a work-counter zero test, so §1 splits
  the `shift`/`copy` test into the three counter/walker atoms
  `NAMED_shiftRem`, `NAMED_walkerRead`, `NAMED_workZero`
  (`branchRead_remPos`).
* **§5 (the acting branches, per step).** `WinPieces` lists the ten step-level
  window residuals `NAMED_winOn` of the seven modes — one per branch of
  `shiftStepW`, `copyStepL`, `homeStepL`, `markEndStepL`, `chooseStepW`,
  `rewindStepW`, plus the `fpp` quantum — and `phasePieces_of_winPieces`
  assembles them, with the branch reads of §1–§4, into
  `CloseoutCoreEnc8.PhasePieces`. This is the whole reduction of the six
  coarse `NAMED_phaseWin` fields of that bundle to step-level data.
* **§6 (the widths, per step).** `wlen_encTapes1` reduces `NAMED_widthEnc1` to
  the unshifted layout `encTapes`; a pure `Control` rewrite conserves it
  outright (`widthEnc_ctl`), and `widthEnc1_of_branches_*` derive the seven
  `NAMED_widthEnc1` obligations from the per-step residual `NAMED_widthStep`,
  branch by branch, along the case analysis of `CloseoutCoreEnc8` §3.

## What is *not* established

The atoms: `NAMED_focusMarks`, `NAMED_focusSource`, `NAMED_shiftRem`,
`NAMED_walkerRead`, `NAMED_workZero` (§3–§4), the ten `NAMED_winOn` fields of
`WinPieces` and `CloseoutCoreEnc8.NAMED_shiftDoneQ` (§5), and `NAMED_widthStep`
for the nine acting steps (§6). Each is stated for one step, or one atom, with
its exact type.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutCoreEnc9

open PalPeg PalPeg.Program
open PalPeg.Local (Window idx idx_val pos rd toList sweep readWin readWin_eq rd_pos LocalStep)
open PalPeg.GalilScaffoldChainInputSupply (ChainVM)
open PalPeg.GalilScaffoldController (Control Mode)
open PalPeg.LocalChain (ChainL)
open PalPeg.LocalReplayParked (Mirrored1 mirrorTick1)
open PalPeg.LocalSysConcrete (Steps Starved stepOf tickC)
open PalPeg.CloseoutCoreStep (Γc blankc tL QL qOfL)
open PalPeg.CloseoutCoreEnc (Kc encTapes QChain tChain qChainOf)
open PalPeg.CloseoutCoreEnc3 (encTapes1 shift1 margin_encTapes1)
open PalPeg.CloseoutCoreEnc5 (wlen)
open PalPeg.CloseoutCoreEnc6 (NAMED_phaseWin)
open PalPeg.CloseoutCoreAgree (SL MarkSetL AtFirstL shiftStepW shiftDoneCtlW chooseStepW
  rewindStepW ffppW)
open PalPeg.LocalRealizesPhase (AtLeftL AtEndL RemPosL copyStepL copyPick homeStepL
  markEndStepL shiftPick)
open PalPeg.GalilTickFun3 (marksOf sourceOf ShiftRemaining CopyRemaining)
open PalPeg.CloseoutCoreEnc8 (padTapesN encPadN rwOf WinOn BranchRead NAMED_branchRead
  NAMED_winOn NAMED_shiftDoneQ NAMED_widthEnc1 PhasePieces margin_encPadN
  rd_padTapesN winOn_of_branch stepOf_SL_shift stepOf_SL_copy stepOf_SL_home
  stepOf_SL_markEnd stepOf_SL_choose stepOf_SL_rewind stepOf_SL_fpp ChooseBr
  shiftStepW_pos shiftStepW_neg copyStepL_pos copyStepL_neg homeStepL_pos homeStepL_neg
  markEndStepL_pos markEndStepL_neg chooseStepW_pos chooseStepW_neg
  rewindStepW_pos rewindStepW_pair rewindStepW_one
  winOn_shift_done phaseWin_of_winOn winOn_congr)

variable {P : ℕ}

/-! ## 1. The `BranchRead` algebra -/

section Algebra

variable {Q : Type} {t : ℕ} {enc : Mirrored1 P → Q × (Fin t → STape Γc)} {md : Mode}

/-- A branch read transports along an equivalence of predicates. -/
def branchRead_congr {pred pred' : Mirrored1 P → Prop} (B : BranchRead Q t enc pred md)
    (h : ∀ m : Mirrored1 P, m.vm.ctl.mode = md → ¬ Starved m.vm → (pred m ↔ pred' m)) :
    BranchRead Q t enc pred' md where
  test := B.test
  spec := fun m hmd hs => (B.spec m hmd hs).trans (h m hmd hs)

/-- Negation. -/
def branchRead_not {pred : Mirrored1 P → Prop} (B : BranchRead Q t enc pred md) :
    BranchRead Q t enc (fun m => ¬ pred m) md where
  test := fun q ws => ! B.test q ws
  spec := fun m hmd hs => by
    rcases hb : B.test (enc m).1 (rwOf enc m) with _ | _
    · simp only [Bool.not_false, true_iff]
      intro hp
      exact absurd ((B.spec m hmd hs).mpr hp) (by simp [hb])
    · simp only [Bool.not_true, Bool.false_eq_true, false_iff, not_not]
      exact (B.spec m hmd hs).mp hb

/-- Conjunction. -/
def branchRead_and {p q : Mirrored1 P → Prop} (B : BranchRead Q t enc p md)
    (C : BranchRead Q t enc q md) : BranchRead Q t enc (fun m => p m ∧ q m) md where
  test := fun x ws => B.test x ws && C.test x ws
  spec := fun m hmd hs => by
    rw [Bool.and_eq_true]
    exact and_congr (B.spec m hmd hs) (C.spec m hmd hs)

/-- Disjunction. -/
def branchRead_or {p q : Mirrored1 P → Prop} (B : BranchRead Q t enc p md)
    (C : BranchRead Q t enc q md) : BranchRead Q t enc (fun m => p m ∨ q m) md where
  test := fun x ws => B.test x ws || C.test x ws
  spec := fun m hmd hs => by
    rw [Bool.or_eq_true]
    exact or_congr (B.spec m hmd hs) (C.spec m hmd hs)

/-- **A test that looks only at the finite control.** -/
def branchRead_ofCtl {pred : Mirrored1 P → Prop} (b : Q → Bool)
    (h : ∀ m : Mirrored1 P, m.vm.ctl.mode = md → ¬ Starved m.vm →
      (b (enc m).1 = true ↔ pred m)) :
    BranchRead Q t enc pred md where
  test := fun q _ => b q
  spec := h

end Algebra

/-! ## 2. The control atoms, closed -/

variable {n delay Lp Lf : ℕ} {rep : ChainVM → ChainL}

/-- `clampCtl` clamps the clock and nothing else. -/
theorem encPadN_odd (m : Mirrored1 P) :
    ((encPadN n delay Lp Lf rep m).1).1.val.odd = m.vm.ctl.odd := rfl

theorem encPadN_pair (m : Mirrored1 P) :
    ((encPadN n delay Lp Lf rep m).1).1.val.pair = m.vm.ctl.pair := rfl

theorem encPadN_mode (m : Mirrored1 P) :
    ((encPadN n delay Lp Lf rep m).1).1.val.mode = m.vm.ctl.mode := rfl

/-- **The parity bit is a branch read**, at every mode. -/
noncomputable def branchRead_odd (md : Mode) :
    NAMED_branchRead (P := P) (encPadN n delay Lp Lf rep) (fun m => m.vm.ctl.odd = true) md :=
  branchRead_ofCtl (fun q => q.1.val.odd) (fun m _ _ => by rw [encPadN_odd])

/-- **The pairing bit is a branch read**, at every mode. -/
noncomputable def branchRead_pair (md : Mode) :
    NAMED_branchRead (P := P) (encPadN n delay Lp Lf rep) (fun m => m.vm.ctl.pair = true) md :=
  branchRead_ofCtl (fun q => q.1.val.pair) (fun m _ _ => by rw [encPadN_pair])

/-! ## 3. The focus atoms -/

/-- **With the margin, window cell `idx Kc 1` is the cell under the head.** -/
theorem readWin_focus (T : STape Γc) (h1 : Kc ≤ pos T) :
    readWin blankc Kc T (idx Kc 1) = rd blankc T (pos T) := by
  rw [readWin_eq blankc Kc T (idx Kc 1), idx_val (show 1 ≤ 2 * Kc by simp [Kc])]
  simp only [Kc] at h1 ⊢
  congr 1
  omega

/-- **A `Fin 9` test of a laid-out `ProgLang` focus is a branch read.**
`g` is the focus the layout carries at index `i`, and `S` the test. -/
def branchRead_ofFocus {pred : Mirrored1 P → Prop} {md : Mode}
    (i : Fin (tL P tChain)) (g : Mirrored1 P → Fin 9) (S : Fin 9 → Bool)
    (hfocus : ∀ m : Mirrored1 P, m.vm.ctl.mode = md → ¬ Starved m.vm →
      rd blankc ((encPadN n delay Lp Lf rep m).2 i)
          (pos ((encPadN n delay Lp Lf rep m).2 i))
        = PalPeg.GalilVMEncode.sDp (g m))
    (hS : ∀ m : Mirrored1 P, m.vm.ctl.mode = md → ¬ Starved m.vm →
      (S (g m) = true ↔ pred m)) :
    NAMED_branchRead (P := P) (encPadN n delay Lp Lf rep) pred md where
  test := fun _ ws =>
    match ws i (idx Kc 1) with
    | Sum.inr (Sum.inr a) => S a
    | _ => false
  spec := fun m hmd hs => by
    have hw : rwOf (encPadN n delay Lp Lf rep) m i (idx Kc 1)
        = PalPeg.GalilVMEncode.sDp (g m) := by
      rw [rwOf, readWin_focus _ (margin_encPadN n delay Lp Lf rep m i)]
      exact hfocus m hmd hs
    rw [show (match rwOf (encPadN n delay Lp Lf rep) m i (idx Kc 1) with
        | Sum.inr (Sum.inr a) => S a
        | _ => false) = S (g m) from by rw [hw]; rfl]
    exact hS m hmd hs

/-- **A carrier for a focus residual**: an index of the layout whose head sits
on the cell `g m`. -/
structure FocusCarrier (n delay Lp Lf : ℕ) (rep : ChainVM → ChainL)
    (g : Mirrored1 P → Fin 9) (md : Mode) : Type where
  idx : Fin (tL P tChain)
  spec : ∀ m : Mirrored1 P, m.vm.ctl.mode = md → ¬ Starved m.vm →
    rd blankc ((encPadN n delay Lp Lf rep m).2 idx)
        (pos ((encPadN n delay Lp Lf rep m).2 idx))
      = PalPeg.GalilVMEncode.sDp (g m)

/-- **Residual: the layout carries MARKS at the head.**  MARKS is tape `8` of
the fpp program; `CloseoutCoreEnc.bufTapes` lays the fpp buffer out with
`dpSTape`, so the claim is that the head of that tape sits on the cell
`GalilScaffoldTape.Tape.focus` of `marksOf (abs' m.vm)`. -/
def NAMED_focusMarks (n delay Lp Lf : ℕ) (rep : ChainVM → ChainL) (md : Mode) : Type :=
  FocusCarrier (P := P) n delay Lp Lf rep
    (fun m => (marksOf (PalPeg.LocalArrival.abs' m.vm)).focus) md

/-- **Residual: the layout carries SOURCE at the head** (tape `7`). -/
def NAMED_focusSource (n delay Lp Lf : ℕ) (rep : ChainVM → ChainL) (md : Mode) : Type :=
  FocusCarrier (P := P) n delay Lp Lf rep
    (fun m => (sourceOf (PalPeg.LocalArrival.abs' m.vm)).focus) md

/-- **`AtEndL` is a branch read**, from the MARKS residual. -/
noncomputable def branchRead_atEnd {md : Mode}
    (h : NAMED_focusMarks (P := P) n delay Lp Lf rep md) :
    NAMED_branchRead (P := P) (encPadN n delay Lp Lf rep) (fun m => AtEndL m.vm) md := by
  classical
  exact branchRead_ofFocus h.idx (fun m => (marksOf (PalPeg.LocalArrival.abs' m.vm)).focus)
    (fun a => decide (a = 5)) h.spec (fun m _ _ => by simp [AtEndL])

/-- **`AtFirstL` is a branch read.** -/
noncomputable def branchRead_atFirst {md : Mode} (first : Fin 9)
    (h : NAMED_focusMarks (P := P) n delay Lp Lf rep md) :
    NAMED_branchRead (P := P) (encPadN n delay Lp Lf rep)
      (fun m => AtFirstL first (PalPeg.LocalArrival.abs' m.vm)) md := by
  classical
  exact branchRead_ofFocus h.idx (fun m => (marksOf (PalPeg.LocalArrival.abs' m.vm)).focus)
    (fun a => decide (a = first)) h.spec (fun m _ _ => by simp [AtFirstL])

/-- **`MarkSetL` is a branch read.** -/
noncomputable def branchRead_markSet {md : Mode} (first : Fin 9)
    (h : NAMED_focusMarks (P := P) n delay Lp Lf rep md) :
    NAMED_branchRead (P := P) (encPadN n delay Lp Lf rep)
      (fun m => MarkSetL first (PalPeg.LocalArrival.abs' m.vm)) md := by
  classical
  exact branchRead_ofFocus h.idx (fun m => (marksOf (PalPeg.LocalArrival.abs' m.vm)).focus)
    (fun a => decide (a = 8) || decide (a = first)) h.spec (fun m _ _ => by simp [MarkSetL])

/-- **`AtLeftL` is a branch read**, from the SOURCE residual. -/
noncomputable def branchRead_atLeft {md : Mode}
    (h : NAMED_focusSource (P := P) n delay Lp Lf rep md) :
    NAMED_branchRead (P := P) (encPadN n delay Lp Lf rep) (fun m => AtLeftL m.vm) md := by
  classical
  exact branchRead_ofFocus h.idx (fun m => (sourceOf (PalPeg.LocalArrival.abs' m.vm)).focus)
    (fun a => decide (a = 4)) h.spec (fun m _ _ => by simp [AtLeftL])

/-- **The `choose` test, reduced to the MARKS read.**  Its parity half is §2. -/
noncomputable def branchRead_chooseBr (first : Fin 9)
    (h : NAMED_focusMarks (P := P) n delay Lp Lf rep .choose) :
    NAMED_branchRead (P := P) (encPadN n delay Lp Lf rep)
      (fun m => ChooseBr first m) .choose :=
  branchRead_and (branchRead_odd .choose) (branchRead_markSet first h)

/-! ## 4. `RemPosL`, split into its three atoms -/

/-- **Residual: the sign of `remaining` is a window read.** -/
def NAMED_shiftRem (n delay Lp Lf : ℕ) (rep : ChainVM → ChainL) (md : Mode) : Type :=
  NAMED_branchRead (P := P) (encPadN n delay Lp Lf rep)
    (fun m => ShiftRemaining (PalPeg.LocalArrival.abs' m.vm)) md

/-- **Residual: "the copy walker reads no letter" is a window read.** -/
def NAMED_walkerRead (n delay Lp Lf : ℕ) (rep : ChainVM → ChainL) (md : Mode) : Type :=
  NAMED_branchRead (P := P) (encPadN n delay Lp Lf rep)
    (fun m => GalilScaffoldPlace.read (PalPeg.LocalArrival.abs' m.vm).fpp.walker = none) md

/-- **Residual: "the work counter is zero" is a window read.** -/
def NAMED_workZero (n delay Lp Lf : ℕ) (rep : ChainVM → ChainL) (md : Mode) : Type :=
  NAMED_branchRead (P := P) (encPadN n delay Lp Lf rep)
    (fun m => GalilScaffoldCounter.zero (PalPeg.LocalArrival.abs' m.vm).fpp.work = true) md

/-- **`RemPosL` is a branch read**, from the three atoms. -/
noncomputable def branchRead_remPos {md : Mode}
    (Bs : NAMED_shiftRem (P := P) n delay Lp Lf rep md)
    (Bw : NAMED_walkerRead (P := P) n delay Lp Lf rep md)
    (Bz : NAMED_workZero (P := P) n delay Lp Lf rep md) :
    NAMED_branchRead (P := P) (encPadN n delay Lp Lf rep) (fun m => RemPosL m.vm) md :=
  branchRead_congr (branchRead_or Bs (branchRead_not (branchRead_or Bw Bz)))
    (fun m _ _ => Iff.rfl)

/-! ## 5. The acting branches, one residual per step -/

section Acting

variable (n delay Lp Lf) (rep) (qq : ℕ) (first : Fin 9)

/-- **The ten step-level window residuals of the seven phase modes.**  Every
field is one branch of one mode's step, with the side condition under which
`CloseoutCoreEnc8` §3 shows that branch is taken.  `shiftDone` is not here: it
is `CloseoutCoreEnc8.NAMED_shiftDoneQ`, and its tape half is already closed. -/
structure WinPieces : Type where
  /-- `shift`, acting branch: one unit of `stepShift`. -/
  shiftPick : NAMED_winOn (P := P) (encPadN n delay Lp Lf rep)
    (fun m => shiftPick m.vm.chain m.vm m.mirL) .shift (fun m => True ∧ RemPosL m.vm)
  /-- `copy`, acting branch: one window cell onto SOURCE. -/
  copyPick : NAMED_winOn (P := P) (encPadN n delay Lp Lf rep)
    (fun m => copyPick (GalilScaffoldPlace.read (PalPeg.LocalArrival.abs' m.vm).fpp.walker) m)
    .copy (fun m => True ∧ RemPosL m.vm)
  /-- `copy`, exit branch: `source.write(END)` and into `home`. -/
  copyDone : NAMED_winOn (P := P) (encPadN n delay Lp Lf rep)
    (fun m => (⟨PalPeg.LocalTick3.copyDoneVm { m.vm.ctl with mode := .home } m.vm, m.mirL⟩ :
      Mirrored1 P)) .copy (fun m => True ∧ ¬ RemPosL m.vm)
  /-- `home`, exit branch: `fpp.start()`. -/
  homeStart : NAMED_winOn (P := P) (encPadN n delay Lp Lf rep)
    (fun m => (⟨PalPeg.LocalTick3.homeStartVm { m.vm.ctl with mode := .fpp } m.vm, m.mirL⟩ :
      Mirrored1 P)) .home (fun m => True ∧ AtLeftL m.vm)
  /-- `home`, acting branch: one cell left on SOURCE. -/
  homeStep : NAMED_winOn (P := P) (encPadN n delay Lp Lf rep)
    (fun m => (⟨PalPeg.LocalTick3.homeStepVm m.vm, m.mirL⟩ : Mirrored1 P))
    .home (fun m => True ∧ ¬ AtLeftL m.vm)
  /-- `markEnd`, exit branch: MARKS left, into `choose`. -/
  markEndDone : NAMED_winOn (P := P) (encPadN n delay Lp Lf rep)
    (fun m => (⟨PalPeg.LocalTick3.marksVm GalilScaffoldTape.moveLeft
      { m.vm.ctl with mode := .choose, odd := false } m.vm, m.mirL⟩ : Mirrored1 P))
    .markEnd (fun m => True ∧ AtEndL m.vm)
  /-- `markEnd`, acting branch: MARKS right. -/
  markEndStep : NAMED_winOn (P := P) (encPadN n delay Lp Lf rep)
    (fun m => (⟨PalPeg.LocalTick3.marksVm GalilScaffoldTape.moveRight m.vm.ctl m.vm, m.mirL⟩ :
      Mirrored1 P)) .markEnd (fun m => True ∧ ¬ AtEndL m.vm)
  /-- `choose`, select branch: `choose_select`, into `rewind`. -/
  chooseSelect : NAMED_winOn (P := P) (encPadN n delay Lp Lf rep)
    (fun m => mirrorTick1 .stay (PalPeg.LocalTick3.chooseVm
      { m.vm.ctl with mode := .rewind, pair := false } m.vm) m)
    .choose (fun m => True ∧ ChooseBr first m)
  /-- `choose`, scan branch: MARKS left and the parity flips. -/
  chooseScan : NAMED_winOn (P := P) (encPadN n delay Lp Lf rep)
    (fun m => mirrorTick1 .stay (PalPeg.LocalTick3.marksVm GalilScaffoldTape.moveLeft
      { m.vm.ctl with odd := !m.vm.ctl.odd } m.vm) m)
    .choose (fun m => True ∧ ¬ ChooseBr first m)
  /-- `rewind`, exit branch: `fpp.reset()`, into `replayStart`. -/
  rewindDone : NAMED_winOn (P := P) (encPadN n delay Lp Lf rep)
    (fun m => mirrorTick1 .stay (PalPeg.LocalTick3.rewindDoneVm
      { m.vm.ctl with mode := .replayStart } m.vm) m)
    .rewind (fun m => True ∧ AtFirstL first (PalPeg.LocalArrival.abs' m.vm))
  /-- `rewind`, paired branch: MARKS left, L left, C left, `length++`, `radius++`. -/
  rewindPair : NAMED_winOn (P := P) (encPadN n delay Lp Lf rep)
    (fun m => mirrorTick1 .left (PalPeg.LocalTick3.rewindPairVm
      { m.vm.ctl with pair := false } m.vm) m)
    .rewind (fun m => (True ∧ ¬ AtFirstL first (PalPeg.LocalArrival.abs' m.vm))
      ∧ m.vm.ctl.pair = true)
  /-- `rewind`, single branch: MARKS left, L left, `length++`. -/
  rewindOne : NAMED_winOn (P := P) (encPadN n delay Lp Lf rep)
    (fun m => mirrorTick1 .stay (PalPeg.LocalTick3.rewindOneVm
      { m.vm.ctl with pair := true } m.vm) m)
    .rewind (fun m => (True ∧ ¬ AtFirstL first (PalPeg.LocalArrival.abs' m.vm))
      ∧ ¬ m.vm.ctl.pair = true)
  /-- `fpp`: one `GalilDpCode` instruction in a fixed window. -/
  fpp : NAMED_winOn (P := P) (encPadN n delay Lp Lf rep)
    (fun m => ffppW qq first m) .fpp (fun _ => True)

/-- **The branch reads of the seven phase modes**, as the atoms §1–§4 leave. -/
structure ReadPieces : Type where
  shiftRem : NAMED_shiftRem (P := P) n delay Lp Lf rep .shift
  shiftWalker : NAMED_walkerRead (P := P) n delay Lp Lf rep .shift
  shiftWork : NAMED_workZero (P := P) n delay Lp Lf rep .shift
  copyRem : NAMED_shiftRem (P := P) n delay Lp Lf rep .copy
  copyWalker : NAMED_walkerRead (P := P) n delay Lp Lf rep .copy
  copyWork : NAMED_workZero (P := P) n delay Lp Lf rep .copy
  homeSource : NAMED_focusSource (P := P) n delay Lp Lf rep .home
  markEndMarks : NAMED_focusMarks (P := P) n delay Lp Lf rep .markEnd
  chooseMarks : NAMED_focusMarks (P := P) n delay Lp Lf rep .choose
  rewindMarks : NAMED_focusMarks (P := P) n delay Lp Lf rep .rewind

variable {n delay Lp Lf rep qq first}

/-- **`copy`'s phase residual**, from its two branches. -/
noncomputable def phaseWin_copy (R : ReadPieces (P := P) n delay Lp Lf rep)
    (W : WinPieces (P := P) n delay Lp Lf rep qq first) :
    NAMED_phaseWin (encPadN n delay Lp Lf rep) (SL (P := P) qq first) .copy :=
  phaseWin_of_winOn
    (winOn_of_branch (fun m => RemPosL m.vm) _ _ _
      (branchRead_remPos R.copyRem R.copyWalker R.copyWork) W.copyPick W.copyDone
      (fun m hmd hs _ hp => by rw [stepOf_SL_copy, copyStepL_pos m hp])
      (fun m hmd hs _ hp => by rw [stepOf_SL_copy, copyStepL_neg m hp]))

/-- **`home`'s phase residual.** -/
noncomputable def phaseWin_home (R : ReadPieces (P := P) n delay Lp Lf rep)
    (W : WinPieces (P := P) n delay Lp Lf rep qq first) :
    NAMED_phaseWin (encPadN n delay Lp Lf rep) (SL (P := P) qq first) .home :=
  phaseWin_of_winOn
    (winOn_of_branch (fun m => AtLeftL m.vm) _ _ _
      (branchRead_atLeft R.homeSource) W.homeStart W.homeStep
      (fun m hmd hs _ hp => by rw [stepOf_SL_home, homeStepL_pos m hp])
      (fun m hmd hs _ hp => by rw [stepOf_SL_home, homeStepL_neg m hp]))

/-- **`markEnd`'s phase residual.** -/
noncomputable def phaseWin_markEnd (R : ReadPieces (P := P) n delay Lp Lf rep)
    (W : WinPieces (P := P) n delay Lp Lf rep qq first) :
    NAMED_phaseWin (encPadN n delay Lp Lf rep) (SL (P := P) qq first) .markEnd :=
  phaseWin_of_winOn
    (winOn_of_branch (fun m => AtEndL m.vm) _ _ _
      (branchRead_atEnd R.markEndMarks) W.markEndDone W.markEndStep
      (fun m hmd hs _ hp => by rw [stepOf_SL_markEnd, markEndStepL_pos m hp])
      (fun m hmd hs _ hp => by rw [stepOf_SL_markEnd, markEndStepL_neg m hp]))

/-- **`choose`'s phase residual.** -/
noncomputable def phaseWin_choose (R : ReadPieces (P := P) n delay Lp Lf rep)
    (W : WinPieces (P := P) n delay Lp Lf rep qq first) :
    NAMED_phaseWin (encPadN n delay Lp Lf rep) (SL (P := P) qq first) .choose :=
  phaseWin_of_winOn
    (winOn_of_branch (fun m => ChooseBr first m) _ _ _
      (branchRead_chooseBr first R.chooseMarks) W.chooseSelect W.chooseScan
      (fun m hmd hs _ hp => by rw [stepOf_SL_choose, chooseStepW_pos first m hp])
      (fun m hmd hs _ hp => by rw [stepOf_SL_choose, chooseStepW_neg first m hp]))

/-- **`rewind`'s phase residual**, from its *three* branches: the `pair` test is
nested under the negative side of the `atFirst` test. -/
noncomputable def phaseWin_rewind (R : ReadPieces (P := P) n delay Lp Lf rep)
    (W : WinPieces (P := P) n delay Lp Lf rep qq first) :
    NAMED_phaseWin (encPadN n delay Lp Lf rep) (SL (P := P) qq first) .rewind :=
  phaseWin_of_winOn
    (winOn_of_branch (fun m => AtFirstL first (PalPeg.LocalArrival.abs' m.vm)) _ _ _
      (branchRead_atFirst first R.rewindMarks) W.rewindDone
      (winOn_of_branch (fun m => m.vm.ctl.pair = true) (fun m => rewindStepW first m) _ _
        (branchRead_pair .rewind) W.rewindPair W.rewindOne
        (fun m hmd hs hsc hp => by rw [rewindStepW_pair first m hsc.2 hp])
        (fun m hmd hs hsc hp => by rw [rewindStepW_one first m hsc.2 hp]))
      (fun m hmd hs _ hp => by rw [stepOf_SL_rewind, rewindStepW_pos first m hp])
      (fun m hmd hs _ hp => by rw [stepOf_SL_rewind]))

/-- **`fpp`'s phase residual.** -/
noncomputable def phaseWin_fpp (W : WinPieces (P := P) n delay Lp Lf rep qq first) :
    NAMED_phaseWin (encPadN n delay Lp Lf rep) (SL (P := P) qq first) .fpp :=
  phaseWin_of_winOn (winOn_congr W.fpp (fun m _ _ _ => stepOf_SL_fpp qq first m))

/-- **The bundle of `CloseoutCoreEnc8`, from step-level data.**  This is the
whole reduction: the six coarse `NAMED_phaseWin` fields of `PhasePieces` become
the ten `NAMED_winOn` fields of `WinPieces` plus the ten atoms of
`ReadPieces`. -/
noncomputable def phasePieces_of_pieces (R : ReadPieces (P := P) n delay Lp Lf rep)
    (W : WinPieces (P := P) n delay Lp Lf rep qq first)
    (D : NAMED_shiftDoneQ (P := P) n delay Lp Lf rep) :
    PhasePieces (P := P) n delay Lp Lf rep qq first where
  shiftBr := branchRead_remPos R.shiftRem R.shiftWalker R.shiftWork
  shiftPick := W.shiftPick
  shiftDone := D
  copy := phaseWin_copy R W
  home := phaseWin_home R W
  fpp := phaseWin_fpp W
  markEnd := phaseWin_markEnd R W
  choose := phaseWin_choose R W
  rewind := phaseWin_rewind R W

end Acting

/-! ## 6. The widths, one residual per step -/

/-- **Residual: one branch conserves the stored width of the layout.** -/
def NAMED_widthStep (rep : ChainVM → ChainL) (f : Mirrored1 P → Mirrored1 P)
    (md : Mode) (sc : Mirrored1 P → Prop) : Prop :=
  ∀ (m : Mirrored1 P) (i : ℕ), m.vm.ctl.mode = md → ¬ Starved m.vm → sc m →
    wlen (encTapes1 rep (f m) i) = wlen (encTapes1 rep m i)

/-- **A pure `Control` rewrite conserves the width**, at every index: the layout
reads no field of `Control`. -/
theorem widthStep_ctl (m : Mirrored1 P) (c : Control) (i : ℕ) :
    wlen (encTapes1 rep (⟨{ m.vm with ctl := c }, m.mirL⟩ : Mirrored1 P) i)
      = wlen (encTapes1 rep m i) := rfl

/-- The reservoir cancels: the width obligation lives on the sentinel layout,
and the sentinel adds one cell to every tape. -/
theorem wlen_encTapes1 (rep : ChainVM → ChainL) (m : Mirrored1 P) (i : ℕ) :
    wlen (encTapes1 rep m i) = wlen (encTapes rep m i) + 1 := by
  simp only [encTapes1, wlen, shift1, pos, List.length_append, List.length_cons,
    List.length_nil]
  omega

/-- **Splitting a width obligation along a branch.** -/
theorem widthEnc1_of_branch {M : Steps P} {md : Mode} (pred : Mirrored1 P → Prop)
    (f g : Mirrored1 P → Mirrored1 P)
    (hf : NAMED_widthStep (P := P) rep f md (fun m => pred m))
    (hg : NAMED_widthStep (P := P) rep g md (fun m => ¬ pred m))
    (hpos : ∀ m : Mirrored1 P, m.vm.ctl.mode = md → ¬ Starved m.vm → pred m →
      stepOf M md m = f m)
    (hneg : ∀ m : Mirrored1 P, m.vm.ctl.mode = md → ¬ Starved m.vm → ¬ pred m →
      stepOf M md m = g m) :
    NAMED_widthEnc1 (P := P) rep M md := by
  classical
  intro m i hmd hs
  by_cases hp : pred m
  · rw [hpos m hmd hs hp]; exact hf m i hmd hs hp
  · rw [hneg m hmd hs hp]; exact hg m i hmd hs hp

/-- **`shift`'s width, from its acting branch alone**: the exit branch rewrites
`Control` only. -/
theorem widthEnc1_shift {qq : ℕ} {first : Fin 9}
    (h : NAMED_widthStep (P := P) rep (fun m => shiftPick m.vm.chain m.vm m.mirL)
      .shift (fun m => RemPosL m.vm)) :
    NAMED_widthEnc1 (P := P) rep (SL qq first) .shift :=
  widthEnc1_of_branch (fun m => RemPosL m.vm) _ _ h
    (fun m i _ _ _ => widthStep_ctl m _ i)
    (fun m hmd hs hp => by rw [stepOf_SL_shift, shiftStepW_pos m hp])
    (fun m hmd hs hp => by rw [stepOf_SL_shift, shiftStepW_neg m hp])

theorem widthEnc1_copy {qq : ℕ} {first : Fin 9}
    (hp : NAMED_widthStep (P := P) rep
      (fun m => copyPick (GalilScaffoldPlace.read (PalPeg.LocalArrival.abs' m.vm).fpp.walker) m)
      .copy (fun m => RemPosL m.vm))
    (hn : NAMED_widthStep (P := P) rep
      (fun m => (⟨PalPeg.LocalTick3.copyDoneVm { m.vm.ctl with mode := .home } m.vm, m.mirL⟩ :
        Mirrored1 P)) .copy (fun m => ¬ RemPosL m.vm)) :
    NAMED_widthEnc1 (P := P) rep (SL qq first) .copy :=
  widthEnc1_of_branch (fun m => RemPosL m.vm) _ _ hp hn
    (fun m hmd hs h => by rw [stepOf_SL_copy, copyStepL_pos m h])
    (fun m hmd hs h => by rw [stepOf_SL_copy, copyStepL_neg m h])

theorem widthEnc1_home {qq : ℕ} {first : Fin 9}
    (hp : NAMED_widthStep (P := P) rep
      (fun m => (⟨PalPeg.LocalTick3.homeStartVm { m.vm.ctl with mode := .fpp } m.vm, m.mirL⟩ :
        Mirrored1 P)) .home (fun m => AtLeftL m.vm))
    (hn : NAMED_widthStep (P := P) rep
      (fun m => (⟨PalPeg.LocalTick3.homeStepVm m.vm, m.mirL⟩ : Mirrored1 P))
      .home (fun m => ¬ AtLeftL m.vm)) :
    NAMED_widthEnc1 (P := P) rep (SL qq first) .home :=
  widthEnc1_of_branch (fun m => AtLeftL m.vm) _ _ hp hn
    (fun m hmd hs h => by rw [stepOf_SL_home, homeStepL_pos m h])
    (fun m hmd hs h => by rw [stepOf_SL_home, homeStepL_neg m h])

theorem widthEnc1_markEnd {qq : ℕ} {first : Fin 9}
    (hp : NAMED_widthStep (P := P) rep
      (fun m => (⟨PalPeg.LocalTick3.marksVm GalilScaffoldTape.moveLeft
        { m.vm.ctl with mode := .choose, odd := false } m.vm, m.mirL⟩ : Mirrored1 P))
      .markEnd (fun m => AtEndL m.vm))
    (hn : NAMED_widthStep (P := P) rep
      (fun m => (⟨PalPeg.LocalTick3.marksVm GalilScaffoldTape.moveRight m.vm.ctl m.vm, m.mirL⟩ :
        Mirrored1 P)) .markEnd (fun m => ¬ AtEndL m.vm)) :
    NAMED_widthEnc1 (P := P) rep (SL qq first) .markEnd :=
  widthEnc1_of_branch (fun m => AtEndL m.vm) _ _ hp hn
    (fun m hmd hs h => by rw [stepOf_SL_markEnd, markEndStepL_pos m h])
    (fun m hmd hs h => by rw [stepOf_SL_markEnd, markEndStepL_neg m h])

theorem widthEnc1_choose {qq : ℕ} {first : Fin 9}
    (hp : NAMED_widthStep (P := P) rep
      (fun m => mirrorTick1 .stay (PalPeg.LocalTick3.chooseVm
        { m.vm.ctl with mode := .rewind, pair := false } m.vm) m)
      .choose (fun m => ChooseBr first m))
    (hn : NAMED_widthStep (P := P) rep
      (fun m => mirrorTick1 .stay (PalPeg.LocalTick3.marksVm GalilScaffoldTape.moveLeft
        { m.vm.ctl with odd := !m.vm.ctl.odd } m.vm) m)
      .choose (fun m => ¬ ChooseBr first m)) :
    NAMED_widthEnc1 (P := P) rep (SL qq first) .choose :=
  widthEnc1_of_branch (fun m => ChooseBr first m) _ _ hp hn
    (fun m hmd hs h => by rw [stepOf_SL_choose, chooseStepW_pos first m h])
    (fun m hmd hs h => by rw [stepOf_SL_choose, chooseStepW_neg first m h])

/-- **`rewind`'s width, from its three branches.** -/
theorem widthEnc1_rewind {qq : ℕ} {first : Fin 9}
    (hd : NAMED_widthStep (P := P) rep
      (fun m => mirrorTick1 .stay (PalPeg.LocalTick3.rewindDoneVm
        { m.vm.ctl with mode := .replayStart } m.vm) m)
      .rewind (fun m => AtFirstL first (PalPeg.LocalArrival.abs' m.vm)))
    (hp : NAMED_widthStep (P := P) rep
      (fun m => mirrorTick1 .left (PalPeg.LocalTick3.rewindPairVm
        { m.vm.ctl with pair := false } m.vm) m)
      .rewind (fun m => ¬ AtFirstL first (PalPeg.LocalArrival.abs' m.vm) ∧ m.vm.ctl.pair = true))
    (ho : NAMED_widthStep (P := P) rep
      (fun m => mirrorTick1 .stay (PalPeg.LocalTick3.rewindOneVm
        { m.vm.ctl with pair := true } m.vm) m)
      .rewind (fun m => ¬ AtFirstL first (PalPeg.LocalArrival.abs' m.vm)
        ∧ ¬ m.vm.ctl.pair = true)) :
    NAMED_widthEnc1 (P := P) rep (SL qq first) .rewind := by
  classical
  intro m i hmd hs
  by_cases h1 : AtFirstL first (PalPeg.LocalArrival.abs' m.vm)
  · rw [stepOf_SL_rewind, rewindStepW_pos first m h1]
    exact hd m i hmd hs h1
  · by_cases h2 : m.vm.ctl.pair = true
    · rw [stepOf_SL_rewind, rewindStepW_pair first m h1 h2]
      exact hp m i hmd hs ⟨h1, h2⟩
    · rw [stepOf_SL_rewind, rewindStepW_one first m h1 h2]
      exact ho m i hmd hs ⟨h1, h2⟩

/-- **`fpp`'s width** is one residual: the quantum is not branched here. -/
theorem widthEnc1_fpp {qq : ℕ} {first : Fin 9}
    (h : NAMED_widthStep (P := P) rep (fun m => ffppW qq first m) .fpp (fun _ => True)) :
    NAMED_widthEnc1 (P := P) rep (SL qq first) .fpp :=
  fun m i hmd hs => by rw [stepOf_SL_fpp]; exact h m i hmd hs trivial

end PalPeg.CloseoutCoreEnc9

#print axioms PalPeg.CloseoutCoreEnc9.branchRead_congr
#print axioms PalPeg.CloseoutCoreEnc9.branchRead_not
#print axioms PalPeg.CloseoutCoreEnc9.branchRead_and
#print axioms PalPeg.CloseoutCoreEnc9.branchRead_or
#print axioms PalPeg.CloseoutCoreEnc9.branchRead_ofCtl
#print axioms PalPeg.CloseoutCoreEnc9.encPadN_odd
#print axioms PalPeg.CloseoutCoreEnc9.encPadN_pair
#print axioms PalPeg.CloseoutCoreEnc9.branchRead_odd
#print axioms PalPeg.CloseoutCoreEnc9.branchRead_pair
#print axioms PalPeg.CloseoutCoreEnc9.readWin_focus
#print axioms PalPeg.CloseoutCoreEnc9.branchRead_ofFocus
#print axioms PalPeg.CloseoutCoreEnc9.branchRead_atEnd
#print axioms PalPeg.CloseoutCoreEnc9.branchRead_atFirst
#print axioms PalPeg.CloseoutCoreEnc9.branchRead_markSet
#print axioms PalPeg.CloseoutCoreEnc9.branchRead_atLeft
#print axioms PalPeg.CloseoutCoreEnc9.branchRead_chooseBr
#print axioms PalPeg.CloseoutCoreEnc9.branchRead_remPos
#print axioms PalPeg.CloseoutCoreEnc9.phaseWin_copy
#print axioms PalPeg.CloseoutCoreEnc9.phaseWin_home
#print axioms PalPeg.CloseoutCoreEnc9.phaseWin_markEnd
#print axioms PalPeg.CloseoutCoreEnc9.phaseWin_choose
#print axioms PalPeg.CloseoutCoreEnc9.phaseWin_rewind
#print axioms PalPeg.CloseoutCoreEnc9.phaseWin_fpp
#print axioms PalPeg.CloseoutCoreEnc9.phasePieces_of_pieces
#print axioms PalPeg.CloseoutCoreEnc9.widthStep_ctl
#print axioms PalPeg.CloseoutCoreEnc9.wlen_encTapes1
#print axioms PalPeg.CloseoutCoreEnc9.widthEnc1_of_branch
#print axioms PalPeg.CloseoutCoreEnc9.widthEnc1_shift
#print axioms PalPeg.CloseoutCoreEnc9.widthEnc1_copy
#print axioms PalPeg.CloseoutCoreEnc9.widthEnc1_home
#print axioms PalPeg.CloseoutCoreEnc9.widthEnc1_markEnd
#print axioms PalPeg.CloseoutCoreEnc9.widthEnc1_choose
#print axioms PalPeg.CloseoutCoreEnc9.widthEnc1_rewind
#print axioms PalPeg.CloseoutCoreEnc9.widthEnc1_fpp
