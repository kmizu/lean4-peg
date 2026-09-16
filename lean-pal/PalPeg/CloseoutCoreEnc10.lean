import PalPeg.CloseoutCoreEnc9

/-!
# Closeout, step 2j: the per-step window residuals, reduced to tape actions

`CloseoutCoreEnc9` leaves the acting branches of the seven phase modes as
thirteen `NAMED_winOn` residuals — one per branch of one mode's step — and the
widths as nine `NAMED_widthStep` residuals.  Both families are still stated in
terms of *windows*: a `WinOn` must exhibit a window function `nx` computing the
next control and, per tape, a window and a displacement.

This file removes the window layer.  It builds no `LocalStep` and proves no new
dynamics, so

**無条件 PAL ∈ PEG は未完.**

## What is established (unconditional)

* **§1 (the window calculus of one micro-action).**  `teq_sweep_of_witness`
  turns an explicit `WinRealizes` witness into a literal `TEq … (sweep …)` — the
  form `WinOn.tape` wants — where `CloseoutCoreEnc4.sweep_of_winRealizes` only
  gives an existential.  `teq_sweep_act` then computes that witness for one
  optional micro-action: the new window is the old window with the head cell
  overwritten (`winAct`), and the displacement is the move (`dOfAct`).  Both
  are *functions of the read window*, which is exactly what `WinOn.nx` must be.
* **§2 (`TapeAct` ⟹ `WinOn`).**  A `TapeAct` says: the next control is a window
  function, and *each* laid-out tape of the successor state is literally the old
  tape acted on by an optional micro-action chosen by that same window function.
  `winOn_of_tapeAct` turns it into a `NAMED_winOn`.  `tapeAct_mono` weakens the
  side condition.  Hence the thirteen window residuals of
  `CloseoutCoreEnc9.WinPieces` become thirteen *tape* residuals (`ActPieces`,
  `winPieces_of_actPieces`): plain statements about what one VM function does to
  one tape, with no window bookkeeping left in them.
* **§3 (the widths, closed on the reservoir).**  `wlen_actOn`: on a tape whose
  head is strictly inside the stored region, **every** micro-action conserves
  the stored width — a right move eats the reservoir, which is itself part of
  `wlen`.  `room_padTapesN` supplies that strictness for `Kc ≤ n`, so
  `widthStep_of_tapeAct` derives a `NAMED_widthStep` from the *same* `TapeAct`
  with no new hypothesis, and `widthEnc1_of_actPieces` discharges all seven
  `NAMED_widthEnc1` obligations of `CloseoutCoreEnc9` §6 at once.  The nine
  `NAMED_widthStep` residuals are therefore **closed** relative to `ActPieces`.

## What is *not* established

The thirteen `NAMED_act…` fields of `ActPieces` (§2), each stated for one branch
of one mode with its exact type; `CloseoutCoreEnc8.NAMED_shiftDoneQ`; and the
five read atoms of `CloseoutCoreEnc9` §3–§4 (`NAMED_focusMarks`,
`NAMED_focusSource`, `NAMED_shiftRem`, `NAMED_walkerRead`, `NAMED_workZero`).

A note on the two focus atoms, recorded here because it constrains how they can
be discharged: `CloseoutCoreEnc9.FocusCarrier` asks for a **fixed** layout index
carrying MARKS (resp. SOURCE) under the head, while
`LocalArrival.abs'` reads the fpp tapes through `LocalBuffers.abs`, which selects
the `A` bank or the `B` bank according to `fppBuf.active`, and
`CloseoutCoreEnc.bufTapes` lays those two banks out at *different* indices.  So a
fixed index can only work on a set of states where `fppBuf.active` is constant;
otherwise the carrier must be selected by the finite control.  `FocusCarrier2`
below is that control-selected form, and `focusCarrier_of_focusCarrier2` is the
exact extra input (`active` is constant on the mode) that collapses it to the
fixed-index form `CloseoutCoreEnc9` expects.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutCoreEnc10

open PalPeg PalPeg.Program
open PalPeg.Local (Window idx idx_val pos rd toList sweep readWin readWin_eq rd_pos
  pos_sweep rd_sweep pos_applyAction rd_applyAction)
open PalPeg.GalilScaffoldChainInputSupply (ChainVM)
open PalPeg.GalilScaffoldController (Control Mode)
open PalPeg.LocalChain (ChainL)
open PalPeg.LocalReplayParked (Mirrored1 mirrorTick1)
open PalPeg.LocalSysConcrete (Steps Starved stepOf)
open PalPeg.CloseoutCoreStep (Γc blankc tL QL qOfL)
open PalPeg.CloseoutCoreEnc (Kc encTapes QChain tChain qChainOf)
open PalPeg.CloseoutCoreEnc3 (encTapes1)
open PalPeg.CloseoutCoreEnc4 (TEq)
open PalPeg.CloseoutCoreEnc5 (wlen wlen_left wlen_stay wlen_right)
open PalPeg.CloseoutCoreAgree (SL AtFirstL ffppW)
open PalPeg.LocalRealizesPhase (AtLeftL AtEndL RemPosL copyPick shiftPick)
open PalPeg.CloseoutCoreEnc8 (padTapesN encPadN rwOf WinOn BranchRead NAMED_branchRead
  NAMED_winOn NAMED_shiftDoneQ NAMED_widthEnc1 margin_encPadN wlen_padTapesN
  room_padTapesN ChooseBr)
open PalPeg.CloseoutCoreEnc9 (WinPieces NAMED_widthStep widthStep_ctl
  widthEnc1_shift widthEnc1_copy widthEnc1_home widthEnc1_markEnd widthEnc1_choose
  widthEnc1_rewind widthEnc1_fpp FocusCarrier NAMED_focusMarks NAMED_focusSource)

/-- The move alphabet of one micro-action. -/
abbrev MoveC : Type := PegSeparation.RealTimeTM.Move

variable {P : ℕ}

/-! ## 1. One optional micro-action, as a window function -/

/-- An optional micro-action on a tape. -/
def actOn (T : STape Γc) : Option (Γc × MoveC) → STape Γc
  | none => T
  | some sm => T.applyAction blankc sm

/-- The window an action leaves behind: the head cell is overwritten, the two
neighbours are untouched.  This is a function of the *read* window. -/
def winAct (w : Window Γc Kc) : Option (Γc × MoveC) → Window Γc Kc
  | none => w
  | some (s, _) => fun i => if (i : ℕ) = 1 then s else w i

/-- The displacement of an action. -/
def dOfAct : Option (Γc × MoveC) → ℤ
  | none => 0
  | some (_, mv) => match mv with | .right => (1 : ℤ) | .left => (-1 : ℤ) | .stay => (0 : ℤ)

theorem dOfAct_le (a : Option (Γc × MoveC)) : |dOfAct a| ≤ (Kc : ℤ) := by
  cases a with
  | none => simp [dOfAct]
  | some sm =>
      obtain ⟨s, mv⟩ := sm
      cases mv <;> simp [dOfAct, Kc]

/-- **From an explicit window witness to a literal sweep.**  The existential
`CloseoutCoreEnc4.sweep_of_winRealizes` forgets the witness; `WinOn` needs it. -/
theorem teq_sweep_of_witness {T T' : STape Γc} {w : Window Γc Kc} {d : ℤ}
    (hK : Kc ≤ pos T) (hd : |d| ≤ (Kc : ℤ))
    (hpos : (pos T' : ℤ) = (pos T : ℤ) + d)
    (hcell : ∀ p : ℕ, rd blankc T' p =
      if pos T - Kc ≤ p ∧ p ≤ pos T + Kc then w (idx Kc (p - (pos T - Kc)))
      else rd blankc T p) :
    TEq T' (sweep blankc Kc T w d) := by
  refine ⟨?_, ?_⟩
  · have h1 : (pos T' : ℤ) = (pos (sweep blankc Kc T w d) : ℤ) := by
      rw [pos_sweep blankc Kc T w d hK hd]; exact hpos
    exact_mod_cast h1
  · intro p
    rw [hcell p, rd_sweep blankc Kc T w d hK p]

/-- **One optional micro-action is a sweep by a window function of the read.** -/
theorem teq_sweep_act (T : STape Γc) (a : Option (Γc × MoveC)) (hK : Kc ≤ pos T) :
    TEq (actOn T a) (sweep blankc Kc T (winAct (readWin blankc Kc T) a) (dOfAct a)) := by
  classical
  cases a with
  | none =>
      refine teq_sweep_of_witness hK (by simp [dOfAct]) (by simp [dOfAct, actOn]) ?_
      intro p
      by_cases hmem : pos T - Kc ≤ p ∧ p ≤ pos T + Kc
      · rw [if_pos hmem]
        have hle : p - (pos T - Kc) ≤ 2 * Kc := by
          simp only [Kc] at hmem ⊢
          omega
        show rd blankc T p = winAct (readWin blankc Kc T) none _
        simp only [winAct]
        rw [readWin_eq, idx_val hle]
        congr 1
        simp only [Kc] at hmem ⊢
        omega
      · rw [if_neg hmem]; rfl
  | some sm =>
      obtain ⟨s, mv⟩ := sm
      have h1 : (1 : ℕ) ≤ pos T := by simpa [Kc] using hK
      refine teq_sweep_of_witness hK (dOfAct_le (some (s, mv))) ?_ ?_
      · show ((pos (T.applyAction blankc (s, mv)) : ℤ)) = _
        rw [pos_applyAction blankc s T mv]
        cases mv <;> simp [dOfAct] <;> omega
      · intro p
        show rd blankc (T.applyAction blankc (s, mv)) p = _
        rw [rd_applyAction blankc s T mv p]
        by_cases hmem : pos T - Kc ≤ p ∧ p ≤ pos T + Kc
        · rw [if_pos hmem]
          have hle : p - (pos T - Kc) ≤ 2 * Kc := by
            simp only [Kc] at hmem ⊢
            omega
          simp only [winAct]
          rw [idx_val hle]
          by_cases hp : p = pos T
          · rw [if_pos hp]
            simp only [Kc]
            rw [if_pos (by omega)]
          · rw [if_neg hp]
            simp only [Kc] at hmem ⊢
            rw [if_neg (by omega), readWin_eq, idx_val (by omega)]
            congr 1
            omega
        · rw [if_neg hmem, if_neg (by simp only [Kc] at hmem ⊢; omega)]

/-! ## 2. `TapeAct`: a branch, as an action on every tape -/

/-- **A tape datum for one branch of one mode.**  `nq` computes the next finite
control from the control and the windows; `act` chooses, per tape index, an
optional micro-action from the same data; and the laid-out tapes of `f m` are
*literally* those actions applied to the laid-out tapes of `m`.  No window
appears in `tape`: this is the residual with the window layer removed. -/
structure TapeAct (n delay Lp Lf : ℕ) (rep : ChainVM → ChainL)
    (f : Mirrored1 P → Mirrored1 P) (md : Mode) (sc : Mirrored1 P → Prop) where
  nq : QL delay Lp Lf P QChain → (Fin (tL P tChain) → Window Γc Kc) →
    QL delay Lp Lf P QChain
  act : QL delay Lp Lf P QChain → (Fin (tL P tChain) → Window Γc Kc) → ℕ →
    Option (Γc × MoveC)
  ctl : ∀ m : Mirrored1 P, m.vm.ctl.mode = md → ¬ Starved m.vm → sc m →
    (encPadN n delay Lp Lf rep (f m)).1
      = nq (encPadN n delay Lp Lf rep m).1 (rwOf (encPadN n delay Lp Lf rep) m)
  tape : ∀ (m : Mirrored1 P) (i : ℕ), m.vm.ctl.mode = md → ¬ Starved m.vm → sc m →
    padTapesN n rep (f m) i
      = actOn (padTapesN n rep m i)
        (act (encPadN n delay Lp Lf rep m).1 (rwOf (encPadN n delay Lp Lf rep) m) i)

variable {n delay Lp Lf : ℕ} {rep : ChainVM → ChainL}

/-- Weakening the side condition. -/
def tapeAct_mono {f : Mirrored1 P → Mirrored1 P} {md : Mode} {sc sc' : Mirrored1 P → Prop}
    (A : TapeAct (P := P) n delay Lp Lf rep f md sc) (h : ∀ m, sc' m → sc m) :
    TapeAct (P := P) n delay Lp Lf rep f md sc' where
  nq := A.nq
  act := A.act
  ctl := fun m hmd hs hsc => A.ctl m hmd hs (h m hsc)
  tape := fun m i hmd hs hsc => A.tape m i hmd hs (h m hsc)

/-- **The window residual, from the tape residual.** -/
noncomputable def winOn_of_tapeAct {f : Mirrored1 P → Mirrored1 P} {md : Mode}
    {sc : Mirrored1 P → Prop} (A : TapeAct (P := P) n delay Lp Lf rep f md sc) :
    NAMED_winOn (P := P) (encPadN n delay Lp Lf rep) f md sc where
  nx := fun q ws => (A.nq q ws, fun j => (winAct (ws j) (A.act q ws j.val),
    dOfAct (A.act q ws j.val)))
  disp := fun q ws j => dOfAct_le _
  ctl := fun m hmd hs hsc => A.ctl m hmd hs hsc
  tape := fun m j hmd hs hsc => by
    have hT : (encPadN n delay Lp Lf rep (f m)).2 j = padTapesN n rep (f m) j.val := rfl
    have hT0 : (encPadN n delay Lp Lf rep m).2 j = padTapesN n rep m j.val := rfl
    have hw : rwOf (encPadN n delay Lp Lf rep) m j
        = readWin blankc Kc (padTapesN n rep m j.val) := rfl
    rw [hT, A.tape m j.val hmd hs hsc]
    show TEq _ (sweep blankc Kc ((encPadN n delay Lp Lf rep m).2 j)
      (winAct (rwOf (encPadN n delay Lp Lf rep) m j) _) _)
    rw [hT0, hw]
    exact teq_sweep_act _ _ (margin_encPadN n delay Lp Lf rep m j)

/-! ### The thirteen tape residuals of the seven phase modes -/

section Pieces

variable (n delay Lp Lf) (rep) (qq : ℕ) (first : Fin 9)

/-- **The thirteen step-level tape residuals.**  Field for field the branches of
`CloseoutCoreEnc9.WinPieces`, with the window layer removed. -/
structure ActPieces : Type where
  shiftPick : TapeAct (P := P) n delay Lp Lf rep
    (fun m => shiftPick m.vm.chain m.vm m.mirL) .shift (fun m => True ∧ RemPosL m.vm)
  copyPick : TapeAct (P := P) n delay Lp Lf rep
    (fun m => copyPick (GalilScaffoldPlace.read (PalPeg.LocalArrival.abs' m.vm).fpp.walker) m)
    .copy (fun m => True ∧ RemPosL m.vm)
  copyDone : TapeAct (P := P) n delay Lp Lf rep
    (fun m => (⟨PalPeg.LocalTick3.copyDoneVm { m.vm.ctl with mode := .home } m.vm, m.mirL⟩ :
      Mirrored1 P)) .copy (fun m => True ∧ ¬ RemPosL m.vm)
  homeStart : TapeAct (P := P) n delay Lp Lf rep
    (fun m => (⟨PalPeg.LocalTick3.homeStartVm { m.vm.ctl with mode := .fpp } m.vm, m.mirL⟩ :
      Mirrored1 P)) .home (fun m => True ∧ AtLeftL m.vm)
  homeStep : TapeAct (P := P) n delay Lp Lf rep
    (fun m => (⟨PalPeg.LocalTick3.homeStepVm m.vm, m.mirL⟩ : Mirrored1 P))
    .home (fun m => True ∧ ¬ AtLeftL m.vm)
  markEndDone : TapeAct (P := P) n delay Lp Lf rep
    (fun m => (⟨PalPeg.LocalTick3.marksVm GalilScaffoldTape.moveLeft
      { m.vm.ctl with mode := .choose, odd := false } m.vm, m.mirL⟩ : Mirrored1 P))
    .markEnd (fun m => True ∧ AtEndL m.vm)
  markEndStep : TapeAct (P := P) n delay Lp Lf rep
    (fun m => (⟨PalPeg.LocalTick3.marksVm GalilScaffoldTape.moveRight m.vm.ctl m.vm, m.mirL⟩ :
      Mirrored1 P)) .markEnd (fun m => True ∧ ¬ AtEndL m.vm)
  chooseSelect : TapeAct (P := P) n delay Lp Lf rep
    (fun m => mirrorTick1 .stay (PalPeg.LocalTick3.chooseVm
      { m.vm.ctl with mode := .rewind, pair := false } m.vm) m)
    .choose (fun m => True ∧ ChooseBr first m)
  chooseScan : TapeAct (P := P) n delay Lp Lf rep
    (fun m => mirrorTick1 .stay (PalPeg.LocalTick3.marksVm GalilScaffoldTape.moveLeft
      { m.vm.ctl with odd := !m.vm.ctl.odd } m.vm) m)
    .choose (fun m => True ∧ ¬ ChooseBr first m)
  rewindDone : TapeAct (P := P) n delay Lp Lf rep
    (fun m => mirrorTick1 .stay (PalPeg.LocalTick3.rewindDoneVm
      { m.vm.ctl with mode := .replayStart } m.vm) m)
    .rewind (fun m => True ∧ AtFirstL first (PalPeg.LocalArrival.abs' m.vm))
  rewindPair : TapeAct (P := P) n delay Lp Lf rep
    (fun m => mirrorTick1 .left (PalPeg.LocalTick3.rewindPairVm
      { m.vm.ctl with pair := false } m.vm) m)
    .rewind (fun m => (True ∧ ¬ AtFirstL first (PalPeg.LocalArrival.abs' m.vm))
      ∧ m.vm.ctl.pair = true)
  rewindOne : TapeAct (P := P) n delay Lp Lf rep
    (fun m => mirrorTick1 .stay (PalPeg.LocalTick3.rewindOneVm
      { m.vm.ctl with pair := true } m.vm) m)
    .rewind (fun m => (True ∧ ¬ AtFirstL first (PalPeg.LocalArrival.abs' m.vm))
      ∧ ¬ m.vm.ctl.pair = true)
  fpp : TapeAct (P := P) n delay Lp Lf rep (fun m => ffppW qq first m) .fpp (fun _ => True)

variable {n delay Lp Lf rep qq first}

/-- **The window residuals of `CloseoutCoreEnc9`, from the tape residuals.** -/
noncomputable def winPieces_of_actPieces (A : ActPieces (P := P) n delay Lp Lf rep qq first) :
    WinPieces (P := P) n delay Lp Lf rep qq first where
  shiftPick := winOn_of_tapeAct A.shiftPick
  copyPick := winOn_of_tapeAct A.copyPick
  copyDone := winOn_of_tapeAct A.copyDone
  homeStart := winOn_of_tapeAct A.homeStart
  homeStep := winOn_of_tapeAct A.homeStep
  markEndDone := winOn_of_tapeAct A.markEndDone
  markEndStep := winOn_of_tapeAct A.markEndStep
  chooseSelect := winOn_of_tapeAct A.chooseSelect
  chooseScan := winOn_of_tapeAct A.chooseScan
  rewindDone := winOn_of_tapeAct A.rewindDone
  rewindPair := winOn_of_tapeAct A.rewindPair
  rewindOne := winOn_of_tapeAct A.rewindOne
  fpp := winOn_of_tapeAct A.fpp

end Pieces

/-! ## 3. The widths: closed on the reservoir -/

/-- **Every micro-action conserves the stored width**, provided the head is
strictly inside it.  A right move eats one cell of the reservoir, and the
reservoir is counted by `wlen`. -/
theorem wlen_actOn (T : STape Γc) (a : Option (Γc × MoveC)) (h : pos T < wlen T) :
    wlen (actOn T a) = wlen T := by
  cases a with
  | none => rfl
  | some sm =>
      obtain ⟨s, mv⟩ := sm
      cases mv with
      | left => exact wlen_left blankc s T
      | stay => exact wlen_stay blankc s T
      | right => exact wlen_right blankc s h

/-- The head of the widened layout is strictly inside the stored region. -/
theorem pos_lt_wlen_padTapesN (hn : Kc ≤ n) (m : Mirrored1 P) (i : ℕ) :
    pos (padTapesN n rep m i) < wlen (padTapesN n rep m i) := by
  have := room_padTapesN n rep m i hn
  simp only [Kc] at this
  omega

/-- **The width residual, from the tape residual** — with no extra hypothesis
beyond the reservoir being at least as wide as the window. -/
theorem widthStep_of_tapeAct {f : Mirrored1 P → Mirrored1 P} {md : Mode}
    {sc : Mirrored1 P → Prop} (A : TapeAct (P := P) n delay Lp Lf rep f md sc)
    (hn : Kc ≤ n) : NAMED_widthStep (P := P) rep f md sc := by
  intro m i hmd hs hsc
  have h0 : wlen (padTapesN n rep (f m) i) = wlen (padTapesN n rep m i) := by
    rw [A.tape m i hmd hs hsc]
    exact wlen_actOn _ _ (pos_lt_wlen_padTapesN hn m i)
  rw [wlen_padTapesN, wlen_padTapesN] at h0
  omega

section Widths

variable {qq : ℕ} {first : Fin 9}

/-- **All seven width obligations of `CloseoutCoreEnc9` §6, at once.** -/
theorem widthEnc1_of_actPieces (A : ActPieces (P := P) n delay Lp Lf rep qq first)
    (hn : Kc ≤ n) (md : Mode) :
    md = .shift ∨ md = .copy ∨ md = .home ∨ md = .markEnd ∨ md = .choose ∨
      md = .rewind ∨ md = .fpp →
    NAMED_widthEnc1 (P := P) rep (SL qq first) md := by
  rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · exact widthEnc1_shift
      (widthStep_of_tapeAct (tapeAct_mono A.shiftPick (fun m h => ⟨trivial, h⟩)) hn)
  · exact widthEnc1_copy
      (widthStep_of_tapeAct (tapeAct_mono A.copyPick (fun m h => ⟨trivial, h⟩)) hn)
      (widthStep_of_tapeAct (tapeAct_mono A.copyDone (fun m h => ⟨trivial, h⟩)) hn)
  · exact widthEnc1_home
      (widthStep_of_tapeAct (tapeAct_mono A.homeStart (fun m h => ⟨trivial, h⟩)) hn)
      (widthStep_of_tapeAct (tapeAct_mono A.homeStep (fun m h => ⟨trivial, h⟩)) hn)
  · exact widthEnc1_markEnd
      (widthStep_of_tapeAct (tapeAct_mono A.markEndDone (fun m h => ⟨trivial, h⟩)) hn)
      (widthStep_of_tapeAct (tapeAct_mono A.markEndStep (fun m h => ⟨trivial, h⟩)) hn)
  · exact widthEnc1_choose
      (widthStep_of_tapeAct (tapeAct_mono A.chooseSelect (fun m h => ⟨trivial, h⟩)) hn)
      (widthStep_of_tapeAct (tapeAct_mono A.chooseScan (fun m h => ⟨trivial, h⟩)) hn)
  · exact widthEnc1_rewind
      (widthStep_of_tapeAct (tapeAct_mono A.rewindDone (fun m h => ⟨trivial, h⟩)) hn)
      (widthStep_of_tapeAct (tapeAct_mono A.rewindPair
        (fun m h => ⟨⟨trivial, h.1⟩, h.2⟩)) hn)
      (widthStep_of_tapeAct (tapeAct_mono A.rewindOne
        (fun m h => ⟨⟨trivial, h.1⟩, h.2⟩)) hn)
  · exact widthEnc1_fpp (widthStep_of_tapeAct A.fpp hn)

end Widths

/-! ## 4. The focus atoms: the bank-selection obstruction, named -/

/-- **A control-selected focus carrier.**  Same content as
`CloseoutCoreEnc9.FocusCarrier`, except that the layout index may depend on the
finite control — which is what the `A`/`B` bank split of `LocalBuffers.abs`
forces on any carrier for MARKS or SOURCE. -/
structure FocusCarrier2 (n delay Lp Lf : ℕ) (rep : ChainVM → ChainL)
    (g : Mirrored1 P → Fin 9) (md : Mode) : Type where
  idxOf : QL delay Lp Lf P QChain → Fin (tL P tChain)
  spec : ∀ m : Mirrored1 P, m.vm.ctl.mode = md → ¬ Starved m.vm →
    rd blankc ((encPadN n delay Lp Lf rep m).2
        (idxOf (encPadN n delay Lp Lf rep m).1))
        (pos ((encPadN n delay Lp Lf rep m).2
          (idxOf (encPadN n delay Lp Lf rep m).1)))
      = PalPeg.GalilVMEncode.sDp (g m)

/-- **Residual: the selected index is constant on the mode.**  Exactly the
statement that the active fpp bank does not vary over the states of mode `md`,
which is what `CloseoutCoreEnc9.FocusCarrier` silently assumes. -/
def NAMED_idxConst (n delay Lp Lf : ℕ) (rep : ChainVM → ChainL)
    {g : Mirrored1 P → Fin 9} {md : Mode}
    (C : FocusCarrier2 (P := P) n delay Lp Lf rep g md) : Prop :=
  ∃ j : Fin (tL P tChain), ∀ m : Mirrored1 P, m.vm.ctl.mode = md → ¬ Starved m.vm →
    C.idxOf (encPadN n delay Lp Lf rep m).1 = j

/-- **Collapsing the control-selected carrier to the fixed-index one.** -/
noncomputable def focusCarrier_of_focusCarrier2 {g : Mirrored1 P → Fin 9} {md : Mode}
    (C : FocusCarrier2 (P := P) n delay Lp Lf rep g md)
    (h : NAMED_idxConst (P := P) n delay Lp Lf rep C) :
    FocusCarrier (P := P) n delay Lp Lf rep g md where
  idx := h.choose
  spec := fun m hmd hs => by
    have hj := h.choose_spec m hmd hs
    have := C.spec m hmd hs
    rw [hj] at this
    exact this

end PalPeg.CloseoutCoreEnc10

#print axioms PalPeg.CloseoutCoreEnc10.dOfAct_le
#print axioms PalPeg.CloseoutCoreEnc10.teq_sweep_of_witness
#print axioms PalPeg.CloseoutCoreEnc10.teq_sweep_act
#print axioms PalPeg.CloseoutCoreEnc10.tapeAct_mono
#print axioms PalPeg.CloseoutCoreEnc10.winOn_of_tapeAct
#print axioms PalPeg.CloseoutCoreEnc10.winPieces_of_actPieces
#print axioms PalPeg.CloseoutCoreEnc10.wlen_actOn
#print axioms PalPeg.CloseoutCoreEnc10.pos_lt_wlen_padTapesN
#print axioms PalPeg.CloseoutCoreEnc10.widthStep_of_tapeAct
#print axioms PalPeg.CloseoutCoreEnc10.widthEnc1_of_actPieces
#print axioms PalPeg.CloseoutCoreEnc10.focusCarrier_of_focusCarrier2
