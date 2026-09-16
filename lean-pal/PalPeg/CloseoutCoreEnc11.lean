import PalPeg.CloseoutCoreEnc10

/-!
# Closeout, step 2k: locating the fpp tapes in the layout

`CloseoutCoreEnc10` reduces the thirteen step residuals of the seven phase modes
to `ActPieces` — per branch, a next-control window function and one optional
micro-action per laid-out tape — and reduces the two focus atoms of
`CloseoutCoreEnc9` to the control-selected form `FocusCarrier2` plus
`NAMED_idxConst`.  Nothing there ever *looks inside* the layout.

This file does.  It builds no `LocalStep` and proves no new dynamics, so

**無条件 PAL ∈ PEG は未完.**

## What is established (unconditional)

* **§1 (the locator).**  `CloseoutCoreEnc.encTapes` is a nested `if` on the
  index; `fppBase P = 24 + P + 32` is where the fpp double buffer starts, and
  `encTapes_fpp` computes the layout there: the `k`-th tape of that block is
  `bufTapes m.vm.fppBuf k`.  `bufTapes_bank` says the *active* bank's tape `k`
  sits at offset `bankOff active k`, and `encTapes_setFppBuf` says a rewrite of
  `fppBuf` changes nothing outside the block.  Transporting through
  `shift1`/`padRN` gives `padTapesN_fppActive`: the head cell of the layout
  index `fppIdx P act k` is `sDp` of the focus of the active bank's tape `k`.
* **§2 (the two focus atoms, reduced).**  `focusCarrier2_marks` and
  `focusCarrier2_source` build `CloseoutCoreEnc10.FocusCarrier2` for MARKS
  (tape 8) and SOURCE (tape 7) outright, by reading `fppBuf.active` off the
  finite control (`fppActive`, `fppActive_qOfL`).  With
  `CloseoutCoreEnc10.focusCarrier_of_focusCarrier2` the residuals
  `CloseoutCoreEnc9.NAMED_focusMarks`/`NAMED_focusSource` are therefore reduced
  to `NAMED_idxConst` alone — the statement that the active fpp bank does not
  change over the states of the mode.
* **§3 (`home`, acting branch `homeStartVm`: closed).**  `homeStartVm` writes
  only `fppPc`, `fppDone`, `fppMode` and `ctl`, none of which the layout
  carries, so the branch moves no tape at all: `tapeAct_homeStart` is a
  `CloseoutCoreEnc10.TapeAct` with every micro-action `none`, hence (with
  `winOn_of_tapeAct`) the `homeStart` field of `ActPieces` and of `WinPieces`.
* **§4 (`NAMED_shiftDoneQ`, reduced).**  `shiftDoneQ_of_reads` derives
  `CloseoutCoreEnc8.NAMED_shiftDoneQ` from two branch reads at mode `.shift`:
  one for `OnLetterL` and one for `leftFirstVM`.  The exit branch's whole
  content is the output refresh, and this is exactly its two atoms.
* **§5 (`copy`, exit branch `copyDoneVm`: reduced to one read).**  `bufAt` is
  located in the layout (`encTapes_bufAt`, `padTapesN_bufAt`: exactly one index
  moves, and it moves by one `.stay` write), so `tapeAct_copyDone` builds the
  `copyDone` field of `ActPieces` from a single input, the branch read
  `CloseoutCoreEnc9.NAMED_walkerRead` — which its `nq` needs only because
  `copyDoneVm` also latches `fppFinalStage = (read walker).isNone`.

## What is *not* established, and why

Eleven of the thirteen `ActPieces` fields (`homeStart` is closed in §3 and
`copyDone` is reduced to one read in §5).  Three separate obstructions were
identified while writing this file; each is a **missing machine fact**, stated
here so the next pass does not rediscover it.

1. *A left move at the left end of a `ProgLang` tape is not window-readable.*
   `GalilScaffoldTape.moveLeft` **clamps** when `left = []`, while
   `STape.applyAction _ (s, .left)` on the sentinel-shifted layout never clamps
   (`shift1` guarantees `pos ≥ 1`).  The two agree only when the tape's own
   `left` is non-empty, and the window cannot tell that: the cell to the left of
   the head reads `blankc` both at the sentinel and at a genuine blank.  This
   kills `homeStep`, `markEndDone`, `chooseScan`, `rewindPair`, `rewindOne`
   (all `moveLeft` on SOURCE/MARKS).
2. *A right move at the right end does not preserve the reservoir literally.*
   `padTapesN` appends exactly `n` blanks; `actOn … (s, .right)` on a tape whose
   stored `right` is empty consumes one of them, leaving `n - 1`.  The two sides
   have the same `pos` and the same `rd` everywhere (which is why §3 of
   `CloseoutCoreEnc10` can still close the widths) but are not the *same term*,
   and `TapeAct.tape` is an equation of terms.  This kills `markEndStep` and the
   SOURCE half of `copyPick`.
3. *Several branches are not one micro-action per tape at all.*  `shiftPick`
   moves the `L` cursor **twice** and ticks the counter bank twice;
   `copyPick` additionally moves the fpp walker, a whole `InputView`
   (four laid-out tapes, a real-time queue rotation); `chooseSelect` *resets*
   two unary counters; `rewindDone` resets the idle bank (`LocalBuffers.resetL`
   also rewrites the `job` tape from `job.getD 0` to `0`, which is a single
   action only if `job = none` beforehand); `fpp` is a quantum of `qq`
   program steps.

The five read atoms: the two focus atoms are reduced to `NAMED_idxConst` (§2);
`NAMED_shiftRem`, `NAMED_walkerRead`, `NAMED_workZero` are *not* reduced here.
`NAMED_shiftRem` is a sign test on a unary counter and `NAMED_workZero` a zero
test on one, and a radius-`1` window cannot read either: both are "is this
`Seg` tape's stored value `0`", i.e. a test on the *length* of a unary block,
which is visible only at the block's end.  The missing machine fact is that the
counter heads park on their sentinel cell, so that the test becomes a focus
read.  `NAMED_walkerRead` is a cursor read of `fppWalker` and needs the
queue-layout repair of `CloseoutCoreEnc3` §2, which `viewTapes` does not have
(`CloseoutCoreEnc2.not_NAMED_queueLayout`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutCoreEnc11

open PalPeg PalPeg.Program
open PalPeg.Local (Window idx idx_val pos rd toList sweep readWin rd_pos)
open PalPeg.GalilScaffoldChainInputSupply (ChainVM)
open PalPeg.GalilScaffoldController (Control Mode BoundedControl Bounded)
open PalPeg.LocalChain (ChainL)
open PalPeg.LocalReplayParked (Mirrored1)
open PalPeg.LocalSysConcrete (Starved)
open PalPeg.CloseoutCoreStep (Γc blankc tL QL qOfL pcOf clampCtl)
open PalPeg.CloseoutCoreEnc (Kc encTapes bufTapes dpSTape QChain tChain qChainOf tChain_eq)
open PalPeg.CloseoutCoreEnc3 (encTapes1 shift1)
open PalPeg.CloseoutCoreEnc8 (padRN padTapesN encPadN rwOf NAMED_shiftDoneQ)
open PalPeg.CloseoutCoreEnc9 (FocusCarrier NAMED_focusMarks NAMED_focusSource)
open PalPeg.CloseoutCoreEnc10 (TapeAct FocusCarrier2 NAMED_idxConst actOn)
open PalPeg.CloseoutCoreAgree (OnLetterL refreshL shiftDoneCtlW)
open PalPeg.GalilScaffoldChainInputSupply (leftFirstVM)

variable {P : ℕ}

/-! ## 1. Locating the fpp double buffer -/

/-- Where the fpp double buffer starts in `CloseoutCoreEnc.encTapes`. -/
def fppBase (P : ℕ) : ℕ := 24 + P + 32

/-- The offset of tape `k` of the **active** bank inside that block. -/
def bankOff (act : Bool) (k : ℕ) : ℕ := if act then k else 9 + k

/-- The layout index of tape `k` of the active bank. -/
def fppIdx (P : ℕ) (act : Bool) (k : ℕ) : ℕ := fppBase P + bankOff act k

theorem bankOff_lt {act : Bool} {k : ℕ} (hk : k < 9) : bankOff act k < 19 := by
  cases act <;> simp [bankOff] <;> omega

theorem fppIdx_lt {act : Bool} {k : ℕ} (hk : k < 9) : fppIdx P act k < tL P tChain := by
  have h := bankOff_lt (act := act) hk
  unfold tL PalPeg.CloseoutCoreStep.nViews PalPeg.CloseoutCoreStep.tView
    PalPeg.CloseoutCoreStep.tMir PalPeg.CloseoutCoreStep.tBuf
  rw [tChain_eq]
  unfold fppIdx fppBase
  omega

/-- The layout index of tape `k` of the active bank, as an index of `tL`. -/
def fppFin (P : ℕ) (act : Bool) (k : Fin 9) : Fin (tL P tChain) :=
  ⟨fppIdx P act k.val, fppIdx_lt k.isLt⟩

/-- **The locator.**  Inside its block the layout is the double buffer. -/
theorem encTapes_fpp (rep : ChainVM → ChainL) (m : Mirrored1 P) (k : ℕ) (hk : k < 19) :
    encTapes rep m (fppBase P + k) = bufTapes m.vm.fppBuf k := by
  unfold fppBase
  dsimp only [encTapes, PalPeg.CloseoutCoreStep.nViews, PalPeg.CloseoutCoreStep.tView,
    PalPeg.CloseoutCoreStep.tMir, PalPeg.CloseoutCoreStep.tBuf]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), dif_neg (by omega)]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos (by omega)]
  congr 1
  omega

/-- **The active bank.** -/
theorem bufTapes_bank (b : PalPeg.LocalBuffers.Buffered 9) (k : Fin 9) :
    bufTapes b (bankOff b.active k.val) = dpSTape (PalPeg.LocalBuffers.abs b k) := by
  cases h : b.active with
  | true =>
      simp only [bankOff, if_true]
      rw [bufTapes, dif_pos k.isLt]
      simp [PalPeg.LocalBuffers.abs, h]
  | false =>
      simp only [bankOff, Bool.false_eq_true, if_false]
      rw [bufTapes, dif_neg (by omega), dif_pos (by omega)]
      simp [PalPeg.LocalBuffers.abs, h]

/-- The same, with the active bit given separately. -/
theorem bufTapes_bank' (b : PalPeg.LocalBuffers.Buffered 9) (act : Bool)
    (h : b.active = act) (k : Fin 9) :
    bufTapes b (bankOff act k.val) = dpSTape (PalPeg.LocalBuffers.abs b k) := by
  subst h; exact bufTapes_bank b k

/-- **A rewrite of `fppBuf` is invisible outside its block.** -/
theorem encTapes_setFppBuf (rep : ChainVM → ChainL) (m : Mirrored1 P)
    (b' : PalPeg.LocalBuffers.Buffered 9) (i : ℕ)
    (h : ¬ (fppBase P ≤ i ∧ i < fppBase P + 19)) :
    encTapes rep (⟨{ m.vm with fppBuf := b' }, m.mirL⟩ : Mirrored1 P) i
      = encTapes rep m i := by
  unfold fppBase at h
  dsimp only [encTapes, PalPeg.CloseoutCoreStep.tView, PalPeg.CloseoutCoreStep.nViews,
    PalPeg.CloseoutCoreStep.tMir, PalPeg.CloseoutCoreStep.tBuf]
  by_cases c1 : i < 4
  · rw [if_pos c1, if_pos c1]
  rw [if_neg c1, if_neg c1]
  by_cases c2 : i < 8
  · rw [if_pos c2, if_pos c2]
  rw [if_neg c2, if_neg c2]
  by_cases c3 : i < 12
  · rw [if_pos c3, if_pos c3]
  rw [if_neg c3, if_neg c3]
  by_cases c4 : i < 16
  · rw [if_pos c4, if_pos c4]
  rw [if_neg c4, if_neg c4]
  by_cases c5 : i < 20
  · rw [if_pos c5, if_pos c5]
  rw [if_neg c5, if_neg c5]
  by_cases c6 : i < 24
  · rw [if_pos c6, if_pos c6]
  rw [if_neg c6, if_neg c6]
  by_cases c7 : i - 24 < P
  · rw [dif_pos c7, dif_pos c7]
  rw [dif_neg c7, dif_neg c7]
  by_cases c8 : i - 24 - P = 0
  · rw [if_pos c8, if_pos c8]
  rw [if_neg c8, if_neg c8]
  by_cases c9 : i - 24 - P = 1
  · rw [if_pos c9, if_pos c9]
  rw [if_neg c9, if_neg c9]
  by_cases c10 : i - 24 - P = 2
  · rw [if_pos c10, if_pos c10]
  rw [if_neg c10, if_neg c10]
  by_cases c11 : i - 24 - P = 3
  · rw [if_pos c11, if_pos c11]
  rw [if_neg c11, if_neg c11]
  by_cases c12 : i - 24 - P = 4
  · rw [if_pos c12, if_pos c12]
  rw [if_neg c12, if_neg c12]
  by_cases c13 : i - 24 - P = 5
  · rw [if_pos c13, if_pos c13]
  rw [if_neg c13, if_neg c13]
  by_cases c14 : i - 24 - P = 6
  · rw [if_pos c14, if_pos c14]
  rw [if_neg c14, if_neg c14]
  by_cases c15 : i - 24 - P < 32
  · rw [if_pos c15, if_pos c15]
  rw [if_neg c15, if_neg c15]
  by_cases c16 : i - 24 - P < 51
  · exact absurd ⟨by omega, by omega⟩ h
  rw [if_neg c16, if_neg c16]
/-- **Transporting the locator through the sentinel shift and the reservoir.** -/
theorem padTapesN_fppActive (n : ℕ) (rep : ChainVM → ChainL) (m : Mirrored1 P) (k : Fin 9) :
    padTapesN n rep m (fppIdx P m.vm.fppBuf.active k.val)
      = padRN blankc n (shift1 blankc
          (dpSTape (PalPeg.LocalBuffers.abs m.vm.fppBuf k))) := by
  rw [padTapesN, encTapes1, fppIdx,
    encTapes_fpp rep m _ (bankOff_lt k.isLt), bufTapes_bank]

/-- The same, with the active bit given separately. -/
theorem padTapesN_fppAt (n : ℕ) (rep : ChainVM → ChainL) (m : Mirrored1 P) (act : Bool)
    (h : m.vm.fppBuf.active = act) (k : Fin 9) :
    padTapesN n rep m (fppIdx P act k.val)
      = padRN blankc n (shift1 blankc
          (dpSTape (PalPeg.LocalBuffers.abs m.vm.fppBuf k))) := by
  rw [padTapesN, encTapes1, fppIdx,
    encTapes_fpp rep m _ (bankOff_lt k.isLt), bufTapes_bank' _ act h]

/-- The head cell of a laid-out `ProgLang` tape is its focus, recoded. -/
theorem rd_head_padRN_shift1_dp (n : ℕ) (t : GalilScaffoldTape.Tape) :
    rd blankc (padRN blankc n (shift1 blankc (dpSTape t)))
        (pos (padRN blankc n (shift1 blankc (dpSTape t))))
      = PalPeg.GalilVMEncode.sDp t.focus := by
  rw [rd_pos]
  rfl

/-! ## 2. The two focus atoms, reduced to `NAMED_idxConst` -/

/-- The active fpp bank, read off the finite control. -/
def fppActive {delay Lp Lf : ℕ} (q : QL delay Lp Lf P QChain) : Bool :=
  q.2.2.2.2.2.2.2.2.1.2.2

@[simp] theorem fppActive_qOfL (delay Lp Lf : ℕ) (rep : ChainVM → ChainL) (m : Mirrored1 P) :
    fppActive (qOfL delay Lp Lf (fun c => qChainOf (rep c)) m) = m.vm.fppBuf.active := rfl

variable {n delay Lp Lf : ℕ} {rep : ChainVM → ChainL}

/-- **The control-selected carrier for one fpp tape.** -/
noncomputable def focusCarrier2_fpp (n delay Lp Lf : ℕ) (rep : ChainVM → ChainL)
    (k : Fin 9) (md : Mode) :
    FocusCarrier2 (P := P) n delay Lp Lf rep
      (fun m => (PalPeg.LocalBuffers.abs m.vm.fppBuf k).focus) md where
  idxOf := fun q => fppFin P (fppActive q) k
  spec := fun m hmd hs => by
    have hx : (encPadN n delay Lp Lf rep m).2
          (fppFin P (fppActive (encPadN n delay Lp Lf rep m).1) k)
        = padRN blankc n (shift1 blankc
            (dpSTape (PalPeg.LocalBuffers.abs m.vm.fppBuf k))) :=
      padTapesN_fppActive n rep m k
    rw [hx]
    exact rd_head_padRN_shift1_dp n _

/-- **MARKS (tape 8), control-selected.** -/
noncomputable def focusCarrier2_marks (n delay Lp Lf : ℕ) (rep : ChainVM → ChainL)
    (md : Mode) :
    FocusCarrier2 (P := P) n delay Lp Lf rep
      (fun m => (PalPeg.GalilTickFun3.marksOf (PalPeg.LocalArrival.abs' m.vm)).focus) md :=
  focusCarrier2_fpp n delay Lp Lf rep 8 md

/-- **SOURCE (tape 7), control-selected.** -/
noncomputable def focusCarrier2_source (n delay Lp Lf : ℕ) (rep : ChainVM → ChainL)
    (md : Mode) :
    FocusCarrier2 (P := P) n delay Lp Lf rep
      (fun m => (PalPeg.GalilTickFun3.sourceOf (PalPeg.LocalArrival.abs' m.vm)).focus) md :=
  focusCarrier2_fpp n delay Lp Lf rep 7 md

/-- **`NAMED_focusMarks` is now exactly `NAMED_idxConst`.** -/
noncomputable def focusMarks_of_idxConst (md : Mode)
    (h : NAMED_idxConst (P := P) n delay Lp Lf rep (focusCarrier2_marks n delay Lp Lf rep md)) :
    NAMED_focusMarks (P := P) n delay Lp Lf rep md :=
  PalPeg.CloseoutCoreEnc10.focusCarrier_of_focusCarrier2 _ h

/-- **`NAMED_focusSource` is now exactly `NAMED_idxConst`.** -/
noncomputable def focusSource_of_idxConst (md : Mode)
    (h : NAMED_idxConst (P := P) n delay Lp Lf rep (focusCarrier2_source n delay Lp Lf rep md)) :
    NAMED_focusSource (P := P) n delay Lp Lf rep md :=
  PalPeg.CloseoutCoreEnc10.focusCarrier_of_focusCarrier2 _ h

/-! ## 3. `home`, acting branch `homeStartVm`: closed -/

/-- **`homeStartVm` moves no tape.**  It writes `fppPc`, `fppDone`, `fppMode`
and `ctl`, and `CloseoutCoreEnc.encTapes` carries none of them. -/
theorem padTapesN_homeStart (n : ℕ) (rep : ChainVM → ChainL) (m : Mirrored1 P)
    (c : Control) (i : ℕ) :
    padTapesN n rep
        (⟨PalPeg.LocalTick3.homeStartVm c m.vm, m.mirL⟩ : Mirrored1 P) i
      = padTapesN n rep m i := rfl

/-- **The `homeStart` branch, as a `TapeAct`.** -/
def tapeAct_homeStart (n delay Lp Lf : ℕ) (rep : ChainVM → ChainL) (md : Mode)
    (sc : Mirrored1 P → Prop) :
    TapeAct (P := P) n delay Lp Lf rep
      (fun m => (⟨PalPeg.LocalTick3.homeStartVm { m.vm.ctl with mode := .fpp } m.vm,
        m.mirL⟩ : Mirrored1 P)) md sc where
  nq := fun q _ =>
    (⟨{ q.1.val with mode := .fpp }, q.1.property⟩,
      q.2.1, q.2.2.1, q.2.2.2.1,
      PalPeg.GalilScaffoldChainInputSupply.FppControl.Mode.run,
      q.2.2.2.2.2.1, q.2.2.2.2.2.2.1, q.2.2.2.2.2.2.2.1,
      (pcOf Lf 320, false, q.2.2.2.2.2.2.2.2.1.2.2),
      q.2.2.2.2.2.2.2.2.2.1, q.2.2.2.2.2.2.2.2.2.2.1, q.2.2.2.2.2.2.2.2.2.2.2)
  act := fun _ _ _ => none
  ctl := fun m hmd hs hsc => rfl
  tape := fun m i hmd hs hsc => rfl

/-! ## 4. `NAMED_shiftDoneQ`, reduced to two reads -/

/-- The controller record the `shift` exit installs: mode `scan`, output `b`. -/
def scanCtl (b : Bool) (c : Control) : Control := { c with mode := .scan, output := b }


/-- **The `shift` exit, from its two atoms.**  The step writes only `ctl`, and
the only non-control content of the new `ctl` is the output refresh
`refreshL = if OnLetterL then leftFirstVM else old`. -/
noncomputable def shiftDoneQ_of_reads
    (B1 : PalPeg.CloseoutCoreEnc8.NAMED_branchRead (P := P) (encPadN n delay Lp Lf rep)
      (fun m => OnLetterL (PalPeg.LocalArrival.abs' m.vm)) .shift)
    (B2 : PalPeg.CloseoutCoreEnc8.NAMED_branchRead (P := P) (encPadN n delay Lp Lf rep)
      (fun m => leftFirstVM (PalPeg.LocalArrival.abs' m.vm)) .shift) :
    NAMED_shiftDoneQ (P := P) n delay Lp Lf rep := by
  classical
  refine ⟨fun q ws =>
    (⟨scanCtl (if B1.test q ws = true then B2.test q ws else q.1.val.output) q.1.val,
      q.1.property⟩, q.2), ?_⟩
  intro m hmd hs hrem
  have hout : refreshL (PalPeg.LocalArrival.abs' m.vm) m.vm.ctl.output
      = (if B1.test (encPadN n delay Lp Lf rep m).1 (rwOf (encPadN n delay Lp Lf rep) m) = true
          then B2.test (encPadN n delay Lp Lf rep m).1 (rwOf (encPadN n delay Lp Lf rep) m)
          else m.vm.ctl.output) := by
    by_cases hL : OnLetterL (PalPeg.LocalArrival.abs' m.vm)
    · rw [refreshL, if_pos hL, if_pos ((B1.spec m hmd hs).mpr hL)]
      by_cases hF : leftFirstVM (PalPeg.LocalArrival.abs' m.vm)
      · rw [(B2.spec m hmd hs).mpr hF]
        simp [hF]
      · have : B2.test (encPadN n delay Lp Lf rep m).1 (rwOf (encPadN n delay Lp Lf rep) m)
            = false := by
          by_contra hc
          exact hF ((B2.spec m hmd hs).mp (by simpa using hc))
        rw [this]
        simp [hF]
    · rw [refreshL, if_neg hL,
        if_neg (show ¬ (B1.test (encPadN n delay Lp Lf rep m).1
          (rwOf (encPadN n delay Lp Lf rep) m) = true) from
          fun hc => hL ((B1.spec m hmd hs).mp hc))]
  show (qOfL delay Lp Lf (fun c => qChainOf (rep c))
      (⟨{ m.vm with ctl := shiftDoneCtlW m.vm }, m.mirL⟩ : Mirrored1 P)) = _
  unfold qOfL
  congr 1
  apply Subtype.ext
  show (clampCtl delay (shiftDoneCtlW m.vm)).val = _
  rw [clampCtl, shiftDoneCtlW, hout]
  rfl

/-! ## 5. `copy`, exit branch `copyDoneVm`: reduced to the walker read -/

/-- **One tape of one bank moved.**  Outside the acted index the double buffer
layout is unchanged. -/
theorem bufTapes_bufAt_ne (b : PalPeg.LocalBuffers.Buffered 9)
    (g : GalilScaffoldTape.Tape → GalilScaffoldTape.Tape) (k : Fin 9) (j : ℕ)
    (hj : j ≠ bankOff b.active k.val) :
    bufTapes (PalPeg.LocalTick3.bufAt k g b) j = bufTapes b j := by
  have hact : (PalPeg.LocalTick3.bufAt k g b).active = b.active := by
    unfold PalPeg.LocalTick3.bufAt PalPeg.LocalBuffers.stepL
    cases b.active <;> rfl
  cases hb : b.active with
  | true =>
      simp only [bankOff, if_true, hb] at hj
      unfold bufTapes PalPeg.LocalTick3.bufAt PalPeg.LocalBuffers.stepL
      rw [hb]
      by_cases h9 : j < 9
      · rw [dif_pos h9, dif_pos h9]
        have : (⟨j, h9⟩ : Fin 9) ≠ k := by
          intro hc; exact hj (by rw [← hc])
        simp [PalPeg.LocalTick3.atTape, this]
      · rw [dif_neg h9, dif_neg h9]
  | false =>
      simp only [bankOff, Bool.false_eq_true, if_false, hb] at hj
      unfold bufTapes PalPeg.LocalTick3.bufAt PalPeg.LocalBuffers.stepL
      rw [hb]
      by_cases h9 : j < 9
      · rw [dif_pos h9, dif_pos h9]
      · rw [dif_neg h9, dif_neg h9]
        by_cases h18 : j - 9 < 9
        · rw [dif_pos h18, dif_pos h18]
          have : (⟨j - 9, h18⟩ : Fin 9) ≠ k := by
            intro hc
            exact hj (by simp only [← hc]; omega)
          simp [PalPeg.LocalTick3.atTape, this]
        · rw [dif_neg h18, dif_neg h18]

/-- `bufAt` does not flip the active bank. -/
theorem active_bufAt (b : PalPeg.LocalBuffers.Buffered 9)
    (g : GalilScaffoldTape.Tape → GalilScaffoldTape.Tape) (k : Fin 9) :
    (PalPeg.LocalTick3.bufAt k g b).active = b.active := by
  unfold PalPeg.LocalTick3.bufAt PalPeg.LocalBuffers.stepL
  cases b.active <;> rfl

/-- **At the acted index.** -/
theorem bufTapes_bufAt_eq (b : PalPeg.LocalBuffers.Buffered 9)
    (g : GalilScaffoldTape.Tape → GalilScaffoldTape.Tape) (k : Fin 9) :
    bufTapes (PalPeg.LocalTick3.bufAt k g b) (bankOff b.active k.val)
      = dpSTape (g (PalPeg.LocalBuffers.abs b k)) := by
  rw [bufTapes_bank' _ b.active (active_bufAt b g k) k, PalPeg.LocalTick3.abs_bufAt]
  simp

/-- **The layout after one action on one fpp tape.** -/
theorem encTapes_bufAt (rep : ChainVM → ChainL) (m : Mirrored1 P)
    (g : GalilScaffoldTape.Tape → GalilScaffoldTape.Tape) (k : Fin 9) (i : ℕ) :
    encTapes rep
        (⟨{ m.vm with fppBuf := PalPeg.LocalTick3.bufAt k g m.vm.fppBuf }, m.mirL⟩ :
          Mirrored1 P) i
      = if i = fppIdx P m.vm.fppBuf.active k.val then
          dpSTape (g (PalPeg.LocalBuffers.abs m.vm.fppBuf k))
        else encTapes rep m i := by
  classical
  by_cases hi : i = fppIdx P m.vm.fppBuf.active k.val
  · rw [if_pos hi, hi, fppIdx, encTapes_fpp rep _ _ (bankOff_lt k.isLt)]
    show bufTapes (PalPeg.LocalTick3.bufAt k g m.vm.fppBuf) (bankOff m.vm.fppBuf.active k.val)
      = _
    exact bufTapes_bufAt_eq _ g k
  · rw [if_neg hi]
    by_cases hr : fppBase P ≤ i ∧ i < fppBase P + 19
    · obtain ⟨d, rfl⟩ : ∃ d, i = fppBase P + d := ⟨i - fppBase P, by omega⟩
      have hd : d < 19 := by omega
      have hk : d ≠ bankOff m.vm.fppBuf.active k.val := by
        intro hc; exact hi (by unfold fppIdx; omega)
      rw [encTapes_fpp rep _ d hd, encTapes_fpp rep m d hd]
      show bufTapes (PalPeg.LocalTick3.bufAt k g m.vm.fppBuf) d = _
      exact bufTapes_bufAt_ne _ g k d hk
    · exact encTapes_setFppBuf rep m _ i hr

/-- The same, on the widened layout. -/
theorem padTapesN_bufAt (n : ℕ) (rep : ChainVM → ChainL) (m : Mirrored1 P)
    (g : GalilScaffoldTape.Tape → GalilScaffoldTape.Tape) (k : Fin 9) (i : ℕ) :
    padTapesN n rep
        (⟨{ m.vm with fppBuf := PalPeg.LocalTick3.bufAt k g m.vm.fppBuf }, m.mirL⟩ :
          Mirrored1 P) i
      = if i = fppIdx P m.vm.fppBuf.active k.val then
          padRN blankc n (shift1 blankc
            (dpSTape (g (PalPeg.LocalBuffers.abs m.vm.fppBuf k))))
        else padTapesN n rep m i := by
  classical
  show padRN blankc n (shift1 blankc (encTapes rep _ i)) = _
  rw [encTapes_bufAt rep m g k i]
  by_cases hi : i = fppIdx P m.vm.fppBuf.active k.val
  · rw [if_pos hi, if_pos hi]
  · rw [if_neg hi, if_neg hi]
    rfl

/-- **The `copyDone` branch, as a `TapeAct`**, given the walker read that its
next control needs for `fppFinalStage`. -/
noncomputable def tapeAct_copyDone (md : Mode) (sc : Mirrored1 P → Prop)
    (Bw : PalPeg.CloseoutCoreEnc8.NAMED_branchRead (P := P) (encPadN n delay Lp Lf rep)
      (fun m => GalilScaffoldPlace.read (PalPeg.LocalArrival.abs' m.vm).fpp.walker = none) md) :
    TapeAct (P := P) n delay Lp Lf rep
      (fun m => (⟨PalPeg.LocalTick3.copyDoneVm { m.vm.ctl with mode := .home } m.vm,
        m.mirL⟩ : Mirrored1 P)) md sc where
  nq := fun q ws =>
    (⟨{ q.1.val with mode := PalPeg.GalilScaffoldController.Mode.home }, q.1.property⟩,
      q.2.1, q.2.2.1, q.2.2.2.1,
      PalPeg.GalilScaffoldChainInputSupply.FppControl.Mode.home,
      Bw.test q ws,
      q.2.2.2.2.2.2.1, q.2.2.2.2.2.2.2.1, q.2.2.2.2.2.2.2.2.1,
      q.2.2.2.2.2.2.2.2.2.1, q.2.2.2.2.2.2.2.2.2.2.1, q.2.2.2.2.2.2.2.2.2.2.2)
  act := fun q _ i =>
    if i = fppIdx P (fppActive q) 7 then some (PalPeg.GalilVMEncode.sDp 5, .stay) else none
  ctl := fun m hmd hs hsc => by
    classical
    have hfs : (GalilScaffoldPlace.read
          (PalPeg.LocalState.absPlace m.vm.fppWalker)).isNone
        = Bw.test (encPadN n delay Lp Lf rep m).1 (rwOf (encPadN n delay Lp Lf rep) m) := by
      by_cases hw : GalilScaffoldPlace.read (PalPeg.LocalArrival.abs' m.vm).fpp.walker = none
      · rw [(Bw.spec m hmd hs).mpr hw]
        show (GalilScaffoldPlace.read (PalPeg.LocalArrival.abs' m.vm).fpp.walker).isNone = true
        rw [hw]; rfl
      · have hb : Bw.test (encPadN n delay Lp Lf rep m).1
            (rwOf (encPadN n delay Lp Lf rep) m) = false := by
          by_contra hc
          exact hw ((Bw.spec m hmd hs).mp (by simpa using hc))
        rw [hb]
        show (GalilScaffoldPlace.read (PalPeg.LocalArrival.abs' m.vm).fpp.walker).isNone = false
        cases hq : GalilScaffoldPlace.read (PalPeg.LocalArrival.abs' m.vm).fpp.walker with
        | none => exact absurd hq hw
        | some a => rfl
    simp only [encPadN, qOfL, PalPeg.LocalTick3.copyDoneVm]
    rw [hfs, active_bufAt]
    rfl
  tape := fun m i hmd hs hsc => by
    classical
    show padTapesN n rep
        (⟨{ m.vm with fppBuf :=
            PalPeg.LocalTick3.bufAt 7 (fun t => GalilScaffoldTape.write t 5) m.vm.fppBuf },
          m.mirL⟩ : Mirrored1 P) i = _
    rw [padTapesN_bufAt n rep m _ 7 i]
    show (if i = fppIdx P m.vm.fppBuf.active 7 then _ else _)
      = actOn (padTapesN n rep m i)
        (if i = fppIdx P m.vm.fppBuf.active 7 then some (PalPeg.GalilVMEncode.sDp 5, .stay)
          else none)
    by_cases hi : i = fppIdx P m.vm.fppBuf.active 7
    · rw [if_pos hi, if_pos hi, hi,
        show padTapesN n rep m (fppIdx P m.vm.fppBuf.active 7)
            = padRN blankc n (shift1 blankc
                (dpSTape (PalPeg.LocalBuffers.abs m.vm.fppBuf 7)))
          from padTapesN_fppAt n rep m _ rfl 7]
      rfl
    · rw [if_neg hi, if_neg hi]
      rfl


end PalPeg.CloseoutCoreEnc11

#print axioms PalPeg.CloseoutCoreEnc11.encTapes_fpp
#print axioms PalPeg.CloseoutCoreEnc11.bufTapes_bank
#print axioms PalPeg.CloseoutCoreEnc11.encTapes_setFppBuf
#print axioms PalPeg.CloseoutCoreEnc11.padTapesN_fppActive
#print axioms PalPeg.CloseoutCoreEnc11.focusCarrier2_fpp
#print axioms PalPeg.CloseoutCoreEnc11.focusCarrier2_marks
#print axioms PalPeg.CloseoutCoreEnc11.focusCarrier2_source
#print axioms PalPeg.CloseoutCoreEnc11.focusMarks_of_idxConst
#print axioms PalPeg.CloseoutCoreEnc11.focusSource_of_idxConst
#print axioms PalPeg.CloseoutCoreEnc11.padTapesN_homeStart
#print axioms PalPeg.CloseoutCoreEnc11.tapeAct_homeStart
#print axioms PalPeg.CloseoutCoreEnc11.shiftDoneQ_of_reads
#print axioms PalPeg.CloseoutCoreEnc11.bufTapes_bufAt_ne
#print axioms PalPeg.CloseoutCoreEnc11.encTapes_bufAt
#print axioms PalPeg.CloseoutCoreEnc11.padTapesN_bufAt
#print axioms PalPeg.CloseoutCoreEnc11.tapeAct_copyDone
