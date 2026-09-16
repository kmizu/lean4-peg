import PalPeg.CloseoutCoreStep

/-!
# Closeout: a word-free `Steps P` and the seven `AgreeOn` obligations

`CloseoutCoreStep.realizes_seven_of_agree` reduces gap (2) — the
word-dependence of the seven phase steps — to seven `AgreeOn` facts.  This
file supplies a concrete **word-free** `SL : Steps P` (no `raw`, no
`Shared`; only the two finite machine constants `qq : ℕ` and `first : Fin 9`
occur) and discharges six of the seven obligations outright, leaving one
NAMED residual.  It builds no `LocalStep` and proves no new dynamics, so

**無条件 PAL ∈ PEG は未完.**

## What is established

* **`copy`, `home`, `markEnd`** (§2): `LocalRealizesPhase.copyStepL`,
  `homeStepL`, `markEndStepL` carry no `Shared` argument at all, so the
  agreement is `rfl` (`agreeOn_refl`).
* **`choose`, `rewind`** (§3): `chooseStepC`/`rewindStepC` consult the frame
  only through `markSet` and `atFirst`, which `galilFrameS` takes from
  `rewindFrame first`; both are the *local MARKS read*
  `(marksOf s).focus = 8 ∨ (marksOf s).focus = first` resp.
  `(marksOf s).focus = first` (`markSet_eq`, `atFirst_eq`, by `rfl`).  The
  word-free `chooseStepW`/`rewindStepW` are therefore definitionally the
  originals (`chooseStepW_eq`, `rewindStepW_eq`).
* **`fpp`** (§4): `TickL3 S q first x` does not depend on `S` at all when
  `x.ctl.mode = .fpp`, because the two `fpp` constructors mention no frame
  field (`tickL3_fpp_congr`).  Hence `LocalWF.ffpp` at the *closed* dummy
  `dumS` agrees with `ffpp Pw` on every `fpp` state (`agree_fpp`), and the
  "fpp quantum" obligation is closed without choosing an instruction
  decoding: the `Classical.choice` witness is the same one on both sides.
* **`shift`** (§5): the only word-dependent read is
  `refreshOf Pw s old = if Pw.onLetter s then decide (Pw.leftFirst s) else old`.
  `leftFirst` is already word-free (`leftFirstVM s := position s.left = 1`),
  and `onLetterVM` is shown here to be *exactly* the local right-head read
  plus one length bound (`onLetterVM_iff`):

  `onLetterVM raw s ↔ (s.right.gap = false ∧ 0 < L ∧ L ≤ raw.length)`,
  `L := s.right.head.left.length`.

  The first two conjuncts are the word-free `OnLetterL`; the third is the
  NAMED residual below.

## The residual (NAMED)

```
RightInBounds (raw : List (Fin 2)) (stOf : ℕ → State GalilVM) : Prop :=
  ∀ m : Mirrored1 P, InvC raw stOf m → m.vm.ctl.mode = .shift →
    ¬ RemPosL m.vm → (abs' m.vm).right.head.left.length ≤ raw.length
```

i.e. *the R head never stands past the end of the input* on a `shift` state
that is about to hand back to `scan`.  This is a reachability fact about the
input supply, not a local read, and is **not proved here**.  Given it,
`agree_shift` closes, and `realizes_seven_SL` gives all seven obligations
for the word-free `SL`.

Gaps (1) and (3) of `CloseoutCoreAudit` — the encoding `encC` and the
window-locality of each step — are untouched.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace PalPeg.CloseoutCoreAgree

open PalPeg PalPeg.Program
open PalPeg.GalilScaffoldTop
open PalPeg.GalilScaffoldController (Control Mode)
open PalPeg.GalilScaffoldChainInputSupply
open PalPeg.LocalState (GalilVML)
open PalPeg.LocalArrival (abs')
open PalPeg.LocalReplayParked (Mirrored1 mirrorTick1)
open PalPeg.LocalSysConcrete (Steps Realizes InvC Needy Starved)
open PalPeg.GalilTickFun3 (marksOf)
open PalPeg.LocalTick3 (TickL3 chooseVm marksVm rewindDoneVm rewindPairVm rewindOneVm)
open PalPeg.LocalRealizesPhase (copyStepL homeStepL markEndStepL shiftStepL shiftPick
  shiftDoneCtl refreshOf RemPosL)
open PalPeg.LocalRealizesScan (chooseStepC rewindStepC)
open PalPeg.CloseoutCoreStep (AgreeOn agreeOn_refl realizes_congr)

variable {P : ℕ}

/-! ## 1. Word-free local reads -/

/-- The local MARKS read behind the frame's `markSet`. -/
def MarkSetL (first : Fin 9) (s : GalilVM) : Prop :=
  (marksOf s).focus = 8 ∨ (marksOf s).focus = first

/-- The local MARKS read behind the frame's `atFirst`. -/
def AtFirstL (first : Fin 9) (s : GalilVM) : Prop := (marksOf s).focus = first

theorem markSet_eq (Pw : Shared) (qq : ℕ) (first : Fin 9) (s : GalilVM) :
    (galilFrameS Pw qq first).markSet s = MarkSetL first s := rfl

theorem atFirst_eq (Pw : Shared) (qq : ℕ) (first : Fin 9) (s : GalilVM) :
    (galilFrameS Pw qq first).atFirst s = AtFirstL first s := rfl

/-- The word-free part of `onLetterVM`: R is not in a gap and has consumed at
least one letter.  Both conjuncts are reads of the R head alone. -/
def OnLetterL (s : GalilVM) : Prop :=
  s.right.gap = false ∧ 0 < s.right.head.left.length

/-- **`onLetterVM` is a local right-head read plus one length bound.** -/
theorem onLetterVM_iff (raw : List (Fin 2)) (s : GalilVM) :
    onLetterVM raw s ↔ OnLetterL s ∧ s.right.head.left.length ≤ raw.length := by
  unfold onLetterVM OnLetterL
  constructor
  · rintro ⟨k, hk, hk2, hp⟩
    cases hg : s.right.gap with
    | true =>
      exfalso
      rw [position, hg, if_pos rfl] at hp
      omega
    | false =>
      rw [position, hg] at hp
      simp only [Bool.false_eq_true, if_false] at hp
      exact ⟨⟨rfl, by omega⟩, by omega⟩
  · rintro ⟨⟨hg, hL⟩, hle⟩
    refine ⟨s.right.head.left.length, hL, hle, ?_⟩
    rw [position, hg]
    simp

/-! ## 2. The word-free steps -/

open Classical in
/-- The word-free output refresh: the local R read decides whether to latch
`left.isFirst`, and `leftFirstVM` is itself word-free. -/
noncomputable def refreshL (s : GalilVM) (old : Bool) : Bool :=
  if OnLetterL s then decide (leftFirstVM s) else old

open Classical in
noncomputable def shiftDoneCtlW (x : GalilVML P) : Control :=
  { x.ctl with mode := .scan, output := refreshL (abs' x) x.ctl.output }

open Classical in
/-- The word-free `shift` step. -/
noncomputable def shiftStepW (m : Mirrored1 P) : Mirrored1 P :=
  if RemPosL m.vm then shiftPick m.vm.chain m.vm m.mirL
  else ⟨{ m.vm with ctl := shiftDoneCtlW m.vm }, m.mirL⟩

open Classical in
/-- The word-free `choose` step: `markSet` inlined as the MARKS read. -/
noncomputable def chooseStepW (first : Fin 9) (m : Mirrored1 P) : Mirrored1 P :=
  if m.vm.ctl.odd = true ∧ MarkSetL first (abs' m.vm) then
    mirrorTick1 .stay (chooseVm
      { m.vm.ctl with mode := .rewind, pair := false } m.vm) m
  else
    mirrorTick1 .stay
      (marksVm GalilScaffoldTape.moveLeft
        { m.vm.ctl with odd := !m.vm.ctl.odd } m.vm) m

open Classical in
/-- The word-free `rewind` step: `atFirst` inlined as the MARKS read. -/
noncomputable def rewindStepW (first : Fin 9) (m : Mirrored1 P) : Mirrored1 P :=
  if AtFirstL first (abs' m.vm) then
    mirrorTick1 .stay (rewindDoneVm
      { m.vm.ctl with mode := .replayStart } m.vm) m
  else if m.vm.ctl.pair = true then
    mirrorTick1 .left (rewindPairVm
      { m.vm.ctl with pair := false } m.vm) m
  else
    mirrorTick1 .stay (rewindOneVm
      { m.vm.ctl with pair := true } m.vm) m

theorem chooseStepW_eq (Pw : Shared) (qq : ℕ) (first : Fin 9) (m : Mirrored1 P) :
    chooseStepC (P := P) Pw qq first m = chooseStepW first m := rfl

theorem rewindStepW_eq (Pw : Shared) (qq : ℕ) (first : Fin 9) (m : Mirrored1 P) :
    rewindStepC (P := P) Pw qq first m = rewindStepW first m := rfl

/-- A closed `Shared`: no word, no input, every effect empty.  It is used only
as the `fpp` carrier, where `TickL3` ignores it (`tickL3_fpp_congr`). -/
def dumS : Shared where
  onLetter := fun _ => False
  leftFirst := fun _ => False
  init := fun _ _ => False
  replayStart := fun _ _ => False
  replayPos := fun _ => false
  replayExhausted := fun _ => false
  shiftGuard := fun _ => False
  beginShift := fun _ _ => False
  beginFallback := fun _ _ => False
  restart := fun _ _ => False
  centre := fun _ => 0
  place := fun _ => ⟨[], false⟩

/-- The word-free `fpp` step. -/
noncomputable def ffppW (qq : ℕ) (first : Fin 9) (m : Mirrored1 P) : Mirrored1 P :=
  PalPeg.LocalWF.ffpp dumS qq first m

/-- **The word-free seven.**  `init`, `scan`, `replayStart` are the identity:
`realizes_seven_of_agree` does not constrain them. -/
noncomputable def SL (qq : ℕ) (first : Fin 9) : Steps P where
  init := id
  scan := id
  shift := shiftStepW
  copy := copyStepL
  home := homeStepL
  fpp := ffppW qq first
  markEnd := markEndStepL
  choose := chooseStepW first
  rewind := rewindStepW first
  replayStart := id

/-! ## 3. The five agreements that are `rfl` -/

variable {raw : List (Fin 2)} {stOf : ℕ → State GalilVM}

theorem agree_copy (qq : ℕ) (first : Fin 9) :
    AgreeOn raw stOf (copyStepL (P := P)) (SL qq first).copy .copy := agreeOn_refl _ _

theorem agree_home (qq : ℕ) (first : Fin 9) :
    AgreeOn raw stOf (homeStepL (P := P)) (SL qq first).home .home := agreeOn_refl _ _

theorem agree_markEnd (qq : ℕ) (first : Fin 9) :
    AgreeOn raw stOf (markEndStepL (P := P)) (SL qq first).markEnd .markEnd :=
  agreeOn_refl _ _

theorem agree_choose (Pw : Shared) (qq : ℕ) (first : Fin 9) :
    AgreeOn raw stOf (chooseStepC (P := P) Pw qq first) (SL qq first).choose .choose :=
  fun m _ _ _ _ _ _ _ => chooseStepW_eq Pw qq first m

theorem agree_rewind (Pw : Shared) (qq : ℕ) (first : Fin 9) :
    AgreeOn raw stOf (rewindStepC (P := P) Pw qq first) (SL qq first).rewind .rewind :=
  fun m _ _ _ _ _ _ _ => rewindStepW_eq Pw qq first m

/-! ## 4. `fpp`: `TickL3` is frame-blind on `fpp` states -/

/-- **On an `fpp` state the local tick relation does not see `Shared`.**  The
two `fpp` constructors mention no frame field, and every other constructor
pins a different mode. -/
theorem tickL3_fpp_congr (S S' : Shared) (q : ℕ) (first : Fin 9) (x : GalilVML P)
    (hmd : x.ctl.mode = .fpp) : TickL3 S q first x = TickL3 S' q first x := by
  have key : ∀ (A B : Shared) (y : GalilVML P), TickL3 A q first x y → TickL3 B q first x y := by
    intro A B y h
    cases h with
    | fpp_slice g pc hm hr hq hrun hprog => exact TickL3.fpp_slice x g pc hm hr hq hrun hprog
    | fpp_done g pc hm hr hq hrun hprog => exact TickL3.fpp_done x g pc hm hr hq hrun hprog
    | _ => exfalso; simp_all
  exact funext fun y => propext ⟨key S S' y, key S' S y⟩

/-- **The fpp quantum is word-free.** -/
theorem ffpp_eq_of_fpp (Pw : Shared) (qq : ℕ) (first : Fin 9) (m : Mirrored1 P)
    (hmd : m.vm.ctl.mode = .fpp) :
    PalPeg.LocalWF.ffpp (P := P) Pw qq first m = ffppW qq first m := by
  unfold ffppW PalPeg.LocalWF.ffpp
  rw [tickL3_fpp_congr Pw dumS qq first m.vm hmd]

theorem agree_fpp (Pw : Shared) (qq : ℕ) (first : Fin 9) :
    AgreeOn raw stOf (PalPeg.LocalWF.ffpp (P := P) Pw qq first) (SL qq first).fpp .fpp :=
  fun m _ _ _ hmd _ _ _ => ffpp_eq_of_fpp Pw qq first m hmd

/-! ## 5. `shift`: the one NAMED residual -/

/-- **NAMED residual.**  The R head never stands past the end of the input on
a `shift` state that is handing back to `scan`.  A reachability fact about the
input supply; *not proved here*. -/
def RightInBounds (P : ℕ) (raw : List (Fin 2)) (stOf : ℕ → State GalilVM) : Prop :=
  ∀ m : Mirrored1 P, InvC raw stOf m → m.vm.ctl.mode = .shift → ¬ RemPosL m.vm →
    (abs' m.vm).right.head.left.length ≤ raw.length

theorem agree_shift {Pw : Shared} (qq : ℕ) (first : Fin 9)
    (H_letter : Pw.onLetter = onLetterVM raw) (H_first : Pw.leftFirst = leftFirstVM)
    (H_bound : RightInBounds P raw stOf) :
    AgreeOn raw stOf (shiftStepL (P := P) Pw) (SL qq first).shift .shift := by
  classical
  intro m k j hinv hmd hns hn hneed
  show shiftStepL Pw m = shiftStepW m
  unfold shiftStepL shiftStepW
  by_cases hp : RemPosL m.vm
  · rw [if_pos hp, if_pos hp]
  · rw [if_neg hp, if_neg hp]
    have hb := H_bound m hinv hmd hp
    have href : refreshOf Pw (abs' m.vm) m.vm.ctl.output
        = refreshL (abs' m.vm) m.vm.ctl.output := by
      unfold refreshOf refreshL
      have hon : Pw.onLetter (abs' m.vm) ↔ OnLetterL (abs' m.vm) := by
        rw [H_letter]
        rw [onLetterVM_iff]
        exact ⟨fun h => h.1, fun h => ⟨h, hb⟩⟩
      by_cases hL : OnLetterL (abs' m.vm)
      · rw [if_pos (hon.2 hL), if_pos hL, H_first]
      · rw [if_neg (fun h => hL (hon.1 h)), if_neg hL]
    show (⟨{ m.vm with ctl := shiftDoneCtl Pw m.vm }, m.mirL⟩ : Mirrored1 P)
      = ⟨{ m.vm with ctl := shiftDoneCtlW m.vm }, m.mirL⟩
    unfold shiftDoneCtl shiftDoneCtlW
    rw [href]

/-! ## 6. The seven obligations for the word-free `SL` -/

/-- **Gap (2) closed, modulo `RightInBounds`.** -/
theorem realizes_seven_SL {Pw : Shared} {qq : ℕ} {first : Fin 9} {delay : ℕ}
    (H_shared : ∀ j, PalPeg.GalilTruncTick.SharedTrunc raw j Pw)
    (H_trace : ∀ k, PalPeg.GalilScaffoldTop.Tick (galilFrameS Pw qq first) delay
      (stOf k) (stOf (k+1)))
    (H_start : PalPeg.LocalWF.NoReplay (stOf 0)) (hq : qq ≤ 64)
    (H_wf : ∀ m : Mirrored1 P, InvC raw stOf m → PalPeg.LocalWF.LocalWF m.vm)
    (H_letter : Pw.onLetter = onLetterVM raw) (H_first : Pw.leftFirst = leftFirstVM)
    (H_bound : RightInBounds P raw stOf) :
    Realizes raw stOf (SL (P := P) qq first).shift .shift ∧
    Realizes raw stOf (SL (P := P) qq first).copy .copy ∧
    Realizes raw stOf (SL (P := P) qq first).home .home ∧
    Realizes raw stOf (SL (P := P) qq first).fpp .fpp ∧
    Realizes raw stOf (SL (P := P) qq first).markEnd .markEnd ∧
    Realizes raw stOf (SL (P := P) qq first).choose .choose ∧
    Realizes raw stOf (SL (P := P) qq first).rewind .rewind :=
  PalPeg.CloseoutCoreStep.realizes_seven_of_agree (SL qq first) H_shared H_trace H_start hq H_wf
    (agree_shift qq first H_letter H_first H_bound)
    (agree_copy qq first) (agree_home qq first) (agree_fpp Pw qq first)
    (agree_markEnd qq first) (agree_choose Pw qq first) (agree_rewind Pw qq first)

end PalPeg.CloseoutCoreAgree

#print axioms PalPeg.CloseoutCoreAgree.onLetterVM_iff
#print axioms PalPeg.CloseoutCoreAgree.markSet_eq
#print axioms PalPeg.CloseoutCoreAgree.chooseStepW_eq
#print axioms PalPeg.CloseoutCoreAgree.rewindStepW_eq
#print axioms PalPeg.CloseoutCoreAgree.tickL3_fpp_congr
#print axioms PalPeg.CloseoutCoreAgree.ffpp_eq_of_fpp
#print axioms PalPeg.CloseoutCoreAgree.agree_shift
#print axioms PalPeg.CloseoutCoreAgree.realizes_seven_SL
