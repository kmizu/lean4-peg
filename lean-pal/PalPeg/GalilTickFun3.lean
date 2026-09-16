import PalPeg.GalilTickFun

/-!
# The phase modes of the scaffold tick

`PalPeg.GalilTickFun.Enabled` covers `init`, `replayStart` and `scan`; the
seven *phase* modes `shift`, `copy`, `home`, `fpp`, `markEnd`, `choose` and
`rewind` are excluded there because the VM effects `shiftOne`/`copyOne`/
`copyEnd`/`atLeft`/`fppStart`/`homeStep`/`fppSlice`/`fppDone`/`markBack`/
`markForward`/`choose`/`fppReset`/`rewindOne`/`rewindPair` have no totality
lemma at that layer.

This module supplies them.  Reading the concrete instantiations in
`galilFrame` (shift fields from `shiftFrame`, copy/home from `fallbackFrame`,
fpp from `fppFrame`, markEnd from `marksFrame`, choose/rewind from
`rewindFrame`) each of these effects is a *functional* relation guarded by a
small side condition, so for every mode there is one precondition under which
some constructor applies:

| mode | constructors | precondition |
|---|---|---|
| `shift` | `shift_one` / `shift_done` | `ShiftStep` (heads can move right, chain watching) whenever `remainingPos` |
| `copy` | `copy_one` / `copy_done` | the copy reading of `remainingPos` dominates the shift one (`ShiftIdle`) |
| `home` | `home_start` / `home_step` | SOURCE has a cell to the left unless it is at `LEFT` |
| `fpp` | `fpp_slice` / `fpp_done` | the FPP program can run one quantum of `q` enabled ticks |
| `markEnd` | `markEnd_found` / `markEnd_step` | MARKS has a cell to the left when it reads `END` |
| `choose` | `choose_select` / `choose_step` | a selectable mark on an odd tick, else MARKS has a cell to the left |
| `rewind` | `rewind_done` / `rewind_one` / `rewind_pair` | MARKS is at `FIRST`, else it has a cell to the left |

`PhaseEnabled` is the disjunction of these, mode by mode, and
`phase_tick_gen` / `phase_tick_exists` give the successor.
-/

set_option autoImplicit false
namespace PalPeg.GalilTickFun3

open PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilTickFun
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter

/-! ## Abbreviations for the two tapes the phase guards read -/

/-- The MARKS tape (tape 8 of the FPP program). -/
def marksOf (s : GalilVM) : GalilScaffoldTape.Tape := marksTape s.fpp

/-- The SOURCE tape (tape 7 of the FPP program). -/
def sourceOf (s : GalilVM) : GalilScaffoldTape.Tape := s.fpp.program.config.tapes 7

/-! ## The per-mode preconditions -/

/-- The shift reading of `remainingPos`: `remaining.sign > 0`. -/
def ShiftRemaining (s : GalilVM) : Prop := positive s.remaining = true

/-- The copy reading of `remainingPos`: the walker still reads a letter and
the work counter has not run out. -/
def CopyRemaining (s : GalilVM) : Prop :=
  ¬ (GalilScaffoldPlace.read s.fpp.walker = none ∨ zero s.fpp.work = true)

/-- One unit of `stepShift` is available: C, L and L's successor can move
right and the chain is watching. -/
def ShiftStep (s : GalilVM) : Prop :=
  GalilScaffoldChainVerifier.canRight s.center ∧ GalilScaffoldChainVerifier.canRight s.left ∧
    GalilScaffoldChainVerifier.canRight (GalilScaffoldChainVerifier.right s.left) ∧
      ∃ w, s.chain = .watch w

/-- `shift` mode ticks: either `remainingPos` is false (and `shift_done`
applies) or a shift unit is available. -/
def ShiftEnabled (s : GalilVM) : Prop :=
  (ShiftRemaining s ∨ CopyRemaining s) → ShiftStep s

/-- `copy` mode ticks: the shift reading of `remainingPos` must not outlive
the copy reading, so that `remainingPos` false really means the copy is over
(`copy_done`) and `remainingPos` true really gives the walker a letter
(`copy_one`). -/
def CopyEnabled (s : GalilVM) : Prop := ShiftRemaining s → CopyRemaining s

/-- `home` mode ticks: unless SOURCE reads `LEFT` (and `home_start` applies)
it must have a cell to the left to move onto. -/
def HomeEnabled (s : GalilVM) : Prop :=
  (sourceOf s).focus ≠ 4 → (sourceOf s).left ≠ []

/-- `fpp` mode ticks: the FPP program is running and a whole quantum of `q`
enabled control ticks is available. -/
def FppEnabled (q : ℕ) (s : GalilVM) : Prop :=
  s.fpp.mode = .run ∧
    ∃ p, GalilScaffoldControl.Run GalilFppMarkedCode.code s.fpp.program
      (List.replicate q true) p

/-- `markEnd` mode ticks: when MARKS reads `END` the phase steps back, so the
window must be non-empty. -/
def MarkEndEnabled (s : GalilVM) : Prop :=
  (marksOf s).focus = 5 → (marksOf s).left ≠ []

/-- MARKS reads a selectable mark. -/
def MarkSet (first : Fin 9) (s : GalilVM) : Prop :=
  (marksOf s).focus = 8 ∨ (marksOf s).focus = first

/-- `choose` mode ticks: either the selection fires, or the phase steps back
and MARKS needs a cell to the left. -/
def ChooseEnabled (first : Fin 9) (c : Control) (s : GalilVM) : Prop :=
  (c.odd = true ∧ MarkSet first s) ∨ (marksOf s).left ≠ []

/-- `rewind` mode ticks: either MARKS is at `FIRST` (and `rewind_done`
applies) or it has a cell to the left. -/
def RewindEnabled (first : Fin 9) (s : GalilVM) : Prop :=
  (marksOf s).focus = first ∨ (marksOf s).left ≠ []

/-- **The enabling condition of the phase modes.** -/
def PhaseEnabled (q : ℕ) (first : Fin 9) (x : State GalilVM) : Prop :=
  (x.ctl.mode = .shift ∧ ShiftEnabled x.vm) ∨
  (x.ctl.mode = .copy ∧ CopyEnabled x.vm) ∨
  (x.ctl.mode = .home ∧ HomeEnabled x.vm) ∨
  (x.ctl.mode = .fpp ∧ FppEnabled q x.vm) ∨
  (x.ctl.mode = .markEnd ∧ MarkEndEnabled x.vm) ∨
  (x.ctl.mode = .choose ∧ ChooseEnabled first x.ctl x.vm) ∨
  (x.ctl.mode = .rewind ∧ RewindEnabled first x.vm)

/-! ## The frame fields, spelled out -/

section Fields

variable (P : Shared) (q : ℕ) (first : Fin 9)

theorem frameS_remainingPos (s : GalilVM) :
    (galilFrameS P q first).remainingPos s ↔ (ShiftRemaining s ∨ CopyRemaining s) := Iff.rfl

theorem frameS_shiftOne {s : GalilVM} {v : ShiftVM}
    (h : (shiftFrame (fun _ => True) (fun _ => True)).shiftOne (shiftLens.get s) v) :
    (galilFrameS P q first).shiftOne s (shiftLens.set s v) :=
  Lens.rel_set _ _ _ _ h

theorem frameS_copyOne {s : GalilVM} {v : FppControl.State}
    (h : (fallbackFrame (fun _ => True) (fun _ => True)).copyOne (fppLens.get s) v) :
    (galilFrameS P q first).copyOne s (fppLens.set s v) :=
  Lens.rel_set _ _ _ _ h

theorem frameS_copyEnd {s : GalilVM} {v : FppControl.State}
    (h : (fallbackFrame (fun _ => True) (fun _ => True)).copyEnd (fppLens.get s) v) :
    (galilFrameS P q first).copyEnd s (fppLens.set s v) :=
  Lens.rel_set _ _ _ _ h

theorem frameS_fppStart {s : GalilVM} {v : FppControl.State}
    (h : (fallbackFrame (fun _ => True) (fun _ => True)).fppStart (fppLens.get s) v) :
    (galilFrameS P q first).fppStart s (fppLens.set s v) :=
  Lens.rel_set _ _ _ _ h

theorem frameS_homeStep {s : GalilVM} {v : FppControl.State}
    (h : (fallbackFrame (fun _ => True) (fun _ => True)).homeStep (fppLens.get s) v) :
    (galilFrameS P q first).homeStep s (fppLens.set s v) :=
  Lens.rel_set _ _ _ _ h

theorem frameS_fppSlice {s : GalilVM} {v : FppControl.State}
    (h : (fppFrame q first (fun _ => True) (fun _ => True)).fppSlice (fppLens.get s) v) :
    (galilFrameS P q first).fppSlice s (fppLens.set s v) :=
  Lens.rel_set _ _ _ _ h

theorem frameS_fppDone {s : GalilVM} {v : FppControl.State}
    (h : (fppFrame q first (fun _ => True) (fun _ => True)).fppDone (fppLens.get s) v) :
    (galilFrameS P q first).fppDone s (fppLens.set s v) :=
  Lens.rel_set _ _ _ _ h

theorem frameS_markForward {s : GalilVM} {v : FppControl.State}
    (h : (marksFrame first (fun _ => True) (fun _ => True)).markForward (fppLens.get s) v) :
    (galilFrameS P q first).markForward s (fppLens.set s v) :=
  Lens.rel_set _ _ _ _ h

theorem frameS_markBack {s : GalilVM} {v : RewindVM}
    (h : (rewindFrame first (fun _ => True) (fun _ => True)).markBack (rewindLens.get s) v) :
    (galilFrameS P q first).markBack s (rewindLens.set s v) :=
  Lens.rel_set _ _ _ _ h

theorem frameS_choose {s : GalilVM} {v : RewindVM}
    (h : (rewindFrame first (fun _ => True) (fun _ => True)).choose (rewindLens.get s) v) :
    (galilFrameS P q first).choose s (rewindLens.set s v) :=
  Lens.rel_set _ _ _ _ h

theorem frameS_fppReset {s : GalilVM} {v : RewindVM}
    (h : (rewindFrame first (fun _ => True) (fun _ => True)).fppReset (rewindLens.get s) v) :
    (galilFrameS P q first).fppReset s (rewindLens.set s v) :=
  Lens.rel_set _ _ _ _ h

theorem frameS_rewindOne {s : GalilVM} {v : RewindVM}
    (h : (rewindFrame first (fun _ => True) (fun _ => True)).rewindOne (rewindLens.get s) v) :
    (galilFrameS P q first).rewindOne s (rewindLens.set s v) :=
  Lens.rel_set _ _ _ _ h

theorem frameS_rewindPair {s : GalilVM} {v : RewindVM}
    (h : (rewindFrame first (fun _ => True) (fun _ => True)).rewindPair (rewindLens.get s) v) :
    (galilFrameS P q first).rewindPair s (rewindLens.set s v) :=
  Lens.rel_set _ _ _ _ h

theorem frameS_atLeft (s : GalilVM) :
    (galilFrameS P q first).atLeft s ↔ (sourceOf s).focus = 4 := Iff.rfl

theorem frameS_atEnd (s : GalilVM) :
    (galilFrameS P q first).atEnd s ↔ (marksOf s).focus = 5 := Iff.rfl

theorem frameS_markSet (s : GalilVM) :
    (galilFrameS P q first).markSet s ↔ MarkSet first s := Iff.rfl

theorem frameS_atFirst (s : GalilVM) :
    (galilFrameS P q first).atFirst s ↔ (marksOf s).focus = first := Iff.rfl

/-- The output refresh is always satisfiable. -/
theorem refresh_exists (s : GalilVM) (old : Bool) :
    ∃ o, refresh (galilFrameS P q first) s old o := by
  classical
  refine ⟨if P.onLetter s then decide (P.leftFirst s) else old, ?_, ?_⟩
  · intro hl
    have hl' : P.onLetter s := hl
    show (if P.onLetter s then decide (P.leftFirst s) else old) = true ↔ P.leftFirst s
    rw [if_pos hl']
    exact decide_eq_true_iff
  · intro hl
    have hl' : ¬ P.onLetter s := hl
    show (if P.onLetter s then decide (P.leftFirst s) else old) = old
    rw [if_neg hl']

end Fields

/-! ## The successor of a phase tick -/

/-- **Every phase mode ticks under its precondition.** Stated for an arbitrary
`Shared`: the phase fields of `galilFrameS` do not depend on it (only the
output refresh of `shift_done` consults `P.onLetter`/`P.leftFirst`, and that
is total). -/
theorem phase_tick_gen (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) (x : State GalilVM)
    (hx : PhaseEnabled q first x) :
    ∃ y, Tick (galilFrameS P q first) delay x y := by
  classical
  obtain ⟨c, s⟩ := x
  rcases hx with ⟨hm, hs⟩ | ⟨hm, hs⟩ | ⟨hm, hs⟩ | ⟨hm, hs⟩ | ⟨hm, hs⟩ | ⟨hm, hs⟩ | ⟨hm, hs⟩
  · -- shift
    by_cases hr : ShiftRemaining s ∨ CopyRemaining s
    · obtain ⟨h1, h2, h3, w, hw⟩ := hs hr
      refine ⟨_, Tick.shift_one (F := galilFrameS P q first) (delay := delay) c s
        (shiftLens.set s ⟨shiftTick (shiftLens.get s).shift,
          .watch (chainShiftOne w), inc (inc s.cycle)⟩) hm hr ?_⟩
      exact frameS_shiftOne P q first ⟨h1, h2, h3, w, hw, rfl⟩
    · obtain ⟨o, ho⟩ := refresh_exists P q first s c.output
      exact ⟨_, Tick.shift_done (F := galilFrameS P q first) (delay := delay) c s o hm hr ho⟩
  · -- copy
    by_cases hr : ShiftRemaining s ∨ CopyRemaining s
    · have hcr : CopyRemaining s := hr.elim hs id
      have hw : GalilScaffoldPlace.read s.fpp.walker ≠ none := fun h => hcr (Or.inl h)
      obtain ⟨a, ha⟩ : ∃ a, GalilScaffoldPlace.read s.fpp.walker = some a := by
        cases h : GalilScaffoldPlace.read s.fpp.walker with
        | none => exact absurd h hw
        | some a => exact ⟨a, rfl⟩
      refine ⟨_, Tick.copy_one (F := galilFrameS P q first) (delay := delay) c s _ hm hr
        (frameS_copyOne P q first (v := {s.fpp with
          program := FppControl.tape s.fpp 7 (fun t => GalilScaffoldTape.moveRight
            (GalilScaffoldTape.write t (GalilFppPreparation.symbol a))),
          work := dec s.fpp.work,
          walker := GalilScaffoldPlace.left s.fpp.walker}) ⟨a, ha, rfl⟩)⟩
    · refine ⟨_, Tick.copy_done (F := galilFrameS P q first) (delay := delay) c s _ hm hr
        (frameS_copyEnd P q first (v := {s.fpp with
          program := FppControl.tape s.fpp 7 (fun t => GalilScaffoldTape.write t 5),
          mode := .home,
          finalStage := (GalilScaffoldPlace.read s.fpp.walker).isNone}) rfl)⟩
  · -- home
    by_cases hl : (sourceOf s).focus = 4
    · exact ⟨_, Tick.home_start (F := galilFrameS P q first) (delay := delay) c s _ hm hl
        (frameS_fppStart P q first (v := {s.fpp with
          program := GalilScaffoldControl.start 320 s.fpp.program, mode := .run}) rfl)⟩
    · exact ⟨_, Tick.home_step (F := galilFrameS P q first) (delay := delay) c s _ hm hl
        (frameS_homeStep P q first (v := {s.fpp with
          program := FppControl.tape s.fpp 7 GalilScaffoldTape.moveLeft}) ⟨hs hl, rfl⟩)⟩
  · -- fpp
    obtain ⟨hrun, p, hp⟩ := hs
    by_cases hd : p.done = true
    · exact ⟨_, Tick.fpp_done (F := galilFrameS P q first) (delay := delay) c s _ hm
        (frameS_fppDone P q first (v := {s.fpp with program := markNew p first})
          ⟨hrun, p, hp, hd, rfl⟩)⟩
    · have hd' : p.done = false := Bool.eq_false_iff.mpr hd
      exact ⟨_, Tick.fpp_slice (F := galilFrameS P q first) (delay := delay) c s _ hm
        (frameS_fppSlice P q first (v := {s.fpp with program := p}) ⟨hrun, hp, hd', rfl⟩)⟩
  · -- markEnd
    by_cases he : (marksOf s).focus = 5
    · exact ⟨_, Tick.markEnd_found (F := galilFrameS P q first) (delay := delay) c s _ hm he
        (frameS_markBack P q first
          (v := {rewindLens.get s with fpp := markStep s.fpp GalilScaffoldTape.moveLeft})
          ⟨hs he, rfl⟩)⟩
    · exact ⟨_, Tick.markEnd_step (F := galilFrameS P q first) (delay := delay) c s _ hm he
        (frameS_markForward P q first
          (v := markStep s.fpp GalilScaffoldTape.moveRight) rfl)⟩
  · -- choose
    by_cases hsel : c.odd = true ∧ MarkSet first s
    · exact ⟨_, Tick.choose_select (F := galilFrameS P q first) (delay := delay) c s _ hm
        hsel.1 hsel.2 (frameS_choose P q first
          (v := {rewindLens.get s with
              left := s.right, center := s.right,
              length := ofNat 1, radius := reset}) rfl)⟩
    · have hne : (marksOf s).left ≠ [] := hs.elim (fun h => absurd h hsel) id
      have hs' : c.odd = false ∨ ¬ (galilFrameS P q first).markSet s := by
        by_cases ho : c.odd = true
        · exact Or.inr (fun h => hsel ⟨ho, h⟩)
        · exact Or.inl (Bool.eq_false_iff.mpr ho)
      exact ⟨_, Tick.choose_step (F := galilFrameS P q first) (delay := delay) c s _ hm hs'
        (frameS_markBack P q first
          (v := {rewindLens.get s with fpp := markStep s.fpp GalilScaffoldTape.moveLeft})
          ⟨hne, rfl⟩)⟩
  · -- rewind
    by_cases hf : (marksOf s).focus = first
    · exact ⟨_, Tick.rewind_done (F := galilFrameS P q first) (delay := delay) c s _ hm hf
        (frameS_fppReset P q first
          (v := {rewindLens.get s with
            fpp := {s.fpp with program := GalilScaffoldControl.reset 320 s.fpp.program}}) rfl)⟩
    · have hne : (marksOf s).left ≠ [] := hs.elim (fun h => absurd h hf) id
      by_cases hp : c.pair = true
      · exact ⟨_, Tick.rewind_pair (F := galilFrameS P q first) (delay := delay) c s _ hm hf hp
          (frameS_rewindPair P q first
            (v := {rewindLens.get s with
              fpp := markStep s.fpp GalilScaffoldTape.moveLeft,
              left := GalilScaffoldInputHead.left s.left, length := inc s.length,
              center := GalilScaffoldInputHead.left s.center, radius := inc s.radius})
            ⟨hne, rfl⟩)⟩
      · exact ⟨_, Tick.rewind_one (F := galilFrameS P q first) (delay := delay) c s _ hm hf
          (Bool.eq_false_iff.mpr hp)
          (frameS_rewindOne P q first
            (v := {rewindLens.get s with
              fpp := markStep s.fpp GalilScaffoldTape.moveLeft,
              left := GalilScaffoldInputHead.left s.left, length := inc s.length})
            ⟨hne, rfl⟩)⟩

section Fixed

variable (onLetter leftFirst : GalilVM → Prop) (centre : GalilVM → Fin 3)
  (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9) (delay : ℕ)

/-- **The phase modes of the concrete `sharedFun`.** -/
theorem phase_tick_exists (x : State GalilVM) (hx : PhaseEnabled q first x) :
    ∃ y, Tick (galilFrameS (sharedFun onLetter leftFirst centre place entry) q first) delay x y :=
  phase_tick_gen _ q first delay x hx

/-- `Enabled` widened by the phase modes: every mode of the controller now has
a successor. -/
def EnabledP (x : State GalilVM) : Prop :=
  Enabled onLetter leftFirst centre place entry x ∨ PhaseEnabled q first x

theorem tick_exists_P (x : State GalilVM)
    (hx : EnabledP onLetter leftFirst centre place entry q first x) :
    ∃ y, Tick (galilFrameS (sharedFun onLetter leftFirst centre place entry) q first) delay x y := by
  rcases hx with h | h
  · exact tick_exists onLetter leftFirst centre place entry q first delay x h
  · exact phase_tick_exists onLetter leftFirst centre place entry q first delay x h

end Fixed

#print axioms phase_tick_gen
#print axioms phase_tick_exists
#print axioms tick_exists_P

end PalPeg.GalilTickFun3
