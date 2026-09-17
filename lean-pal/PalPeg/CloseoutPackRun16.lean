import PalPeg.CloseoutPackRun15

/-!
# `CloseoutPackRun16`: producers for `MarksEntry`, and the guarded variant

`CloseoutPackRun15` isolated the last tick branch of the centre margin as
`MarksEntry first s` at `choose_select`: the `FIRST` cell `f` of the MARKS
tape satisfies `mh s + 2 ≤ position R + f`.  This file settles what that
residual is on the machine.

* §1 **`MarksEntry` is not free.**  Because `f ≤ mh s`, `MarksEntry` forces
  `2 ≤ position R` outright (`two_le_right_of_marksEntry`), so at any
  selecting `choose` state whose right head sits on input place `1`
  (`position R = 1`) it is **false** (`marksEntry_false_at_place_one`).  With
  the FPP layout (`FIRST` at cell `1`, `fpp_then_markEnd_All`) and the
  selected cell `mh s`, the rewind walk lands `L` at
  `position R − (mh s − 1)`; `MarksEntry` says exactly that this is `≥ 2`,
  i.e. the chosen palindromic suffix does not start at input place `1`.
  Whether that corner is *reachable* is the leftmost-live-centre invariant
  (a whole-prefix palindrome cannot mismatch at the tracked centre); it is not
  available in the existing files, so the unguarded form is only produced
  under the explicit hypothesis `mh s ≠ position R` (`marksEntry_of_layout`).

* §2 `ChooseLayout first s` — **(NAMED)** the choose-state facts the FPP phase
  delivers (`denote = update (marks w) 1 first`, `1 ≤ mh s ≤ w.length`) plus
  the *tight* window bound `w.length ≤ position R` (the copy walker never
  crosses the origin; `CPack.fpp` only records `≤ 2·position R`).  It is
  preserved by `choose_step` while `2 ≤ mh s` (`chooseLayout_step`).

* §3 `MarksEntry'` — the **guarded** residual `mh s + 1 ≤ position R + f`,
  produced from `ChooseLayout` with no side condition
  (`marksEntry'_of_layout`), and `MarksInv'` (guarded (a)) carried by every
  tick (`marksInv'_tick`) and along runs (`marksInv'_of_run`) under
  `H_marksEntry'`.

* §4 The guarded corners: at every `rewind` state `1 ≤ position L`, and when
  `¬ atFirst` the `FIRST` cell is strictly left of the head, so
  `2 ≤ position L ≤ position C`, giving `0 < position (left L)`,
  `0 < position (left C)`, and `CentreMargin`'s inequality
  (`rewindLeft_of_marksInv'`, `rewindCentre_of_marksInv'`,
  `centreMargin_of_marksInv'_notFirst`).  These are exactly what
  `rewind_one` / `rewind_pair` need; the unguarded `rewind_done` demand
  `2 ≤ position L` is the one `MarksEntry` (not `MarksEntry'`) buys.

## Honest status

Standard axioms only; unconditional `PAL ∈ PEG` remains open.  The remaining
hypothesis is `ChooseLayout` at selecting `choose` states along a run — its
tight window bound `w.length ≤ position R` and the evenness of `w.length`
(which keeps the walk from passing cell `1` with `odd = false`) are not yet
derived from the run.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPackRun16

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldInputHead GalilScaffoldCounter
open PalPeg.CloseoutPackRun13 PalPeg.CloseoutPackRun15
open PalPeg.GalilCentreLive (mh)

/-! ## 1. `MarksEntry` excludes the right head at input place `1` -/

/-- `MarksEntry` forces `2 ≤ position R`: the `FIRST` cell is at or left of
the head. -/
theorem two_le_right_of_marksEntry {first : Fin 9} {s : GalilVM}
    (h : MarksEntry first s) : 2 ≤ position s.right := by
  obtain ⟨f, -, hfm, -, hb⟩ := h
  omega

/-- **`MarksEntry` is false whenever the right head is at input place `1`
(or the origin).** -/
theorem marksEntry_false_at_place_one {first : Fin 9} {s : GalilVM}
    (h : position s.right ≤ 1) : ¬ MarksEntry first s := by
  intro hme
  have := two_le_right_of_marksEntry hme
  omega

#print axioms two_le_right_of_marksEntry
#print axioms marksEntry_false_at_place_one

/-! ## 2. The choose-state layout -/

/-- **(NAMED) the choose-state layout.**  The MARKS tape is the FPP layout of
a window `w` with `FIRST` at cell `1`, the head is between cell `1` and cell
`w.length`, and the window is at most `position R` long (the copy walker
cannot cross the input origin). -/
def ChooseLayout (first : Fin 9) (s : GalilVM) : Prop :=
  ∃ w : List (Fin 3),
    GalilScaffoldTape.denote (marksTape s.fpp) =
      Function.update (GalilFppMarkedLayout.marks w) 1 first ∧
    1 ≤ mh s ∧ mh s ≤ w.length ∧ w.length ≤ position s.right

theorem first_cell_of_layout {first : Fin 9} {s : GalilVM} {w : List (Fin 3)}
    (h : GalilScaffoldTape.denote (marksTape s.fpp) =
      Function.update (GalilFppMarkedLayout.marks w) 1 first) :
    GalilScaffoldTape.denote (marksTape s.fpp) 1 = first := by
  rw [h]; simp

/-- **The unguarded residual from the layout, under `mh s ≠ position R`.**
The side condition says the selected cell is not the whole input prefix. -/
theorem marksEntry_of_layout {first : Fin 9} {s : GalilVM}
    (h : ChooseLayout first s) (hne : mh s ≠ position s.right) : MarksEntry first s := by
  obtain ⟨w, hden, h1, hmw, hwr⟩ := h
  exact ⟨1, le_refl 1, h1, first_cell_of_layout hden, by omega⟩

/-- Conversely the layout turns the residual into the side condition only
through the `FIRST` cell at `1`: `MarksEntry` alone gives `2 ≤ position R`
(§1); with `mh s = w.length = position R` (the whole prefix selected) the
layout refutes it. -/
theorem marksEntry_false_of_whole_prefix {first : Fin 9} {s : GalilVM}
    (h : ChooseLayout first s) (hfirst : ∀ f, GalilScaffoldTape.denote (marksTape s.fpp) f = first → f = 1)
    (heq : mh s = position s.right) : ¬ MarksEntry first s := by
  intro hme
  obtain ⟨f, -, -, hden, hb⟩ := hme
  have := hfirst f hden
  obtain ⟨w, -, -, -, -⟩ := h
  omega

/-- **`choose_step` preserves the layout** while the head is right of cell `1`. -/
theorem chooseLayout_step (P : Shared) (q : ℕ) (first : Fin 9)
    {s t : GalilVM} (h : ChooseLayout first s) (h2 : 2 ≤ mh s)
    (hb : (galilFrameS P q first).markBack s t) : ChooseLayout first t := by
  obtain ⟨⟨hleft, heq⟩, hset⟩ := hb
  have hfpp : t.fpp = markStep s.fpp GalilScaffoldTape.moveLeft := by rw [hset, heq]; rfl
  have hr : t.right = s.right := by rw [hset, heq]; rfl
  have hpos : 0 < GalilScaffoldTape.head (marksTape s.fpp) :=
    (GalilScaffoldTape.left_legal _).1 hleft
  obtain ⟨w, hden, h1, hmw, hwr⟩ := h
  have hmt : mh t = mh s - 1 := by
    unfold mh; rw [hfpp, markStep_tape, GalilScaffoldTape.left_head _ hpos]
  have hdt : GalilScaffoldTape.denote (marksTape t.fpp) =
      GalilScaffoldTape.denote (marksTape s.fpp) := by
    rw [hfpp, markStep_tape, GalilScaffoldTape.left_denote]
  refine ⟨w, by rw [hdt]; exact hden, ?_, ?_, by rw [hr]; exact hwr⟩
  · rw [hmt]; omega
  · rw [hmt]; omega

#print axioms marksEntry_of_layout
#print axioms marksEntry_false_of_whole_prefix
#print axioms chooseLayout_step

/-- The run-wide `H_marksEntry` from the layout plus the side condition at
every selecting `choose` state. -/
theorem h_marksEntry_of_layout (P : Shared) (q : ℕ) (first : Fin 9)
    (hl : ∀ (c : Control) (s : GalilVM), c.mode = Mode.choose → c.odd = true →
      (galilFrameS P q first).markSet s → ChooseLayout first s ∧ mh s ≠ position s.right) :
    H_marksEntry P q first := by
  intro c s hm ho hs
  obtain ⟨h, hne⟩ := hl c s hm ho hs
  exact marksEntry_of_layout h hne

#print axioms h_marksEntry_of_layout

/-! ## 3. The guarded residual and its invariant -/

/-- **(NAMED) the guarded residual.**  `mh s + 1 ≤ position R + f`: the
chosen palindromic suffix may start at input place `1`, not at the origin. -/
def MarksEntry' (first : Fin 9) (s : GalilVM) : Prop :=
  ∃ f, 1 ≤ f ∧ f ≤ mh s ∧ GalilScaffoldTape.denote (marksTape s.fpp) f = first ∧
    mh s + 1 ≤ position s.right + f

def H_marksEntry' (P : Shared) (q : ℕ) (first : Fin 9) : Prop :=
  ∀ (c : Control) (s : GalilVM), c.mode = Mode.choose → c.odd = true →
    (galilFrameS P q first).markSet s → MarksEntry' first s

theorem marksEntry'_of_marksEntry {first : Fin 9} {s : GalilVM}
    (h : MarksEntry first s) : MarksEntry' first s := by
  obtain ⟨f, h1, hfm, hden, hb⟩ := h
  exact ⟨f, h1, hfm, hden, by omega⟩

/-- **The guarded residual from the layout, with no side condition.** -/
theorem marksEntry'_of_layout {first : Fin 9} {s : GalilVM}
    (h : ChooseLayout first s) : MarksEntry' first s := by
  obtain ⟨w, hden, h1, hmw, hwr⟩ := h
  exact ⟨1, le_refl 1, h1, first_cell_of_layout hden, by omega⟩

theorem h_marksEntry'_of_layout (P : Shared) (q : ℕ) (first : Fin 9)
    (hl : ∀ (c : Control) (s : GalilVM), c.mode = Mode.choose → c.odd = true →
      (galilFrameS P q first).markSet s → ChooseLayout first s) :
    H_marksEntry' P q first :=
  fun c s hm ho hs => marksEntry'_of_layout (hl c s hm ho hs)

#print axioms marksEntry'_of_layout
#print axioms h_marksEntry'_of_layout

/-- **(NAMED) the guarded MARKS-tape invariant during `rewind`.**  (a) with
`mh s + 1 ≤ position L + f`; (b) as in `MarksInv`. -/
def MarksInv' (first : Fin 9) (c : Control) (s : GalilVM) : Prop :=
  c.mode = Mode.rewind →
    (∃ f, 1 ≤ f ∧ f ≤ mh s ∧ GalilScaffoldTape.denote (marksTape s.fpp) f = first ∧
      mh s + 1 ≤ position s.left + f) ∧
    (∃ r, s.radius = ofNat r ∧ position s.left + r + pairOff c ≤ position s.center)

theorem marksInv'_of_marksInv {first : Fin 9} {c : Control} {s : GalilVM}
    (h : MarksInv first c s) : MarksInv' first c s := by
  intro hm
  obtain ⟨⟨f, h1, hfm, hden, hb⟩, hr⟩ := h hm
  exact ⟨⟨f, h1, hfm, hden, by omega⟩, hr⟩

theorem marksInv'_of_mode {first : Fin 9} {c : Control} {s : GalilVM} {m : Mode}
    (h1 : m ≠ Mode.rewind) (h : c.mode = m) : MarksInv' first c s := by
  intro hm; exact absurd (h.symm.trans hm) h1

macro "vacuous_mi'" : tactic =>
  `(tactic| first
    | exact marksInv'_of_mode (m := Mode.init) (by decide) (by first | rfl | assumption)
    | exact marksInv'_of_mode (m := Mode.scan) (by decide) (by first | rfl | assumption)
    | exact marksInv'_of_mode (m := Mode.shift) (by decide) (by first | rfl | assumption)
    | exact marksInv'_of_mode (m := Mode.copy) (by decide) (by first | rfl | assumption)
    | exact marksInv'_of_mode (m := Mode.home) (by decide) (by first | rfl | assumption)
    | exact marksInv'_of_mode (m := Mode.fpp) (by decide) (by first | rfl | assumption)
    | exact marksInv'_of_mode (m := Mode.markEnd) (by decide) (by first | rfl | assumption)
    | exact marksInv'_of_mode (m := Mode.choose) (by decide) (by first | rfl | assumption)
    | exact marksInv'_of_mode (m := Mode.replayStart) (by decide)
        (by first | rfl | assumption))

/-- **(KEY) one tick preserves `MarksInv'`**, given `MarksEntry'` at a
selecting `choose` source. -/
theorem marksInv'_tick (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    {c c' : Control} {s t : GalilVM} (hp : MarksInv' first c s)
    (he : c.mode = Mode.choose → c.odd = true → (galilFrameS P q first).markSet s →
      MarksEntry' first s)
    (h : Tick (galilFrameS P q first) delay ⟨c, s⟩ ⟨c', t⟩) : MarksInv' first c' t := by
  cases h
  all_goals try vacuous_mi'
  case choose_select =>
    rename_i hm hodd hs hi
    obtain ⟨heq, hset⟩ := hi
    have hl : t.left = s.right := by rw [hset, heq]; rfl
    have hc : t.center = s.right := by rw [hset, heq]; rfl
    have hr : t.radius = reset := by rw [hset, heq]; rfl
    have hfpp : t.fpp = s.fpp := by rw [hset, heq]; rfl
    obtain ⟨f, hf1, hfm, hden, hb⟩ := he hm hodd hs
    intro _
    refine ⟨⟨f, hf1, ?_, ?_, ?_⟩, ⟨0, by rw [hr]; rfl, ?_⟩⟩
    · unfold mh; rw [hfpp]; exact hfm
    · rw [hfpp]; exact hden
    · unfold mh; rw [hfpp, hl]; exact hb
    · rw [hl, hc]; simp [pairOff]
  case rewind_one =>
    rename_i hm hf hpr hi
    obtain ⟨⟨hleft, heq⟩, hset⟩ := hi
    have hl : t.left = GalilScaffoldInputHead.left s.left := by rw [hset, heq]; rfl
    have hc : t.center = s.center := by rw [hset, heq]; rfl
    have hr : t.radius = s.radius := by rw [hset, heq]; rfl
    have hfpp : t.fpp = markStep s.fpp GalilScaffoldTape.moveLeft := by rw [hset, heq]; rfl
    have hpos : 0 < GalilScaffoldTape.head (marksTape s.fpp) :=
      (GalilScaffoldTape.left_legal _).1 hleft
    have hnf : (marksTape s.fpp).focus ≠ first := hpr
    intro _
    obtain ⟨⟨f, hf1, hfm, hden, hb⟩, ⟨r, hrad, hle⟩⟩ := hp hm
    have hmt : mh t = mh s - 1 := by
      unfold mh; rw [hfpp, markStep_tape, GalilScaffoldTape.left_head _ hpos]
    have hdt : GalilScaffoldTape.denote (marksTape t.fpp) =
        GalilScaffoldTape.denote (marksTape s.fpp) := by
      rw [hfpp, markStep_tape, GalilScaffoldTape.left_denote]
    have hne : f ≠ mh s := by
      intro hfe
      apply hnf
      rw [← GalilScaffoldTape.focus_eq, ← hden, hfe]; rfl
    have hpo : pairOff c = 0 := by simp [pairOff, hf]
    have hpo' : pairOff {c with pair := true} = 1 := by simp [pairOff]
    rw [hpo] at hle
    refine ⟨⟨f, hf1, ?_, ?_, ?_⟩, ⟨r, by rw [hr]; exact hrad, ?_⟩⟩
    · rw [hmt]; omega
    · rw [hdt]; exact hden
    · rw [hmt, hl, position_left]; omega
    · rw [hl, hc, position_left, hpo']; omega
  case rewind_pair =>
    rename_i hm hf hpr hi
    obtain ⟨⟨hleft, heq⟩, hset⟩ := hi
    have hl : t.left = GalilScaffoldInputHead.left s.left := by rw [hset, heq]; rfl
    have hc : t.center = GalilScaffoldInputHead.left s.center := by rw [hset, heq]; rfl
    have hr : t.radius = inc s.radius := by rw [hset, heq]; rfl
    have hfpp : t.fpp = markStep s.fpp GalilScaffoldTape.moveLeft := by rw [hset, heq]; rfl
    have hpos : 0 < GalilScaffoldTape.head (marksTape s.fpp) :=
      (GalilScaffoldTape.left_legal _).1 hleft
    have hnf : (marksTape s.fpp).focus ≠ first := hpr
    intro _
    obtain ⟨⟨f, hf1, hfm, hden, hb⟩, ⟨r, hrad, hle⟩⟩ := hp hm
    have hmt : mh t = mh s - 1 := by
      unfold mh; rw [hfpp, markStep_tape, GalilScaffoldTape.left_head _ hpos]
    have hdt : GalilScaffoldTape.denote (marksTape t.fpp) =
        GalilScaffoldTape.denote (marksTape s.fpp) := by
      rw [hfpp, markStep_tape, GalilScaffoldTape.left_denote]
    have hne : f ≠ mh s := by
      intro hfe
      apply hnf
      rw [← GalilScaffoldTape.focus_eq, ← hden, hfe]; rfl
    have hpo : pairOff c = 1 := by simp [pairOff, hf]
    have hpo' : pairOff {c with pair := false} = 0 := by simp [pairOff]
    rw [hpo] at hle
    refine ⟨⟨f, hf1, ?_, ?_, ?_⟩, ⟨r + 1, by rw [hr, hrad, inc_ofNat], ?_⟩⟩
    · rw [hmt]; omega
    · rw [hdt]; exact hden
    · rw [hmt, hl, position_left]; omega
    · rw [hl, hc, position_left, position_left, hpo']; omega

#print axioms marksInv'_tick

theorem marksInv'_steps (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (he : H_marksEntry' P q first) {n : ℕ} {x y : State GalilVM}
    (h : Steps (galilFrameS P q first) delay n x y)
    (hp : MarksInv' first x.ctl x.vm) : MarksInv' first y.ctl y.vm := by
  induction h with
  | zero x => exact hp
  | @succ n x w y ht _ ih =>
    exact ih (marksInv'_tick P q first delay hp (fun hm ho hs => he x.ctl x.vm hm ho hs) ht)

/-- `MarksInv'` on every state of a run parked outside `rewind`. -/
theorem marksInv'_of_run (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (he : H_marksEntry' P q first) {n : ℕ} {x y : State GalilVM}
    (h : Steps (galilFrameS P q first) delay n x y)
    {m : Mode} (h1 : m ≠ Mode.rewind) (hx : x.ctl.mode = m) :
    MarksInv' first y.ctl y.vm :=
  marksInv'_steps P q first delay he h (marksInv'_of_mode h1 hx)

#print axioms marksInv'_steps
#print axioms marksInv'_of_run

/-! ## 4. The guarded corners -/

/-- At every `rewind` state the left head is off the origin. -/
theorem one_le_left_of_marksInv' {first : Fin 9} {c : Control} {s : GalilVM}
    (h : MarksInv' first c s) (hm : c.mode = Mode.rewind) : 1 ≤ position s.left := by
  obtain ⟨⟨f, -, hfm, -, hb⟩, -⟩ := h hm
  omega

/-- When the head is not on the `FIRST` cell, that cell is strictly left of
the head (`focus_eq`), so `2 ≤ position L`. -/
theorem two_le_left_of_marksInv' {first : Fin 9} {c : Control} {s : GalilVM}
    (h : MarksInv' first c s) (hm : c.mode = Mode.rewind)
    (hnf : (marksTape s.fpp).focus ≠ first) : 2 ≤ position s.left := by
  obtain ⟨⟨f, -, hfm, hden, hb⟩, -⟩ := h hm
  have hne : f ≠ mh s := by
    intro hfe
    apply hnf
    rw [← GalilScaffoldTape.focus_eq, ← hden, hfe]; rfl
  omega

/-- **The guarded left corner** (`rewind_one` / `rewind_pair`). -/
theorem rewindLeft_of_marksInv' (P : Shared) (q : ℕ) {first : Fin 9} {c : Control}
    {s : GalilVM} (h : MarksInv' first c s) (hm : c.mode = Mode.rewind)
    (hnf : ¬ (galilFrameS P q first).atFirst s) :
    0 < position (GalilScaffoldInputHead.left s.left) :=
  PalPeg.CloseoutLPack4.left_pos_of_two (two_le_left_of_marksInv' h hm hnf)

/-- **The guarded centre corner** (`rewind_pair`): the centre is at or right
of the left head by (b). -/
theorem rewindCentre_of_marksInv' (P : Shared) (q : ℕ) {first : Fin 9} {c : Control}
    {s : GalilVM} (h : MarksInv' first c s) (hm : c.mode = Mode.rewind)
    (hnf : ¬ (galilFrameS P q first).atFirst s) :
    0 < position (GalilScaffoldInputHead.left s.center) := by
  have h2 := two_le_left_of_marksInv' h hm hnf
  obtain ⟨-, ⟨r, -, hle⟩⟩ := h hm
  exact PalPeg.CloseoutLPack4.left_pos_of_two (by omega)

/-- **`CentreMargin`'s inequality off the `FIRST` cell.** -/
theorem centreMargin_of_marksInv'_notFirst (P : Shared) (q : ℕ) {first : Fin 9}
    {c : Control} {s : GalilVM} (h : MarksInv' first c s) (hm : c.mode = Mode.rewind)
    (hnf : ¬ (galilFrameS P q first).atFirst s) :
    ∀ r : ℕ, s.radius = ofNat r → r + pairOff c + 2 ≤ position s.center := by
  intro r hrad
  have h2 := two_le_left_of_marksInv' h hm hnf
  obtain ⟨-, ⟨r', hr', hle⟩⟩ := h hm
  have := ofNat_eq_of_radius hrad hr'
  subst this
  omega

/-- Packaged along a run: both guarded corners at every `rewind` state off
the `FIRST` cell, under `H_marksEntry'`. -/
theorem corners_of_marks' (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (he : H_marksEntry' P q first) {n : ℕ} {x y : State GalilVM}
    (h : Steps (galilFrameS P q first) delay n x y)
    {m : Mode} (h1 : m ≠ Mode.rewind) (hx : x.ctl.mode = m)
    (hm : y.ctl.mode = Mode.rewind) (hnf : ¬ (galilFrameS P q first).atFirst y.vm) :
    0 < position (GalilScaffoldInputHead.left y.vm.left) ∧
      0 < position (GalilScaffoldInputHead.left y.vm.center) := by
  have hi := marksInv'_of_run P q first delay he h h1 hx
  exact ⟨rewindLeft_of_marksInv' P q hi hm hnf, rewindCentre_of_marksInv' P q hi hm hnf⟩

#print axioms one_le_left_of_marksInv'
#print axioms rewindLeft_of_marksInv'
#print axioms rewindCentre_of_marksInv'
#print axioms centreMargin_of_marksInv'_notFirst
#print axioms corners_of_marks'

end PalPeg.CloseoutPackRun16
