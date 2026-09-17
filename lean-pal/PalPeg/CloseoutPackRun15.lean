import PalPeg.CloseoutPackRun14
import PalPeg.GalilCentreLive

/-!
# `CloseoutPackRun15`: `CentreMargin` from a MARKS-tape invariant

`CloseoutPackRun13` reduced both rewind corners to the single leaf
`CentreMargin` (`radius + pairOff + 2 ≤ position C` during `rewind`) and
recorded that the leaf is a fact about the MARKS tape invisible to `Tick`.
This file names that fact and carries it.

* §1 `MarksInv first c s` — **(NAMED)** during `rewind`, (a) some cell `f ≥ 1`
  at or left of the MARKS head carries the `FIRST` mark and the walk that
  remains (`mh − f` cells, one input place each for `L`) stops with
  `2 ≤ position L`, i.e. `mh + 2 ≤ position L + f`; and (b) the exact
  (untruncated) coupling `position L + radius + pairOff ≤ position C`, the
  lower half that `RCouple` (which only has `≤` the other way) cannot give.
* §2 `centreMargin_of_marksInv` — `MarksInv → CentreMargin`, pointwise.
* §3 `MarksEntry first s` — **(NAMED)** the residual at the selection tick
  `choose_select`: at the selected cell `mh s`, the `FIRST` cell `f` satisfies
  `mh s + 2 ≤ position R + f`.  With the FPP layout (`markNew` writes `FIRST`
  at cell `1`, `GalilCentreLive.fpp_done`) this reads `mh s + 1 ≤ position R`:
  the chosen palindromic suffix does not start at input place `1`.
* §4 `marksInv_tick` — every tick of `galilFrameS` preserves `MarksInv`, with
  `MarksEntry` supplied only at `choose_select`; `rewind_one` / `rewind_pair`
  are closed by `focus_eq` (`¬ atFirst` ⇒ the `FIRST` cell is strictly left
  of the head) and `position_left`.  §5 `marksInv_steps` / `marksInv_of_run`
  / `centreMargin_of_marks` — along a run parked outside `rewind`, under the
  run-wide `H_marksEntry`.

## Honest status

Standard axioms only; unconditional `PAL ∈ PEG` remains open.  The only tick
branch left is `choose_select`, isolated as `MarksEntry` (`H_marksEntry` along
a run).  Note that the unguarded `CentreMargin` demands `2 ≤ position L` also
at the final `rewind_done` state, so `MarksEntry` genuinely excludes a chosen
palindrome starting at place `1`; the guarded corner of `CloseoutPackRun13`
(`¬ atFirst → 0 < position (left L)`) would only need `mh s + 1 ≤ position R + f`.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPackRun15

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldInputHead GalilScaffoldCounter
open PalPeg.CloseoutPackRun13
open PalPeg.GalilCentreLive (mh)

/-! ## 1. The MARKS-tape invariant -/

/-- **(NAMED) the MARKS-tape invariant during `rewind`.**  (a) a `FIRST` cell
`f ≥ 1` sits at or left of the MARKS head and the walk left to it keeps
`2 ≤ position L`; (b) the exact lower coupling of the centre. -/
def MarksInv (first : Fin 9) (c : Control) (s : GalilVM) : Prop :=
  c.mode = Mode.rewind →
    (∃ f, 1 ≤ f ∧ f ≤ mh s ∧ GalilScaffoldTape.denote (marksTape s.fpp) f = first ∧
      mh s + 2 ≤ position s.left + f) ∧
    (∃ r, s.radius = ofNat r ∧ position s.left + r + pairOff c ≤ position s.center)

theorem marksInv_of_mode {first : Fin 9} {c : Control} {s : GalilVM} {m : Mode}
    (h1 : m ≠ Mode.rewind) (h : c.mode = m) : MarksInv first c s := by
  intro hm; exact absurd (h.symm.trans hm) h1

macro "vacuous_mi" : tactic =>
  `(tactic| first
    | exact marksInv_of_mode (m := Mode.init) (by decide) (by first | rfl | assumption)
    | exact marksInv_of_mode (m := Mode.scan) (by decide) (by first | rfl | assumption)
    | exact marksInv_of_mode (m := Mode.shift) (by decide) (by first | rfl | assumption)
    | exact marksInv_of_mode (m := Mode.copy) (by decide) (by first | rfl | assumption)
    | exact marksInv_of_mode (m := Mode.home) (by decide) (by first | rfl | assumption)
    | exact marksInv_of_mode (m := Mode.fpp) (by decide) (by first | rfl | assumption)
    | exact marksInv_of_mode (m := Mode.markEnd) (by decide) (by first | rfl | assumption)
    | exact marksInv_of_mode (m := Mode.choose) (by decide) (by first | rfl | assumption)
    | exact marksInv_of_mode (m := Mode.replayStart) (by decide)
        (by first | rfl | assumption))

/-! ## 2. The margin is read off the invariant -/

theorem ofNat_eq_of_radius {s : GalilVM} {r r' : ℕ} (h : s.radius = ofNat r)
    (h' : s.radius = ofNat r') : r = r' := by
  have hv := congrArg value (h.symm.trans h')
  rw [ofNat_value, ofNat_value] at hv
  exact_mod_cast hv

/-- **`MarksInv` delivers `CentreMargin`.** -/
theorem centreMargin_of_marksInv {first : Fin 9} {c : Control} {s : GalilVM}
    (h : MarksInv first c s) : CentreMargin c s := by
  intro hm r hrad
  obtain ⟨⟨f, hf1, hfm, -, hb⟩, ⟨r', hr', hle⟩⟩ := h hm
  have := ofNat_eq_of_radius hrad hr'
  subst this
  omega

#print axioms centreMargin_of_marksInv

/-! ## 3. The residual at the selection tick -/

/-- **(NAMED) the residual.**  At the cell selected by `choose_select` the
`FIRST` cell `f` is at or left of the head and `mh s + 2 ≤ position R + f`. -/
def MarksEntry (first : Fin 9) (s : GalilVM) : Prop :=
  ∃ f, 1 ≤ f ∧ f ≤ mh s ∧ GalilScaffoldTape.denote (marksTape s.fpp) f = first ∧
    mh s + 2 ≤ position s.right + f

/-- The run-wide form: at every `choose` state that selects. -/
def H_marksEntry (P : Shared) (q : ℕ) (first : Fin 9) : Prop :=
  ∀ (c : Control) (s : GalilVM), c.mode = Mode.choose → c.odd = true →
    (galilFrameS P q first).markSet s → MarksEntry first s

/-! ## 4. Preservation by one tick -/

/-- **(KEY) one tick preserves `MarksInv`**, given `MarksEntry` at a selecting
`choose` source. -/
theorem marksInv_tick (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    {c c' : Control} {s t : GalilVM} (hp : MarksInv first c s)
    (he : c.mode = Mode.choose → c.odd = true → (galilFrameS P q first).markSet s →
      MarksEntry first s)
    (h : Tick (galilFrameS P q first) delay ⟨c, s⟩ ⟨c', t⟩) : MarksInv first c' t := by
  cases h
  all_goals try vacuous_mi
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

#print axioms marksInv_tick

/-! ## 5. Along a run -/

theorem marksInv_steps (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (he : H_marksEntry P q first) {n : ℕ} {x y : State GalilVM}
    (h : Steps (galilFrameS P q first) delay n x y)
    (hp : MarksInv first x.ctl x.vm) : MarksInv first y.ctl y.vm := by
  induction h with
  | zero x => exact hp
  | @succ n x w y ht _ ih =>
    exact ih (marksInv_tick P q first delay hp (fun hm ho hs => he x.ctl x.vm hm ho hs) ht)

/-- `MarksInv` on every state of a run parked outside `rewind`. -/
theorem marksInv_of_run (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (he : H_marksEntry P q first) {n : ℕ} {x y : State GalilVM}
    (h : Steps (galilFrameS P q first) delay n x y)
    {m : Mode} (h1 : m ≠ Mode.rewind) (hx : x.ctl.mode = m) :
    MarksInv first y.ctl y.vm :=
  marksInv_steps P q first delay he h (marksInv_of_mode h1 hx)

/-- **`centreMargin_of_marks`.**  Along any run of `galilFrameS` parked outside
`rewind`, `CentreMargin` holds at every state, given the MARKS-tape residual
`H_marksEntry` at the selection ticks. -/
theorem centreMargin_of_marks (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (he : H_marksEntry P q first) {n : ℕ} {x y : State GalilVM}
    (h : Steps (galilFrameS P q first) delay n x y)
    {m : Mode} (h1 : m ≠ Mode.rewind) (hx : x.ctl.mode = m) :
    CentreMargin y.ctl y.vm :=
  centreMargin_of_marksInv (marksInv_of_run P q first delay he h h1 hx)

#print axioms marksInv_steps
#print axioms marksInv_of_run
#print axioms centreMargin_of_marks

end PalPeg.CloseoutPackRun15
