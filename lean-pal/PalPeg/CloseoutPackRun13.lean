import PalPeg.CloseoutPackRun11
import PalPeg.GalilRewindSafe

/-!
# `CloseoutPackRun13`: the rewind corner, located and halved

`CloseoutPackRun11` left `Extra'.rewindMargin` (`2 ≤ position L` at every
`rewind` state, equivalently `LTickLeavesN.rewindLeft` by
`CloseoutLPack4.left_pos_iff`) as the surviving origin corner, consumed only by
the `rewind_one` / `rewind_pair` branches of `lpackN_tick`.  This file settles
what that corner is.

* §1 `position_left` — `position (left p) = position p - 1`, unconditionally
  (the truncated form of `GalilFrontier.left_position_pos`; at the origin both
  sides are `0`).
* §3 `rewind_left_step` / `rewind_position_step` — **the leaf cannot be
  deleted.**  Every tick that stays inside `rewind` carries
  `left := left x.left` (`GalilScaffoldTopRewind.rewindOne` / `rewindPair`), so
  the left head walks **left**, one place per tick, from its landing place
  `left := right` at `choose_select`.  It is the centre that only moves every
  second tick.  So `rewindLeft` guards a real `GalilScaffoldInputTrace` step and
  the "rewind only moves L right" reading is false.
* §2 `RCouple`, `rcouple_tick` (KEY), §4 `rcouple_steps` / `rcouple_of_run` —
  the exact counter identity behind that walk, in the truncated form that
  survives the origin:

    `position L ≤ position C ≤ position L + radius + pairOff`.

  It is established at `choose_select` (`L = C = R`, `radius := reset`) and
  preserved by `rewind_one` (`L--`, `pair := 1`) and `rewind_pair` (`L--`,
  `C--`, `radius++`, `pair := 0`).  Unlike `GalilRewindSafe.RewindPhase`, which
  needs `CentreLive` as a side condition, `RCouple` is preserved by **every**
  tick with no hypothesis, so on any run parked outside `rewind` it is a
  theorem, not a leaf (`rcouple_of_run`).
* §5 `CentreMargin`, `rewindMargin_of_centreMargin`, `rewindLeft_of_centreMargin`,
  `centreLive_of_rewindMargin`, `corners_of_centreMargin` — **the two rewind
  corners are one.**  `CentreMargin` (`radius + pairOff + 2 ≤ position C` during
  `rewind`) delivers `Extra'.rewindMargin`; and conversely `rewindMargin`
  already implies `GalilRewindSafe.CentreLive`, because `L ≤ C`.  So the left
  head is the binding one and the pair `{rewindMargin, CentreLive}` collapses to
  the single named leaf `CentreMargin`.

## Honest status

Standard axioms only; unconditional `PAL ∈ PEG` remains open.  What is *not*
proved here is `CentreMargin` itself.  By the identity it is equivalent to "the
backward walk never puts `L` on the origin gap", i.e. "the `FIRST` mark sits at
place `≥ 1`".  In `ScaffoldGalil.stepFpp` the mark is written after
`marks.move(1)`, so this is plausible, but it is a property of the MARKS tape
and is invisible to `Tick` — the same reading `GalilRewindSafe` records for
`CentreLive`.

One structural consequence for the next transcript: like `scanLeft` before it
(`CloseoutPackRun11` §2, via `CloseoutScanMargin4`), `rewindLeft` is stated for
*all* `rewind` states but consumed only where the walk actually steps, i.e.
under `¬ atFirst`.  The guarded leaf
`c.mode = rewind → ¬ F.atFirst s → 0 < position (left s.left)` is what
`lpackN_tick` needs, and it is strictly weaker: the unguarded form also demands
`2 ≤ position L` at the final `rewind_done` state, where the machine has already
stopped.  Re-cutting `lpackN_tick` over the guarded field (a `LTickLeavesN'`
with twenty-two unchanged branches) is the remaining mechanical step.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPackRun13

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldInputHead GalilScaffoldCounter

/-! ## 1. A left step always lowers the place by one (truncated) -/

theorem position_left (p : PlaceHead) :
    position (GalilScaffoldInputHead.left p) = position p - 1 := by
  by_cases h : 0 < position p
  · have := left_position_pos h; omega
  · have hz : position p = 0 := by omega
    have hn : ¬ (0 < position (GalilScaffoldInputHead.left p)) := by
      intro hc
      have := PalPeg.CloseoutLPack4.two_le_of_left_pos hc
      omega
    omega

#print axioms position_left


/-! ## 2. The rewind coupling invariant -/

/-- The half-step carried by the `pair` flag. -/
def pairOff (c : Control) : ℕ := if c.pair then 1 else 0

/-- **(NAMED) the rewind coupling.**  While the controller walks back, the
left head is never right of the centre, and it is never more than
`radius + pairOff` places left of it. -/
def RCouple (c : Control) (s : GalilVM) : Prop :=
  c.mode = Mode.rewind →
    ∃ r, s.radius = ofNat r ∧
      position s.left ≤ position s.center ∧
      position s.center ≤ position s.left + r + pairOff c

theorem rcouple_of_mode {c : Control} {s : GalilVM} {m : Mode}
    (h1 : m ≠ Mode.rewind) (h : c.mode = m) : RCouple c s := by
  intro hm; exact absurd (h.symm.trans hm) h1

macro "vacuous_rw" : tactic =>
  `(tactic| first
    | exact rcouple_of_mode (m := Mode.init) (by decide) (by first | rfl | assumption)
    | exact rcouple_of_mode (m := Mode.scan) (by decide) (by first | rfl | assumption)
    | exact rcouple_of_mode (m := Mode.shift) (by decide) (by first | rfl | assumption)
    | exact rcouple_of_mode (m := Mode.copy) (by decide) (by first | rfl | assumption)
    | exact rcouple_of_mode (m := Mode.home) (by decide) (by first | rfl | assumption)
    | exact rcouple_of_mode (m := Mode.fpp) (by decide) (by first | rfl | assumption)
    | exact rcouple_of_mode (m := Mode.markEnd) (by decide) (by first | rfl | assumption)
    | exact rcouple_of_mode (m := Mode.choose) (by decide) (by first | rfl | assumption)
    | exact rcouple_of_mode (m := Mode.replayStart) (by decide)
        (by first | rfl | assumption))

/-- **(KEY) one tick preserves the coupling.** -/
theorem rcouple_tick (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    {c c' : Control} {s t : GalilVM} (hp : RCouple c s)
    (h : Tick (galilFrameS P q first) delay ⟨c, s⟩ ⟨c', t⟩) : RCouple c' t := by
  cases h
  all_goals try vacuous_rw
  case choose_select =>
    rename_i hm hodd hs hi
    obtain ⟨heq, hset⟩ := hi
    have hl : t.left = s.right := by rw [hset, heq]; rfl
    have hc : t.center = s.right := by rw [hset, heq]; rfl
    have hr : t.radius = reset := by rw [hset, heq]; rfl
    intro _
    refine ⟨0, by rw [hr]; rfl, ?_, ?_⟩
    · rw [hl, hc]
    · rw [hl, hc]; simp [pairOff]
  case rewind_one =>
    rename_i hm hf hpr hi
    obtain ⟨⟨-, heq⟩, hset⟩ := hi
    have hl : t.left = GalilScaffoldInputHead.left s.left := by rw [hset, heq]; rfl
    have hc : t.center = s.center := by rw [hset, heq]; rfl
    have hr : t.radius = s.radius := by rw [hset, heq]; rfl
    intro _
    obtain ⟨r, hrad, h1, h2⟩ := hp hm
    have hpo : pairOff c = 0 := by simp [pairOff, hf]
    rw [hpo] at h2
    refine ⟨r, by rw [hr]; exact hrad, ?_, ?_⟩
    · rw [hl, hc, position_left]; omega
    · rw [hl, hc, position_left]
      have : pairOff {c with pair := true} = 1 := by simp [pairOff]
      rw [this]; omega
  case rewind_pair =>
    rename_i hm hf hpr hi
    obtain ⟨⟨-, heq⟩, hset⟩ := hi
    have hl : t.left = GalilScaffoldInputHead.left s.left := by rw [hset, heq]; rfl
    have hc : t.center = GalilScaffoldInputHead.left s.center := by rw [hset, heq]; rfl
    have hr : t.radius = inc s.radius := by rw [hset, heq]; rfl
    intro _
    obtain ⟨r, hrad, h1, h2⟩ := hp hm
    have hpo : pairOff c = 1 := by simp [pairOff, hf]
    rw [hpo] at h2
    refine ⟨r + 1, by rw [hr, hrad, inc_ofNat], ?_, ?_⟩
    · rw [hl, hc, position_left, position_left]; omega
    · rw [hl, hc, position_left, position_left]
      have : pairOff {c with pair := false} = 0 := by simp [pairOff]
      rw [this]; omega

#print axioms rcouple_tick

/-! ## 3. The left head really does walk left -/

/-- **The corner is not deletable.**  Every tick that stays inside `rewind`
moves the left head one place *left* (`rewind_one` and `rewind_pair` both carry
`left := left x.left`), so `LTickLeavesN.rewindLeft` is discharging a real
`GalilScaffoldInputTrace` step, not a no-op. -/
theorem rewind_left_step (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    {c c' : Control} {s t : GalilVM} (hm : c.mode = Mode.rewind)
    (hf : c'.mode = Mode.rewind)
    (h : Tick (galilFrameS P q first) delay ⟨c, s⟩ ⟨c', t⟩) :
    t.left = GalilScaffoldInputHead.left s.left := by
  cases h
  case rewind_one =>
    rename_i hm' hpair hat hi
    obtain ⟨⟨-, heq⟩, hset⟩ := hi
    rw [hset, heq]; rfl
  case rewind_pair =>
    rename_i hm' hpair hat hi
    obtain ⟨⟨-, heq⟩, hset⟩ := hi
    rw [hset, heq]; rfl
  all_goals (exfalso; simp_all)

#print axioms rewind_left_step

/-- The place strictly decreases while the head is off the origin. -/
theorem rewind_position_step (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    {c c' : Control} {s t : GalilVM} (hm : c.mode = Mode.rewind)
    (hf : c'.mode = Mode.rewind)
    (h : Tick (galilFrameS P q first) delay ⟨c, s⟩ ⟨c', t⟩) :
    position t.left = position s.left - 1 := by
  rw [rewind_left_step P q first delay hm hf h, position_left]

#print axioms rewind_position_step

/-! ## 4. The coupling holds along any run that does not start in `rewind` -/

theorem rcouple_steps (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) {n : ℕ}
    {x y : State GalilVM} (h : Steps (galilFrameS P q first) delay n x y)
    (hp : RCouple x.ctl x.vm) : RCouple y.ctl y.vm := by
  induction h with
  | zero x => exact hp
  | @succ n x w y ht _ ih => exact ih (rcouple_tick P q first delay hp ht)

/-- **`RCouple` is unconditional on a run parked outside `rewind`.**  Unlike
`GalilRewindSafe.RewindPhase`, the coupling needs no side condition at all. -/
theorem rcouple_of_run (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) {n : ℕ}
    {x y : State GalilVM} (h : Steps (galilFrameS P q first) delay n x y)
    {m : Mode} (h1 : m ≠ Mode.rewind) (hx : x.ctl.mode = m) :
    RCouple y.ctl y.vm :=
  rcouple_steps P q first delay h (rcouple_of_mode h1 hx)

#print axioms rcouple_of_run

/-! ## 5. Both corners reduce to one centre margin -/

/-- **(NAMED) the residual.**  During `rewind` the centre still has
`radius + pairOff + 2` places to its left.  Equivalently: the backward walk
stops at the `FIRST` mark before it has consumed the word — a fact about the
MARKS tape, exactly the one `GalilRewindSafe.CentreLive` isolates. -/
def CentreMargin (c : Control) (s : GalilVM) : Prop :=
  c.mode = Mode.rewind → ∀ r : ℕ, s.radius = ofNat r →
    r + pairOff c + 2 ≤ position s.center

/-- **The rewind corner from the centre margin.**  `Extra'.rewindMargin`
(`2 ≤ position L`, hence `LTickLeavesN.rewindLeft` by
`CloseoutLPack4.left_pos_of_two`) follows from `RCouple` and `CentreMargin`. -/
theorem rewindMargin_of_centreMargin {c : Control} {s : GalilVM}
    (hco : RCouple c s) (hcm : CentreMargin c s) (hm : c.mode = Mode.rewind) :
    2 ≤ position s.left := by
  obtain ⟨r, hrad, -, h2⟩ := hco hm
  have := hcm hm r hrad
  omega

#print axioms rewindMargin_of_centreMargin

/-- The consumed form. -/
theorem rewindLeft_of_centreMargin {c : Control} {s : GalilVM}
    (hco : RCouple c s) (hcm : CentreMargin c s) (hm : c.mode = Mode.rewind) :
    0 < position (GalilScaffoldInputHead.left s.left) :=
  PalPeg.CloseoutLPack4.left_pos_of_two (rewindMargin_of_centreMargin hco hcm hm)

#print axioms rewindLeft_of_centreMargin

/-- **The left head is the binding one.**  `2 ≤ position L` already implies
`GalilRewindSafe.CentreLive`, so the rewind corner subsumes the centre
assumption of `GalilRewindSafe`: the two leaves are one. -/
theorem centreLive_of_rewindMargin {c : Control} {s : GalilVM}
    (hco : RCouple c s) (hL : c.mode = Mode.rewind → 2 ≤ position s.left) :
    CentreLive c s := by
  intro hm _
  obtain ⟨r, -, h1, -⟩ := hco hm
  have := hL hm
  omega

#print axioms centreLive_of_rewindMargin

/-- Packaged: one named leaf discharges both corners. -/
theorem corners_of_centreMargin {c : Control} {s : GalilVM}
    (hco : RCouple c s) (hcm : CentreMargin c s) :
    (c.mode = Mode.rewind → 2 ≤ position s.left) ∧ CentreLive c s := by
  refine ⟨fun hm => rewindMargin_of_centreMargin hco hcm hm, ?_⟩
  exact centreLive_of_rewindMargin hco (fun hm => rewindMargin_of_centreMargin hco hcm hm)

#print axioms corners_of_centreMargin

end PalPeg.CloseoutPackRun13
