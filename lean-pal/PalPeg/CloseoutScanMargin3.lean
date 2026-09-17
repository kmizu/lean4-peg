import PalPeg.CloseoutScanMargin2
import PalPeg.CloseoutLPack3

/-!
# `CloseoutScanMargin3`: the origin cell is not the scan corner — `position 1` is

`CloseoutPackRun7` located the scan/rewind trouble at the *origin gap cell*
`position L = 0`, and proposed to weaken
`CloseoutLPack3.LTickLeaves.scanLeft` / `CloseoutLPack5.LTickLeavesG.scanLeft`
(`0 < position (left L)`, i.e. `2 ≤ position L`) to a statement about
`position L = 0`.  This file shows that repair is **vacuous**, and names the
place where the model really is wrong.

* §1 `lrep_pos`: under the `LPack` field `lrep` itself
  (`Represents L.head w ∧ L.head.focus ≠ none`) we already have
  `0 < position L`.  Presence *is* a nonempty left stack
  (`CloseoutLPack3.present_iff_left`), and either parity of a nonempty stack
  gives a positive place.  So `position L = 0` is unreachable at *every*
  state carrying `lrep` — not just in `scan`.  A leaf of the shape
  `position L = 0 → ¬ scan_match` is therefore a tautology-in-context
  (`scanLeft0_vacuous`), and it delivers nothing towards
  `CloseoutLPack3.lrep_left`'s hypothesis `0 < position (left L)`.

* §2 The genuine corner is one cell further in: `position L = 1`.  There
  (`pos_one_shape`) `L.gap = false` and the left stack is the single cell
  `[none`], so the compare step lands with `focus = none` and `position = 0`
  (`left_absent_at_pos_one`): `lrep` is destroyed by the step, in all three
  of `scan_match` / `scan_shift` / `scan_fallback`, which share `hcmp`.

* §3 Nothing in the model stops that step.  `compare` for the scan frame is
  an unconditional left move (`CloseoutScanMargin2` §1); `matched` is
  `read left = read right` (`GalilScaffoldTopScan.scanFrame`), and two absent
  focuses *match* (`matched_of_both_absent`), so even `scan_match` is
  available; and `Tick.scan_match`'s only other guard,
  `c.replaying = true ∨ F.available s`, is discharged by `c.replaying = true`
  alone, so the right head's `canRight` cannot rescue the left head during a
  replay.

**Verdict.**  The answer to "what does the next scan tick do at
`position L = 0`?" is: that state does not exist under `lrep`.  The obligation
that must be discharged is still `position L ≠ 1` — i.e. `Margin`, which
`CloseoutScanMargin2.margin_false_witness` refutes at the initial scan state
of a one-letter word.  So this is a **model defect, not a missing leaf**: the
scan `compare` relation omits the machine's stopping rule at the left end of
the input (Scala never compares with the left head on the first letter), and
until `compare` carries that guard, `scanLeft` cannot be proved and cannot be
weakened into anything usable.
Standard axioms only; unconditional `PAL ∈ PEG` remains open.
-/

set_option autoImplicit false

namespace PalPeg.CloseoutScanMargin3

open PalPeg PalPeg.GalilScaffoldInputHead PalPeg.GalilScaffoldChainInputSupply
open PalPeg.CloseoutScanMargin

abbrev PH := GalilScaffoldInputHead.PlaceHead

/-! ## 1. `lrep` already excludes the origin cell -/

/-- **Presence implies a positive place.**  Both parities of a nonempty left
stack are `> 0`. -/
theorem lrep_pos {w : List (Fin 2)} {p : PH}
    (hh : GalilScaffoldInputTrace.Represents p.head w) (hp : p.head.focus ≠ none) :
    0 < position p := by
  have hl : 0 < p.head.left.length := (CloseoutLPack3.present_iff_left hh).1 hp
  cases hg : p.gap with
  | false => simp only [position, hg, Bool.false_eq_true, if_false]; omega
  | true => simp only [position, hg, if_true]; omega

/-- **The proposed `scanLeft0` is vacuous.**  Its hypothesis `position L = 0`
contradicts the `lrep` field that the very same pack carries. -/
theorem scanLeft0_vacuous {w : List (Fin 2)} {p : PH}
    (hh : GalilScaffoldInputTrace.Represents p.head w) (hp : p.head.focus ≠ none)
    (hz : position p = 0) : False := by
  have := lrep_pos hh hp
  omega

/-- The same, phrased as the elimination actually wanted: anything follows. -/
theorem of_origin_absurd {w : List (Fin 2)} {p : PH} {P : Prop}
    (hh : GalilScaffoldInputTrace.Represents p.head w) (hp : p.head.focus ≠ none)
    (hz : position p = 0) : P :=
  absurd hz (by have := lrep_pos hh hp; omega)

/-! ## 2. The real corner: `position L = 1` -/

/-- At `position p = 1` a represented head has left stack exactly `[none]`. -/
theorem pos_one_stack {w : List (Fin 2)} {p : PH}
    (hh : GalilScaffoldInputTrace.Represents p.head w) (h : position p = 1) :
    p.head.left = [none] := by
  have hlen := (pos_one_shape h).2
  obtain ⟨xs, rs, q, he, -⟩ := hh
  rw [he] at hlen ⊢
  cases xs with
  | nil => simp [GalilScaffoldInputHead.layout] at hlen
  | cons a xs =>
    cases xs with
    | nil => simp [GalilScaffoldInputHead.layout]
    | cons b xs => simp [GalilScaffoldInputHead.layout] at hlen

/-- **The step out of `position 1` destroys `lrep`.**  The landing place has
an absent focus and sits on the origin. -/
theorem left_absent_at_pos_one {w : List (Fin 2)} {p : PH}
    (hh : GalilScaffoldInputTrace.Represents p.head w) (h : position p = 1) :
    (GalilScaffoldInputHead.left p).head.focus = none ∧
      position (GalilScaffoldInputHead.left p) = 0 := by
  have hg : p.gap = false := (pos_one_shape h).1
  have hs : p.head.left = [none] := pos_one_stack hh h
  have hml : GalilScaffoldInputHead.moveLeft p.head
      = ⟨none, [], p.head.focus :: p.head.right, p.head.incoming⟩ := by
    unfold GalilScaffoldInputHead.moveLeft; rw [hs]
  constructor
  · show (if p.gap then p.head else GalilScaffoldInputHead.moveLeft p.head).focus = none
    rw [hg]; simp [hml]
  · show position ⟨if p.gap then p.head else GalilScaffoldInputHead.moveLeft p.head, !p.gap⟩ = 0
    rw [hg]; simp [position, hml]

/-- Hence `CloseoutLPack3.lrep_left`'s hypothesis genuinely fails there: the
obligation is `position L ≠ 1`, not `position L ≠ 0`. -/
theorem lrep_left_hyp_fails {w : List (Fin 2)} {p : PH}
    (hh : GalilScaffoldInputTrace.Represents p.head w) (h : position p = 1) :
    ¬ (0 < position (GalilScaffoldInputHead.left p)) := by
  have := (left_absent_at_pos_one hh h).2
  omega

/-! ## 3. Nothing in the model forbids the step -/

/-- An absent focus reads as `none`. -/
theorem read_of_absent {p : PH} (h : p.head.focus = none) :
    GalilScaffoldInputHead.read p = none := by
  simp [GalilScaffoldInputHead.read, h]

/-- **Two absent focuses match.**  `matched` for the scan frame is
`read left = read right`, so the mismatch branches are not forced either: even
`Tick.scan_match` can fire off the end of the input. -/
theorem matched_of_both_absent {l r : PH}
    (hl : l.head.focus = none) (hr : r.head.focus = none) :
    GalilScaffoldInputHead.read l = GalilScaffoldInputHead.read r := by
  rw [read_of_absent hl, read_of_absent hr]

/-- And the `available` guard is no protection: `c.replaying = true` satisfies
`Tick.scan_*`'s disjunction on its own. -/
theorem replaying_bypasses_available {σ : Type} (F : GalilScaffoldTop.Frame σ) (s : σ)
    {c : GalilScaffoldController.Control} (hr : c.replaying = true) :
    c.replaying = true ∨ F.available s := Or.inl hr

#print axioms lrep_pos
#print axioms scanLeft0_vacuous
#print axioms of_origin_absurd
#print axioms pos_one_stack
#print axioms left_absent_at_pos_one
#print axioms lrep_left_hyp_fails
#print axioms matched_of_both_absent
#print axioms replaying_bypasses_available

end PalPeg.CloseoutScanMargin3
