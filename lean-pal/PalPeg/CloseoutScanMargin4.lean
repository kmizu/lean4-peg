import PalPeg.CloseoutScanMargin3
import PalPeg.CloseoutPackRun10

/-!
# `CloseoutScanMargin4`: the Lean `read` already agrees with Scala, and `scanLeft` follows

`CloseoutScanMargin3` closed with the verdict "model defect": it observed that
two absent focuses *match* (`matched_of_both_absent`), and concluded that a
scan comparison could fire with the left head stepping off the origin.

That reading was too pessimistic, and this file corrects it.  The Scala source
of truth says `PlaceHead.read()` is `None` **only** at the origin (place `0`);
a gap place returns the sentinel symbol and a letter place returns the letter.
The Lean `read`

    read p = p.head.focus.map (fun a => if p.gap then 2 else letter a)

has exactly that behaviour: `read p = none ↔ p.head.focus = none ↔ place 0`
(the gap flag only picks *which* symbol is returned, never absence).  So
`matched_of_both_absent` is real but applies to **origin vs. origin only**, and
in a scan the right head is at place `position L + 2 * radius ≥ 1`, never the
origin.  Hence `Tick.scan_match` cannot fire out of `position L = 1`.

* §1 `right_present`: under `ScanInvariant` + `canRight`, the post-compare
  right head still has a focus (the represented right stack is `rs.map some`,
  so a FIFO step never uncovers an absent cell).
* §2 `no_scanMatch_at_pos_one`: at `position L = 1` the compared pair is
  `none` vs. `some _`, so `scanFrame.matched` fails.
* §3 `scanLeft_of_scanInv`: therefore a matched scan tick forces
  `2 ≤ position L`, i.e. `0 < position (left L)` — the
  `CloseoutPackRun10.LTickLeavesM.scanLeft` leaf, discharged from
  `ScanInvariant` alone.

Standard axioms only; unconditional `PAL ∈ PEG` remains open.
-/

set_option autoImplicit false

namespace PalPeg.CloseoutScanMargin4

open PalPeg PalPeg.GalilScaffoldInputHead PalPeg.GalilScaffoldChainVerifier
open PalPeg.GalilScaffoldChainInputSupply
open PalPeg.CloseoutScanMargin

abbrev PH := GalilScaffoldInputHead.PlaceHead

/-! ## 0. `read` is absent exactly at the origin -/

/-- **The gap place is not absent.**  `read` only fails on a missing focus. -/
theorem read_eq_none_iff {p : PH} :
    GalilScaffoldInputHead.read p = none ↔ p.head.focus = none := by
  cases h : p.head.focus <;> simp [GalilScaffoldInputHead.read, h]

/-- Present focus, present reading — for either parity of the place. -/
theorem read_ne_none {p : PH} (h : p.head.focus ≠ none) :
    GalilScaffoldInputHead.read p ≠ none := fun hr => h (read_eq_none_iff.1 hr)

/-! ## 1. The right head survives its own step -/

/-- **A FIFO step never uncovers an absent cell.**  `Represents` stores the
right stack as `rs.map some`, so `right` lands on a real letter whenever it is
enabled. -/
theorem right_present {w : List (Fin 2)} {p : PH}
    (hh : GalilScaffoldInputTrace.Represents p.head w) (hp : p.head.focus ≠ none)
    (hc : canRight p) : (right p).head.focus ≠ none := by
  rcases p with ⟨h, g⟩
  cases g with
  | false => simpa [right] using hp
  | true =>
    obtain ⟨xs, rs, q, he, -⟩ := hh
    show (GalilScaffoldInputTrace.moveRight h).focus ≠ none
    subst he
    simp only [canRight] at hc
    cases rs with
    | cons a rs =>
      rw [GalilScaffoldInputTrace.right_saved xs a rs q]
      cases xs <;> simp [GalilScaffoldInputHead.layout]
    | nil =>
      cases q with
      | nil =>
        exfalso
        rcases hc with h' | h' | h'
        · exact absurd h' (by simp)
        · exact h' (by cases xs <;> simp [GalilScaffoldInputHead.layout])
        · exact h' (by cases xs <;> simp [GalilScaffoldInputHead.layout])
      | cons a q =>
        simp only [List.map_nil]
        rw [GalilScaffoldInputTrace.right_incoming xs a q]
        cases xs <;> simp [GalilScaffoldInputHead.layout]

/-! ## 2. `scan_match` cannot fire at `position L = 1` -/

/-- **The scan corner is unreachable by a match.**  Stepping the left head out
of place `1` lands on the origin (`read = none`), while the right head is still
on a real cell (`read ≠ none`); the scan frame's `matched` is the equality of
those two readings, so it fails. -/
theorem no_scanMatch_at_pos_one {w : List (Fin 2)} {C r : ℕ} {L R : PH}
    (hi : ScanInvariant w C r L R) (hc : canRight R) (h1 : position L = 1) :
    GalilScaffoldInputHead.read (GalilScaffoldInputHead.left L)
      ≠ GalilScaffoldInputHead.read (right R) := by
  have hl : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left L) = none :=
    CloseoutScanMargin3.read_of_absent
      (CloseoutScanMargin3.left_absent_at_pos_one hi.leftRep h1).1
  have hr : GalilScaffoldInputHead.read (right R) ≠ none :=
    read_ne_none (right_present hi.rightRep hi.rightPresent hc)
  intro he; exact hr (he ▸ hl)

/-- The same statement in the shape of the scan frame's `matched` field. -/
theorem no_scanFrame_matched_at_pos_one {w : List (Fin 2)} {C r : ℕ} {L R : PH}
    {onLetter leftFirst : GalilScaffoldChainInputSupply.ScanVM → Prop}
    {ch' : GalilScaffoldChainInputSupply.ChainVM}
    (hi : ScanInvariant w C r L R) (hc : canRight R) (h1 : position L = 1) :
    ¬ (GalilScaffoldChainInputSupply.scanFrame onLetter leftFirst).matched
        ⟨GalilScaffoldInputHead.left L, right R, ch'⟩ :=
  fun h => no_scanMatch_at_pos_one (C := C) (r := r) hi hc h1 h

/-! ## 3. `LTickLeavesM.scanLeft`, discharged -/

/-- **The margin, from the invariant plus the firing of the comparison.**
`lrep` excludes `position L = 0` (`CloseoutScanMargin3.lrep_pos`) and §2
excludes `position L = 1`, so `2 ≤ position L`. -/
theorem two_le_position_of_matched {w : List (Fin 2)} {C r : ℕ} {L R : PH}
    (hi : ScanInvariant w C r L R) (hc : canRight R)
    (hmt : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left L)
      = GalilScaffoldInputHead.read (right R)) : 2 ≤ position L := by
  have h0 : 0 < position L := CloseoutScanMargin3.lrep_pos hi.leftRep hi.leftPresent
  have h1 : position L ≠ 1 := by
    intro h; exact no_scanMatch_at_pos_one (C := C) (r := r) hi hc h hmt
  omega

/-- **The `scanLeft` leaf.**  `CloseoutPackRun10.LTickLeavesM.scanLeft` asks for
`0 < position (left L)` in `scan` mode; by `CloseoutLPack4.left_pos_iff` that is
`2 ≤ position L`, which the matched scan comparison supplies. -/
theorem scanLeft_of_scanInv {w : List (Fin 2)} {C r : ℕ} {L R : PH}
    (hi : ScanInvariant w C r L R) (hc : canRight R)
    (hmt : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left L)
      = GalilScaffoldInputHead.read (right R)) :
    0 < position (GalilScaffoldInputHead.left L) :=
  CloseoutLPack4.left_pos_iff.2 (two_le_position_of_matched hi hc hmt)

/-- `Margin` (the named predicate of `CloseoutScanMargin`) at a matched scan
step, hence both `CloseoutPackRun3` fields through
`CloseoutScanMargin.scanMargin_of_margin`. -/
theorem margin_of_matched {w : List (Fin 2)} {C r : ℕ} {L R : PH}
    (hi : ScanInvariant w C r L R) (hc : canRight R)
    (hmt : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left L)
      = GalilScaffoldInputHead.read (right R)) : r + 2 ≤ C := by
  have h2 := two_le_position_of_matched hi hc hmt
  have hl := hi.leftPos
  have hp := CloseoutLPack4.scanInv_pos hi
  omega

#print axioms read_eq_none_iff
#print axioms read_ne_none
#print axioms right_present
#print axioms no_scanMatch_at_pos_one
#print axioms no_scanFrame_matched_at_pos_one
#print axioms two_le_position_of_matched
#print axioms scanLeft_of_scanInv
#print axioms margin_of_matched

end PalPeg.CloseoutScanMargin4
