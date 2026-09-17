import PalPeg.CloseoutLPack4

/-!
# `CloseoutScanMargin`: how far the origin margins actually go

`CloseoutPackRun3.lean:113` (`Extra.scanMargin`) asks, in `scan`, for

  `ScanInvariant w (position C) r L R → r + 2 ≤ position C`,

and `:116` (`Extra.rewindMargin`) for `2 ≤ position L` in `rewind`.
`CloseoutLPack4.scanInv_pos` gets liveness as far as `1 ≤ position L`, i.e.
`r + 1 ≤ position C`, and stops there.

This file settles *why* it stops, and with what the last place is bought.

* §1 `scanMargin_succ` — **the `+1` version is unconditional.**  It is exactly
  `scanInv_pos` restated as a margin, and it is the strongest consequence of
  `ScanInvariant` plus `GalilLiveCentre.Live` alone.
* §2 `scanMargin_iff_ne_one`, `scanMargin_of_gap`, `scanMargin_of_two_le_len` —
  **the `+2` version is the `+1` version minus one state.**  The only
  configuration with `1 ≤ position L` and not `2 ≤ position L` is
  `position L = 1`, which by `position` (`= 2*len` at a gap, `= 2*len-1` at a
  letter) means `L.gap = false` and `L.head.left.length = 1`: the left head is
  on `w[0]` and its next left step lands on the origin gap cell.  So `+2` is
  available on any hypothesis that excludes that single state — an even place
  (`gap = true`), or two letters to the left.
* §3 `rewindMargin_iff`, `rewindMargin_of_gap`, `rewindMargin_of_two_le_len` —
  the same for the rewind corner, via `CloseoutLPack4.left_pos_iff`: there
  `2 ≤ position L` *is* `0 < position (left L)`, so the field is literally "the
  left head can still step left", with no invariant to appeal to.
* §4 `Margin` — the missing fact isolated as one named predicate, with
  `scanMargin_of_margin` / `rewindMargin_of_margin` delivering both
  `CloseoutPackRun3` fields from it.

## Honest status

`Extra.scanMargin` is **not** derivable from `ScanInvariant` and liveness: the
state `position L = 1` satisfies every hypothesis and refutes the conclusion
(there `r + 1 = position C`).  The gap is exactly `PackRun7`'s reading — the
machine's stopping rule, that a scan comparison never fires with the left head
on the origin gap cell, is a fact about the *transition relation*, not about the
invariant.  Standard axioms only; unconditional `PAL ∈ PEG` remains open.
-/

set_option autoImplicit false

namespace PalPeg.CloseoutScanMargin

open PalPeg PalPeg.GalilScaffoldInputHead PalPeg.GalilScaffoldChainInputSupply PalPeg.CloseoutLPack4

abbrev PH := GalilScaffoldInputHead.PlaceHead

/-! ## 1. The unconditional `+1` margin -/

/-- **`r + 1 ≤ C` is free.**  `CloseoutLPack4.scanInv_pos` as a margin. -/
theorem scanMargin_succ {w : List (Fin 2)} {C r : ℕ} {l rh : PH}
    (hi : ScanInvariant w C r l rh) : r + 1 ≤ C := by
  have h1 := scanInv_pos hi
  have hl := hi.leftPos
  omega

#print axioms scanMargin_succ

/-! ## 2. The `+2` margin is the `+1` margin minus the state `position L = 1` -/

/-- **The exact shortfall.**  Given the scan invariant, `r + 2 ≤ C` holds iff
the left head is not on the first letter. -/
theorem scanMargin_iff_ne_one {w : List (Fin 2)} {C r : ℕ} {l rh : PH}
    (hi : ScanInvariant w C r l rh) : r + 2 ≤ C ↔ position l ≠ 1 := by
  have h1 := scanInv_pos hi
  have hl := hi.leftPos
  constructor
  · intro h; omega
  · intro h; omega

#print axioms scanMargin_iff_ne_one

/-- `position L = 1` forces the letter place with a single letter to the left. -/
theorem pos_one_shape {l : PH} (h : position l = 1) :
    l.gap = false ∧ l.head.left.length = 1 := by
  cases hg : l.gap with
  | false =>
    refine ⟨rfl, ?_⟩
    simp only [position, hg, Bool.false_eq_true, if_false] at h
    omega
  | true =>
    simp only [position, hg, if_true] at h
    omega

#print axioms pos_one_shape

/-- **`+2` at a gap place.**  An even place that is nonzero is at least `2`. -/
theorem scanMargin_of_gap {w : List (Fin 2)} {C r : ℕ} {l rh : PH}
    (hi : ScanInvariant w C r l rh) (hg : l.gap = true) : r + 2 ≤ C := by
  refine (scanMargin_iff_ne_one hi).2 ?_
  intro h
  exact absurd hg (by simp [(pos_one_shape h).1])

#print axioms scanMargin_of_gap

/-- **`+2` with two letters to the left.** -/
theorem scanMargin_of_two_le_len {w : List (Fin 2)} {C r : ℕ} {l rh : PH}
    (hi : ScanInvariant w C r l rh) (hlen : 2 ≤ l.head.left.length) :
    r + 2 ≤ C := by
  refine (scanMargin_iff_ne_one hi).2 ?_
  intro h
  have := (pos_one_shape h).2
  omega

#print axioms scanMargin_of_two_le_len

/-! ## 3. The rewind corner -/

/-- **`rewindMargin` is "the left head can still step left".** -/
theorem rewindMargin_iff {p : PH} :
    2 ≤ position p ↔ 0 < position (GalilScaffoldInputHead.left p) :=
  left_pos_iff.symm

#print axioms rewindMargin_iff

theorem rewindMargin_of_gap {p : PH} (hg : p.gap = true)
    (hlen : 0 < p.head.left.length) : 2 ≤ position p := by
  simp only [position, hg, if_true]
  omega

#print axioms rewindMargin_of_gap

theorem rewindMargin_of_two_le_len {p : PH} (hlen : 2 ≤ p.head.left.length) :
    2 ≤ position p := by
  simp only [position]
  split <;> omega

#print axioms rewindMargin_of_two_le_len

/-! ## 4. The missing fact, named once -/

/-- **(NAMED) the stopping rule.**  The left head of a reachable scan/rewind
state is never on the first letter — equivalently, it can always still step
left.  This is a property of the machine's transitions; no invariant in the
pack implies it (see `scanMargin_iff_ne_one`). -/
def Margin (l : PH) : Prop := position l ≠ 1

theorem scanMargin_of_margin {w : List (Fin 2)} {C r : ℕ} {l rh : PH}
    (hi : ScanInvariant w C r l rh) (hm : Margin l) : r + 2 ≤ C :=
  (scanMargin_iff_ne_one hi).2 hm

theorem rewindMargin_of_margin {p : PH} (hm : Margin p)
    (hpos : 1 ≤ position p) : 2 ≤ position p := by
  unfold Margin at hm; omega

#print axioms scanMargin_of_margin
#print axioms rewindMargin_of_margin

end PalPeg.CloseoutScanMargin
