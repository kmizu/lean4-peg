import PalPeg.CloseoutPackRun16

/-!
# Closeout pack run 20: `rChoosePackL` from a right-head field in `choose` mode

The contract `BigResid6.rChoosePackL` (`CloseoutPackRun11`) asks, at a
`choose` state with `odd = true`, that the `choose` landing `t` have
`Represents t.left.head w ∧ t.left.head.focus ≠ none`.  The landing is
`choose_select` (`GalilScaffoldTopRewind.rewindFrame.choose`): `t.left := s.right`.
So the contract is exactly a statement about the **right** head at the source.

`BigPack2M` carries `Represents` for the **left** head only (`LPackM.lrepM`);
the right head's representation is a field of `ScanInvariant`, which the pack
exposes only in `scan` (`LPackM.scanGeom`) — as `CloseoutPackRun6` already
noted.  This file therefore

* names the single missing fact `RRepChoose` — `Represents s.right.head w` and
  presence of the right focus at every selecting `choose` state — and
* proves the contract from it (`rChoosePackL_of_pack`), and
* shows presence can be bought from `0 < position s.right` instead
  (`rrepChoose_of_pos`), so a pack field carrying `Represents R` plus the
  origin exclusion `position R ≥ 1` suffices.

Where it should live: a sixth field of `LPackM` (say `rrepChoose`), guarded by
`c.mode = Mode.choose`, established at `markEnd → choose` and preserved by
`markBack` (which keeps `right`).

Standard axioms only; unconditional `PAL ∈ PEG` remains open.
-/

set_option autoImplicit false

namespace PalPeg.CloseoutPackRun20

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldInputHead GalilScaffoldCounter
open PalPeg.GalilRunSkeleton PalPeg.CloseoutPackRun11

/-! ## 1. The `choose` landing copies the right head into the left -/

theorem choose_left_eq_right (P : Shared) (q : ℕ) (first : Fin 9) {s t : GalilVM}
    (h : (galilFrameS P q first).choose s t) : t.left = s.right := by
  obtain ⟨heq, hset⟩ := h
  rw [hset, heq]; rfl

#print axioms choose_left_eq_right

/-! ## 2. The one missing fact, named -/

section Contract
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **(NAMED) the right head is represented and present at every selecting
`choose` state of the pack.**  This is the field `BigPack2M` lacks. -/
def RRepChoose (w : List (Fin 2)) : Prop :=
  ∀ x : State GalilVM, BigPack2M centre place entry q first w x →
    x.ctl.mode = Mode.choose → x.ctl.odd = true →
    GalilScaffoldInputTrace.Represents x.vm.right.head w ∧ x.vm.right.head.focus ≠ none

/-- **`rChoosePackL` from `RRepChoose`.**  Exactly the type of
`BigResid6.rChoosePackL`. -/
theorem rChoosePackL_of_pack {w : List (Fin 2)}
    (hR : RRepChoose centre place entry q first w) :
    ∀ x : State GalilVM, BigPack2M centre place entry q first w x →
      x.ctl.mode = Mode.choose → x.ctl.odd = true → ∀ t : GalilVM,
      (galilFrameS (PofC centre place entry w) q first).choose x.vm t →
      GalilScaffoldInputTrace.Represents t.left.head w ∧ t.left.head.focus ≠ none := by
  intro x hx hm ho t ht
  have hl := choose_left_eq_right (PofC centre place entry w) q first ht
  rw [hl]
  exact hR x hx hm ho

/-- Presence of the right focus follows from `Represents` and `0 < position`:
`position` is `2·len` or `2·len − 1`, both positive only for `0 < len`. -/
theorem present_of_rep_pos {w : List (Fin 2)} {p : PlaceHead}
    (hh : GalilScaffoldInputTrace.Represents p.head w) (hp : 0 < position p) :
    p.head.focus ≠ none := by
  rw [PalPeg.CloseoutLPack3.present_iff_left hh]
  by_contra hlen
  have h0 : p.head.left.length = 0 := by omega
  cases hg : p.gap <;> simp [position, hg, h0] at hp

/-- `RRepChoose` from `Represents R` plus the origin exclusion `1 ≤ position R`
(the copy walker never crosses the input origin, cf. `ChooseLayout`). -/
theorem rrepChoose_of_pos {w : List (Fin 2)}
    (hR : ∀ x : State GalilVM, BigPack2M centre place entry q first w x →
      x.ctl.mode = Mode.choose → x.ctl.odd = true →
      GalilScaffoldInputTrace.Represents x.vm.right.head w ∧ 0 < position x.vm.right) :
    RRepChoose centre place entry q first w := by
  intro x hx hm ho
  obtain ⟨hh, hp⟩ := hR x hx hm ho
  exact ⟨hh, present_of_rep_pos hh hp⟩

end Contract

#print axioms rChoosePackL_of_pack
#print axioms present_of_rep_pos
#print axioms rrepChoose_of_pos

end PalPeg.CloseoutPackRun20
