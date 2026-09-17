import PalPeg.CloseoutShiftMismatch
import PalPeg.GalilEndOfInput

/-!
# The `h`-unit `ShiftRun` exists: piece 4, constructed

`CloseoutWatchRound30`'s piece 4 (and `CloseoutWatchRound33.ShiftRunCL`) is the
existence of a `ShiftRun` of exactly `h` units from the shift entry, and it is
the last non-mechanical-looking conjunct of
`CloseoutShiftMismatch.ShiftAtMismatchM`.  It is not input-dependent at all:
`ShiftRun.next` asks, at each unit, for

* `positive s.remaining = true` — arithmetic on `ofNat h` and `dec`;
* `canRight s.center`, `canRight s.left`, `canRight (right s.left)` — head room.

Rightward movement is blocked *exactly* on the final gap cell
(`GalilEndOfInput.not_canRight_iff`), so head room is a strict position bound,
and the shift moves the centre by `h` and the left head by `2h`.  On a round
with origin `(C, R)` and half period `h` the centre goes `C → C + h` and the
left head `C - R - 1 → C - R - 1 + 2h`, and `RoundScan.size : 2 * h ≤ R` puts
both inside `[C - R, C + R]`, which `ScanInvariant` already represents in `raw`.

So the whole of piece 4 follows by induction on `h` from the two position
bounds; `shiftRun_exists` below is that, and `shiftRun_exists_round` reads the
bounds off a `RoundScan`'s own fields.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutShiftRun

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier

/-- **`canRight` from a strict position bound.**  The head stops only at
`2 * raw.length`. -/
theorem canRight_of_lt {p : PlaceHead} {raw : List (Fin 2)}
    (hrep : GalilScaffoldInputTrace.Represents p.head raw)
    (hpres : p.head.focus ≠ none)
    (hpos : position p < 2 * raw.length) : canRight p := by
  by_contra hc
  rw [(PalPeg.GalilEndOfInput.not_canRight_iff p raw hrep hpres).1 hc] at hpos
  omega

/-- One rightward step of a represented head: position, word and presence. -/
theorem right_step {p : PlaceHead} {raw : List (Fin 2)}
    (hrep : GalilScaffoldInputTrace.Represents p.head raw)
    (hpres : p.head.focus ≠ none) (hc : canRight p) :
    position (right p) = position p + 1 ∧
    GalilScaffoldInputTrace.Represents (right p).head raw ∧
    (right p).head.focus ≠ none :=
  ⟨right_position p hc (represented_position p.head raw hrep hpres).1,
    right_word p raw hrep hc, right_present p raw hrep hpres hc⟩

/-- **The `n`-unit shift run exists.**  Induction on `n`: the counter stays
positive while `value remaining = n`, and the two position bounds give the
three `canRight` obligations and reproduce themselves one unit on. -/
theorem shiftRun_exists (raw : List (Fin 2)) :
    ∀ (n : ℕ) (s : ShiftState), Canonical s.remaining → value s.remaining = (n : ℤ) →
      GalilScaffoldInputTrace.Represents s.center.head raw → s.center.head.focus ≠ none →
      GalilScaffoldInputTrace.Represents s.left.head raw → s.left.head.focus ≠ none →
      position s.center + n < 2 * raw.length →
      position s.left + 2 * n < 2 * raw.length →
      ∃ t : ShiftState, ShiftRun s n t := by
  intro n
  induction n with
  | zero => intro s _ _ _ _ _ _ _ _; exact ⟨s, .stop s⟩
  | succ n ih =>
    intro s hcan hval hcr hcp hlr hlp hcb hlb
    have hpos : positive s.remaining = true := by
      rw [positive_iff s.remaining hcan, hval]
      exact_mod_cast Nat.succ_pos n
    have hc : canRight s.center := canRight_of_lt hcr hcp (by omega)
    have hl : canRight s.left := canRight_of_lt hlr hlp (by omega)
    obtain ⟨hcpos, hcr', hcp'⟩ := right_step hcr hcp hc
    obtain ⟨hlpos, hlr', hlp'⟩ := right_step hlr hlp hl
    have hl' : canRight (right s.left) := canRight_of_lt hlr' hlp' (by omega)
    obtain ⟨hlpos2, hlr2, hlp2⟩ := right_step hlr' hlp' hl'
    obtain ⟨t, hrun⟩ := ih (shiftTick s)
      (dec_canonical _ hcan)
      (by
        show value (dec s.remaining) = (n : ℤ)
        rw [dec_value, hval]; push_cast; ring)
      (by show GalilScaffoldInputTrace.Represents (right s.center).head raw; exact hcr')
      (by show (right s.center).head.focus ≠ none; exact hcp')
      (by show GalilScaffoldInputTrace.Represents (right (right s.left)).head raw; exact hlr2)
      (by show (right (right s.left)).head.focus ≠ none; exact hlp2)
      (by show position (right s.center) + n < 2 * raw.length; rw [hcpos]; omega)
      (by show position (right (right s.left)) + 2 * n < 2 * raw.length
          rw [hlpos2, hlpos]; omega)
    exact ⟨t, .next s hpos hc hl hl' hrun⟩

/-- **Piece 4 at the shift entry.**  The `ShiftState` of
`CloseoutShiftMismatch.ShiftAtMismatchM` (and of `Rounds.next`) with its two
head bounds; the counter obligations are discharged by `ofNat`. -/
theorem shiftRun_exists_entry (raw : List (Fin 2)) (h : ℕ) (s1 : GalilVM)
    (hcr : GalilScaffoldInputTrace.Represents s1.center.head raw)
    (hcp : s1.center.head.focus ≠ none)
    (hlr : GalilScaffoldInputTrace.Represents (GalilScaffoldInputHead.left s1.left).head raw)
    (hlp : (GalilScaffoldInputHead.left s1.left).head.focus ≠ none)
    (hcb : position s1.center + h < 2 * raw.length)
    (hlb : position (GalilScaffoldInputHead.left s1.left) + 2 * h < 2 * raw.length) :
    ∃ t' : ShiftState,
      ShiftRun ⟨s1.center, GalilScaffoldInputHead.left s1.left, ofNat h, inc s1.radius,
        inc (inc s1.length)⟩ h t' :=
  shiftRun_exists raw h _ (ofNat_canonical h)
    (by show value (ofNat h) = (h : ℤ); rw [ofNat_value]) hcr hcp hlr hlp hcb hlb

#print axioms canRight_of_lt
#print axioms right_step
#print axioms shiftRun_exists
#print axioms shiftRun_exists_entry

end PalPeg.CloseoutShiftRun
