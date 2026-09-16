import PalPeg.GalilLiveCentreReplay

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open Manacher GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-- A mismatching comparison kills the centre at the next place. -/
theorem not_live_of_mismatch {raw : List (Fin 2)} {C k : ℕ} {l r : PlaceHead}
    (hi : ScanInvariant raw C k l r) (hav : canRight r)
    (hmis : read (left l) ≠ read (right r)) : ¬ Live raw (position r + 1) C := by
  rintro ⟨_, hlt, hp⟩
  have hpl := hi.leftPos
  have hpr := hi.rightPos
  have hkC : k + 1 < C := by omega
  have hb : k < C := by omega
  have hposr_pos : 0 < position r := by omega
  have hposl_pos : 0 < position l := by omega
  have hposl : 0 < l.head.left.length := by
    rcases Nat.eq_zero_or_pos l.head.left.length with h0 | hpos
    · exfalso
      have : position l = 0 := by unfold position; rw [h0]; split <;> simp
      omega
    · exact hpos
  have hposr : 0 < r.head.left.length := by
    rcases Nat.eq_zero_or_pos r.head.left.length with h0 | hpos
    · exfalso
      have : position r = 0 := by unfold position; rw [h0]; split <;> simp
      omega
    · exact hpos
  obtain ⟨heq_left, heq_right⟩ :=
    comparison_positions l r C k hposl hposr hav hb hpl hpr
  have hposr1 : position r + 1 - C = k + 1 := by omega
  rw [hposr1] at hp
  have hleftWordRep : GalilScaffoldInputTrace.Represents (left l).head raw :=
    left_word l raw hi.leftRep hi.leftPresent
  have hrightWordRep : GalilScaffoldInputTrace.Represents (right r).head raw :=
    right_word r raw hi.rightRep hav
  have hleftFocus : (left l).head.focus ≠ none :=
    present_of_position (left l) hleftWordRep (by omega)
  have hrightFocus : (right r).head.focus ≠ none :=
    present_of_position (right r) hrightWordRep (by omega)
  have e1 : read (left l) = (encoded raw)[position (left l)]? :=
    represented_read (left l) raw hleftWordRep hleftFocus
  have e2 : read (right r) = (encoded raw)[position (right r)]? :=
    represented_read (right r) raw hrightWordRep hrightFocus
  apply hmis
  rw [e1, e2, heq_left, heq_right]
  exact hp.2.2 (k + 1) le_rfl

end PalPeg.GalilScaffoldChainInputSupply

#print axioms PalPeg.GalilScaffoldChainInputSupply.not_live_of_mismatch
