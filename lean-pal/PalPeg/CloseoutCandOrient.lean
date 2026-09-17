import PalPeg.GalilDpSuffix

/-!
# The bare prefix→suffix `Candidate` transport is false

`GalilDpCorrect.Candidate` speaks about *prefixes* of the word handed to the DP,
`GalilDpSuffix.Candidate` about *suffixes* of the logical window.  An earlier
closeout step (`CloseoutPackRun39.H_candOrient`) named the unrestricted
transport between them as a hypothesis.  This file refutes that hypothesis, so
that it cannot be reintroduced: the honest bridge is `GalilDpSuffix.candidate_iff`
(via `w.reverse`), which relates the two at the *same* window, not at a prefix of
one and the whole of the other.

Witness: `W = [0,0,0,0,0,1]`, `n = 5`, `lower = 0`, `h = 1`.
`W.take 5 = [0,0,0,0,0]` has palindromic prefixes of lengths `3` and `5`, while
`W.drop (6-3) = [0,0,1]` is not a palindrome.

The two `Candidate` predicates are themselves fine; only the *unrestricted*
transport is not.  `candidate_iff` below is quoted to show the correct shape.
-/

set_option autoImplicit false

namespace PalPeg.CloseoutCandOrient

private def badWindow : List (Fin 3) := [0, 0, 0, 0, 0, 1]

theorem prefix_ok : GalilDpCorrect.Candidate (badWindow.take 5) 0 1 := by
  unfold GalilDpCorrect.Candidate badWindow
  refine ⟨by omega, by decide, by decide, by decide⟩

theorem suffix_bad : ¬ GalilDpSuffix.Candidate badWindow 0 1 := by
  unfold GalilDpSuffix.Candidate badWindow
  rintro ⟨-, -, h3, -⟩
  exact absurd h3 (by decide)

/-- **The unrestricted prefix→suffix transport is false.**  This is exactly the
shape of the discarded `H_candOrient` hypothesis. -/
theorem unrestricted_transport_false :
    ¬ (∀ (W : List (Fin 3)) (n lower h : ℕ),
      GalilDpCorrect.Candidate (W.take n) lower h →
      GalilDpSuffix.Candidate W lower h) := by
  intro h
  exact suffix_bad (h badWindow 5 0 1 prefix_ok)

/-- The correct bridge, for contrast: the two predicates agree on the *same*
window once the reversal is taken into account.  (Restatement of
`GalilDpSuffix.candidate_iff`.) -/
theorem correct_bridge (w : List (Fin 3)) (lower h : ℕ) :
    GalilDpCorrect.Candidate w.reverse lower h ↔ GalilDpSuffix.Candidate w lower h :=
  GalilDpSuffix.candidate_iff w lower h

#print axioms unrestricted_transport_false
#print axioms correct_bridge

end PalPeg.CloseoutCandOrient
