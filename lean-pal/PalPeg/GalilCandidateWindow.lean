import PalPeg.GalilMinimalPeriod

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply

/-- A candidate in a shorter prefix window is a candidate in any longer window that still
contains its `4g+1` places. -/
theorem candidate_window_mono {T : List (Fin 3)} {m n lower g : ℕ}
    (hc : GalilDpCorrect.Candidate (T.take m) lower g) (hn : 4*g+1 ≤ n) :
    GalilDpCorrect.Candidate (T.take n) lower g := by
  obtain ⟨h1, h2, h3, h4⟩ := hc
  have hmlen : (T.take m).length = min m T.length := List.length_take
  have hnlen : (T.take n).length = min n T.length := List.length_take
  refine ⟨h1, ?_, ?_, ?_⟩
  · rw [hnlen]; omega
  · have e1 : (T.take n).take (2*g+1) = T.take (2*g+1) := by
      rw [List.take_take]; congr 1; omega
    have e2 : (T.take m).take (2*g+1) = T.take (2*g+1) := by
      rw [List.take_take]; congr 1; omega
    rw [e1, ← e2]; exact h3
  · have e1 : (T.take n).take (4*g+1) = T.take (4*g+1) := by
      rw [List.take_take]; congr 1; omega
    have e2 : (T.take m).take (4*g+1) = T.take (4*g+1) := by
      rw [List.take_take]; congr 1; omega
    rw [e1, ← e2]; exact h4

#print axioms candidate_window_mono

/-- From the DP's least candidate `k` on the search window `T.take (span+1)`: no smaller
candidate on any window `T.take (m+1)`. -/
theorem no_candidate_below_least {T : List (Fin 3)} {lower span m : ℕ} {y : GalilFppWide.Config 12}
    (hres : GalilDpCorrect.Result (T.take (span+1)) lower 0 y) (hy : y.pc = 346) :
    ∀ g, g < y.pos 11 → ¬ GalilDpCorrect.Candidate (T.take (m+1)) lower g := by
  obtain ⟨k, hk, hpos, hmin⟩ := result_least hres hy
  intro g hgk hcand
  rw [hpos] at hgk
  have hklen : 4*k+1 ≤ (T.take (span+1)).length := hk.2.1
  have hspan : 4*g+1 ≤ span+1 := by
    have : (T.take (span+1)).length ≤ span+1 := by
      rw [List.length_take]; omega
    omega
  exact hmin g hgk (candidate_window_mono hcand hspan)

#print axioms no_candidate_below_least

end PalPeg.GalilScaffoldChainInputSupply
