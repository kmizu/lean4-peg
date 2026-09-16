import PalPeg.GalilDpCorrect

set_option autoImplicit false
namespace PalPeg.GalilDpSuffix
open GalilFppWide

/-- Search copies a window right-to-left. Its prefix lengths therefore
denote suffix lengths in the original window. -/
theorem reverse_prefix_pal (w : List (Fin 3)) (n : ℕ) :
    (w.reverse.take n).reverse = w.reverse.take n ↔
      (w.drop (w.length-n)).reverse = w.drop (w.length-n) := by
  rw [List.take_reverse]
  simp only [List.reverse_reverse]
  exact eq_comm

def Candidate (w : List (Fin 3)) (lower h : ℕ) : Prop :=
  lower < h ∧ 4*h+1 ≤ w.length ∧
    (w.drop (w.length-(2*h+1))).reverse = w.drop (w.length-(2*h+1)) ∧
    (w.drop (w.length-(4*h+1))).reverse = w.drop (w.length-(4*h+1))

theorem candidate_iff (w : List (Fin 3)) (lower h : ℕ) :
    GalilDpCorrect.Candidate w.reverse lower h ↔ Candidate w lower h := by
  simp only [GalilDpCorrect.Candidate, Candidate, List.length_reverse, reverse_prefix_pal]

def Result (w : List (Fin 3)) (lower : ℕ) (y : Config 12) : Prop :=
  (∃ h, Candidate w lower h ∧
    (∀ k, k < h → ¬ Candidate w lower k) ∧
    y.pc = 346 ∧ y.tape 11 = GalilDpCounters.output h ∧ y.pos 11 = h) ∨
  (y.pc = 347 ∧ ∀ h, ¬ Candidate w lower h)

theorem result_of_reverse {w : List (Fin 3)} {lower : ℕ} {y : Config 12}
    (hr : GalilDpCorrect.Result w.reverse lower 0 y) : Result w lower y := by
  rcases hr with ⟨h,_,hc,hmin,hp,ht⟩ | ⟨hp,hnone⟩
  · left
    refine ⟨h,(candidate_iff w lower h).mp hc,?_,hp,ht⟩
    intro k hk hc
    exact hmin k (Nat.zero_le _) hk ((candidate_iff w lower k).mpr hc)
  · right
    refine ⟨hp,?_⟩
    intro h hc
    exact hnone h (Nat.zero_le _) ((candidate_iff w lower h).mpr hc)

/-- Correct suffix search on a reversed physical preload. This bridges
the DP mathematical contract to Search's window orientation; it does not
assume or prove the online copy/reset mechanism itself. -/
theorem initial_correct (w : List (Fin 3)) (lower : ℕ) :
    ∃ y qs, Completed GalilDpCode.code (GalilDpPrepared.initial w.reverse lower) qs y ∧
      Result w lower y := by
  obtain ⟨y, qs, hs, hr⟩ := GalilDpCorrect.initial_correct w.reverse lower
  exact ⟨y,qs,hs,result_of_reverse hr⟩

/-- Search copies at most span+1 symbols while walking left. Truncating
that reversed source is exactly selecting the corresponding suffix window. -/
theorem window_correct (w : List (Fin 3)) (span lower : ℕ) :
    ∃ y qs, Completed GalilDpCode.code
      (GalilDpPrepared.initial (w.reverse.take (span+1)) lower) qs y ∧
      Result (w.drop (w.length-(span+1))) lower y := by
  simpa only [List.take_reverse] using
    initial_correct (w.drop (w.length-(span+1))) lower

#print axioms initial_correct
#print axioms window_correct
end PalPeg.GalilDpSuffix
