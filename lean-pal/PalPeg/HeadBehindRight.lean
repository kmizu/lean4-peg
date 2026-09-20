import PalPeg.GalilNeedBound

/-!
# A head behind the right head

A head consumes a letter by moving right only when it stands on its own front (`gap = true`, empty
right stack).  A represented, sane head that has used no more letters than the right head and
stands no further right does not consume more than the right head by moving right.  So where the
lookahead of the right head has arrived, such a head can still move right after truncation to
the arrived letters: the starvation test on it follows from the need of the right head.
-/

set_option autoImplicit false

namespace PalPeg.HeadBehindRight

open PalPeg PalPeg.GalilThrottledRun PalPeg.GalilTruncTick PalPeg.GalilNeedBound
open PalPeg.GalilScaffoldChainInputSupply

/-- A head that is not on its own front does not consume a letter by moving right. -/
theorem usedPH_right_of_not_front (n : ℕ) (p : GalilScaffoldInputHead.PlaceHead)
    (h : ¬ (p.gap = true ∧ p.head.right = [])) :
    usedPH n (GalilScaffoldChainVerifier.right p) = usedPH n p := by
  rcases p with ⟨⟨f, ls, rs, q⟩, g⟩
  cases g
  · rfl
  · cases rs with
    | nil => exact absurd ⟨rfl, rfl⟩ h
    | cons a rs => rfl

/-- On its front, what a right move consumes depends on the pending letters only. -/
theorem usedPH_right_of_front (n : ℕ) (p : GalilScaffoldInputHead.PlaceHead) (hg : p.gap = true) (hrs : p.head.right = []) :
    usedPH n (GalilScaffoldChainVerifier.right p) = n - (p.head.incoming.length - 1) := by
  rcases p with ⟨⟨f, ls, rs, q⟩, g⟩
  simp only at hg hrs
  subst hg; subst hrs
  cases q with
  | nil => simp [usedPH, GalilScaffoldChainVerifier.right, GalilScaffoldChainVerifier.headRight,
      GalilScaffoldInputTrace.moveRight]
  | cons a q => simp [usedPH, GalilScaffoldChainVerifier.right,
      GalilScaffoldChainVerifier.headRight, GalilScaffoldInputTrace.moveRight]

theorem incoming_length_le {raw : List (Fin 2)} {p : GalilScaffoldInputHead.PlaceHead}
    (hrep : GalilScaffoldInputTrace.Represents p.head raw) :
    p.head.incoming.length ≤ raw.length := by
  obtain ⟨xs, rs, q, hhead, hraw⟩ := hrep
  rw [hhead, hraw]
  cases xs <;> simp [GalilScaffoldInputHead.layout] <;> omega

/-- **A head behind the right head does not consume more than the right head by moving right.** -/
theorem usedPH_right_le_right (raw : List (Fin 2)) (X R : GalilScaffoldInputHead.PlaceHead)
    (hX : GalilScaffoldInputTrace.Represents X.head raw) (hXs : GalilFrontMono.Sane X)
    (hR : GalilScaffoldInputTrace.Represents R.head raw) (hRs : GalilFrontMono.Sane R)
    (hused : usedPH raw.length X ≤ usedPH raw.length R) (hpos : position X ≤ position R) :
    usedPH raw.length (GalilScaffoldChainVerifier.right X)
      ≤ usedPH raw.length (GalilScaffoldChainVerifier.right R) := by
  have hmonoR := usedPH_right_mono raw.length R
  by_cases hfront : X.gap = true ∧ X.head.right = []
  · rcases Nat.lt_or_ge (usedPH raw.length X) (usedPH raw.length R) with hlt | hge
    · have h1 := usedPH_right_mono raw.length (GalilScaffoldChainVerifier.right X)
      have h2 := usedPH_right_right_le raw.length X
      omega
    · have hx := two_usedPH_of_rep raw X hX hXs
      have hr := two_usedPH_of_rep raw R hR hRs
      rw [hfront.1, hfront.2] at hx
      simp only [if_true, List.length_nil] at hx
      have hRfront : R.gap = true ∧ R.head.right = [] := by
        cases hg : R.gap
        · rw [hg] at hr
          simp only [Bool.false_eq_true, if_false] at hr
          omega
        · rw [hg] at hr
          simp only [if_true] at hr
          exact ⟨rfl, List.length_eq_zero_iff.mp (by omega)⟩
      rw [usedPH_right_of_front _ X hfront.1 hfront.2, usedPH_right_of_front _ R hRfront.1 hRfront.2]
      have hxi := incoming_length_le hX
      have hri := incoming_length_le hR
      unfold usedPH at hused hge
      omega
  · rw [usedPH_right_of_not_front _ X hfront]
    omega

/-- **Where the lookahead of the right head has arrived, a head behind it can still move right
after truncation to the arrived letters.** -/
theorem canRight_trunc_of_behind (raw : List (Fin 2)) (j : ℕ)
    (X R : GalilScaffoldInputHead.PlaceHead)
    (hX : GalilScaffoldInputTrace.Represents X.head raw) (hXs : GalilFrontMono.Sane X)
    (hR : GalilScaffoldInputTrace.Represents R.head raw) (hRs : GalilFrontMono.Sane R)
    (hused : usedPH raw.length X ≤ usedPH raw.length R) (hpos : position X ≤ position R)
    (hcanRight : GalilScaffoldChainVerifier.canRight X)
    (hlook : usedPH raw.length (GalilScaffoldChainVerifier.right R) ≤ j) :
    GalilScaffoldChainVerifier.canRight (truncPH (raw.length - j) X) :=
  canRight_truncPH raw.length j X hcanRight
    ((usedPH_right_le_right raw X R hX hXs hR hRs hused hpos).trans hlook)

#print axioms canRight_trunc_of_behind

end PalPeg.HeadBehindRight
