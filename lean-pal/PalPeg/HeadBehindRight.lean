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

/-- **The converse of `canRight_truncPH`.**  A head that has used at most `j` letters and can
still move right after truncation to the `j` arrived letters uses at most `j` letters after the
move: on its front, the truncated pending list is not empty, so the letter it consumes has
arrived. -/
theorem usedPH_right_le_of_canRight_trunc (n j : ℕ) (p : GalilScaffoldInputHead.PlaceHead)
    (hpending : p.head.incoming.length ≤ n) (hused : usedPH n p ≤ j)
    (hcanRight : GalilScaffoldChainVerifier.canRight (truncPH (n - j) p)) :
    usedPH n (GalilScaffoldChainVerifier.right p) ≤ j := by
  by_cases hfront : p.gap = true ∧ p.head.right = []
  · rw [usedPH_right_of_front n p hfront.1 hfront.2]
    rcases p with ⟨⟨f, ls, rs, q⟩, g⟩
    simp only at hfront hpending
    obtain ⟨hg, hrs⟩ := hfront
    subst hg; subst hrs
    have hnonempty : dropN (n - j) q ≠ [] := by
      rcases hcanRight with h | h | h
      · exact absurd h (by simp [truncPH])
      · exact absurd h (by simp [truncPH])
      · simpa [truncPH] using h
    have hlength : 0 < (dropN (n - j) q).length := List.length_pos_of_ne_nil hnonempty
    simp only [dropN, List.length_take] at hlength
    show n - (q.length - 1) ≤ j
    omega
  · rw [usedPH_right_of_not_front n p hfront]
    exact hused

#print axioms usedPH_right_le_of_canRight_trunc

/-- **A head that stands no further right than the right head looks ahead within the arrived
letters as soon as the right head does.**  Off its front the move consumes nothing, and the
letters the head has used have arrived; on its front its place pins the letters it has used, so
they are at most those of the right head, and `usedPH_right_le_right` applies.  No comparison of
the letters used by the two heads is assumed: only their places. -/
theorem usedPH_right_le_of_position_le (raw : List (Fin 2)) (j : ℕ)
    (X R : GalilScaffoldInputHead.PlaceHead)
    (hX : GalilScaffoldInputTrace.Represents X.head raw) (hXs : GalilFrontMono.Sane X)
    (hR : GalilScaffoldInputTrace.Represents R.head raw) (hRs : GalilFrontMono.Sane R)
    (hpos : position X ≤ position R) (husedX : usedPH raw.length X ≤ j)
    (hlookR : usedPH raw.length (GalilScaffoldChainVerifier.right R) ≤ j) :
    usedPH raw.length (GalilScaffoldChainVerifier.right X) ≤ j := by
  by_cases hfront : X.gap = true ∧ X.head.right = []
  · have hx := two_usedPH_of_rep raw X hX hXs
    have hr := two_usedPH_of_rep raw R hR hRs
    rw [hfront.1, hfront.2] at hx
    simp only [if_true, List.length_nil] at hx
    have hused : usedPH raw.length X ≤ usedPH raw.length R := by
      split_ifs at hr <;> omega
    exact (usedPH_right_le_right raw X R hX hXs hR hRs hused hpos).trans hlookR
  · rw [usedPH_right_of_not_front raw.length X hfront]
    exact husedX

#print axioms usedPH_right_le_of_position_le

/-- **A head whose next place is not right of a head that has arrived moves right within the
arrived letters.**  Unlike `usedPH_right_le_of_position_le` the position is that of the moved
head, and nothing is asked of the head before the move except that it represents the word: off
its front a right move consumes nothing, and on its front the head has its gap bit set, so it is
sane and its position is twice the letters it has used. -/
theorem usedPH_right_le_of_next_position_le (raw : List (Fin 2)) (j : ℕ)
    (X R : GalilScaffoldInputHead.PlaceHead)
    (hX : GalilScaffoldInputTrace.Represents X.head raw)
    (hR : GalilScaffoldInputTrace.Represents R.head raw) (hRs : GalilFrontMono.Sane R)
    (hposNext : position (GalilScaffoldChainVerifier.right X) ≤ position R)
    (husedX : usedPH raw.length X ≤ j) (husedR : usedPH raw.length R ≤ j) :
    usedPH raw.length (GalilScaffoldChainVerifier.right X) ≤ j := by
  by_cases hfront : X.gap = true ∧ X.head.right = []
  · have hXs : GalilFrontMono.Sane X := Or.inl hfront.1
    have hx := two_usedPH_of_rep raw X hX hXs
    have hr := two_usedPH_of_rep raw R hR hRs
    rw [hfront.1, hfront.2] at hx
    simp only [if_true, List.length_nil] at hx
    by_cases hcanRight : GalilScaffoldChainVerifier.canRight X
    · have hnext := (GalilFrontMono.right_sane hcanRight hXs).1
      have hstep := usedPH_right_right_le raw.length X
      have hmono := usedPH_right_mono raw.length X
      rw [usedPH_right_of_front _ X hfront.1 hfront.2] at *
      have hpending := incoming_length_le hX
      have husedEq : usedPH raw.length X = raw.length - X.head.incoming.length := rfl
      split_ifs at hr <;> omega
    · have hpendingNil : X.head.incoming = [] := by
        by_contra hne
        exact hcanRight (Or.inr (Or.inr hne))
      rw [usedPH_right_of_front _ X hfront.1 hfront.2, hpendingNil]
      have husedEq : usedPH raw.length X = raw.length - X.head.incoming.length := rfl
      rw [hpendingNil] at husedEq
      simp only [List.length_nil] at husedEq ⊢
      omega
  · rw [usedPH_right_of_not_front _ X hfront]
    exact husedX

#print axioms usedPH_right_le_of_next_position_le

end PalPeg.HeadBehindRight
