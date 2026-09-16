import PalPeg.ReplayArrivalRate

set_option autoImplicit false
namespace PalPeg.ReplayContraction
open PalPeg.ReplayLoopEvents

/-- A fixed speed selected from the fixed inner-machine round cost. -/
def speed (B : ℕ) := 8 * (B + 5)

/-- A cycle satisfying the physical worker bound accumulates at most
one eighth of its previous size, plus the one boundary-frame arrival.
The cycle bound is still a premise: this is not the global scheduler proof. -/
theorem shrink (B a b d fresh : ℕ)
    (hd : d ≤ max a b + b * B + 4)
    (ha : fresh * speed B ≤ d + speed B) :
    fresh ≤ max a b / 8 + 2 := by
  let m := max a b
  have hb : b ≤ m := Nat.le_max_right _ _
  have hm : d ≤ (m + 1) * (B + 5) := by
    have hh := Nat.mul_le_mul_right B hb
    dsimp only [m] at *
    nlinarith
  have hs : (8 * fresh) * (B + 5) ≤ (m + 9) * (B + 5) := by
    unfold speed at ha
    nlinarith
  have hc : 8 * fresh ≤ m + 9 := by nlinarith
  dsimp only [m] at hc
  omega

theorem segment_shrink {Terminal : Type} (B : ℕ) (w : List Terminal)
    (pre seg post : List (Event Terminal))
    (he : events (speed B) w = pre ++ seg ++ post) (a b : ℕ)
    (hd : work seg ≤ max a b + b * B + 4) :
    (arrivals seg).length ≤ max a b / 8 + 2 :=
  shrink B a b (work seg) (arrivals seg).length hd
    (PalPeg.ReplayArrivalRate.segment_budget (speed B) w pre seg post he)

/-- Two successive batches contract the pair maximum. A single batch
cannot do so because the preceding batch is retained for cleanup. -/
theorem two_batches (a b c d : ℕ)
    (hc : c ≤ max a b / 8 + 2) (hd : d ≤ max b c / 8 + 2) :
    max c d ≤ max a b / 8 + 3 := by
  have hb : b ≤ max a b := Nat.le_max_right _ _
  have hbc : max b c ≤ max a b + 2 := by omega
  omega

theorem strict_decrease (a b c d : ℕ) (hm : 4 ≤ max a b)
    (hc : c ≤ max a b / 8 + 2) (hd : d ≤ max b c / 8 + 2) :
    max c d < max a b := by
  have hh := two_batches a b c d hc hd
  omega

/-- Once each concrete cycle meets the recurrence, a bounded backlog is
reached in finitely many cycles. This does not assert zero lag. -/
theorem eventually_small (f : ℕ → ℕ)
    (h : ∀ n, f (n + 2) ≤ max (f n) (f (n + 1)) / 8 + 2) :
    ∀ n, ∃ j, n ≤ j ∧ max (f j) (f (j + 1)) ≤ 3 := by
  have aux : ∀ m n, max (f n) (f (n + 1)) = m →
      ∃ j, n ≤ j ∧ max (f j) (f (j + 1)) ≤ 3 := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro n hm
      by_cases hs : m ≤ 3
      · exact ⟨n, le_refl _, hm ▸ hs⟩
      · have hd := strict_decrease (f n) (f (n + 1)) (f (n + 2)) (f (n + 3))
          (by omega) (h n) (by simpa [Nat.add_assoc] using h (n + 1))
        obtain ⟨j, hj, hb⟩ := ih (max (f (n + 2)) (f (n + 3))) (by omega)
          (n + 2) (by simp [Nat.add_assoc])
        exact ⟨j, by omega, hb⟩
  intro n
  exact aux _ n rfl

/-- Worst-case worker budget of one concrete boundary cycle. -/
def cycleCost (B a b : ℕ) := max a b + b * B + 4

/-- Above the small-backlog threshold, two cycles can be paid for by
the decrease in the pair maximum. This gives a linear total budget. -/
theorem pair_cost_drop (B a b c d : ℕ) (hm : 4 ≤ max a b)
    (hc : c ≤ max a b / 8 + 2) (hd : d ≤ max b c / 8 + 2) :
    cycleCost B a b + cycleCost B b c ≤ speed B * (max a b - max c d) := by
  have ht := two_batches a b c d hc hd
  have hb : b ≤ max a b := Nat.le_max_right _ _
  have hcm : c ≤ max a b := by omega
  have hbc : max b c ≤ max a b := max_le hb hcm
  have hdelta : max a b ≤ 4 * (max a b - max c d) := by omega
  have hbB := Nat.mul_le_mul_right B hb
  have hcB := Nat.mul_le_mul_right B hcm
  have hcost : cycleCost B a b + cycleCost B b c ≤ 2 * max a b * (B + 5) := by
    unfold cycleCost
    nlinarith
  have hscale := Nat.mul_le_mul_right (2 * (B + 5)) hdelta
  unfold speed
  nlinarith

/-- Sum of worst-case worker costs for r successive pairs of cycles. -/
def pairWork (B : ℕ) (f : ℕ → ℕ) (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | r + 1 => cycleCost B (f n) (f (n + 1)) + cycleCost B (f (n + 1)) (f (n + 2)) +
      pairWork B f (n + 2) r

/-- A sequence satisfying the concrete-cycle recurrence reaches size at
most three within a linear total worker budget, not just eventually.
The recurrence must still be instantiated along the actual finite trace. -/
theorem small_with_budget (B : ℕ) (f : ℕ → ℕ)
    (h : ∀ n, f (n + 2) ≤ max (f n) (f (n + 1)) / 8 + 2) :
    ∀ n, ∃ r, r ≤ max (f n) (f (n + 1)) ∧
      max (f (n + 2 * r)) (f (n + 2 * r + 1)) ≤ 3 ∧
      pairWork B f n r ≤ speed B * max (f n) (f (n + 1)) := by
  have aux : ∀ m n, max (f n) (f (n + 1)) = m →
      ∃ r, r ≤ m ∧ max (f (n + 2 * r)) (f (n + 2 * r + 1)) ≤ 3 ∧
        pairWork B f n r ≤ speed B * m := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro n hm
      by_cases hs : m ≤ 3
      · exact ⟨0, by omega, by simpa only [Nat.mul_zero, Nat.add_zero] using
          (show max (f n) (f (n + 1)) ≤ 3 by omega), by simp [pairWork]⟩
      · have hn := h n
        have hn1 : f (n + 3) ≤ max (f (n + 1)) (f (n + 2)) / 8 + 2 := by
          simpa [Nat.add_assoc] using h (n + 1)
        have hd := strict_decrease (f n) (f (n + 1)) (f (n + 2)) (f (n + 3))
          (by omega) hn hn1
        have hp := pair_cost_drop B (f n) (f (n + 1)) (f (n + 2)) (f (n + 3))
          (by omega) hn hn1
        obtain ⟨r, hr, hsmall, hwork⟩ := ih (max (f (n + 2)) (f (n + 3))) (by omega)
          (n + 2) (by simp [Nat.add_assoc])
        refine ⟨r + 1, by omega, ?_, ?_⟩
        · convert hsmall using 1 <;> congr 2 <;> omega
        · rw [pairWork]
          have he : max (f n) (f (n + 1)) - max (f (n + 2)) (f (n + 3)) +
              max (f (n + 2)) (f (n + 3)) = m := by omega
          nlinarith
  intro n
  exact aux _ n rfl

/-- info: 'PalPeg.ReplayContraction.small_with_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms small_with_budget

/-- info: 'PalPeg.ReplayContraction.eventually_small' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms eventually_small

/-- info: 'PalPeg.ReplayContraction.segment_shrink' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms segment_shrink

end PalPeg.ReplayContraction
