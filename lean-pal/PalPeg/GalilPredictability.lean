import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
# Predictability gives real time (the abstract FIFO argument)

The abstract core of `docs/palindromes-in-peg/GALIL_CLOCK.md` §"Predictability
and FIFO service": a source that, after reading letter `m`, needs `d m` work
transitions to produce answer `m`, with tentative centres `C m` that never
decrease and never lag the input (`m ≤ C m`), and whose work is bounded by
`c·(δ+1)` for the centre advance `δ`. Served FIFO at rate `2c` per input
round, every positive answer (`C i = i`) is produced within its own round:
the backlog after round `i` is `0`.

Everything here is arithmetic; the three hypotheses are exactly the source
contracts still to be proven for the scaffold (work ledger, centre
monotonicity/non-lag, positive answers have the centre at the input).
-/

set_option autoImplicit false
namespace PalPeg.Predictability

open Finset

/-- Work outstanding after round `i`: `2c` service per round, `d i` new work. -/
def backlog (d : ℕ → ℕ) (c : ℕ) : ℕ → ℕ
  | 0 => 0
  | i+1 => backlog d c i + d (i+1) - 2*c

/-- Work arriving in rounds `j+1 .. i`. -/
def work (d : ℕ → ℕ) (j i : ℕ) : ℕ := ∑ m ∈ Ico (j+1) (i+1), d m

theorem work_self (d : ℕ → ℕ) (j : ℕ) : work d j j = 0 := by simp [work]

theorem work_succ (d : ℕ → ℕ) {j i : ℕ} (h : j ≤ i) : work d j (i+1) = work d j i + d (i+1) := by
  unfold work
  rw [Finset.sum_Ico_succ_top (by omega)]

/-- The start of the current busy period: the last round with no backlog. -/
theorem exists_last_zero (d : ℕ → ℕ) (c : ℕ) (i : ℕ) :
    ∃ j0, j0 ≤ i ∧ backlog d c j0 = 0 ∧ ∀ m, j0 < m → m ≤ i → 0 < backlog d c m := by
  induction i with
  | zero => exact ⟨0, le_rfl, rfl, fun m h1 h2 => by omega⟩
  | succ i ih =>
    by_cases h : backlog d c (i+1) = 0
    · exact ⟨i+1, le_rfl, h, fun m h1 h2 => by omega⟩
    · obtain ⟨j0, hj, hz, hpos⟩ := ih
      refine ⟨j0, by omega, hz, fun m h1 h2 => ?_⟩
      rcases Nat.lt_or_ge m (i+1) with hm | hm
      · exact hpos m h1 (by omega)
      · have hm' : m = i+1 := by omega
        subst hm'
        exact Nat.pos_of_ne_zero h

/-- Inside a busy period the backlog telescopes exactly. -/
theorem backlog_telescope (d : ℕ → ℕ) (c : ℕ) {j0 : ℕ} :
    ∀ i, j0 ≤ i → (∀ m, j0 < m → m ≤ i → 0 < backlog d c m) →
      (backlog d c i : ℤ) = backlog d c j0 + work d j0 i - 2*c*((i - j0 : ℕ) : ℤ) := by
  intro i
  induction i with
  | zero =>
    intro h _
    have h0 : j0 = 0 := by omega
    subst h0
    simp [work_self]
  | succ i ih =>
    intro hle hpos
    rcases Nat.eq_or_lt_of_le hle with heq | hlt
    · subst heq
      simp [work_self]
    · have hi := ih (by omega) (fun m h1 h2 => hpos m h1 (by omega))
      have hp := hpos (i+1) (by omega) le_rfl
      have hb : backlog d c (i+1) = backlog d c i + d (i+1) - 2*c := rfl
      have hge : 2*c ≤ backlog d c i + d (i+1) := by
        by_contra hlt2
        push_neg at hlt2
        rw [hb] at hp
        omega
      rw [work_succ d (by omega)]
      have e : i + 1 - j0 = (i - j0) + 1 := by omega
      rw [e, hb]
      push_cast [hge]
      linarith

/-- If the work of every window `j+1..i` fits in its service, the backlog
after round `i` is zero. -/
theorem backlog_zero_of_bounds (d : ℕ → ℕ) (c : ℕ) (i : ℕ)
    (hb : ∀ j, j ≤ i → work d j i ≤ 2*c*(i - j)) : backlog d c i = 0 := by
  obtain ⟨j0, hj, hz, hpos⟩ := exists_last_zero d c i
  by_contra hne
  have hpos' : 0 < backlog d c i := Nat.pos_of_ne_zero hne
  have ht := backlog_telescope d c i hj hpos
  have hw := hb j0 hj
  rw [hz] at ht
  have hw' : (work d j0 i : ℤ) ≤ 2*c*((i - j0 : ℕ) : ℤ) := by exact_mod_cast hw
  have : (backlog d c i : ℤ) ≤ 0 := by rw [ht]; push_cast; linarith
  omega

/-- The predictability bound: with non-decreasing, non-lagging centres and
work at most `c·(δ+1)` per round, the work of `j+1..i` is at most
`2c(i-j)` whenever the answer at `i` is positive (`C i = i`). -/
theorem work_bound_of_centres (d : ℕ → ℕ) (C : ℕ → ℕ) (c : ℕ)
    (hmono : ∀ m, C m ≤ C (m+1)) (hC : ∀ m, m ≤ C m)
    (hd : ∀ m, (d (m+1) : ℤ) ≤ c * ((C (m+1) : ℤ) - C m + 1))
    {i : ℕ} (hi : C i = i) : ∀ j, j ≤ i → work d j i ≤ 2*c*(i - j) := by
  have key : ∀ n, ∀ j, j ≤ n →
      (work d j n : ℤ) + c * C j ≤ c * C n + c * ((n - j : ℕ) : ℤ) := by
    intro n
    induction n with
    | zero =>
      intro j h
      have h0 : j = 0 := by omega
      subst h0
      simp [work_self]
    | succ n ih =>
      intro j h
      rcases Nat.eq_or_lt_of_le h with heq | hlt
      · subst heq
        simp [work_self]
      · have h1 := ih j (by omega)
        have h2 := hd n
        rw [work_succ d (by omega)]
        have e : n + 1 - j = (n - j) + 1 := by omega
        rw [e]
        push_cast
        linarith
  intro j hj
  have h1 := key i j hj
  have h2 : (j : ℤ) ≤ C j := by exact_mod_cast hC j
  have h3 : (C i : ℤ) = i := by exact_mod_cast hi
  have h4 : ((i - j : ℕ) : ℤ) = (i : ℤ) - j := by push_cast [hj]; ring
  have : (work d j i : ℤ) ≤ 2*c*((i - j : ℕ) : ℤ) := by
    rw [h4] at h1 ⊢
    nlinarith
  exact_mod_cast this

/-- **Predictability gives real time.** A positive answer at round `i` is
produced within round `i` by the FIFO server of rate `2c`. -/
theorem realtime_of_predictable (d : ℕ → ℕ) (C : ℕ → ℕ) (c : ℕ)
    (hmono : ∀ m, C m ≤ C (m+1)) (hC : ∀ m, m ≤ C m)
    (hd : ∀ m, (d (m+1) : ℤ) ≤ c * ((C (m+1) : ℤ) - C m + 1))
    {i : ℕ} (hi : C i = i) : backlog d c i = 0 :=
  backlog_zero_of_bounds d c i (work_bound_of_centres d C c hmono hC hd hi)

/-- The buffered wrapper answers the source's answer when caught up and `0`
(reject) while behind. With a sound and complete source whose positive
answers have the centre at the input, the wrapper is exact at every round. -/
theorem wrapper_exact (d : ℕ → ℕ) (C : ℕ → ℕ) (c : ℕ)
    (hmono : ∀ m, C m ≤ C (m+1)) (hC : ∀ m, m ≤ C m)
    (hd : ∀ m, (d (m+1) : ℤ) ≤ c * ((C (m+1) : ℤ) - C m + 1))
    (answer : ℕ → Bool) (pal : ℕ → Prop)
    (hsource : ∀ i, answer i = true ↔ pal i) (hcentre : ∀ i, pal i → C i = i) (i : ℕ) :
    ((if backlog d c i = 0 then answer i else false) = true) ↔ pal i := by
  by_cases hb : backlog d c i = 0
  · rw [if_pos hb]; exact hsource i
  · rw [if_neg hb]
    constructor
    · intro h; cases h
    · intro hp
      exact absurd (realtime_of_predictable d C c hmono hC hd (hcentre i hp)) hb

#print axioms wrapper_exact

#print axioms realtime_of_predictable

end PalPeg.Predictability
