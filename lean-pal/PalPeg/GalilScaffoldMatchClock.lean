import PalPeg.GalilScaffoldSearchFinish

set_option autoImplicit false
namespace PalPeg.GalilScaffoldMatchClock

/-- Decoded g.clock update: only available scan ticks decrement the clock;
at 1, compare fires and the clock wraps to matchDelay. -/
def run (delay : ℕ) : ℕ → List Bool → ℕ × ℕ
  | clock, [] => (clock,0)
  | clock, false :: bs => run delay clock bs
  | clock, true :: bs =>
      if clock = 1 then
        let result := run delay delay bs
        (result.1,result.2+1)
      else run delay (clock-1) bs

theorem run_invariant (delay clock : ℕ) (bs : List Bool) (hd : 0 < delay)
    (hc : 1 ≤ clock ∧ clock ≤ delay) :
    1 ≤ (run delay clock bs).1 ∧ (run delay clock bs).1 ≤ delay ∧
    bs.count true + (run delay clock bs).1 = clock + (run delay clock bs).2 * delay := by
  induction bs generalizing clock with
  | nil => simp [run]; omega
  | cons b bs ih =>
    cases b with
    | false => simpa [run] using ih clock hc
    | true =>
      by_cases he : clock = 1
      · have ht := ih delay (by omega)
        simp only [run,he,ite_true]
        simp only [List.count_cons_self]
        obtain ⟨h₁,h₂,h₃⟩ := ht
        refine ⟨h₁,h₂,?_⟩
        rw [Nat.add_mul]
        simp only [Nat.one_mul]
        omega
      · have ht := ih (clock-1) (by omega)
        simp only [run,he,ite_false,List.count_cons_self]
        obtain ⟨h₁,h₂,h₃⟩ := ht
        exact ⟨h₁,h₂,by omega⟩

/-- Between clock resets, compares cannot exceed one per delay available
ticks. Search.advanceMatch is a subset of those compares. -/
theorem compare_budget (delay : ℕ) (bs : List Bool) (hd : 0 < delay) :
    (run delay delay bs).2 * delay ≤ bs.count true := by
  obtain ⟨_,h₂,h₃⟩ := run_invariant delay delay bs hd (by omega)
  omega

theorem compare_remainder (delay : ℕ) (bs : List Bool) (hd : 0 < delay) :
    bs.count true < ((run delay delay bs).2+1) * delay := by
  obtain ⟨h₁,_,h₃⟩ := run_invariant delay delay bs hd (by omega)
  rw [Nat.add_mul]
  simp only [Nat.one_mul]
  omega

#print axioms run_invariant
#print axioms compare_budget
#print axioms compare_remainder
end PalPeg.GalilScaffoldMatchClock
