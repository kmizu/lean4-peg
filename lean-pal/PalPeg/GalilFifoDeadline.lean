import Mathlib

set_option autoImplicit false
namespace PalPeg.GalilFifoDeadline

/-- Completion time in worker units. Job n arrives at time 2*c*n.
The work includes every source transition assigned to that job. -/
def finish (c : ℕ) (work : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => max (finish c work n) (2 * c * n) + work n

/-- The source's prediction credit pays for delayed negative answers.
This is a scheduling theorem, not an implementation of the local FIFO. -/
theorem finish_bound (c : ℕ) (work prediction : ℕ → ℕ)
    (hwork : ∀ n, work n + c * prediction n ≤ 2 * c + c * prediction (n + 1)) :
    ∀ n, finish c work n ≤ 2 * c * n + c * prediction n := by
  intro n
  induction n with
  | zero => simp [finish]
  | succ n ih =>
    have hm : max (finish c work n) (2 * c * n) ≤ 2 * c * n + c * prediction n :=
      max_le ih (Nat.le_add_right _ _)
    have hw := hwork n
    rw [finish]
    nlinarith

/-- A positive output has no prediction credit and meets its own deadline.
No assumption says that every negative output finishes on time. -/
theorem positive_deadline (c : ℕ) (work prediction : ℕ → ℕ) (positive : ℕ → Prop)
    (hwork : ∀ n, work n + c * prediction n ≤ 2 * c + c * prediction (n + 1))
    (hpositive : ∀ n, positive n → prediction n = 0) (n : ℕ) (hn : positive n) :
    finish c work n ≤ 2 * c * n := by
  simpa only [hpositive n hn, Nat.mul_zero, Nat.add_zero] using finish_bound c work prediction hwork n

/-- The external answer is false until the source's answer for this prefix
is complete, as in Scala's buffer.answer update. -/
def answer (c : ℕ) (work : ℕ → ℕ) (source : ℕ → Bool) (n : ℕ) : Bool :=
  if finish c work n ≤ 2 * c * n then source n else false

theorem answer_eq_source (c : ℕ) (work prediction : ℕ → ℕ) (source : ℕ → Bool)
    (hwork : ∀ n, work n + c * prediction n ≤ 2 * c + c * prediction (n + 1))
    (hpositive : ∀ n, source n = true → prediction n = 0) :
    ∀ n, answer c work source n = source n := by
  intro n
  cases hs : source n with
  | false => simp [answer, hs]
  | true =>
    have hd := positive_deadline c work prediction (fun i => source i = true) hwork hpositive n hs
    simp [answer, hd, hs]

/-- Derive the prediction inequality from the source's center-move cost.
These are the exact coordinates used by Scala's ContractAudit.observeOutput. -/
theorem move_predictability (alpha beta size current next ticks : ℕ)
    (hcurrent : size ≤ current) (hnext : size + 1 ≤ next) (hmono : current ≤ next)
    (htime : ticks ≤ alpha * (next - current) + beta) :
    ticks + (alpha + beta) * (current - size - 1) ≤
      2 * (alpha + beta) + (alpha + beta) * (next - (size + 1) - 1) := by
  by_cases he : next = current
  · have hk : current - size - 1 ≤ (next - (size + 1) - 1) + 1 := by omega
    have hs := Nat.mul_le_mul_left (alpha + beta) hk
    simp only [he, Nat.sub_self, Nat.mul_zero, Nat.zero_add] at htime
    nlinarith
  · have hd : 1 ≤ next - current := by omega
    have hk : current - size - 1 + (next - current) ≤ next - (size + 1) - 1 + 2 := by omega
    have hs := Nat.mul_le_mul_left (alpha + beta) hk
    have hb := Nat.mul_le_mul_left beta hd
    nlinarith

/-- End-to-end scheduling consequence of the center invariant and move
cost: fixed service 2*(alpha+beta) preserves every source answer. -/
theorem center_answer_eq (alpha beta : ℕ) (work center : ℕ → ℕ) (source : ℕ → Bool)
    (hcenter : ∀ n, n ≤ center n)
    (hmono : ∀ n, center n ≤ center (n + 1))
    (htime : ∀ n, work n ≤ alpha * (center (n + 1) - center n) + beta)
    (hpositive : ∀ n, source n = true → center n = n) :
    ∀ n, answer (alpha + beta) work source n = source n := by
  apply answer_eq_source (alpha + beta) work (fun n => center n - n - 1) source
  · intro n
    exact move_predictability alpha beta n (center n) (center (n + 1)) (work n)
      (hcenter n) (hcenter (n + 1)) (hmono n) (htime n)
  · intro n hn
    simp [hpositive n hn]

/-- Regression: the second answer in the Scala scripted-source example is
late. Its fifth (positive) answer is on time. Universal zero lag is unnecessary. -/
example : finish 3 (fun n => if n = 0 then 1 else if n = 1 then 10 else if n = 2 then 2 else 1) 2 > 12 ∧
    finish 3 (fun n => if n = 0 then 1 else if n = 1 then 10 else if n = 2 then 2 else 1) 5 ≤ 30 := by
  decide

/-- info: 'PalPeg.GalilFifoDeadline.answer_eq_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms answer_eq_source

/-- info: 'PalPeg.GalilFifoDeadline.center_answer_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms center_answer_eq

end PalPeg.GalilFifoDeadline
