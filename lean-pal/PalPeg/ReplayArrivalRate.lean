import PalPeg.ReplayLoopEventCut

set_option autoImplicit false
namespace PalPeg.ReplayArrivalRate
open PalPeg.ReplayLoopEvents PalPeg.ReplayLoopEventCut
variable {Terminal : Type}

/-- Before a frame ends, its arrival is the only possible one not backed
by C completed worker ticks. This bound includes cuts inside a frame. -/
theorem prefix_budget (C : ℕ) (w : List Terminal) (n : ℕ) :
    (arrivals ((events C w).take n)).length * C ≤ work ((events C w).take n) + C := by
  induction w generalizing n with
  | nil => simp [events, arrivals, work]
  | cons a w ih =>
    cases n with
    | zero => simp [arrivals, work]
    | succ n =>
      change (arrivals ((.arrival a :: (List.replicate C .tick ++ events C w)).take (n + 1))).length * C ≤
        work ((.arrival a :: (List.replicate C .tick ++ events C w)).take (n + 1)) + C
      simp only [List.take_succ_cons, arrivals, List.filterMap_cons, List.length_cons, Nat.succ_mul, work]
      by_cases hn : n ≤ C
      · have ht : (List.replicate C (Event.tick : Event Terminal) ++ events C w).take n =
            List.replicate n .tick := by
          rw [List.take_append_of_le_length (by simpa using hn)]
          simp [List.take_replicate, Nat.min_eq_left hn]
        rw [ht]
        simp [List.filterMap_replicate, work, work_ticks]
      · have ht : (List.replicate C (Event.tick : Event Terminal) ++ events C w).take n =
            List.replicate C .tick ++ (events C w).take (n - C) := by
          rw [List.take_append]
          simp [List.take_replicate, Nat.min_eq_right (by omega : C ≤ n)]
        rw [ht]
        have hh := ih (n - C)
        simp only [arrivals] at hh
        simp only [List.filterMap_append, List.filterMap_replicate, List.nil_append,
          work, work_append, work_ticks]
        omega

theorem prefix_work (C : ℕ) (w : List Terminal) (n : ℕ) :
    work ((events C w).take n) ≤ (arrivals ((events C w).take n)).length * C := by
  induction w generalizing n with
  | nil => simp [events, arrivals, work]
  | cons a w ih =>
    cases n with
    | zero => simp [arrivals, work]
    | succ n =>
      change work ((.arrival a :: (List.replicate C .tick ++ events C w)).take (n + 1)) ≤
        (arrivals ((.arrival a :: (List.replicate C .tick ++ events C w)).take (n + 1))).length * C
      simp only [List.take_succ_cons, arrivals, List.filterMap_cons, List.length_cons, Nat.succ_mul, work]
      by_cases hn : n ≤ C
      · have ht : (List.replicate C (Event.tick : Event Terminal) ++ events C w).take n =
            List.replicate n .tick := by
          rw [List.take_append_of_le_length (by simpa using hn)]
          simp [List.take_replicate, Nat.min_eq_left hn]
        rw [ht]
        simpa [work_ticks] using hn
      · have ht : (List.replicate C (Event.tick : Event Terminal) ++ events C w).take n =
            List.replicate C .tick ++ (events C w).take (n - C) := by
          rw [List.take_append]
          simp [List.take_replicate, Nat.min_eq_right (by omega : C ≤ n)]
        rw [ht]
        have hh := ih (n - C)
        simp only [arrivals] at hh
        simp only [List.filterMap_append, List.filterMap_replicate, List.nil_append,
          work_append, work_ticks]
        omega

/-- Any contiguous segment, including one beginning in the middle of a
frame, contains at most one arrival beyond its completed worker budget. -/
theorem segment_budget (C : ℕ) (w : List Terminal) (pre seg post : List (Event Terminal))
    (he : events C w = pre ++ seg ++ post) :
    (arrivals seg).length * C ≤ work seg + C := by
  have hpre : (events C w).take pre.length = pre := by
    rw [he, List.append_assoc]
    simp
  have hseg : (events C w).take (pre ++ seg).length = pre ++ seg := by
    rw [he]
    exact List.take_left
  have hhi := prefix_budget C w (pre ++ seg).length
  have hlo := prefix_work C w pre.length
  rw [hpre] at hlo
  rw [hseg, work_append] at hhi
  simp only [arrivals, List.filterMap_append, List.length_append, Nat.add_mul] at hhi
  simp only [arrivals] at hlo ⊢
  omega

/-- info: 'PalPeg.ReplayArrivalRate.segment_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms segment_budget

/-- info: 'PalPeg.ReplayArrivalRate.prefix_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prefix_budget

end PalPeg.ReplayArrivalRate
