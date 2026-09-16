import PalPeg.SlotClockGeneration
import PalPeg.SlotClockStartup

set_option autoImplicit false
namespace PalPeg.SlotClockPosition
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.SlotClock
open PalPeg.SlotClockSweep PalPeg.SlotClockGeneration

/-- A nonempty prefix stopping strictly before the next left boundary. -/
theorem prefix_left (a : Bool) (p : Fin 30) (he : p.val % 2 = 0)
    (k m : ℕ) (junk right : List Symbol) (s : Symbol) (T : Fin 2 → STape Symbol)
    (ha : T (slot a) = ⟨List.replicate (k + 1 + m) .tick ++ .edge :: junk, s, right⟩) :
    let y := run (k + 1) ⟨((a, p), 0), T⟩
    y.state = ((a, p), 0) ∧ y.tape (slot a) =
      ⟨List.replicate m .tick ++ .edge :: junk, .tick, List.replicate k .tick ++ s :: right⟩ := by
  induction k generalizing right s T with
  | zero =>
    have ht : moved (a, p) T (slot a) =
        ⟨List.replicate m .tick ++ .edge :: junk, .tick, s :: right⟩ := by
      rw [moved_active, ha]
      simp [he, STape.applyAction, Nat.add_comm 1 m, List.replicate_succ]
    rw [run_succ, round_nonedge a p T (by rw [ht]; exact (by decide : Symbol.tick ≠ Symbol.edge))]
    exact ⟨rfl, ht⟩
  | succ k ih =>
    have ht : moved (a, p) T (slot a) =
        ⟨List.replicate (k + 1 + m) .tick ++ .edge :: junk, .tick, s :: right⟩ := by
      rw [moved_active, ha]
      rw [show k + 1 + 1 + m = (k + 1 + m) + 1 by omega]
      simp [he, STape.applyAction, List.replicate_succ]
    rw [run_succ, round_nonedge a p T (by rw [ht]; exact (by decide : Symbol.tick ≠ Symbol.edge))]
    have hh := ih (s :: right) .tick (moved (a, p) T) ht
    simpa only [List.replicate_succ', List.append_assoc, List.singleton_append] using hh

/-- Includes phase 29: the control does not exchange roles before the boundary. -/
theorem prefix_right (a : Bool) (p : Fin 30) (he : p.val % 2 ≠ 0)
    (k m : ℕ) (left junk : List Symbol) (s : Symbol) (T : Fin 2 → STape Symbol)
    (ha : T (slot a) = ⟨left, s, List.replicate (k + 1 + m) .tick ++ .edge :: junk⟩) :
    let y := run (k + 1) ⟨((a, p), 0), T⟩
    y.state = ((a, p), 0) ∧ y.tape (slot a) =
      ⟨List.replicate k .tick ++ s :: left, .tick, List.replicate m .tick ++ .edge :: junk⟩ := by
  induction k generalizing left s T with
  | zero =>
    have ht : moved (a, p) T (slot a) =
        ⟨s :: left, .tick, List.replicate m .tick ++ .edge :: junk⟩ := by
      rw [moved_active, ha]
      simp [he, STape.applyAction, Nat.add_comm 1 m, List.replicate_succ]
    rw [run_succ, round_nonedge a p T (by rw [ht]; exact (by decide : Symbol.tick ≠ Symbol.edge))]
    exact ⟨rfl, ht⟩
  | succ k ih =>
    have ht : moved (a, p) T (slot a) =
        ⟨s :: left, .tick, List.replicate (k + 1 + m) .tick ++ .edge :: junk⟩ := by
      rw [moved_active, ha]
      rw [show k + 1 + 1 + m = (k + 1 + m) + 1 by omega]
      simp [he, STape.applyAction, List.replicate_succ]
    rw [run_succ, round_nonedge a p T (by rw [ht]; exact (by decide : Symbol.tick ≠ Symbol.edge))]
    have hh := ih (s :: left) .tick (moved (a, p) T) ht
    simpa only [List.replicate_succ', List.append_assoc, List.singleton_append] using hh

def direction (p : Fin 30) : Bool := decide (p.val % 2 = 0)

theorem prefix_state (a : Bool) (p : Fin 30) (n r : ℕ) (hr : r < n + 1)
    (junk grown : List Symbol) (u : Symbol) :
    (run r (endpoint a p (direction p) n junk grown u)).state = ((a, p), 0) := by
  cases r with
  | zero => rfl
  | succ k =>
    have hn : n = k + 1 + (n - (k + 1)) := by omega
    by_cases he : p.val % 2 = 0
    · have hh := prefix_left a p he k (n - (k + 1)) junk [] .edge
        (endpoint a p (direction p) n junk grown u).tape
        (by simp [endpoint, direction, he, ← hn])
      exact hh.1
    · have hh := prefix_right a p he k (n - (k + 1)) junk [] .edge
        (endpoint a p (direction p) n junk grown u).tape
        (by simp [endpoint, direction, he, ← hn])
      exact hh.1

theorem boundary_step (a : Bool) (p : Fin 30) (hp : p.val < 29)
    (n : ℕ) (junk grown : List Symbol) (u : Symbol) :
    run (n + 1) (endpoint a p (direction p) n junk grown u) =
      endpoint a (nextPhase p) (direction (nextPhase p)) n junk
        (grownNext p n grown) (focusNext p u) := by
  have hn : (nextPhase p).val = p.val + 1 := by
    simp [nextPhase, show p.val + 1 < 30 by omega]
  by_cases he : p.val % 2 = 0
  · have ho : (nextPhase p).val % 2 ≠ 0 := by omega
    simpa only [direction, he, ho, decide_true, decide_false] using left_step a p he n junk grown u
  · have ho : (nextPhase p).val % 2 = 0 := by omega
    have h29 : p ≠ 29 := by intro h; subst p; contradiction
    simpa only [direction, he, ho, decide_true, decide_false] using right_step a p he h29 n junk grown u

theorem boundaries (a : Bool) (p : Fin 30) (n : ℕ) (junk grown : List Symbol)
    (u : Symbol) (k : ℕ) (hk : p.val + k < 30) :
    ∃ g v, run (k * (n + 1)) (endpoint a p (direction p) n junk grown u) =
      endpoint a ⟨p.val + k, hk⟩ (direction ⟨p.val + k, hk⟩) n junk g v := by
  induction k with
  | zero => exact ⟨grown, u, by simp [run]⟩
  | succ k ih =>
    obtain ⟨g, v, h⟩ := ih (by omega)
    rw [Nat.succ_mul, run_add, h]
    let pp : Fin 30 := ⟨p.val + k, by omega⟩
    have hp : pp.val < 29 := by dsimp [pp]; omega
    have he : nextPhase pp = (⟨p.val + (k + 1), hk⟩ : Fin 30) := by
      apply Fin.ext
      simp [nextPhase, pp, hk, Nat.add_assoc]
    refine ⟨grownNext pp n g, focusNext pp v, ?_⟩
    exact (boundary_step a pp hp n junk g v).trans (by rw [he])

theorem phase_offset (a : Bool) (p : Fin 30) (n k r : ℕ)
    (hk : p.val + k < 30) (hr : r < n + 1)
    (junk grown : List Symbol) (u : Symbol) :
    (run (k * (n + 1) + r) (endpoint a p (direction p) n junk grown u)).state =
      ((a, ⟨p.val + k, hk⟩), 0) := by
  obtain ⟨g, v, h⟩ := boundaries a p n junk grown u k hk
  rw [run_add, h]
  exact prefix_state a _ n r hr junk g v

/-- The actual finite control at every time strictly before this generation
ends, including starts at a nonzero phase as used by the startup circuit. -/
theorem phase_at_time (a : Bool) (p : Fin 30) (n t : ℕ)
    (ht : p.val + t / (n + 1) < 30) (junk grown : List Symbol) (u : Symbol) :
    (run t (endpoint a p (direction p) n junk grown u)).state =
      ((a, ⟨p.val + t / (n + 1), ht⟩), 0) := by
  have hh := phase_offset a p n (t / (n + 1)) (t % (n + 1)) ht
    (Nat.mod_lt _ (by omega)) junk grown u
  simpa only [Nat.mul_comm, Nat.div_add_mod] using hh

theorem idle_boundaries (a : Bool) (n : ℕ) (junk grown : List Symbol) (u : Symbol)
    (k : ℕ) (hk : k ≤ 14) :
    run (k * (n + 1)) (endpoint a 0 true n junk grown u) =
      endpoint a ⟨k, by omega⟩ (direction ⟨k, by omega⟩) n junk grown u := by
  induction k with
  | zero => simp [run, direction]
  | succ k ih =>
    rw [Nat.succ_mul, run_add, ih (by omega)]
    let pp : Fin 30 := ⟨k, by omega⟩
    have hp : pp.val < 29 := by dsimp [pp]; omega
    have he : nextPhase pp = (⟨k + 1, by omega⟩ : Fin 30) := by
      apply Fin.ext
      simp [nextPhase, pp, show k + 1 < 30 by omega]
    have hh := boundary_step a pp hp n junk grown u
    rw [he] at hh
    simpa only [grownNext, focusNext, if_pos (show pp.val < 14 by dsimp [pp]; omega)] using hh

/-- The startup phases skip only idle sweeps, so their first generation still
produces a full sixteenfold interval; it merely takes fewer rounds. -/
theorem generation_from_phase (a : Bool) (p : Fin 30) (hp : p.val ≤ 14)
    (he : p.val % 2 = 0) (n : ℕ) (junk grown : List Symbol) (u : Symbol) :
    run ((30 - p.val) * (n + 1)) (endpoint a p true n junk grown u) =
      endpoint (!a) 0 true (16 * (n + 1) - 1) grown
        (List.replicate n .tick ++ .edge :: junk) .edge := by
  have hs := idle_boundaries a n junk grown u p.val hp
  have hf := generation a n junk grown u
  have hsplit : 30 * (n + 1) = p.val * (n + 1) + (30 - p.val) * (n + 1) := by
    rw [← Nat.add_mul, Nat.add_sub_of_le (by omega : p.val ≤ 30)]
  rw [hsplit, run_add, hs] at hf
  simpa only [direction, he, decide_true] using hf

/-- info: 'PalPeg.SlotClockPosition.generation_from_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms generation_from_phase

theorem first_generation_from_blank (i : Fin 4) :
    SlotClockStartup.slice i (SlotClockStartup.machine.srun
      (List.replicate 32 () ++ List.replicate
        ((30 - (SlotClockStartup.initialPhase i).val) * SlotClockStartup.initialWidth i) ())) =
      endpoint true 0 true (16 * SlotClockStartup.initialWidth i - 1) []
        (List.replicate (SlotClockStartup.initialWidth i - 1) .tick ++ [.edge]) .edge := by
  have hp : (SlotClockStartup.initialPhase i).val ≤ 14 := by fin_cases i <;> decide
  have he : (SlotClockStartup.initialPhase i).val % 2 = 0 := by fin_cases i <;> decide
  have hq : 0 < SlotClockStartup.initialWidth i := by fin_cases i <;> decide
  have hw : SlotClockStartup.initialWidth i - 1 + 1 = SlotClockStartup.initialWidth i := by omega
  rw [SlotClockStartup.from_blank]
  change run _ (endpoint false (SlotClockStartup.initialPhase i) true
    (SlotClockStartup.initialWidth i - 1) [] [] .blank) = _
  have hh := generation_from_phase false (SlotClockStartup.initialPhase i) hp he
    (SlotClockStartup.initialWidth i - 1) [] [] .blank
  simpa only [hw, Bool.not_false] using hh

/-- info: 'PalPeg.SlotClockPosition.first_generation_from_blank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms first_generation_from_blank

/-- info: 'PalPeg.SlotClockPosition.phase_at_time' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms phase_at_time
/-- info: 'PalPeg.SlotClockPosition.prefix_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prefix_left
/-- info: 'PalPeg.SlotClockPosition.prefix_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prefix_right

end PalPeg.SlotClockPosition
