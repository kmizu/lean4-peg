import PalPeg.SlotClockPosition

set_option autoImplicit false
namespace PalPeg.SlotClockTime
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.SlotClock
open PalPeg.SlotClockSweep PalPeg.SlotClockGeneration PalPeg.SlotClockPosition

theorem next_length (b : Boundary) : b.next.interior + 1 = 16 * (b.interior + 1) := by
  change 16 * (b.interior + 1) - 1 + 1 = _
  omega

/-- Exact elapsed time, stated additively to avoid truncated subtraction. -/
theorem elapsed_balance (k : ℕ) (b : Boundary) :
    elapsed k b + 2 * (b.interior + 1) = 2 * (16 ^ k * (b.interior + 1)) := by
  induction k generalizing b with
  | zero => simp [elapsed]
  | succ k ih =>
    calc
      elapsed (k + 1) b + 2 * (b.interior + 1) =
          elapsed k b.next + 2 * (b.next.interior + 1) := by
            rw [elapsed, next_length]
            omega
      _ = 2 * (16 ^ k * (b.next.interior + 1)) := ih b.next
      _ = 2 * (16 ^ (k + 1) * (b.interior + 1)) := by rw [next_length, pow_succ]; ring

theorem elapsed_closed (k : ℕ) (b : Boundary) :
    elapsed k b = 2 * (16 ^ k - 1) * (b.interior + 1) := by
  have h := elapsed_balance k b
  have hp : 0 < (16 : ℕ) ^ k := pow_pos (by decide) _
  have he : (16 : ℕ) ^ k = (16 ^ k - 1) + 1 := by omega
  rw [he] at h
  nlinarith

theorem elapsed_succ (k : ℕ) (b : Boundary) :
    elapsed (k + 1) b = elapsed k b + 30 * (((Boundary.next^[k]) b).interior + 1) := by
  have h1 := elapsed_balance (k + 1) b
  have h0 := elapsed_balance k b
  rw [interval_growth]
  rw [pow_succ] at h1
  nlinarith

theorem elapsed_ge (k : ℕ) (b : Boundary) : k ≤ elapsed k b := by
  induction k with
  | zero => omega
  | succ k ih => rw [elapsed_succ]; omega

/-- Every round lies in a finite-length generation interval. This
existence proof does not put a generation number into the finite controller. -/
theorem time_decomposition (t : ℕ) (b : Boundary) :
    ∃ k r, t = elapsed k b + r ∧ r < 30 * (((Boundary.next^[k]) b).interior + 1) := by
  have hex : ∃ k, t < elapsed k b := ⟨t + 1, by have := elapsed_ge (t + 1) b; omega⟩
  let j := Nat.find hex
  have hj : t < elapsed j b := Nat.find_spec hex
  have hj0 : j ≠ 0 := by intro h; rw [h] at hj; simp [elapsed] at hj
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hj0
  have hlo : elapsed k b ≤ t := by
    have hh := Nat.find_min hex (show k < Nat.find hex by change k < j; omega)
    omega
  refine ⟨k, t - elapsed k b, by omega, ?_⟩
  rw [hk, elapsed_succ] at hj
  omega

/-- Actual control at every round, not just generation boundaries. -/
theorem control_at_time (t : ℕ) (b : Boundary) :
    ∃ k r, t = elapsed k b + r ∧
      r < 30 * (((Boundary.next^[k]) b).interior + 1) ∧
      (run t b.config).state.1.1 = ((Boundary.next^[k]) b).active ∧
      (run t b.config).state.1.2.val = r / (((Boundary.next^[k]) b).interior + 1) ∧
      (run t b.config).state.2 = 0 := by
  obtain ⟨k, r, ht, hr⟩ := time_decomposition t b
  refine ⟨k, r, ht, hr, ?_⟩
  let c := (Boundary.next^[k]) b
  have hp : r / (c.interior + 1) < 30 := (Nat.div_lt_iff_lt_mul (by omega)).mpr hr
  have hh := phase_at_time c.active 0 c.interior r (by simpa using hp) c.junk c.grown c.focus
  rw [ht, run_add, generations]
  change (run r c.config).state.1.1 = c.active ∧
    (run r c.config).state.1.2.val = r / (c.interior + 1) ∧ (run r c.config).state.2 = 0
  change (run r c.config).state = _ at hh
  rw [hh]
  exact ⟨rfl, by simp, rfl⟩

theorem canonical_window (g : ℕ) (hg : 3 ≤ g) (i : Fin 4) (hi : g % 4 = i.val)
    (r : ℕ) (hr : r < 30 * 2 ^ (g - 2)) (hn : 32 ≤ 2 * 2 ^ (g - 2) + r) :
    SlotSchedule.quarter (2 * 2 ^ (g - 2) + r) i = 2 ^ (g - 2) ∧
    SlotSchedule.phaseAt (2 * 2 ^ (g - 2) + r) i = r / 2 ^ (g - 2) ∧
    SlotSchedule.resAt (2 * 2 ^ (g - 2) + r) i = r % 2 ^ (g - 2) := by
  have hlow : 2 ^ (g - 1) = 2 * 2 ^ (g - 2) := by
    rw [show g - 1 = (g - 2) + 1 by omega, pow_succ, Nat.mul_comm]
  have hhigh : 2 ^ (g + 3) = 32 * 2 ^ (g - 2) := by
    rw [show g + 3 = (g - 2) + 5 by omega, pow_add]
    norm_num
    omega
  have he := SlotSchedule.genExp_unique hn i hi (by rw [hlow]; omega) (by rw [hhigh]; omega)
  have hq : SlotSchedule.quarter (2 * 2 ^ (g - 2) + r) i = 2 ^ (g - 2) := by
    simp only [SlotSchedule.quarter, ← he]
  have hb : SlotSchedule.elapsed (2 * 2 ^ (g - 2) + r) i = r := by
    simp only [SlotSchedule.elapsed, SlotSchedule.birth, ← he, hlow]
    omega
  exact ⟨hq, by rw [SlotSchedule.phaseAt, hb, hq], by rw [SlotSchedule.resAt, hb, hq]⟩

/-- Starting at the mathematical birth time of a power-of-two interval, the
actual phase agrees with canonSlot at every later global time at least 32. -/
theorem phase_matches_schedule (b : Boundary) (g : ℕ) (hg : 3 ≤ g)
    (i : Fin 4) (hi : g % 4 = i.val) (hq : b.interior + 1 = 2 ^ (g - 2))
    (t : ℕ) (hn : 32 ≤ 2 * (b.interior + 1) + t) :
    (run t b.config).state.1.2.val = SlotSchedule.phaseAt (2 * (b.interior + 1) + t) i := by
  obtain ⟨k, r, ht, hr, _, hp, _⟩ := control_at_time t b
  let c := (Boundary.next^[k]) b
  have hc : c.interior + 1 = 2 ^ ((g + 4 * k) - 2) := by
    rw [interval_growth, hq, show g + 4 * k - 2 = (g - 2) + 4 * k by omega, pow_add, pow_mul]
    norm_num
    ring
  have htime : 2 * (b.interior + 1) + t = 2 * (c.interior + 1) + r := by
    have hh := elapsed_balance k b
    have hl := interval_growth k b
    change c.interior + 1 = _ at hl
    rw [← hl] at hh
    omega
  have hm : (g + 4 * k) % 4 = i.val := by omega
  have hh := canonical_window (g + 4 * k) (by omega) i hm r
    (by simpa only [← hc] using hr) (by simpa only [← hc, ← htime] using hn)
  rw [hp, htime, hc]
  exact hh.2.1.symm

/-- info: 'PalPeg.SlotClockTime.phase_matches_schedule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms phase_matches_schedule

/-- All four concrete clocks, from all-blank startup, have the canonical
schedule phase at every global time 32+t. -/
theorem startup_phase_matches (i : Fin 4) (t : ℕ) :
    (SlotClockStartup.slice i (SlotClockStartup.machine.srun
      (List.replicate 32 () ++ List.replicate t ()))).state.1.2.val =
      SlotSchedule.phaseAt (32 + t) i := by
  let q := SlotClockStartup.initialWidth i
  let p := SlotClockStartup.initialPhase i
  let g := SlotSchedule.genExp 32 i
  let b : Boundary := ⟨false, q - 1, [], [], .blank⟩
  have hq : 0 < q := by fin_cases i <;> decide
  have hw : q - 1 + 1 = q := by omega
  have hp : p.val ≤ 14 := by fin_cases i <;> decide
  have he : p.val % 2 = 0 := by fin_cases i <;> decide
  have h32 : 2 * q + p.val * q = 32 := by fin_cases i <;> decide
  have hg : 3 ≤ g := SlotSchedule.genExp_ge_three (by decide) i
  have hi : g % 4 = i.val := SlotSchedule.genExp_mod (by decide) i
  have hb : b.interior + 1 = 2 ^ (g - 2) := by
    change q - 1 + 1 = 2 ^ (g - 2)
    rw [hw]
    exact (SlotClockStartup.schedule_at_32 i).1.symm
  have hs : run (p.val * q) b.config = endpoint false p true (q - 1) [] [] .blank := by
    have hh := idle_boundaries false (q - 1) [] [] .blank p.val hp
    simpa [b, Boundary.config, hw, direction, he] using hh
  have htime : 2 * (b.interior + 1) + (p.val * q + t) = 32 + t := by
    change 2 * (q - 1 + 1) + (p.val * q + t) = _
    rw [hw]
    omega
  have hh := phase_matches_schedule b g hg i hi hb (p.val * q + t) (by rw [htime]; omega)
  rw [htime, run_add, hs] at hh
  rw [SlotClockStartup.from_blank]
  exact hh

/-- info: 'PalPeg.SlotClockTime.startup_phase_matches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms startup_phase_matches

def resident (x : SConfig (SlotClockStartup.Control × Fin 2) Symbol 8) (i : Fin 4) : Bool :=
  decide ((x.state.1.2 i).2.val < 14)

theorem startup_resident (i : Fin 4) (t : ℕ) :
    resident (SlotClockStartup.machine.srun (List.replicate 32 () ++ List.replicate t ())) i =
      SlotSchedule.activeAt (32 + t) i := by
  have hh := startup_phase_matches i t
  change ((SlotClockStartup.machine.srun _).state.1.2 i).2.val = _ at hh
  simp only [resident, SlotSchedule.activeAt, hh]

/-- info: 'PalPeg.SlotClockTime.startup_resident' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms startup_resident

/-- info: 'PalPeg.SlotClockTime.control_at_time' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms control_at_time
/-- info: 'PalPeg.SlotClockTime.elapsed_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms elapsed_closed

end PalPeg.SlotClockTime
