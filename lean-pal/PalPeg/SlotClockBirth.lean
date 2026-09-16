import PalPeg.SlotClockTime

set_option autoImplicit false
namespace PalPeg.SlotClockBirth
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.SlotClock

abbrev Flags := Fin 4 → Bool
local instance : DecidableEq Flags := fun a b => Fintype.decidablePiFintype a b
local instance : DecidableEq (Fin 4 → Ctrl) := fun a b => Fintype.decidablePiFintype a b
abbrev Control := (SlotClockStartup.Control × Fin 2) × Flags × Flags
instance instDecidableEqControl : DecidableEq Control := inferInstanceAs
  (DecidableEq (((Fin 33 × (Fin 4 → Ctrl)) × Fin 2) × Flags × Flags))

def birthCanon (n : ℕ) (i : Fin 4) : Bool :=
  decide (SlotSchedule.phaseAt n i = 0 ∧ SlotSchedule.resAt n i = 1)

def level (q : SlotClockStartup.Control) : Flags := fun i =>
  decide (q.1 = 32 ∧ (q.2 i).2 = 0)

/-- Sample phase 0 at the beginning of each actual arrival. Its rising edge
is therefore emitted one arrival after entering that phase, as required. -/
def machine : StructuredMachine Unit Control Symbol 8 2 where
  tapeCount_pos := by decide
  blank := .blank
  initial := (SlotClockStartup.machine.initial, fun _ => false, fun _ => false)
  accepting := fun _ => false
  micro := fun q a σ =>
    let r := SlotClockStartup.machine.micro q.1 a σ
    if q.1.2 = 0 then
      ((r.1, level q.1.1, fun i => level q.1.1 i && !(q.2.1 i)), r.2)
    else ((r.1, q.2.1, q.2.2), r.2)

def project (x : SConfig Control Symbol 8) :
    SConfig (SlotClockStartup.Control × Fin 2) Symbol 8 := ⟨x.state.1, x.tape⟩

theorem micro_project (x : SConfig Control Symbol 8) (a : Option Unit) :
    project (machine.sMicroStep x a) = SlotClockStartup.machine.sMicroStep (project x) a := by
  simp only [StructuredMachine.sMicroStep, machine, project]
  split <;> rfl

theorem steps_project (ops : List (Option Unit)) (x : SConfig Control Symbol 8) :
    project (ops.foldl machine.sMicroStep x) =
      ops.foldl SlotClockStartup.machine.sMicroStep (project x) := by
  induction ops generalizing x with
  | nil => rfl
  | cons a ops ih => simp only [List.foldl_cons, ih, micro_project]

theorem round_project (x : SConfig Control Symbol 8) (a : Unit) :
    project (machine.sRound x a) = SlotClockStartup.machine.sRound (project x) a :=
  steps_project _ _

theorem rounds_project (input : List Unit) (x : SConfig Control Symbol 8) :
    project (input.foldl machine.sRound x) =
      input.foldl SlotClockStartup.machine.sRound (project x) := by
  induction input generalizing x with
  | nil => rfl
  | cons a input ih => simp only [List.foldl_cons, ih, round_project]

theorem run_project (input : List Unit) :
    project (machine.srun input) = SlotClockStartup.machine.srun input :=
  rounds_project input machine.sInit

theorem round_form (q : SlotClockStartup.Control) (seen pulse : Flags)
    (T : Fin 8 → STape Symbol) (a : Unit) :
    machine.sRound ⟨((q, 0), seen, pulse), T⟩ a =
      let z := SlotClockStartup.machine.sRound ⟨(q, 0), T⟩ a
      ⟨(z.state, level q, fun i => level q i && !(seen i)), z.tape⟩ := by
  rfl

def atTime (n : ℕ) := machine.srun (List.replicate n ())

theorem at_succ (n : ℕ) : atTime (n + 1) = machine.sRound (atTime n) () := by
  simp only [atTime, StructuredMachine.srun, List.replicate_succ', List.foldl_append,
    List.foldl_cons, List.foldl_nil]

theorem phase_zero (n : ℕ) : (atTime n).state.1.2 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [at_succ]
    have hx : atTime n = ⟨(((atTime n).state.1.1, 0), (atTime n).state.2), (atTime n).tape⟩ := by
      rw [← ih]
    rw [hx, round_form]
    rfl

theorem sampled (n : ℕ) :
    (atTime (n + 1)).state.2.1 = level (atTime n).state.1.1 ∧
    (atTime (n + 1)).state.2.2 = fun i =>
      level (atTime n).state.1.1 i && !((atTime n).state.2.1 i) := by
  have hx : atTime n = ⟨(((atTime n).state.1.1, 0), (atTime n).state.2), (atTime n).tape⟩ := by
    rw [← phase_zero n]
  rw [at_succ, hx, round_form]
  exact ⟨rfl, rfl⟩

theorem delayed_edge (n : ℕ) (i : Fin 4) :
    (atTime (n + 2)).state.2.2 i =
      (level (atTime (n + 1)).state.1.1 i && !(level (atTime n).state.1.1 i)) := by
  rw [(sampled (n + 1)).2, (sampled n).1]

theorem entry_step (s : SlotSchedule.SlotSt) :
    ((SlotSchedule.slotStep s).p = 0 ∧ s.p ≠ 0) ↔
      ((SlotSchedule.slotStep s).p = 0 ∧ (SlotSchedule.slotStep s).r = 0) := by
  by_cases hr : s.r + 1 < s.q
  · simp only [SlotSchedule.slotStep, hr, ↓reduceIte]
    omega
  · by_cases hp : s.p + 1 < 30
    · simp only [SlotSchedule.slotStep, hr, hp, ↓reduceIte]
      omega
    · simp [SlotSchedule.slotStep, hr, hp, show s.p ≠ 0 by omega]

theorem restart_step (s : SlotSchedule.SlotSt) (hq : 2 ≤ s.q) :
    ((SlotSchedule.slotStep s).p = 0 ∧ (SlotSchedule.slotStep s).r = 1) ↔
      (s.p = 0 ∧ s.r = 0) := by
  by_cases hr : s.r + 1 < s.q
  · simp only [SlotSchedule.slotStep, hr, ↓reduceIte]
    omega
  · by_cases hp : s.p + 1 < 30
    · simp only [SlotSchedule.slotStep, hr, hp, ↓reduceIte]
      omega
    · simp only [SlotSchedule.slotStep, hr, hp, ↓reduceIte]
      omega

theorem quarter_two (n : ℕ) (hn : 32 ≤ n) (i : Fin 4) :
    2 ≤ SlotSchedule.quarter n i := by
  have hg := SlotSchedule.genExp_ge_three hn i
  exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ SlotSchedule.genExp n i - 2)

theorem canonical_edge (n : ℕ) (hn : 32 ≤ n) (i : Fin 4) :
    (SlotSchedule.phaseAt (n + 1) i = 0 ∧ SlotSchedule.phaseAt n i ≠ 0) ↔
      (SlotSchedule.phaseAt (n + 2) i = 0 ∧ SlotSchedule.resAt (n + 2) i = 1) := by
  have h1 := entry_step (SlotSchedule.canonSlot n i)
  have h2 := restart_step (SlotSchedule.canonSlot (n + 1) i) (quarter_two (n + 1) (by omega) i)
  rw [SlotSchedule.canonSlot_step hn i] at h1
  rw [SlotSchedule.canonSlot_step (by omega : 32 ≤ n + 1) i] at h2
  exact h1.trans h2.symm

theorem level_schedule (t : ℕ) (i : Fin 4) :
    level (atTime (32 + t)).state.1.1 i = decide (SlotSchedule.phaseAt (32 + t) i = 0) := by
  let input := List.replicate 32 () ++ List.replicate t ()
  have hx : (atTime (32 + t)).state.1 = (SlotClockStartup.machine.srun input).state := by
    have hh := congrArg SConfig.state (run_project (List.replicate (32 + t) ()))
    simpa only [project, atTime, List.replicate_add] using hh
  have hc : (SlotClockStartup.machine.srun input).state.1.1 = 32 := by
    have hh := (SlotClockStartup.live_rounds (List.replicate t ()) SlotClockStartup.ready rfl i).1
    change ((List.replicate 32 () ++ List.replicate t ()).foldl
      SlotClockStartup.machine.sRound SlotClockStartup.machine.sInit).state.1.1 = _
    rw [List.foldl_append]
    change ((List.replicate t ()).foldl SlotClockStartup.machine.sRound
      (SlotClockStartup.machine.srun (List.replicate 32 ()))).state.1.1 = _
    rw [SlotClockStartup.startup]
    exact hh
  have hp := SlotClockTime.startup_phase_matches i t
  change ((SlotClockStartup.machine.srun input).state.1.2 i).2.val = _ at hp
  simp [level, hx, hc, Fin.ext_iff, hp]

theorem pulse_later (t : ℕ) (i : Fin 4) :
    (atTime (34 + t)).state.2.2 i = birthCanon (34 + t) i := by
  rw [show 34 + t = (32 + t) + 2 by omega, delayed_edge]
  have h1 := level_schedule (t + 1) i
  rw [show 32 + (t + 1) = (32 + t) + 1 by omega] at h1
  rw [h1, level_schedule, birthCanon]
  apply Bool.eq_iff_iff.mpr
  simpa using canonical_edge (32 + t) (by omega) i

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem pulse_initial (i : Fin 4) :
    (atTime 32).state.2.2 i = birthCanon 32 i ∧
    (atTime 33).state.2.2 i = birthCanon 33 i := by
  fin_cases i <;> decide

theorem pulse_matches (n : ℕ) (hn : 32 ≤ n) (i : Fin 4) :
    (atTime n).state.2.2 i = birthCanon n i := by
  by_cases h32 : n = 32
  · subst n; exact (pulse_initial i).1
  by_cases h33 : n = 33
  · subst n; exact (pulse_initial i).2
  have hh := pulse_later (n - 34) i
  simpa only [Nat.add_sub_of_le (by omega : 34 ≤ n)] using hh

theorem birthCanon_iff_birth (n : ℕ) (hn : 32 ≤ n) (i : Fin 4) :
    birthCanon n i = true ↔ n = SlotSchedule.birth n i + 1 := by
  simp only [birthCanon, decide_eq_true_eq]
  constructor
  · rintro ⟨hp, hr⟩
    have he := SlotSchedule.n_eq hn i
    rw [hp, hr] at he
    rw [SlotSchedule.birth_eq hn i]
    omega
  · intro h
    have he : SlotSchedule.elapsed n i = 1 := by unfold SlotSchedule.elapsed; omega
    have hq := quarter_two n hn i
    simp only [SlotSchedule.phaseAt, SlotSchedule.resAt, he]
    exact ⟨Nat.div_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)⟩

def fires (n : ℕ) : Bool := decide (∃ i, (atTime n).state.2.2 i = true)

/-- The actual finite clock emits one of these birth pulses precisely on
the arrival after a power-of-two prefix. Startup supplies the first at 33. -/
theorem fires_iff_power (n : ℕ) (hn : 32 ≤ n) :
    fires n = true ↔ ∃ g : ℕ, n = 2 ^ g + 1 := by
  simp only [fires, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi⟩
    rw [pulse_matches n hn i, birthCanon_iff_birth n hn i] at hi
    exact ⟨SlotSchedule.genExp n i - 1, hi⟩
  · rintro ⟨g, hg⟩
    let i : Fin 4 := ⟨(g + 1) % 4, Nat.mod_lt _ (by decide)⟩
    have hpos : 0 < 2 ^ g := pow_pos (by decide) g
    have hhigh : 2 ^ ((g + 1) + 3) = 2 ^ g * 16 := by
      rw [show (g + 1) + 3 = g + 4 by omega, pow_add]
      norm_num
    have he := SlotSchedule.genExp_unique hn i (g := g + 1) rfl
      (by simpa only [Nat.add_sub_cancel] using (show 2 ^ g ≤ n by omega))
      (by rw [hhigh]; omega)
    refine ⟨i, ?_⟩
    rw [pulse_matches n hn i, birthCanon_iff_birth n hn i]
    simpa only [SlotSchedule.birth, ← he, Nat.add_sub_cancel] using hg

/-- This bit is available before the next clock round, so a consumer may
route that same arrival into the newly started pass without buffering it. -/
def startNow (q : Control) : Bool :=
  decide (∃ i, level q.1.1 i = true ∧ q.2.1 i = false)

theorem startNow_at (n : ℕ) : startNow (atTime n).state = fires (n + 1) := by
  simp [startNow, fires, (sampled n).2]

theorem startNow_power (n : ℕ) (hn : 32 ≤ n) :
    startNow (atTime n).state = true ↔ ∃ g : ℕ, n = 2 ^ g := by
  rw [startNow_at, fires_iff_power (n + 1) (by omega)]
  constructor
  · rintro ⟨g, h⟩; exact ⟨g, by omega⟩
  · rintro ⟨g, h⟩; exact ⟨g, by omega⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem startNow_early : ∀ n : Fin 32, startNow (atTime n.val).state = false := by
  decide

/-- info: 'PalPeg.SlotClockBirth.startNow_power' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms startNow_power

/-- info: 'PalPeg.SlotClockBirth.fires_iff_power' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fires_iff_power

/-- info: 'PalPeg.SlotClockBirth.pulse_matches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pulse_matches

/-- info: 'PalPeg.SlotClockBirth.run_project' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_project
/-- info: 'PalPeg.SlotClockBirth.delayed_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms delayed_edge

end PalPeg.SlotClockBirth
