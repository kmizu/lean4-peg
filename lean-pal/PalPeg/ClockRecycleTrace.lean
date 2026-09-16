import PalPeg.ClockRecycleMachine

set_option autoImplicit false
namespace PalPeg.ClockRecycleTrace
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ClockRecycleMachine
variable {k : ℕ}

def run (blank : Fin k) (C n : ℕ)
    (x : SConfig (Core × Fin (C + 2)) (SlotClock.Symbol × Fin k) 164) :=
  (List.replicate n ()).foldl (machine blank C).sRound x

/-- Read the phase from each real configuration before its next round. -/
def phases (blank : Fin k) (C : ℕ) (i : Fin 4) : ℕ →
    SConfig (Core × Fin (C + 2)) (SlotClock.Symbol × Fin k) 164 → List (Fin 30)
  | 0, _ => []
  | n + 1, x => observedPhase x.state.1.1 i :: phases blank C i n ((machine blank C).sRound x ())

theorem phases_length (blank : Fin k) (C : ℕ) (i : Fin 4) (n : ℕ)
    (x : SConfig (Core × Fin (C + 2)) (SlotClock.Symbol × Fin k) 164) :
    (phases blank C i n x).length = n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp only [phases, List.length_cons, ih]

theorem phases_add (blank : Fin k) (C : ℕ) (i : Fin 4) (n m : ℕ)
    (x : SConfig (Core × Fin (C + 2)) (SlotClock.Symbol × Fin k) 164) :
    phases blank C i (n + m) x = phases blank C i n x ++ phases blank C i m (run blank C n x) := by
  induction n generalizing x with
  | zero => simp [phases, run]
  | succ n ih =>
    rw [Nat.succ_add]
    simp only [phases, ih, List.cons_append]
    rfl

theorem phases_get (blank : Fin k) (C : ℕ) (i : Fin 4) (n r : ℕ) (hr : r < n)
    (x : SConfig (Core × Fin (C + 2)) (SlotClock.Symbol × Fin k) 164) :
    (phases blank C i n x)[r]? = some (observedPhase (run blank C r x).state.1.1 i) := by
  induction r generalizing n x with
  | zero => cases n <;> first | omega | rfl
  | succ r ih =>
    cases n with
    | zero => omega
    | succ n => exact ih n (by omega) ((machine blank C).sRound x ())

theorem observed_from_blank (blank : Fin k) (C t : ℕ) (i : Fin 4) :
    (observedPhase ((machine blank C).srun (List.replicate (32 + t) ())).state.1.1 i).val =
      SlotSchedule.phaseAt (32 + t) i := by
  let input := List.replicate 32 () ++ List.replicate t ()
  have h1 := clock_from_blank blank C input
  have h2 := SlotClockEvents.run_project input
  have hs : ((machine blank C).srun input).state.1.1.1 = (SlotClockStartup.machine.srun input).state :=
    congrArg SConfig.state ((congrArg SlotClockEvents.project h1).trans h2)
  have hc : (SlotClockStartup.machine.srun input).state.1.1 = 32 := by
    change ((List.replicate 32 () ++ List.replicate t ()).foldl
      SlotClockStartup.machine.sRound SlotClockStartup.machine.sInit).state.1.1 = _
    rw [List.foldl_append]
    change ((List.replicate t ()).foldl SlotClockStartup.machine.sRound
      (SlotClockStartup.machine.srun (List.replicate 32 ()))).state.1.1 = _
    rw [SlotClockStartup.startup]
    exact (SlotClockStartup.live_rounds (List.replicate t ()) SlotClockStartup.ready rfl i).1
  have hp := SlotClockTime.startup_phase_matches i t
  change ((SlotClockStartup.machine.srun input).state.1.2 i).2.val = _ at hp
  rw [List.replicate_add]
  change (observedPhase ((machine blank C).srun input).state.1.1 i).val = _
  simp only [observedPhase, hs, hc, ↓reduceIte]
  exact hp

theorem phases_canonical (blank : Fin k) (C t n r : ℕ) (hr : r < n) (i : Fin 4) :
    ((phases blank C i n ((machine blank C).srun (List.replicate (32 + t) ())))[r]?).map Fin.val =
      some (SlotSchedule.phaseAt (32 + (t + r)) i) := by
  rw [phases_get blank C i n r hr]
  have he : run blank C r ((machine blank C).srun (List.replicate (32 + t) ())) =
      (machine blank C).srun (List.replicate (32 + (t + r)) ()) := by
    simp only [run, StructuredMachine.srun, List.replicate_add, List.foldl_append]
  rw [he]
  exact congrArg some (observed_from_blank blank C (t + r) i)

theorem work_trace (blank : Fin k) (C n : ℕ)
    (x : SConfig (Core × Fin (C + 2)) (SlotClock.Symbol × Fin k) 164)
    (hx : x.state.2 = 0) (i : Fin 4) (j : Fin 39) :
    work (run blank C n x) i j =
      (phases blank C i n x).foldl (fun T p => ((worker blank p)^[C]) T) (work x i j) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    change work (run blank C n ((machine blank C).sRound x ())) i j = _
    rw [ih _ (round_phase blank C x hx), work_round blank C x hx]
    rfl

theorem worker_block (blank : Fin k) (p : Fin 30) (C : ℕ) (T : STape (Fin k))
    (hp : ProgramRecycleWindow.enabled p = true) :
    ((worker blank p)^[C]) T =
      (List.replicate C (ProgramRecycleWindow.direction p)).foldl
        (fun T d => T.applyAction blank (blank, d)) T := by
  induction C generalizing T with
  | zero => rfl
  | succ C ih =>
    simp only [Function.iterate_succ_apply, worker, hp, ↓reduceIte,
      List.replicate_succ, List.foldl_cons]
    exact ih _

theorem work_blocks (blank : Fin k) (C : ℕ) (ps : List (Fin 30)) (T : STape (Fin k))
    (hp : ∀ p ∈ ps, ProgramRecycleWindow.enabled p = true) :
    ps.foldl (fun T p => ((worker blank p)^[C]) T) T =
      (ps.flatMap (fun p => List.replicate C (ProgramRecycleWindow.direction p))).foldl
        (fun T d => T.applyAction blank (blank, d)) T := by
  induction ps generalizing T with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.foldl_cons, List.flatMap_cons, List.foldl_append]
    rw [worker_block blank p C T (hp p (by simp))]
    exact ih _ (fun p h => hp p (by simp [h]))

theorem phases_enabled (q : ℕ) :
    ∀ p ∈ ProgramRecycleWindow.phaseWords q, ProgramRecycleWindow.enabled p = true := by
  intro p hp
  obtain ⟨s, hs, hm⟩ := List.mem_flatMap.mp hp
  have he : p = s := List.eq_of_mem_replicate hm
  subst p
  simp at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem repeated_get {A : Type} (ps : List A) (q : ℕ) (hq : 0 < q)
    (r : ℕ) (hr : r < q * ps.length) :
    (ps.flatMap (fun p => List.replicate q p))[r]? = ps[r / q]? := by
  induction ps generalizing r with
  | nil => simp at hr
  | cons p ps ih =>
    rw [List.flatMap_cons]
    by_cases hlt : r < q
    · rw [List.getElem?_append_left (by simpa using hlt)]
      simp [hlt, Nat.div_eq_of_lt hlt]
    · have hge : q ≤ r := by omega
      rw [List.getElem?_append_right (by simpa using hge)]
      simp only [List.length_replicate]
      have hsub : r - q < q * ps.length := by
        simp only [List.length_cons, Nat.mul_add, Nat.mul_one] at hr
        omega
      rw [ih (r - q) hsub]
      have hd : r / q = (r - q) / q + 1 := by
        conv_lhs => rw [show r = (r - q) + q by omega]
        exact Nat.add_div_right _ hq
      rw [hd]
      rfl

theorem phaseWords_get (q r : ℕ) (hq : 0 < q) (hr : r < 6 * q) :
    ((ProgramRecycleWindow.phaseWords q)[r]?).map Fin.val = some (14 + r / q) := by
  have hdiv : r / q < 6 := (Nat.div_lt_iff_lt_mul hq).mpr hr
  rw [ProgramRecycleWindow.phaseWords, repeated_get _ q hq r (by simp; omega)]
  generalize he : r / q = d at *
  interval_cases d <;> rfl

theorem phaseWords_length (q : ℕ) : (ProgramRecycleWindow.phaseWords q).length = 6 * q := by
  simp [ProgramRecycleWindow.phaseWords]
  omega

theorem phases_six (blank : Fin k) (C g : ℕ) (hg : 3 ≤ g) (i : Fin 4) (hi : g % 4 = i.val) :
    phases blank C i (6 * 2 ^ (g - 2))
      ((machine blank C).srun (List.replicate (16 * 2 ^ (g - 2)) ())) =
        ProgramRecycleWindow.phaseWords (2 ^ (g - 2)) := by
  let q := 2 ^ (g - 2)
  have hq : 0 < q := pow_pos (by decide) _
  have hq2 : 2 ≤ q := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ g - 2)
  have hstart : 32 + (16 * q - 32) = 16 * q := by omega
  have hinj : Function.Injective (Option.map (Fin.val : Fin 30 → ℕ)) := by
    intro a b h
    cases a <;> cases b <;> simp_all [Fin.ext_iff]
  apply List.ext_getElem?
  intro r
  by_cases hr : r < 6 * q
  · apply hinj
    have h1 := phases_canonical blank C (16 * q - 32) (6 * q) r hr i
    rw [hstart] at h1
    have ht : 32 + (16 * q - 32 + r) = 2 * q + (14 * q + r) := by omega
    have hc := SlotClockTime.canonical_window g hg i hi (14 * q + r) (by change _ < 30 * q; omega)
      (by change 32 ≤ 2 * q + (14 * q + r); omega)
    change SlotSchedule.quarter (2 * q + (14 * q + r)) i = q ∧
      SlotSchedule.phaseAt (2 * q + (14 * q + r)) i = (14 * q + r) / q ∧ _ at hc
    rw [ht, hc.2.1, Nat.mul_comm 14 q, Nat.mul_add_div hq] at h1
    exact h1.trans (phaseWords_get q r hq hr).symm
  · rw [List.getElem?_eq_none (by rw [phases_length]; change 6 * q ≤ r; omega),
      List.getElem?_eq_none (by rw [phaseWords_length]; change 6 * q ≤ r; omega)]

/-- Exact real execution, conditional only on the clock phase trace and
the workspace bound. No cleanup action list is supplied to the machine. -/
theorem reset_of_trace (blank : Fin k) (C q m : ℕ)
    (x : SConfig (Core × Fin (C + 2)) (SlotClock.Symbol × Fin k) 164)
    (hx : x.state.2 = 0) (i : Fin 4)
    (hp : phases blank C i (6 * q) x = ProgramRecycleWindow.phaseWords q)
    (h : ∀ j, MiddleClear.Near blank (ProgramRecycle.view (work x i j)) m)
    (hm : m < C * q) :
    ∀ j, STape.BlankEq blank (work (run blank C (6 * q) x) i j) (STape.blankTape blank) := by
  intro j
  rw [work_trace blank C _ x hx, hp, work_blocks blank C _ _ (phases_enabled q),
    ProgramRecycleWindow.phase_commands]
  exact ProgramRecycleWindow.clear_tape blank (work x i j) m (C * q) (h j) hm

theorem run_phase (blank : Fin k) (C n : ℕ)
    (x : SConfig (Core × Fin (C + 2)) (SlotClock.Symbol × Fin k) 164) (hx : x.state.2 = 0) :
    (run blank C n x).state.2 = 0 := by
  induction n generalizing x with
  | zero => exact hx
  | succ n ih => exact ih _ (round_phase blank C x hx)

/-- Actual cleanup from phase 14 to phase 20 in the all-blank-started
combined machine. No phase trace or action list is assumed. -/
theorem reset_six (blank : Fin k) (C g m : ℕ) (hg : 3 ≤ g)
    (i : Fin 4) (hi : g % 4 = i.val)
    (h : ∀ j, MiddleClear.Near blank (ProgramRecycle.view
      (work ((machine blank C).srun (List.replicate (16 * 2 ^ (g - 2)) ())) i j)) m)
    (hm : m < C * 2 ^ (g - 2)) :
    ∀ j, STape.BlankEq blank
      (work ((machine blank C).srun (List.replicate (22 * 2 ^ (g - 2)) ())) i j) (STape.blankTape blank) := by
  let q := 2 ^ (g - 2)
  have hx : ((machine blank C).srun (List.replicate (16 * q) ())).state.2 = 0 :=
    run_phase blank C (16 * q) (machine blank C).sInit rfl
  have hh := reset_of_trace blank C q m _ hx i (phases_six blank C g hg i hi) h hm
  have he : run blank C (6 * q) ((machine blank C).srun (List.replicate (16 * q) ())) =
      (machine blank C).srun (List.replicate (22 * q) ()) := by
    simp only [run, StructuredMachine.srun, ← List.foldl_append, ← List.replicate_add]
    congr 2
    omega
  rw [he] at hh
  exact hh

/-- info: 'PalPeg.ClockRecycleTrace.reset_six' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reset_six

theorem phases_eq_of_clock (blank : Fin k) (C n : ℕ) (i : Fin 4)
    (x y : SConfig (Core × Fin (C + 2)) (SlotClock.Symbol × Fin k) 164)
    (hx : x.state.2 = 0) (hy : y.state.2 = 0) (hc : clock x = clock y) :
    phases blank C i n x = phases blank C i n y := by
  induction n generalizing x y with
  | zero => rfl
  | succ n ih =>
    have hs : x.state.1.1 = y.state.1.1 := congrArg SConfig.state hc
    simp only [phases, hs]
    congr 1
    apply ih _ _ (round_phase blank C x hx) (round_phase blank C y hy)
    rw [clock_round blank C x hx, clock_round blank C y hy, hc]

/-- The six-phase result applies to arbitrary used workspaces. Only the clock
projection must be at the actual phase-14 boundary; work contents are unrestricted
apart from the movement bound needed for the clearing deadline. -/
theorem reset_window (blank : Fin k) (C g m : ℕ) (hg : 3 ≤ g) (i : Fin 4) (hi : g % 4 = i.val)
    (x : SConfig (Core × Fin (C + 2)) (SlotClock.Symbol × Fin k) 164) (hx : x.state.2 = 0)
    (hc : clock x = clock ((machine blank C).srun (List.replicate (16 * 2 ^ (g - 2)) ())))
    (h : ∀ j, MiddleClear.Near blank (ProgramRecycle.view (work x i j)) m)
    (hm : m < C * 2 ^ (g - 2)) :
    ∀ j, STape.BlankEq blank (work (run blank C (6 * 2 ^ (g - 2)) x) i j) (STape.blankTape blank) := by
  have hy : ((machine blank C).srun (List.replicate (16 * 2 ^ (g - 2)) ())).state.2 = 0 :=
    run_phase blank C _ (machine blank C).sInit rfl
  have hp := phases_eq_of_clock blank C (6 * 2 ^ (g - 2)) i x _ hx hy hc
  rw [phases_six blank C g hg i hi] at hp
  exact reset_of_trace blank C _ m x hx i hp h hm

/-- info: 'PalPeg.ClockRecycleTrace.reset_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reset_window

/-- info: 'PalPeg.ClockRecycleTrace.reset_of_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reset_of_trace
/-- info: 'PalPeg.ClockRecycleTrace.phases_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms phases_canonical

end PalPeg.ClockRecycleTrace
