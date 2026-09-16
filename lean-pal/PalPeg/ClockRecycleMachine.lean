import PalPeg.SlotClockEvents
import PalPeg.ProgramRecycleWindow

set_option autoImplicit false
namespace PalPeg.ClockRecycleMachine
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang

variable {k : ℕ}

def mapTape {A B : Type} (f : A → B) (T : STape A) : STape B :=
  ⟨T.left.map f, f T.focus, T.right.map f⟩

theorem map_action {A B : Type} (f : A → B) (blank : A) (T : STape A) (a : A × Move) :
    mapTape f (T.applyAction blank a) = (mapTape f T).applyAction (f blank) (f a.1, a.2) := by
  rcases T with ⟨l, x, r⟩
  rcases a with ⟨w, d⟩
  cases d <;> cases l <;> cases r <;> rfl

abbrev Saved := Fin 4 → Fin 30
local instance : DecidableEq Saved := fun a b => Fintype.decidablePiFintype a b
abbrev Core := SlotClockEvents.Control × Saved
instance instDecidableEqCore : DecidableEq Core := inferInstanceAs (DecidableEq (SlotClockEvents.Control × Saved))

def clockAddr (j : Fin 8) : Fin 164 := finSumFinEquiv (Sum.inl j : Fin 8 ⊕ Fin 156)
def workAddr (i : Fin 4) (j : Fin 39) : Fin 164 :=
  finSumFinEquiv (Sum.inr (finProdFinEquiv (i, j)) : Fin 8 ⊕ Fin 156)

def observedPhase (q : SlotClockEvents.Control) (i : Fin 4) : Fin 30 :=
  if q.1.1.1 = 32 then (q.1.1.2 i).2 else 0

/-- The first two microsteps run the concrete clock/event machine. The next
C microsteps sweep all 156 work tapes, using the phase saved before the
clock advanced. C is a fixed machine parameter, not a runtime register. -/
def body (blank : Fin k) (C : ℕ) :
    PhaseBody Unit Core (SlotClock.Symbol × Fin k) 164 (C + 2) := fun q a ph σ =>
  if ph.val < 2 then
    let r := SlotClockEvents.machine.micro q.1 a (fun j => (σ (clockAddr j)).1)
    ((r.1, if ph.val = 0 then observedPhase q.1 else q.2), fun j =>
      match (finSumFinEquiv.symm j : Fin 8 ⊕ Fin 156) with
      | .inl c => ((r.2 c |>.1, (σ j).2), (r.2 c).2)
      | .inr _ => (σ j, .stay))
  else
    (q, fun j => match (finSumFinEquiv.symm j : Fin 8 ⊕ Fin 156) with
      | .inl _ => (σ j, .stay)
      | .inr w =>
        let ij : Fin 4 × Fin 39 := finProdFinEquiv.symm w
        if ProgramRecycleWindow.enabled (q.2 ij.1) then
          (((σ j).1, blank), ProgramRecycleWindow.direction (q.2 ij.1))
        else (σ j, .stay))

def machine (blank : Fin k) (C : ℕ) :
    StructuredMachine Unit (Core × Fin (C + 2)) (SlotClock.Symbol × Fin k) 164 (C + 2) :=
  ofPhases (by decide) (by omega) (.blank, blank)
    (SlotClockEvents.machine.initial, fun _ => 0) (fun _ => false) (body blank C)

def clock {C : ℕ} (x : SConfig (Core × Fin (C + 2)) (SlotClock.Symbol × Fin k) 164) :
    SConfig SlotClockEvents.Control SlotClock.Symbol 8 :=
  ⟨x.state.1.1, fun j => mapTape Prod.fst (x.tape (clockAddr j))⟩

def work {C : ℕ} (x : SConfig (Core × Fin (C + 2)) (SlotClock.Symbol × Fin k) 164)
    (i : Fin 4) (j : Fin 39) : STape (Fin k) := mapTape Prod.snd (x.tape (workAddr i j))

theorem clock_tick (blank : Fin k) (C : ℕ)
    (x : SConfig (Core × Fin (C + 2)) (SlotClock.Symbol × Fin k) 164)
    (h : x.state.2.val < 2) (a : Option Unit) :
    clock ((machine blank C).sMicroStep x a) = SlotClockEvents.machine.sMicroStep (clock x) a := by
  simp only [clock, StructuredMachine.sMicroStep, machine, ofPhases, body, h, ↓reduceIte,
    clockAddr, Equiv.symm_apply_apply, map_action]
  rfl

theorem clock_idle (blank : Fin k) (C : ℕ)
    (x : SConfig (Core × Fin (C + 2)) (SlotClock.Symbol × Fin k) 164)
    (h : ¬ x.state.2.val < 2) (a : Option Unit) :
    clock ((machine blank C).sMicroStep x a) = clock x := by
  simp only [clock, StructuredMachine.sMicroStep, machine, ofPhases, body, h, ↓reduceIte,
    clockAddr, Equiv.symm_apply_apply, map_action]
  rfl

theorem work_tick (blank : Fin k) (C : ℕ)
    (x : SConfig (Core × Fin (C + 2)) (SlotClock.Symbol × Fin k) 164)
    (h : ¬ x.state.2.val < 2) (a : Option Unit) (i : Fin 4) (j : Fin 39) :
    work ((machine blank C).sMicroStep x a) i j =
      if ProgramRecycleWindow.enabled (x.state.1.2 i) then
        (work x i j).applyAction blank (blank, ProgramRecycleWindow.direction (x.state.1.2 i))
      else work x i j := by
  simp only [work, StructuredMachine.sMicroStep, machine, ofPhases, body, h, ↓reduceIte,
    workAddr, Equiv.symm_apply_apply]
  split <;> rw [map_action]
  · rfl

theorem work_idle (blank : Fin k) (C : ℕ)
    (x : SConfig (Core × Fin (C + 2)) (SlotClock.Symbol × Fin k) 164)
    (h : x.state.2.val < 2) (a : Option Unit) (i : Fin 4) (j : Fin 39) :
    work ((machine blank C).sMicroStep x a) i j = work x i j := by
  simp only [work, StructuredMachine.sMicroStep, machine, ofPhases, body, h, ↓reduceIte,
    workAddr, Equiv.symm_apply_apply, map_action]
  rfl

theorem phase_step (blank : Fin k) (C : ℕ)
    (x : SConfig (Core × Fin (C + 2)) (SlotClock.Symbol × Fin k) 164) (a : Option Unit) :
    ((machine blank C).sMicroStep x a).state.2 = nextPhase x.state.2 := rfl

theorem clock_tail (blank : Fin k) (C : ℕ) (ops : List (Option Unit))
    (x : SConfig (Core × Fin (C + 2)) (SlotClock.Symbol × Fin k) 164)
    (hpos : 2 ≤ x.state.2.val) (hlen : x.state.2.val + ops.length ≤ C + 2) :
    clock (ops.foldl (machine blank C).sMicroStep x) = clock x := by
  induction ops generalizing x with
  | nil => rfl
  | cons a ops ih =>
    have hh := clock_idle blank C x (by omega) a
    cases ops with
    | nil => exact hh
    | cons b ops =>
      have hnext : x.state.2.val + 1 < C + 2 := by simp only [List.length_cons] at hlen; omega
      have hv : ((machine blank C).sMicroStep x a).state.2.val = x.state.2.val + 1 := by
        rw [phase_step]
        simp only [nextPhase, dif_pos hnext]
      exact (ih ((machine blank C).sMicroStep x a) (by rw [hv]; omega)
        (by rw [hv]; simp only [List.length_cons] at hlen ⊢; omega)).trans hh

theorem clock_round (blank : Fin k) (C : ℕ)
    (x : SConfig (Core × Fin (C + 2)) (SlotClock.Symbol × Fin k) 164)
    (hx : x.state.2 = 0) :
    clock ((machine blank C).sRound x ()) = SlotClockEvents.machine.sRound (clock x) () := by
  let x1 := (machine blank C).sMicroStep x (some ())
  let x2 := (machine blank C).sMicroStep x1 none
  have h1 : x1.state.2.val = 1 := by
    change ((machine blank C).sMicroStep x (some ())).state.2.val = 1
    rw [phase_step, hx]
    simp [nextPhase]
  have hc1 := clock_tick blank C x (by rw [hx]; simp) (some ())
  have hc2 := clock_tick blank C x1 (by omega) none
  have hclock : clock x2 = SlotClockEvents.machine.sRound (clock x) () := by
    change clock ((machine blank C).sMicroStep x1 none) = _
    rw [hc2]
    change SlotClockEvents.machine.sMicroStep (clock ((machine blank C).sMicroStep x (some ()))) none = _
    rw [hc1]
    rfl
  have hshape : (machine blank C).sRound x () =
      (List.replicate C none).foldl (machine blank C).sMicroStep x2 := rfl
  rw [hshape]
  cases C with
  | zero => exact hclock
  | succ C =>
    have h2 : x2.state.2.val = 2 := by
      change ((machine blank (C + 1)).sMicroStep x1 none).state.2.val = 2
      rw [phase_step]
      simp [nextPhase, h1]
    exact (clock_tail blank (C + 1) _ x2 (by omega)
      (by rw [h2, List.length_replicate]; omega)).trans hclock

def worker (blank : Fin k) (p : Fin 30) (T : STape (Fin k)) : STape (Fin k) :=
  if ProgramRecycleWindow.enabled p then T.applyAction blank (blank, ProgramRecycleWindow.direction p) else T

theorem core_idle (blank : Fin k) (C : ℕ)
    (x : SConfig (Core × Fin (C + 2)) (SlotClock.Symbol × Fin k) 164)
    (h : ¬ x.state.2.val < 2) (a : Option Unit) :
    ((machine blank C).sMicroStep x a).state.1 = x.state.1 := by
  simp only [StructuredMachine.sMicroStep, machine, ofPhases, body, h, ↓reduceIte]

theorem work_tail (blank : Fin k) (C n : ℕ)
    (x : SConfig (Core × Fin (C + 2)) (SlotClock.Symbol × Fin k) 164)
    (hpos : 2 ≤ x.state.2.val) (hlen : x.state.2.val + n ≤ C + 2) (i : Fin 4) (j : Fin 39) :
    work ((List.replicate n none).foldl (machine blank C).sMicroStep x) i j =
      ((worker blank (x.state.1.2 i))^[n]) (work x i j) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    have ht : work ((machine blank C).sMicroStep x none) i j =
        worker blank (x.state.1.2 i) (work x i j) := work_tick blank C x (by omega) none i j
    simp only [List.replicate_succ, List.foldl_cons]
    cases n with
    | zero => exact ht
    | succ n =>
      have hnext : x.state.2.val + 1 < C + 2 := by omega
      have hv : ((machine blank C).sMicroStep x none).state.2.val = x.state.2.val + 1 := by
        rw [phase_step]
        simp only [nextPhase, dif_pos hnext]
      have hh := ih ((machine blank C).sMicroStep x none) (by rw [hv]; omega) (by rw [hv]; omega)
      rw [core_idle blank C x (by omega) none, ht] at hh
      exact hh

theorem work_round (blank : Fin k) (C : ℕ)
    (x : SConfig (Core × Fin (C + 2)) (SlotClock.Symbol × Fin k) 164)
    (hx : x.state.2 = 0) (i : Fin 4) (j : Fin 39) :
    work ((machine blank C).sRound x ()) i j =
      ((worker blank (observedPhase x.state.1.1 i))^[C]) (work x i j) := by
  let x1 := (machine blank C).sMicroStep x (some ())
  let x2 := (machine blank C).sMicroStep x1 none
  have h1 : x1.state.2.val = 1 := by
    change ((machine blank C).sMicroStep x (some ())).state.2.val = 1
    rw [phase_step, hx]
    simp [nextPhase]
  have hs1 : x1.state.1.2 = observedPhase x.state.1.1 := by
    simp [x1, StructuredMachine.sMicroStep, machine, ofPhases, body, hx]
  have hs2 : x2.state.1.2 = x1.state.1.2 := by
    have h10 : x1.state.2 ≠ 0 := by intro he; rw [he] at h1; simp at h1
    simp [x2, StructuredMachine.sMicroStep, machine, ofPhases, body, h1, h10]
  have hw1 : work x1 i j = work x i j := work_idle blank C x (by rw [hx]; simp) (some ()) i j
  have hw2 : work x2 i j = work x1 i j := work_idle blank C x1 (by omega) none i j
  have hshape : (machine blank C).sRound x () =
      (List.replicate C none).foldl (machine blank C).sMicroStep x2 := rfl
  rw [hshape]
  cases C with
  | zero => exact hw2.trans hw1
  | succ C =>
    have h2 : x2.state.2.val = 2 := by
      change ((machine blank (C + 1)).sMicroStep x1 none).state.2.val = 2
      rw [phase_step]
      simp [nextPhase, h1]
    have hh := work_tail blank (C + 1) (C + 1) x2 (by omega) (by omega) i j
    rw [hs2, hs1, hw2, hw1] at hh
    exact hh

/-- info: 'PalPeg.ClockRecycleMachine.work_round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms work_round

theorem round_phase (blank : Fin k) (C : ℕ)
    (x : SConfig (Core × Fin (C + 2)) (SlotClock.Symbol × Fin k) 164)
    (hx : x.state.2 = 0) : ((machine blank C).sRound x ()).state.2 = 0 := by
  have he : x = ⟨(x.state.1, 0), x.tape⟩ := by rw [← hx]
  rw [he]
  have hh := ofPhases_round (by decide : 0 < 164) (by omega : 0 < C + 2)
    (SlotClock.Symbol.blank, blank) (SlotClockEvents.machine.initial, fun _ => (0 : Fin 30))
    (fun _ => false) (body blank C) x.state.1 x.tape ()
  simpa only [machine, Fin.zero_eta] using congrArg (fun y => y.state.2) hh

theorem clock_rounds (blank : Fin k) (C : ℕ) (input : List Unit)
    (x : SConfig (Core × Fin (C + 2)) (SlotClock.Symbol × Fin k) 164)
    (hx : x.state.2 = 0) :
    clock (input.foldl (machine blank C).sRound x) =
      input.foldl SlotClockEvents.machine.sRound (clock x) := by
  induction input generalizing x with
  | nil => rfl
  | cons a input ih =>
    cases a
    simp only [List.foldl_cons]
    rw [ih _ (round_phase blank C x hx), clock_round blank C x hx]

theorem clock_from_blank (blank : Fin k) (C : ℕ) (input : List Unit) :
    clock ((machine blank C).srun input) = SlotClockEvents.machine.srun input :=
  clock_rounds blank C input (machine blank C).sInit rfl

theorem pulse_matches (blank : Fin k) (C n : ℕ) (hn : 32 ≤ n) (i : Fin 4) :
    ((machine blank C).srun (List.replicate n ())).state.1.1.2.2 i = SlotSchedule.rsCanon n i := by
  have hh := congrArg (fun x => x.state.2.2 i) (clock_from_blank blank C (List.replicate n ()))
  exact hh.trans (SlotClockEvents.pulse_matches n hn i)

/-- info: 'PalPeg.ClockRecycleMachine.clock_from_blank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms clock_from_blank
/-- info: 'PalPeg.ClockRecycleMachine.pulse_matches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pulse_matches

/-- info: 'PalPeg.ClockRecycleMachine.clock_round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms clock_round

/-- info: 'PalPeg.ClockRecycleMachine.clock_tick' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms clock_tick
/-- info: 'PalPeg.ClockRecycleMachine.work_tick' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms work_tick

end PalPeg.ClockRecycleMachine
