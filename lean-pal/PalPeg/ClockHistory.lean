import PalPeg.HistoryLoop
import PalPeg.SlotClockBirth
import PalPeg.ClockRecycleMachine

set_option autoImplicit false
namespace PalPeg.ClockHistory
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang
open PalPeg.ClockRecycleMachine (mapTape map_action)
variable {k : ℕ} {Terminal : Type}

local instance : DecidableEq (HistoryLoop.Control 32) := inferInstance
abbrev Core := SlotClockBirth.Control × HistoryLoop.Control 32
instance instDecidableEqCore : DecidableEq Core := inferInstanceAs
  (DecidableEq (SlotClockBirth.Control × HistoryLoop.Control 32))

def clockAddr (j : Fin 8) : Fin 12 := finSumFinEquiv (Sum.inl j : Fin 8 ⊕ Fin 4)
def historyAddr (j : Fin 4) : Fin 12 := finSumFinEquiv (Sum.inr j : Fin 8 ⊕ Fin 4)

/-- Clock and history share the same real arrival. The clock advances in
the first two ticks, history in all 33 ticks. The birth bit is computed
before either advances, so the triggering symbol enters the new log. -/
def body (blank : Fin k) (enc : Terminal → Fin k) :
    PhaseBody Terminal Core (SlotClock.Symbol × Fin k) 12 33 := fun q a ph σ =>
  let c := if ph.val < 2 then
      SlotClockBirth.machine.micro q.1 (a.map (fun _ => ())) (fun j => (σ (clockAddr j)).1)
    else (q.1, fun j => ((σ (clockAddr j)).1, Move.stay))
  let h := (HistoryLoop.machine blank enc 32).micro q.2
    (a.map (fun a => (a, SlotClockBirth.startNow q.1))) (fun j => (σ (historyAddr j)).2)
  ((c.1, h.1), fun j => match (finSumFinEquiv.symm j : Fin 8 ⊕ Fin 4) with
    | .inl i => ((c.2 i |>.1, (σ j).2), (c.2 i).2)
    | .inr i => (((σ j).1, h.2 i |>.1), (h.2 i).2))

def machine (blank : Fin k) (enc : Terminal → Fin k) :
    StructuredMachine Terminal (Core × Fin 33) (SlotClock.Symbol × Fin k) 12 33 :=
  ofPhases (by decide) (by decide) (.blank, blank)
    (SlotClockBirth.machine.initial, (HistoryLoop.machine blank enc 32).initial)
    (fun q => (HistoryLoop.machine blank enc 32).accepting q.2) (body blank enc)

def clock (x : SConfig (Core × Fin 33) (SlotClock.Symbol × Fin k) 12) :
    SConfig SlotClockBirth.Control SlotClock.Symbol 8 :=
  ⟨x.state.1.1, fun j => mapTape Prod.fst (x.tape (clockAddr j))⟩

def history (x : SConfig (Core × Fin 33) (SlotClock.Symbol × Fin k) 12) :
    SConfig (HistoryLoop.Control 32) (Fin k) 4 :=
  ⟨x.state.1.2, fun j => mapTape Prod.snd (x.tape (historyAddr j))⟩

theorem phase_step (blank : Fin k) (enc : Terminal → Fin k)
    (x : SConfig (Core × Fin 33) (SlotClock.Symbol × Fin k) 12) (a : Option Terminal) :
    ((machine blank enc).sMicroStep x a).state.2 = nextPhase x.state.2 := rfl

theorem clock_tick (blank : Fin k) (enc : Terminal → Fin k)
    (x : SConfig (Core × Fin 33) (SlotClock.Symbol × Fin k) 12)
    (h : x.state.2.val < 2) (a : Option Terminal) :
    clock ((machine blank enc).sMicroStep x a) =
      SlotClockBirth.machine.sMicroStep (clock x) (a.map (fun _ => ())) := by
  simp only [clock, StructuredMachine.sMicroStep, machine, ofPhases, body, h, ↓reduceIte,
    clockAddr, Equiv.symm_apply_apply, map_action]
  rfl

theorem clock_idle (blank : Fin k) (enc : Terminal → Fin k)
    (x : SConfig (Core × Fin 33) (SlotClock.Symbol × Fin k) 12)
    (h : ¬ x.state.2.val < 2) (a : Option Terminal) :
    clock ((machine blank enc).sMicroStep x a) = clock x := by
  simp only [clock, StructuredMachine.sMicroStep, machine, ofPhases, body, h, ↓reduceIte,
    clockAddr, Equiv.symm_apply_apply, map_action]
  rfl

theorem history_tick (blank : Fin k) (enc : Terminal → Fin k)
    (x : SConfig (Core × Fin 33) (SlotClock.Symbol × Fin k) 12) (a : Option Terminal) :
    history ((machine blank enc).sMicroStep x a) =
      (HistoryLoop.machine blank enc 32).sMicroStep (history x)
        (a.map (fun a => (a, SlotClockBirth.startNow (clock x).state))) := by
  simp only [history, clock, StructuredMachine.sMicroStep, machine, ofPhases, body,
    historyAddr, Equiv.symm_apply_apply, map_action]
  rfl

theorem history_none (blank : Fin k) (enc : Terminal → Fin k) (n : ℕ)
    (x : SConfig (Core × Fin 33) (SlotClock.Symbol × Fin k) 12) :
    history ((List.replicate n none).foldl (machine blank enc).sMicroStep x) =
      (List.replicate n none).foldl (HistoryLoop.machine blank enc 32).sMicroStep (history x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ, List.foldl_cons]
    rw [ih, history_tick]
    rfl

/-- Exact consumer projection for a whole real arrival, including the
start signal from the pre-arrival clock control. -/
theorem history_round (blank : Fin k) (enc : Terminal → Fin k)
    (x : SConfig (Core × Fin 33) (SlotClock.Symbol × Fin k) 12) (a : Terminal) :
    history ((machine blank enc).sRound x a) =
      (HistoryLoop.machine blank enc 32).sRound (history x)
        (a, SlotClockBirth.startNow (clock x).state) := by
  rw [StructuredMachine.sRound, Speedup.MultiStepMachine.roundInputs, List.foldl_cons,
    history_none, history_tick]
  rw [StructuredMachine.sRound, Speedup.MultiStepMachine.roundInputs, List.foldl_cons]
  rfl

theorem clock_tail (blank : Fin k) (enc : Terminal → Fin k) (ops : List (Option Terminal))
    (x : SConfig (Core × Fin 33) (SlotClock.Symbol × Fin k) 12)
    (hpos : 2 ≤ x.state.2.val) (hlen : x.state.2.val + ops.length ≤ 33) :
    clock (ops.foldl (machine blank enc).sMicroStep x) = clock x := by
  induction ops generalizing x with
  | nil => rfl
  | cons a ops ih =>
    have hh := clock_idle blank enc x (by omega) a
    cases ops with
    | nil => exact hh
    | cons b ops =>
      have hnext : x.state.2.val + 1 < 33 := by simp only [List.length_cons] at hlen; omega
      have hv : ((machine blank enc).sMicroStep x a).state.2.val = x.state.2.val + 1 := by
        rw [phase_step]
        simp only [nextPhase, dif_pos hnext]
      exact (ih ((machine blank enc).sMicroStep x a) (by rw [hv]; omega)
        (by rw [hv]; simp only [List.length_cons] at hlen ⊢; omega)).trans hh

theorem clock_round (blank : Fin k) (enc : Terminal → Fin k)
    (x : SConfig (Core × Fin 33) (SlotClock.Symbol × Fin k) 12)
    (hx : x.state.2 = 0) (a : Terminal) :
    clock ((machine blank enc).sRound x a) = SlotClockBirth.machine.sRound (clock x) () := by
  let x1 := (machine blank enc).sMicroStep x (some a)
  let x2 := (machine blank enc).sMicroStep x1 none
  have h1 : x1.state.2.val = 1 := by
    change ((machine blank enc).sMicroStep x (some a)).state.2.val = 1
    rw [phase_step, hx]
    rfl
  have h2 : x2.state.2.val = 2 := by
    change ((machine blank enc).sMicroStep x1 none).state.2.val = 2
    rw [phase_step]
    simp [nextPhase, h1]
  have hc1 := clock_tick blank enc x (by rw [hx]; simp) (some a)
  have hc2 := clock_tick blank enc x1 (by omega) none
  have hclock : clock x2 = SlotClockBirth.machine.sRound (clock x) () := by
    change clock ((machine blank enc).sMicroStep x1 none) = _
    rw [hc2]
    change SlotClockBirth.machine.sMicroStep (clock ((machine blank enc).sMicroStep x (some a))) none = _
    rw [hc1]
    rfl
  rw [StructuredMachine.sRound, Speedup.MultiStepMachine.roundInputs,
    show List.replicate (33 - 1) (none : Option Terminal) = none :: List.replicate 31 none from rfl,
    List.foldl_cons, List.foldl_cons]
  exact (clock_tail blank enc _ x2 (by omega) (by rw [h2, List.length_replicate])).trans hclock

theorem round_phase (blank : Fin k) (enc : Terminal → Fin k)
    (x : SConfig (Core × Fin 33) (SlotClock.Symbol × Fin k) 12)
    (hx : x.state.2 = 0) (a : Terminal) : ((machine blank enc).sRound x a).state.2 = 0 := by
  have he : x = ⟨(x.state.1, 0), x.tape⟩ := by rw [← hx]
  rw [he]
  have hh := ofPhases_round (by decide : 0 < 12) (by decide : 0 < 33)
    (SlotClock.Symbol.blank, blank)
    (SlotClockBirth.machine.initial, (HistoryLoop.machine blank enc 32).initial)
    (fun q : Core => (HistoryLoop.machine blank enc 32).accepting q.2)
    (body blank enc) x.state.1 x.tape a
  simpa only [machine, Fin.zero_eta] using congrArg (fun y => y.state.2) hh

theorem clock_rounds (blank : Fin k) (enc : Terminal → Fin k) (w : List Terminal)
    (x : SConfig (Core × Fin 33) (SlotClock.Symbol × Fin k) 12) (hx : x.state.2 = 0) :
    clock (w.foldl (machine blank enc).sRound x) =
      (List.replicate w.length ()).foldl SlotClockBirth.machine.sRound (clock x) := by
  induction w generalizing x with
  | nil => rfl
  | cons a w ih =>
    rw [List.foldl_cons, ih _ (round_phase blank enc x hx a), clock_round blank enc x hx a]
    rfl

/-- The combined machine's clock projection starts from actual blank tapes
and remains exactly the concrete clock, independently of input contents. -/
theorem clock_from_blank (blank : Fin k) (enc : Terminal → Fin k) (w : List Terminal) :
    clock ((machine blank enc).srun w) = SlotClockBirth.atTime w.length :=
  clock_rounds blank enc w (machine blank enc).sInit rfl

theorem trigger_from_blank (blank : Fin k) (enc : Terminal → Fin k)
    (w : List Terminal) (hw : 32 ≤ w.length) :
    SlotClockBirth.startNow (clock ((machine blank enc).srun w)).state = true ↔
      ∃ g : ℕ, w.length = 2 ^ g := by
  rw [clock_from_blank]
  exact SlotClockBirth.startNow_power w.length hw

theorem history_from_blank_step (blank : Fin k) (enc : Terminal → Fin k)
    (w : List Terminal) (a : Terminal) :
    history ((machine blank enc).srun (w ++ [a])) =
      (HistoryLoop.machine blank enc 32).sRound (history ((machine blank enc).srun w))
        (a, SlotClockBirth.startNow (SlotClockBirth.atTime w.length).state) := by
  have he : (machine blank enc).srun (w ++ [a]) =
      (machine blank enc).sRound ((machine blank enc).srun w) a := by
    simp only [StructuredMachine.srun, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [he, history_round, clock_from_blank]

/-- info: 'PalPeg.ClockHistory.trigger_from_blank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms trigger_from_blank

/-- info: 'PalPeg.ClockHistory.history_round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms history_round

/-- info: 'PalPeg.ClockHistory.clock_round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms clock_round

end PalPeg.ClockHistory
