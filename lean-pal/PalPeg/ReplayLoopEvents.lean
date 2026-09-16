import PalPeg.ReplayLoopCapture
import PalPeg.ReplayLoopRecovery

set_option autoImplicit false
namespace PalPeg.ReplayLoopEvents
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ReplayLoop
variable {Terminal Q : Type} [Fintype Q] [DecidableEq Q] {k t B : ℕ}
local instance : DecidableEq (Control Q B) := inferInstance

/-- Proof events for the existing real-input machine, not a new external
input alphabet or commands supplied to the runtime controller. -/
inductive Event (Terminal : Type)
  | arrival (a : Terminal)
  | tick

def step (M : StructuredMachine Terminal Q (Fin k) t B) (hB : 0 < B)
    (enc : Terminal → Fin k) (decode : Fin k → Terminal)
    (x : SConfig (Control Q B) (Fin k) (4 + t)) (e : Event Terminal) :=
  match e with
  | .arrival a =>
    let z := bodyStep M.blank (body M hB enc decode 0) ⟨0, by decide⟩ (some a) (x.state, x.tape)
    (⟨z.1, z.2⟩ : SConfig (Control Q B) (Fin k) (4 + t))
  | .tick => (worker M hB decode).sMicroStep x none

def events (C : ℕ) (w : List Terminal) : List (Event Terminal) :=
  w.flatMap (fun a => .arrival a :: List.replicate C .tick)

def run (M : StructuredMachine Terminal Q (Fin k) t B) (hB : 0 < B)
    (enc : Terminal → Fin k) (decode : Fin k → Terminal)
    (es : List (Event Terminal)) (x : SConfig (Control Q B) (Fin k) (4 + t)) :=
  es.foldl (step M hB enc decode) x

theorem ticks (M : StructuredMachine Terminal Q (Fin k) t B) (hB : 0 < B)
    (enc : Terminal → Fin k) (decode : Fin k → Terminal) (n : ℕ)
    (x : SConfig (Control Q B) (Fin k) (4 + t)) :
    run M hB enc decode (List.replicate n .tick) x = ReplayLoopReplay.run M hB decode n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    change run M hB enc decode (List.replicate n .tick)
      ((worker M hB decode).sMicroStep x none) = _
    rw [ih]
    rfl

theorem one_frame (M : StructuredMachine Terminal Q (Fin k) t B) (hB : 0 < B)
    (enc : Terminal → Fin k) (decode : Fin k → Terminal) (C : ℕ)
    (x : SConfig (Control Q B) (Fin k) (4 + t)) (a : Terminal) :
    let y := run M hB enc decode (.arrival a :: List.replicate C .tick) x
    (machine M hB enc decode C).sRound ⟨(x.state, 0), x.tape⟩ a = ⟨(y.state, 0), y.tape⟩ := by
  have hr := ReplayLoopCapture.frame M hB enc decode C x a
  change (machine M hB enc decode C).sRound _ _ =
    ⟨((run M hB enc decode (List.replicate C .tick) (step M hB enc decode x (.arrival a))).state, 0),
      (run M hB enc decode (List.replicate C .tick) (step M hB enc decode x (.arrival a))).tape⟩
  rw [ticks]
  exact hr

/-- Every actual input word is exactly the interleaved capture/tick trace,
even when one frame crosses several recovery/replay/rotation boundaries. -/
theorem actual_word (M : StructuredMachine Terminal Q (Fin k) t B) (hB : 0 < B)
    (enc : Terminal → Fin k) (decode : Fin k → Terminal) (C : ℕ) (w : List Terminal)
    (x : SConfig (Control Q B) (Fin k) (4 + t)) :
    let y := run M hB enc decode (events C w) x
    w.foldl (machine M hB enc decode C).sRound ⟨(x.state, 0), x.tape⟩ = ⟨(y.state, 0), y.tape⟩ := by
  induction w generalizing x with
  | nil => rfl
  | cons a w ih =>
    simp only [List.foldl_cons, one_frame]
    rw [ih]
    simp only [run, events, List.flatMap_cons, List.foldl_append]

theorem events_append (C : ℕ) (u v : List Terminal) :
    events C (u ++ v) = events C u ++ events C v := by
  simp only [events, List.flatMap_append]

def arrivals (es : List (Event Terminal)) : List Terminal :=
  es.filterMap (fun e => match e with | .arrival a => some a | .tick => none)

theorem arrivals_events (C : ℕ) (w : List Terminal) : arrivals (events C w) = w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp only [events, List.flatMap_cons, arrivals, List.filterMap_append,
      List.filterMap_cons, List.filterMap_replicate]
    simpa [arrivals, events] using congrArg (List.cons a) ih

def work : List (Event Terminal) → ℕ
  | [] => 0
  | .arrival _ :: es => work es
  | .tick :: es => work es + 1

def appendLog (blank : Fin k) (enc : Terminal → Fin k) (as : List Terminal) (S : STape (Fin k)) :=
  as.foldl (fun S a => S.applyAction blank (enc a, .right)) S

theorem appendLog_frontier (blank : Fin k) (enc : Terminal → Fin k)
    (as : List Terminal) (out : List (Fin k)) :
    appendLog blank enc as ⟨out, blank, []⟩ = ⟨(as.map enc).reverse ++ out, blank, []⟩ := by
  induction as generalizing out with
  | nil => rfl
  | cons a as ih =>
    change appendLog blank enc as ⟨enc a :: out, blank, []⟩ = _
    rw [ih]
    simp only [List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append]

theorem recovery_arrival (M : StructuredMachine Terminal Q (Fin k) t B) (hB : 0 < B)
    (enc : Terminal → Fin k) (decode : Fin k → Terminal) (roles : Fin 4 ≃ Fin 4)
    (log : STape (Fin k)) (x : SConfig Q (Fin k) t)
    (y : SConfig (Fin 3 → Fin 3) (Fin k) 3) (a : Terminal) :
    step M hB enc decode (ReplayLoopRecovery.lift roles log x y) (.arrival a) =
      ReplayLoopRecovery.lift roles (log.applyAction M.blank (enc a, .right)) x y := by
  have hh := ReplayLoopRecovery.capture_lift M hB enc decode 0 roles log x y a
  exact congrArg (fun z => (⟨z.1, z.2⟩ : SConfig (Control Q B) (Fin k) (4 + t))) hh

/-- Arbitrarily interleaved arrivals during recovery preserve the matcher,
append input in order, and advance recovery by exactly the worker-tick
count. Only the interval before its automatic handoff is required. -/
theorem recovery_interleaved (M : StructuredMachine Terminal Q (Fin k) t B) (hB : 0 < B)
    (enc : Terminal → Fin k) (decode : Fin k → Terminal) (roles : Fin 4 ≃ Fin 4)
    (es : List (Event Terminal)) (log : STape (Fin k)) (x : SConfig Q (Fin k) t)
    (y : SConfig (Fin 3 → Fin 3) (Fin k) 3)
    (h : ∀ i, i < work es → ¬ ∀ j, (HistoryRecover.run M.blank i y).state j = 2) :
    run M hB enc decode es (ReplayLoopRecovery.lift roles log x y) =
      ReplayLoopRecovery.lift roles (appendLog M.blank enc (arrivals es) log) x
        (HistoryRecover.run M.blank (work es) y) := by
  induction es generalizing log y with
  | nil => rfl
  | cons e es ih =>
    cases e with
    | arrival a =>
      change run M hB enc decode es
        (step M hB enc decode (ReplayLoopRecovery.lift roles log x y) (.arrival a)) = _
      rw [recovery_arrival, ih _ y h]
      rfl
    | tick =>
      change run M hB enc decode es
        ((worker M hB decode).sMicroStep (ReplayLoopRecovery.lift roles log x y) none) = _
      rw [ReplayLoopRecovery.tick_lift M hB decode roles log x y (h 0 (by simp [work]))]
      rw [ih]
      · rfl
      · intro i hi
        exact h (i + 1) (by simp only [work]; omega)

def appendBuffers (blank : Fin k) (enc : Terminal → Fin k) (roles : Fin 4 ≃ Fin 4)
    (as : List Terminal) (F : Fin 4 → STape (Fin k)) :=
  as.foldl (fun F a => ReplayLoopCapture.store blank (enc a) roles F) F

theorem replay_arrival (M : StructuredMachine Terminal Q (Fin k) t B) (hB : 0 < B)
    (enc : Terminal → Fin k) (decode : Fin k → Terminal) (roles : Fin 4 ≃ Fin 4)
    (F : Fin 4 → STape (Fin k)) (x : SConfig (Q × Fin B) (Fin k) (1 + t)) (a : Terminal) :
    step M hB enc decode (ReplayLoopReplay.lift roles F x) (.arrival a) =
      ReplayLoopReplay.lift roles (ReplayLoopCapture.store M.blank (enc a) roles F) x := by
  have hh := ReplayLoopCapture.capture_lift M hB enc decode 0 roles F x a
  exact congrArg (fun z => (⟨z.1, z.2⟩ : SConfig (Control Q B) (Fin k) (4 + t))) hh

theorem replay_interleaved (M : StructuredMachine Terminal Q (Fin k) t B) (hB : 0 < B)
    (enc : Terminal → Fin k) (decode : Fin k → Terminal) (roles : Fin 4 ≃ Fin 4)
    (es : List (Event Terminal)) (F : Fin 4 → STape (Fin k))
    (x : SConfig (Q × Fin B) (Fin k) (1 + t))
    (h : ∀ i, i < work es → ¬ ((TapeReplay.run M hB decode i x).state.2.val = 0 ∧
      ((TapeReplay.run M hB decode i x).tape TapeReplay.sourceAddr).focus = M.blank)) :
    run M hB enc decode es (ReplayLoopReplay.lift roles F x) =
      ReplayLoopReplay.lift roles (appendBuffers M.blank enc roles (arrivals es) F)
        (TapeReplay.run M hB decode (work es) x) := by
  induction es generalizing F x with
  | nil => rfl
  | cons e es ih =>
    cases e with
    | arrival a =>
      change run M hB enc decode es
        (step M hB enc decode (ReplayLoopReplay.lift roles F x) (.arrival a)) = _
      rw [replay_arrival, ih _ x h]
      rfl
    | tick =>
      change run M hB enc decode es
        ((worker M hB decode).sMicroStep (ReplayLoopReplay.lift roles F x) none) = _
      rw [ReplayLoopReplay.tick_lift M hB decode roles F x (h 0 (by simp [work]))]
      rw [ih]
      · rfl
      · intro i hi
        exact h (i + 1) (by simp only [work]; omega)

theorem appendBuffers_log (blank : Fin k) (enc : Terminal → Fin k) (roles : Fin 4 ≃ Fin 4)
    (as : List Terminal) (F : Fin 4 → STape (Fin k)) :
    appendBuffers blank enc roles as F (roles 3) = appendLog blank enc as (F (roles 3)) := by
  induction as generalizing F with
  | nil => rfl
  | cons a as ih =>
    change appendBuffers blank enc roles as (ReplayLoopCapture.store blank (enc a) roles F) (roles 3) = _
    rw [ih]
    simp only [ReplayLoopCapture.store, ↓reduceIte, appendLog, List.foldl_cons]

/-- info: 'PalPeg.ReplayLoopEvents.replay_interleaved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms replay_interleaved

/-- info: 'PalPeg.ReplayLoopEvents.recovery_interleaved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms recovery_interleaved

/-- info: 'PalPeg.ReplayLoopEvents.actual_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms actual_word

end PalPeg.ReplayLoopEvents
