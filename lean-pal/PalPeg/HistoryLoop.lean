import PalPeg.HistoryRotation

set_option autoImplicit false
namespace PalPeg.HistoryLoop
open PegSeparation.RealTimeTM PalPeg.Program
variable {k : ℕ} {Terminal : Type}

abbrev Inner (C : ℕ) := HistoryNext.Control × Fin (C + 1)
abbrev Control (C : ℕ) := (Fin 4 ≃ Fin 4) × Inner C

/-- The role assignment is finite control. A start bit on a real arrival
rotates it once and starts a new pass on that same arrival. A clock must
only start after the prior pass has met its layout/deadline contract. -/
def machine (blank : Fin k) (enc : Terminal → Fin k) (C : ℕ) :
    StructuredMachine (Terminal × Bool) (Control C) (Fin k) 4 (C + 1) where
  tapeCount_pos := by decide
  blank := blank
  initial := (Equiv.refl _, (HistoryNextInput.machine blank enc C).initial)
  accepting := fun q => (HistoryNextInput.machine blank enc C).accepting q.2
  micro := fun q a σ =>
    let start := match a with | none => false | some p => p.2
    let e := if start then HistoryRotation.roles.trans q.1 else q.1
    let c := if start then (HistoryNextInput.machine blank enc C).initial else q.2
    let d := (TapeRename.machine (HistoryNextInput.machine blank enc C) e).micro c (a.map Prod.fst) σ
    ((e, d.1), d.2)

def embed {C : ℕ} (e : Fin 4 ≃ Fin 4) (x : SConfig (Inner C) (Fin k) 4) :
    SConfig (Control C) (Fin k) 4 := ⟨(e, x.state), x.tape⟩

def quiet (a : Terminal) : Terminal × Bool := (a, false)

theorem micro_quiet (blank : Fin k) (enc : Terminal → Fin k) (C : ℕ)
    (e : Fin 4 ≃ Fin 4) (x : SConfig (Inner C) (Fin k) 4) (a : Option Terminal) :
    (machine blank enc C).sMicroStep (embed e x) (a.map quiet) =
      embed e ((TapeRename.machine (HistoryNextInput.machine blank enc C) e).sMicroStep x a) := by
  cases a <;> rfl

theorem micro_start (blank : Fin k) (enc : Terminal → Fin k) (C : ℕ)
    (e : Fin 4 ≃ Fin 4) (x : SConfig (Inner C) (Fin k) 4) (a : Terminal) :
    (machine blank enc C).sMicroStep (embed e x) (some (a, true)) =
      embed (HistoryRotation.roles.trans e)
        ((HistoryRotation.cycle blank enc C e).sMicroStep
          ⟨(HistoryNextInput.machine blank enc C).initial, x.tape⟩ (some a)) := by
  rfl

theorem steps_quiet (blank : Fin k) (enc : Terminal → Fin k) (C : ℕ)
    (e : Fin 4 ≃ Fin 4) (ops : List (Option Terminal)) (x : SConfig (Inner C) (Fin k) 4) :
    (ops.map (Option.map quiet)).foldl (machine blank enc C).sMicroStep (embed e x) =
      embed e (ops.foldl (TapeRename.machine (HistoryNextInput.machine blank enc C) e).sMicroStep x) := by
  induction ops generalizing x with
  | nil => rfl
  | cons a ops ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [micro_quiet, ih]

theorem round_quiet (blank : Fin k) (enc : Terminal → Fin k) (C : ℕ)
    (e : Fin 4 ≃ Fin 4) (x : SConfig (Inner C) (Fin k) 4) (a : Terminal) :
    (machine blank enc C).sRound (embed e x) (quiet a) =
      embed e ((TapeRename.machine (HistoryNextInput.machine blank enc C) e).sRound x a) := by
  simpa only [StructuredMachine.sRound, Speedup.MultiStepMachine.roundInputs,
    List.map_cons, List.map_replicate, Option.map_some, Option.map_none] using
    steps_quiet blank enc C e (Speedup.MultiStepMachine.roundInputs (C + 1) a) x

theorem round_start (blank : Fin k) (enc : Terminal → Fin k) (C : ℕ)
    (e : Fin 4 ≃ Fin 4) (x : SConfig (Inner C) (Fin k) 4) (a : Terminal) :
    (machine blank enc C).sRound (embed e x) (a, true) =
      embed (HistoryRotation.roles.trans e) ((HistoryRotation.cycle blank enc C e).sRound
        ⟨(HistoryNextInput.machine blank enc C).initial, x.tape⟩ a) := by
  simp only [StructuredMachine.sRound, Speedup.MultiStepMachine.roundInputs,
    Nat.add_sub_cancel, List.foldl_cons]
  rw [micro_start]
  simpa only [List.map_replicate, Option.map_none, HistoryRotation.cycle] using
    steps_quiet blank enc C (HistoryRotation.roles.trans e) (List.replicate C none)
      ((HistoryRotation.cycle blank enc C e).sMicroStep
        ⟨(HistoryNextInput.machine blank enc C).initial, x.tape⟩ (some a))

theorem run_quiet (blank : Fin k) (enc : Terminal → Fin k) (C : ℕ)
    (e : Fin 4 ≃ Fin 4) (w : List Terminal) (x : SConfig (Inner C) (Fin k) 4) :
    (w.map quiet).foldl (machine blank enc C).sRound (embed e x) =
      embed e (w.foldl (TapeRename.machine (HistoryNextInput.machine blank enc C) e).sRound x) := by
  induction w generalizing x with
  | nil => rfl
  | cons a w ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [round_quiet, ih]

/-- The trigger arrival is logged by the new pass, not dropped or replayed.
No role change occurs during the subsequent non-triggering arrivals. -/
theorem run_block (blank : Fin k) (enc : Terminal → Fin k) (C : ℕ)
    (e : Fin 4 ≃ Fin 4) (a : Terminal) (w : List Terminal)
    (x : SConfig (Inner C) (Fin k) 4) :
    ((a, true) :: w.map quiet).foldl (machine blank enc C).sRound (embed e x) =
      embed (HistoryRotation.roles.trans e)
        ((a :: w).foldl (HistoryRotation.cycle blank enc C e).sRound
          ⟨(.inl 0, 0), x.tape⟩) := by
  rw [List.foldl_cons, round_start, run_quiet]
  rfl

theorem block_layout (blank : Fin k) (enc : Terminal → Fin k) (C : ℕ)
    (e : Fin 4 ≃ Fin 4) (a : Terminal) (w : List Terminal) (u v : List (Fin k))
    (hu : blank ∉ u) (hv : blank ∉ v) (x : SConfig (Inner C) (Fin k) 4)
    (h : HistoryRotation.Layout blank e u v x.tape)
    (budget : 2 * (u.length + v.length) + v.length + 8 ≤ (a :: w).length * C) :
    let y := ((a, true) :: w.map quiet).foldl (machine blank enc C).sRound (embed e x)
    y.state.1 = HistoryRotation.roles.trans e ∧
      y.state.2 = (.inr (.inr (fun _ => 2)), 0) ∧
      HistoryRotation.Layout blank y.state.1 (u ++ v) ((a :: w).map enc) y.tape := by
  have hc := HistoryRotation.cycled blank enc C e (a :: w) u v hu hv x.tape h budget
  rw [run_block]
  exact ⟨rfl, hc⟩

/-- A single input-independent worker speed suffices for an eighth-length
history window, even without assuming h is a power of two. -/
theorem short_window_budget (h v : ℕ) (hh : 32 ≤ h) (hv : v ≤ h) :
    2 * h + v + 8 ≤ (h / 8) * 32 := by
  omega

theorem block_by_eighth (blank : Fin k) (enc : Terminal → Fin k)
    (e : Fin 4 ≃ Fin 4) (a : Terminal) (w : List Terminal) (u v : List (Fin k))
    (hu : blank ∉ u) (hv : blank ∉ v) (x : SConfig (Inner 32) (Fin k) 4)
    (h : HistoryRotation.Layout blank e u v x.tape) (hlen : 32 ≤ u.length + v.length)
    (window : (u.length + v.length) / 8 ≤ (a :: w).length) :
    let y := ((a, true) :: w.map quiet).foldl (machine blank enc 32).sRound (embed e x)
    y.state.1 = HistoryRotation.roles.trans e ∧
      y.state.2 = (.inr (.inr (fun _ => 2)), 0) ∧
      HistoryRotation.Layout blank y.state.1 (u ++ v) ((a :: w).map enc) y.tape := by
  apply block_layout blank enc 32 e a w u v hu hv x h
  exact (short_window_budget (u.length + v.length) v.length hlen (by omega)).trans
    (Nat.mul_le_mul_right 32 window)

/-- info: 'PalPeg.HistoryLoop.block_by_eighth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms block_by_eighth

/-- info: 'PalPeg.HistoryLoop.block_layout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms block_layout

end PalPeg.HistoryLoop
