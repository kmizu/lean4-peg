import PalPeg.ProgLangPersist2

/-! One real arrival followed by a fixed number of internal machine ticks.
The inner machine keeps its entire finite control between input rounds. -/
set_option autoImplicit false

namespace PalPeg.Program
open PegSeparation.RealTimeTM PalPeg.ProgLangPersist2

variable {Terminal Q Γ : Type} [Fintype Q] [DecidableEq Q]
  [Fintype Γ] [DecidableEq Γ] {t L B : ℕ}

def frameBody (inner : StructuredMachine Terminal Q Γ t L)
    (arr : ArriveAct Terminal Γ t) (hB : 0 < B) :
    PhaseBody Terminal Q Γ t B := fun c a ph σ =>
  if ph = ⟨0, hB⟩ then (c, arr a σ) else inner.micro c a σ

theorem frameBody_zero (inner : StructuredMachine Terminal Q Γ t L)
    (arr : ArriveAct Terminal Γ t) (hB : 0 < B)
    (a : Option Terminal) (c : Q) (T : Fin t → STape Γ) :
    bodyStep inner.blank (frameBody inner arr hB) ⟨0, hB⟩ a (c, T) =
      (c, arriveA inner.blank arr a T) := by
  simp only [bodyStep, frameBody, ↓reduceIte]
  rfl

theorem frameBody_ne (inner : StructuredMachine Terminal Q Γ t L)
    (arr : ArriveAct Terminal Γ t) (hB : 0 < B)
    (a : Option Terminal) (ph : Fin B) (hph : ph ≠ ⟨0, hB⟩)
    (x : SConfig Q Γ t) :
    bodyStep inner.blank (frameBody inner arr hB) ph a (x.state, x.tape) =
      let y := inner.sMicroStep x a
      (y.state, y.tape) := by
  simp only [bodyStep, frameBody, if_neg hph, StructuredMachine.sMicroStep]

theorem frameBody_tail (inner : StructuredMachine Terminal Q Γ t L)
    (arr : ArriveAct Terminal Γ t) (hB : 0 < B)
    (l : List (Option Terminal)) (ph : Fin B) (x : SConfig Q Γ t)
    (hlen : ph.val + l.length ≤ B) (hpos : 0 < ph.val) :
    phaseRun inner.blank (frameBody inner arr hB) l ph (x.state, x.tape) =
      let y := l.foldl inner.sMicroStep x
      (y.state, y.tape) := by
  induction l generalizing ph x with
  | nil => rfl
  | cons a l ih =>
    have hne : ph ≠ ⟨0, hB⟩ := by intro h; subst ph; simp at hpos
    rw [phaseRun_cons, frameBody_ne inner arr hB a ph hne]
    by_cases hl : l = []
    · subst l; rfl
    · have hll : 0 < l.length := List.length_pos_iff.mpr hl
      have hb : ph.val + 1 < B := by simp only [List.length_cons] at hlen; omega
      apply ih
      · simp only [nextPhase, dif_pos hb]
        simp only [List.length_cons] at hlen
        omega
      · simp only [nextPhase, dif_pos hb]; omega

/-- The clock multiplier K is a fixed natural in the machine definition,
not a function of input length or an unbounded queue/pattern value. -/
def frameMachine (inner : StructuredMachine Terminal Q Γ t L)
    (arr : ArriveAct Terminal Γ t) (K : ℕ) :
    StructuredMachine Terminal (Q × Fin (K + 1)) Γ t (K + 1) :=
  ofPhases inner.tapeCount_pos (Nat.zero_lt_succ K) inner.blank inner.initial
    inner.accepting (frameBody inner arr (Nat.zero_lt_succ K))

/-- Every external round performs exactly one arrival action and K inner
microsteps, without resetting or duplicating the inner control. -/
theorem frameMachine_round (inner : StructuredMachine Terminal Q Γ t L)
    (arr : ArriveAct Terminal Γ t) (K : ℕ) (a : Terminal)
    (c : Q) (T : Fin t → STape Γ) :
    (frameMachine inner arr K).sRound
      { state := (c, ⟨0, Nat.zero_lt_succ K⟩), tape := T } a =
      let y := (List.replicate K none).foldl inner.sMicroStep
        { state := c, tape := arriveA inner.blank arr (some a) T }
      { state := (y.state, ⟨0, Nat.zero_lt_succ K⟩), tape := y.tape } := by
  rw [frameMachine, ofPhases_round]
  have hp : phaseRun inner.blank (frameBody inner arr (Nat.zero_lt_succ K))
      (PalPeg.Speedup.MultiStepMachine.roundInputs (K + 1) a)
      ⟨0, Nat.zero_lt_succ K⟩ (c, T) =
      let y := (List.replicate K none).foldl inner.sMicroStep
        { state := c, tape := arriveA inner.blank arr (some a) T }
      (y.state, y.tape) := by
    simp only [PalPeg.Speedup.MultiStepMachine.roundInputs, Nat.add_sub_cancel,
      phaseRun_cons, frameBody_zero]
    cases K with
    | zero => rfl
    | succ K =>
      apply frameBody_tail inner arr _ _ _
        { state := c, tape := arriveA inner.blank arr (some a) T }
      · simp [nextPhase, List.length_replicate]; omega
      · simp [nextPhase]
  rw [hp]

/-- info: 'PalPeg.Program.frameMachine_round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms frameMachine_round

end PalPeg.Program
