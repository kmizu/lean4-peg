import PalPeg.ProgLangCallFrame

/-! Exact physical prefixes of an input frame, including an internal
call boundary at which a source phase finishes before the frame does. -/
set_option autoImplicit false

namespace PalPeg.Program
open PegSeparation.RealTimeTM PalPeg.ProgLangPersist2

variable {Terminal Q Γ : Type} [Fintype Q] [DecidableEq Q]
  [Fintype Γ] [DecidableEq Γ] {t L : ℕ}

theorem frameMachine_prefix (inner : StructuredMachine Terminal Q Γ t L)
    (arr : ArriveAct Terminal Γ t) (K N : ℕ) (hN : N ≤ K) (a : Terminal)
    (c : Q) (T : Fin t → STape Γ) :
    (some a :: List.replicate N none).foldl (frameMachine inner arr K).sMicroStep
      { state := (c, ⟨0, Nat.zero_lt_succ K⟩), tape := T } =
      let y := (List.replicate N none).foldl inner.sMicroStep
        { state := c, tape := arriveA inner.blank arr (some a) T }
      { state := (y.state, nextPhase^[N + 1] (⟨0, Nat.zero_lt_succ K⟩ : Fin (K + 1))), tape := y.tape } := by
  rw [frameMachine, ofPhases_foldl]
  have hp : phaseRun inner.blank (frameBody inner arr (Nat.zero_lt_succ K))
      (some a :: List.replicate N none) ⟨0, Nat.zero_lt_succ K⟩ (c, T) =
      let y := (List.replicate N none).foldl inner.sMicroStep
        { state := c, tape := arriveA inner.blank arr (some a) T }
      (y.state, y.tape) := by
    rw [phaseRun_cons, frameBody_zero]
    cases N with
    | zero => rfl
    | succ N =>
      apply frameBody_tail inner arr _ _ _
        { state := c, tape := arriveA inner.blank arr (some a) T }
      · have hh : (0 : ℕ) + 1 < K + 1 := by omega
        simp only [nextPhase, dif_pos hh, List.length_replicate]
        omega
      · have hh : (0 : ℕ) + 1 < K + 1 := by omega
        simp only [nextPhase, dif_pos hh]
        omega
  rw [hp]
  simp only [List.length_cons, List.length_replicate]

end PalPeg.Program

namespace PalPeg.ProgLangBank
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang
open PalPeg.ProgLangPersist PalPeg.ProgLangPersist2

variable {A C D Terminal Γ : Type} {n t : ℕ}
  [DecidableEq A] [DecidableEq C] [Fintype D] [DecidableEq D]
  [Fintype Γ] [DecidableEq Γ]

theorem callFrameMachine_prefix
    (progs : Fin n → Prog A C) (I : Fin n → InterpF Terminal A C Γ t)
    (choose : D → (Fin t → Γ) → D × Fin n) (H R N : ℕ) (hN : N ≤ R) (blank : Γ)
    (ht : 0 < t) (initialOuter : D) (initialIndex : Fin n)
    (arr : ArriveAct Terminal Γ t) (a : Terminal)
    (c : CallCtrl progs D) (T : Fin t → STape Γ) :
    (some a :: List.replicate (N * (H + 1)) none).foldl
      (callFrameMachine progs I choose H R blank ht initialOuter initialIndex arr).sMicroStep
      { state := ((c, ⟨0, Nat.zero_lt_succ H⟩), ⟨0, Nat.zero_lt_succ _⟩), tape := T } =
      let y := (callRun progs I choose H blank)^[N] (c, arriveA blank arr (some a) T)
      { state := ((y.1, ⟨0, Nat.zero_lt_succ H⟩),
          nextPhase^[N * (H + 1) + 1] (⟨0, Nat.zero_lt_succ _⟩ : Fin (R * (H + 1) + 1))), tape := y.2 } := by
  rw [callFrameMachine, frameMachine_prefix _ _ _ _ (Nat.mul_le_mul_right (H + 1) hN)]
  have hblank : (callMachine progs I choose H blank ht initialOuter initialIndex).blank = blank := rfl
  rw [hblank, callMachine_noneBlocks progs I choose H blank ht initialOuter initialIndex N
    (c, arriveA blank arr (some a) T)]

/-- info: 'PalPeg.ProgLangBank.callFrameMachine_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms callFrameMachine_prefix

end PalPeg.ProgLangBank
