import PalPeg.TextFeedPipelineControl

/-! Tape-only waiting gates distinguish a missing input symbol from a
mismatch. A sentinel-only branch remains available without future input. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelineWaitSource
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang
open PalPeg.TextFeedControl PalPeg.TextFeedPipelineControl

variable {k : ℕ}

theorem scan_waits (e : Env k) (σ : Fin 39 → Fin k)
    (hp : σ 11 ≠ e.endSym) (ht : σ 12 = e.blank) (r : Stack (TaskAct k) (TaskCond k)) :
    stepStack (taskEval e σ) (beforeCond (.inl .matchOk) :: r) =
      (.skip :: beforeCond (.inl .matchOk) :: r, some (.inr (.inl .supply))) := by
  have hc : taskEval e σ (.inr (.inr (.inr .scanWait))) = true := decide_eq_true ⟨hp, ht⟩
  simp only [beforeCond, stepStack_loop, hc, if_true]

theorem scan_passes (e : Env k) (σ : Fin 39 → Fin k)
    (h : σ 11 = e.endSym ∨ σ 12 ≠ e.blank) (r : Stack (TaskAct k) (TaskCond k)) :
    stepStack (taskEval e σ) (beforeCond (.inl .matchOk) :: r) = stepStack (taskEval e σ) r := by
  have hc : taskEval e σ (.inr (.inr (.inr .scanWait))) = false := by
    apply decide_eq_false
    intro hh
    rcases h with h | h
    · exact hh.1 h
    · exact h hh.2
  simp only [beforeCond, stepStack_loop, hc, Bool.false_eq_true, if_false]

theorem verify_waits (e : Env k) (σ : Fin 39 → Fin k)
    (hp : σ 19 ≠ e.endSym) (ht : σ 20 = e.blank) (r : Stack (TaskAct k) (TaskCond k)) :
    stepStack (taskEval e σ) (beforeCond (.inl .compOk) :: r) =
      (.skip :: beforeCond (.inl .compOk) :: r, some (.inr (.inr (.inl (GSVProg.tX, true, .stay))))) := by
  have hc : taskEval e σ (.inr (.inr (.inr .verifyWait))) = true := decide_eq_true ⟨hp, ht⟩
  simp only [beforeCond, stepStack_loop, hc, if_true]

theorem verify_passes (e : Env k) (σ : Fin 39 → Fin k)
    (h : σ 19 = e.endSym ∨ σ 20 ≠ e.blank) (r : Stack (TaskAct k) (TaskCond k)) :
    stepStack (taskEval e σ) (beforeCond (.inl .compOk) :: r) = stepStack (taskEval e σ) r := by
  have hc : taskEval e σ (.inr (.inr (.inr .verifyWait))) = false := by
    apply decide_eq_false
    intro hh
    rcases h with h | h
    · exact hh.1 h
    · exact h hh.2
  simp only [beforeCond, stepStack_loop, hc, Bool.false_eq_true, if_false]

theorem text_right_waits (e : Env k) (σ : Fin 39 → Fin k) (keep : Bool)
    (ht : σ 12 = e.blank) (r : Stack (TaskAct k) (TaskCond k)) :
    (stepStack (taskEval e σ)
      (liftVerify (.act (.inl (GSVProg.e8 GSTapes.tT, keep, .right))) :: r)).2 =
      some (.inr (.inl .supply)) := by
  have hc : taskEval e σ (.inr (.inl .blankText)) = true := by
    change decide (σ 12 = e.blank) = true
    exact decide_eq_true ht
  simp only [liftVerify, verifyAct, beforeVerify, if_true, stepStack_seq, waitText1, stepStack_loop, hc]

theorem verifier_right_waits (e : Env k) (σ : Fin 39 → Fin k) (keep : Bool)
    (ht : σ 20 = e.blank) (r : Stack (TaskAct k) (TaskCond k)) :
    (stepStack (taskEval e σ)
      (liftVerify (.act (.inl (GSVProg.tX, keep, .right))) :: r)).2 =
      some (.inr (.inr (.inl (GSVProg.tX, true, .stay)))) := by
  have hc : taskEval e σ (.inr (.inr (.inr .blankX))) = true := decide_eq_true ht
  have hne : GSVProg.tX ≠ GSVProg.e8 GSTapes.tT := by decide
  simp only [liftVerify, verifyAct, beforeVerify, if_true, hne, if_false,
    stepStack_seq, waitText2, stepStack_loop, hc]

theorem condition_ready (e : Env k) (σ : Fin 39 → Fin k)
    (c : GSVProg.Cond10 ⊕ GSVProgZLoop.DCond)
    (hs : c = .inl .matchOk → σ 11 = e.endSym ∨ σ 12 ≠ e.blank)
    (hv : c = .inl .compOk → σ 19 = e.endSym ∨ σ 20 ≠ e.blank)
    (r : Stack (TaskAct k) (TaskCond k)) :
    stepStack (taskEval e σ) (beforeCond c :: r) = stepStack (taskEval e σ) r := by
  cases c with
  | inl c =>
    cases c with
    | matchOk => exact scan_passes e σ (hs rfl) r
    | compOk => exact verify_passes e σ (hv rfl) r
    | notMark j => simp only [beforeCond, stepStack_skip]
    | notStart => simp only [beforeCond, stepStack_skip]
    | notStartU => simp only [beforeCond, stepStack_skip]
  | inr c => simp only [beforeCond, stepStack_skip]

theorem branch_ready (e : Env k) (σ : Fin 39 → Fin k)
    (c : GSVProg.Cond10 ⊕ GSVProgZLoop.DCond)
    (hs : c = .inl .matchOk → σ 11 = e.endSym ∨ σ 12 ≠ e.blank)
    (hv : c = .inl .compOk → σ 19 = e.endSym ∨ σ 20 ≠ e.blank)
    (p q : GSVProgZLoop.DProg) (r : Stack (TaskAct k) (TaskCond k)) :
    stepStack (taskEval e σ) (liftVerify (.ite c p q) :: r) =
      stepStack (taskEval e σ) (.ite (verifyCond c) (liftVerify p) (liftVerify q) :: r) := by
  rw [liftVerify, stepStack_seq, condition_ready e σ c hs hv]

/-- info: 'PalPeg.TextFeedPipelineWaitSource.branch_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms branch_ready

/-- info: 'PalPeg.TextFeedPipelineWaitSource.scan_waits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms scan_waits

/-- info: 'PalPeg.TextFeedPipelineWaitSource.verifier_right_waits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms verifier_right_waits

end PalPeg.TextFeedPipelineWaitSource
