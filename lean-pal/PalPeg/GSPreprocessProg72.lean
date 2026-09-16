import PalPeg.GSPreprocessProg71

/-! # Restoring counter tests and finite counter clearing -/
set_option autoImplicit false
namespace PalPeg.PrepInstance
open PegSeparation.RealTimeTM PalPeg.PatternTapes PalPeg.PatternProg PalPeg.ProgLang
variable {sc : ℕ} {Terminal : Type} {blank mark : Fin sc}

theorem counterProbe_restore {i : Fin 15} {n : ℕ} {S : Tapes sc}
    (hc : Tape.CounterView' blank mark (S i) n) :
    runG blank [.put i blank .left, .keep i .right] S = S := by
  funext j
  simp only [runG_cons, runG_nil]
  by_cases hj : j = i
  · subst j
    rw [applyG_keep_self, applyG_put_self]
    cases n with
    | zero => exact probe_restore_tape blank (S i) (by simpa using hc.left_eq) hc.focus_blank
    | succ n =>
      exact probe_restore_tape blank (S i)
        (by simpa [List.replicate_succ] using hc.left_eq) hc.focus_blank
  · rw [applyG_ne blank _ _ hj, applyG_ne blank _ _ hj]

/-- Test a counter, restoring its head before either branch starts. -/
def counterCaseProg (i : Fin 15) (mark : Fin sc)
    (zero nonzero : Prog (ActG 15 sc) (CondG 15 sc)) :
    Prog (ActG 15 sc) (CondG 15 sc) :=
  .seq (ACT (.put i blank .left))
    (.ite (i, mark) (.seq (ACT (.keep i .right)) nonzero)
      (.seq (ACT (.keep i .right)) zero))

theorem counterCase_exec {i : Fin 15} {n : ℕ} {S : Tapes sc}
    {zero nonzero : Prog (ActG 15 sc) (CondG 15 sc)} {trace : List (TAct 15 sc)}
    (hne : mark ≠ blank) (hc : Tape.CounterView' blank mark (S i) n)
    (he : ExecG Terminal blank (if n = 0 then zero else nonzero) S trace) :
    ExecG Terminal blank (counterCaseProg (blank := blank) i mark zero nonzero) S
      ([.put i blank .left, .keep i .right] ++ trace) := by
  have hr := counterProbe_restore hc
  change applyG blank (applyG blank S (.put i blank .left)) (.keep i .right) = S at hr
  have er : ExecG Terminal blank
      (.seq (ACT (.keep i .right)) (if n = 0 then zero else nonzero))
      (applyG blank S (.put i blank .left)) (.keep i .right :: trace) := by
    apply execG_seq (execG_act _ _)
    change ExecG Terminal blank _
      (applyG blank (applyG blank S (.put i blank .left)) (.keep i .right)) trace
    rw [hr]
    exact he
  apply execG_seq (execG_act _ _)
  by_cases hn : n = 0
  · apply execG_ite_neg
    · exact (decLoop_cond hne hc).trans (by simp [hn])
    · change ExecG Terminal blank _ (applyG blank S (.put i blank .left))
        (.keep i .right :: trace)
      simpa only [if_pos hn] using er
  · apply execG_ite_pos
    · exact (decLoop_cond hne hc).trans (by simp [hn])
    · change ExecG Terminal blank _ (applyG blank S (.put i blank .left))
        (.keep i .right :: trace)
      simpa only [if_neg hn] using er

theorem clearCounter_spec (i : Fin 15) (n : ℕ) (S : Tapes sc)
    (hne : mark ≠ blank) (hc : Tape.CounterView' blank mark (S i) n) :
    ∃ trace, ExecG Terminal blank (decLoopProg blank i [] mark) S trace ∧
      Tape.CounterView' blank mark (runG blank trace S i) 0 ∧
      (∀ j, j ≠ i → runG blank trace S j = S j) ∧ trace.length = 2 * n + 2 := by
  let trace := decActsN blank i [] n
  have hv := Fifteen.decActsN_counter blank mark [] (cs := i) (by simp) n S hc
  have hr := probeRestore_id hv
  refine ⟨trace ++ [.put i blank .left, .keep i .right],
    decLoopProg_exec hne (by simp) n S hc, ?_, ?_, ?_⟩
  · rw [runG_append, hr]
    exact hv
  · intro j hji
    rw [runG_append, hr]
    clear hr hv trace hc
    induction n generalizing S with
    | zero => rfl
    | succ n ih =>
      simp only [decActsN, decRound, List.cons_append, List.nil_append, runG_cons]
      rw [ih, applyG_ne blank _ _ hji, applyG_ne blank _ _ hji]
  · simp [trace, decActsN_length]

end PalPeg.PrepInstance
