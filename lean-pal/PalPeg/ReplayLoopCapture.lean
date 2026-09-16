import PalPeg.ReplayLoopReplay

set_option autoImplicit false
namespace PalPeg.ReplayLoopCapture
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ReplayLoop PalPeg.ReplayLoopReplay
variable {Terminal Q : Type} [Fintype Q] [DecidableEq Q] {k t B : ℕ}
local instance : DecidableEq (Control Q B) := inferInstance

def store (blank a : Fin k) (roles : Fin 4 ≃ Fin 4) (F : Fin 4 → STape (Fin k)) :=
  fun i => if i = roles 3 then (F i).applyAction blank (a, .right) else F i

/-- The real frame's capture action changes only the arrival log, leaving
the complete replay configuration (including the matcher) unchanged. -/
theorem capture_lift (M : StructuredMachine Terminal Q (Fin k) t B) (hB : 0 < B)
    (enc : Terminal → Fin k) (decode : Fin k → Terminal) (C : ℕ)
    (roles : Fin 4 ≃ Fin 4) (F : Fin 4 → STape (Fin k))
    (x : SConfig (Q × Fin B) (Fin k) (1 + t)) (a : Terminal) :
    bodyStep M.blank (body M hB enc decode C) ⟨0, by omega⟩ (some a)
      ((lift roles F x).state, (lift roles F x).tape) =
      ((lift roles (store M.blank (enc a) roles F) x).state,
        (lift roles (store M.blank (enc a) roles F) x).tape) := by
  simp only [bodyStep, body, lift, ↓reduceIte]
  congr 1
  funext j
  have hj := (finSumFinEquiv : Fin 4 ⊕ Fin t ≃ Fin (4 + t)).apply_symm_apply j
  cases h : (finSumFinEquiv.symm j : Fin 4 ⊕ Fin t) with
  | inl i =>
    rw [h] at hj
    rw [← hj]
    simp only [buf, Equiv.symm_apply_apply, Equiv.apply_eq_iff_eq, Sum.inl.injEq]
    have hn : roles 2 ≠ roles 3 := fun h => (by decide : (2 : Fin 4) ≠ 3) (roles.injective h)
    by_cases h2 : i = roles 2
    · subst i
      simp only [hn, ↓reduceIte]
      rfl
    · simp only [h2, ↓reduceIte, store]
      by_cases h3 : i = roles 3
      · simp only [h3, ↓reduceIte]
      · simp only [h3, ↓reduceIte]
        rfl
  | inr i =>
    rw [h] at hj
    rw [← hj]
    simp only [buf, Equiv.symm_apply_apply, Equiv.apply_eq_iff_eq, Sum.inr_ne_inl, ↓reduceIte]
    rfl

theorem store_log (blank a : Fin k) (roles : Fin 4 ≃ Fin 4)
    (F : Fin 4 → STape (Fin k)) (out : List (Fin k))
    (h : F (roles 3) = ⟨out, blank, []⟩) :
    store blank a roles F (roles 3) = ⟨a :: out, blank, []⟩ := by
  simp only [store, ↓reduceIte, h]
  rfl

/-- Capturing an arrival and then running a replay segment is exactly
the old replay segment with the new symbol retained in the log. -/
theorem capture_then_replay (M : StructuredMachine Terminal Q (Fin k) t B) (hB : 0 < B)
    (enc : Terminal → Fin k) (decode : Fin k → Terminal) (C n : ℕ)
    (roles : Fin 4 ≃ Fin 4) (F : Fin 4 → STape (Fin k))
    (x : SConfig (Q × Fin B) (Fin k) (1 + t)) (a : Terminal)
    (h : ∀ i, i < n → ¬ ((TapeReplay.run M hB decode i x).state.2.val = 0 ∧
      ((TapeReplay.run M hB decode i x).tape TapeReplay.sourceAddr).focus = M.blank)) :
    let z := bodyStep M.blank (body M hB enc decode C) ⟨0, by omega⟩ (some a)
      ((lift roles F x).state, (lift roles F x).tape)
    run M hB decode n ⟨z.1, z.2⟩ =
      lift roles (store M.blank (enc a) roles F) (TapeReplay.run M hB decode n x) := by
  rw [capture_lift]
  exact run_lift M hB decode roles (store M.blank (enc a) roles F) n x h

theorem phase_tail (M : StructuredMachine Terminal Q (Fin k) t B) (hB : 0 < B)
    (enc : Terminal → Fin k) (decode : Fin k → Terminal) (C n : ℕ)
    (p : Fin (C + 1)) (hp : 0 < p.val) (hn : p.val + n ≤ C + 1)
    (x : SConfig (Control Q B) (Fin k) (4 + t)) :
    phaseRun M.blank (body M hB enc decode C) (List.replicate n none) p (x.state, x.tape) =
      ((run M hB decode n x).state, (run M hB decode n x).tape) := by
  induction n generalizing p x with
  | zero => rfl
  | succ n ih =>
    have hs : bodyStep M.blank (body M hB enc decode C) p none (x.state, x.tape) =
        (((worker M hB decode).sMicroStep x none).state,
          ((worker M hB decode).sMicroStep x none).tape) := by
      simp only [bodyStep, body, show p.val ≠ 0 by omega, ↓reduceIte,
        StructuredMachine.sMicroStep, worker]
    rw [List.replicate_succ, phaseRun_cons, hs]
    cases n with
    | zero => rfl
    | succ n =>
      have hv : (nextPhase p).val = p.val + 1 := by
        simp only [nextPhase, dif_pos (show p.val + 1 < C + 1 by omega)]
      rw [ih _ (by rw [hv]; omega) (by rw [hv]; omega)]
      rfl

/-- An entire actual-input frame consists of precisely one capture and C
autonomous worker ticks, including any handoffs inside those ticks. -/
theorem frame (M : StructuredMachine Terminal Q (Fin k) t B) (hB : 0 < B)
    (enc : Terminal → Fin k) (decode : Fin k → Terminal) (C : ℕ)
    (x : SConfig (Control Q B) (Fin k) (4 + t)) (a : Terminal) :
    let z := bodyStep M.blank (body M hB enc decode C) ⟨0, by omega⟩ (some a) (x.state, x.tape)
    let y := run M hB decode C ⟨z.1, z.2⟩
    (machine M hB enc decode C).sRound ⟨(x.state, 0), x.tape⟩ a = ⟨(y.state, 0), y.tape⟩ := by
  have hr := ofPhases_round (by omega : 0 < 4 + t) (by omega : 0 < C + 1)
    M.blank (worker M hB decode).initial (fun q => M.accepting q.1)
    (body M hB enc decode C) x.state x.tape a
  change (machine M hB enc decode C).sRound _ _ = _ at hr
  dsimp only
  simp only [Fin.zero_eta] at hr
  rw [hr]
  simp only [Speedup.MultiStepMachine.roundInputs, Nat.add_sub_cancel, phaseRun_cons]
  cases C with
  | zero => rfl
  | succ C =>
    have hp : (nextPhase (⟨0, by omega⟩ : Fin (C + 1 + 1))).val = 1 := by
      simp only [nextPhase, dif_pos (show 0 + 1 < C + 1 + 1 by omega)]
    let z := bodyStep M.blank (body M hB enc decode (C + 1)) 0 (some a) (x.state, x.tape)
    have ht := phase_tail M hB enc decode (C + 1) (C + 1)
      (nextPhase ⟨0, by omega⟩) (by rw [hp]; omega) (by rw [hp]; omega) ⟨z.1, z.2⟩
    dsimp only [z] at ht
    simp only [Prod.mk.eta, Fin.zero_eta] at ht
    rw [ht]
    simp only [Fin.zero_eta]

/-- info: 'PalPeg.ReplayLoopCapture.frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms frame

/-- info: 'PalPeg.ReplayLoopCapture.capture_then_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms capture_then_replay

end PalPeg.ReplayLoopCapture
