import PalPeg.ReplayLoopReplay

set_option autoImplicit false
namespace PalPeg.ReplayLoopRecovery
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ReplayLoop
variable {Terminal Q : Type} [Fintype Q] [DecidableEq Q] {k t B : ℕ}

def lift (roles : Fin 4 ≃ Fin 4) (log : STape (Fin k))
    (x : SConfig Q (Fin k) t) (y : SConfig (Fin 3 → Fin 3) (Fin k) 3) :
    SConfig (Control Q B) (Fin k) (4 + t) :=
  ⟨(x.state, roles, .inl y.state), fun j =>
    match (finSumFinEquiv.symm j : Fin 4 ⊕ Fin t) with
    | .inl i => let r := roles.symm i
        if h : r.val < 3 then y.tape ⟨r.val, h⟩ else log
    | .inr i => x.tape i⟩

/-- A recovery tick in the actual loop equals the three-head recovery
machine and leaves the matcher and arrival log unchanged. -/
theorem tick_lift (M : StructuredMachine Terminal Q (Fin k) t B) (hB : 0 < B)
    (decode : Fin k → Terminal) (roles : Fin 4 ≃ Fin 4) (log : STape (Fin k))
    (x : SConfig Q (Fin k) t) (y : SConfig (Fin 3 → Fin 3) (Fin k) 3)
    (h : ¬ ∀ i, y.state i = 2) :
    (worker M hB decode).sMicroStep (lift roles log x y) none =
      lift roles log x ((HistoryRecover.machine M.blank).sRound y ()) := by
  simp only [StructuredMachine.sMicroStep, worker, lift, buf, dataAddr,
    Equiv.symm_apply_apply, h, ↓reduceIte]
  simp only [Fin.isLt, ↓reduceDIte, Fin.eta]
  simp only [StructuredMachine.sRound, Speedup.MultiStepMachine.roundInputs,
    Nat.sub_self, List.replicate_zero, List.foldl_cons, List.foldl_nil,
    StructuredMachine.sMicroStep]
  congr 1
  funext j
  cases hj : (finSumFinEquiv.symm j : Fin 4 ⊕ Fin t) with
  | inl i =>
    by_cases hi : (roles.symm i).val < 3
    · simp only [hi, ↓reduceDIte]
      rfl
    · simp only [hi, ↓reduceDIte]
      rfl
  | inr i => rfl

theorem run_lift (M : StructuredMachine Terminal Q (Fin k) t B) (hB : 0 < B)
    (decode : Fin k → Terminal) (roles : Fin 4 ≃ Fin 4) (log : STape (Fin k))
    (x : SConfig Q (Fin k) t) (n : ℕ) (y : SConfig (Fin 3 → Fin 3) (Fin k) 3)
    (h : ∀ i, i < n → ¬ ∀ j, (HistoryRecover.run M.blank i y).state j = 2) :
    ReplayLoopReplay.run M hB decode n (lift roles log x y) =
      lift roles log x (HistoryRecover.run M.blank n y) := by
  induction n generalizing y with
  | zero => rfl
  | succ n ih =>
    change ReplayLoopReplay.run M hB decode n
      ((worker M hB decode).sMicroStep (lift roles log x y) none) = _
    rw [tick_lift M hB decode roles log x y (h 0 (by omega)), ih]
    · rfl
    · intro i hi
      exact h (i + 1) (by omega)

theorem switch_tick (M : StructuredMachine Terminal Q (Fin k) t B) (hB : 0 < B)
    (decode : Fin k → Terminal) (roles : Fin 4 ≃ Fin 4) (log : STape (Fin k))
    (x : SConfig Q (Fin k) t) (y : SConfig (Fin 3 → Fin 3) (Fin k) 3)
    (h : ∀ i, y.state i = 2) :
    (worker M hB decode).sMicroStep (lift roles log x y) none =
      ⟨(x.state, roles, .inr ⟨0, hB⟩), (lift (B := B) roles log x y).tape⟩ := by
  simp only [StructuredMachine.sMicroStep, worker, lift, h, ↓reduceIte]
  rfl

theorem stopped (blank : Fin k) (n : ℕ) (y : SConfig (Fin 3 → Fin 3) (Fin k) 3)
    (h : ∀ i, y.state i = 2) : HistoryRecover.run blank n y = y := by
  have hy : y = ⟨fun _ => 2, y.tape⟩ := by rw [← funext h]
  rw [hy]
  induction n with
  | zero => rfl
  | succ n ih =>
    change HistoryRecover.run blank n
      ((HistoryRecover.machine blank).sRound ⟨fun _ => 2, y.tape⟩ ()) = _
    rw [HistoryRecover.done_round, ih]

/-- Recovery completion automatically enters replay with exactly the
recovered buffers, retaining the matcher and all newly logged input. -/
theorem handoff (M : StructuredMachine Terminal Q (Fin k) t B) (hB : 0 < B)
    (decode : Fin k → Terminal) (roles : Fin 4 ≃ Fin 4) (log : STape (Fin k))
    (x : SConfig Q (Fin k) t) (n : ℕ) (y : SConfig (Fin 3 → Fin 3) (Fin k) 3)
    (h : ∀ i, (HistoryRecover.run M.blank n y).state i = 2) :
    ∃ d, d ≤ n + 1 ∧ ReplayLoopReplay.run M hB decode d (lift roles log x y) =
      ⟨(x.state, roles, .inr ⟨0, hB⟩),
        (lift (B := B) roles log x (HistoryRecover.run M.blank n y)).tape⟩ := by
  let P := fun n => ∀ i, (HistoryRecover.run M.blank n y).state i = 2
  have hex : ∃ n, P n := ⟨n, h⟩
  let d := Nat.find hex
  have hd : P d := Nat.find_spec hex
  have hn : d ≤ n := Nat.find_min' hex h
  have hp : ∀ i, i < d → ¬ P i := fun i hi => Nat.find_min hex hi
  have he : HistoryRecover.run M.blank n y = HistoryRecover.run M.blank d y := by
    rw [show n = d + (n - d) by omega]
    simp only [HistoryRecover.run, List.replicate_add, List.foldl_append]
    exact stopped M.blank _ _ hd
  refine ⟨d + 1, by omega, ?_⟩
  have hr : ReplayLoopReplay.run M hB decode (d + 1) (lift roles log x y) =
      (worker M hB decode).sMicroStep
        (ReplayLoopReplay.run M hB decode d (lift roles log x y)) none := by
    simp only [ReplayLoopReplay.run, List.replicate_succ', List.foldl_append,
      List.foldl_cons, List.foldl_nil]
  rw [hr, run_lift M hB decode roles log x d y hp, he]
  exact switch_tick M hB decode roles log x _ hd

/-- Concrete consumed/frozen logs enter replay within max(lengths)+3
ticks, with the consumed buffers reusable and the batch forward-readable. -/
theorem buffers_handoff (M : StructuredMachine Terminal Q (Fin k) t B) (hB : 0 < B)
    (decode : Fin k → Terminal) (roles : Fin 4 ≃ Fin 4) (log : STape (Fin k))
    (x : SConfig Q (Fin k) t) (old batch : List (Fin k))
    (ho : M.blank ∉ old) (hb : M.blank ∉ batch) (T : Fin 3 → STape (Fin k))
    (h0 : T 0 = ⟨old.reverse ++ [M.blank], M.blank, []⟩)
    (h1 : T 1 = ⟨[M.blank], M.blank, []⟩)
    (h2 : T 2 = ⟨batch.reverse ++ [M.blank], M.blank, []⟩) :
    ∃ (d : ℕ) (U : Fin 3 → STape (Fin k)), d ≤ max old.length batch.length + 3 ∧
      ReplayLoopReplay.run M hB decode d (lift roles log x ⟨fun _ => 0, T⟩) =
        ⟨(x.state, roles, .inr ⟨0, hB⟩), (lift (B := B) roles log x ⟨fun _ => 2, U⟩).tape⟩ ∧
      STape.BlankEq M.blank (U 0) ⟨[M.blank], M.blank, []⟩ ∧
      STape.BlankEq M.blank (U 1) ⟨[M.blank], M.blank, []⟩ ∧
      STape.BlankEq M.blank (U 2) (HistoryConcat.source M.blank batch [M.blank]) := by
  let N := max old.length batch.length + 2
  let y := HistoryRecover.run M.blank N ⟨fun _ => 0, T⟩
  have ha := HistoryRecover.erase_lane M.blank 0 (by decide) old.reverse (by simpa using ho)
    N (by dsimp only [N]; simp) T h0
  have hc := HistoryRecover.erase_lane M.blank 1 (by decide) [] (by simp)
    N (by dsimp only [N]; simp) T h1
  have hr := HistoryRecover.rewind_lane M.blank batch hb N (by dsimp only [N]; omega) T h2
  have hs : ∀ i, y.state i = 2 := by
    intro i
    fin_cases i
    · exact ha.1
    · exact hc.1
    · exact hr.1
  obtain ⟨d, hd, hh⟩ := handoff M hB decode roles log x N ⟨fun _ => 0, T⟩ hs
  refine ⟨d, y.tape, by dsimp only [N] at hd; omega, ?_, ha.2, hc.2, hr.2⟩
  exact hh

theorem capture_lift (M : StructuredMachine Terminal Q (Fin k) t B) (hB : 0 < B)
    (enc : Terminal → Fin k) (decode : Fin k → Terminal) (C : ℕ)
    (roles : Fin 4 ≃ Fin 4) (log : STape (Fin k))
    (x : SConfig Q (Fin k) t) (y : SConfig (Fin 3 → Fin 3) (Fin k) 3) (a : Terminal) :
    bodyStep M.blank (body M hB enc decode C) ⟨0, by omega⟩ (some a)
      ((lift (B := B) roles log x y).state, (lift (B := B) roles log x y).tape) =
      ((lift (B := B) roles (log.applyAction M.blank (enc a, .right)) x y).state,
        (lift (B := B) roles (log.applyAction M.blank (enc a, .right)) x y).tape) := by
  simp only [bodyStep, body, lift, ↓reduceIte]
  congr 1
  funext j
  have hj := (finSumFinEquiv : Fin 4 ⊕ Fin t ≃ Fin (4 + t)).apply_symm_apply j
  cases h : (finSumFinEquiv.symm j : Fin 4 ⊕ Fin t) with
  | inl i =>
    rw [h] at hj
    rw [← hj]
    simp only [buf, Equiv.apply_eq_iff_eq, Sum.inl.injEq]
    by_cases hi : i = roles 3
    · subst i
      simp only [Equiv.symm_apply_apply, show ¬ (3 : Fin 4).val < 3 by decide, ↓reduceDIte, ↓reduceIte]
    · have hr : roles.symm i ≠ 3 := by
        intro hr
        apply hi
        rw [← roles.apply_symm_apply i, hr]
      have hv : (roles.symm i).val ≠ 3 := fun h => hr (Fin.ext h)
      have hl : (roles.symm i).val < 3 := by omega
      simp only [hi, hl, ↓reduceDIte, ↓reduceIte]
      rfl
  | inr i =>
    rw [h] at hj
    rw [← hj]
    simp only [buf, Equiv.apply_eq_iff_eq, Sum.inr_ne_inl, ↓reduceIte]
    rfl

/-- info: 'PalPeg.ReplayLoopRecovery.capture_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms capture_lift

/-- info: 'PalPeg.ReplayLoopRecovery.buffers_handoff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms buffers_handoff

/-- info: 'PalPeg.ReplayLoopRecovery.handoff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms handoff

/-- info: 'PalPeg.ReplayLoopRecovery.run_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_lift

end PalPeg.ReplayLoopRecovery
