import PalPeg.ReplayLoopEvents
import PalPeg.ReplayLoopRotation

set_option autoImplicit false
namespace PalPeg.ReplayLoopEventCut
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ReplayLoop PalPeg.ReplayLoopEvents
variable {Terminal Q : Type} [Fintype Q] [DecidableEq Q] {k t B : ℕ}

theorem work_append (as bs : List (Event Terminal)) : work (as ++ bs) = work as + work bs := by
  induction as with
  | nil => simp [work]
  | cons a as ih => cases a <;> simp [work, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Locate a worker tick without losing or moving any arrivals preceding
it. The cut uses proof data; runtime handoff is still source/control driven. -/
theorem split_tick (es : List (Event Terminal)) (n : ℕ) (hn : n < work es) :
    ∃ pre post, es = pre ++ .tick :: post ∧ work pre = n := by
  induction es generalizing n with
  | nil => simp [work] at hn
  | cons e es ih =>
    cases e with
    | arrival a =>
      obtain ⟨pre, post, he, hp⟩ := ih n hn
      exact ⟨.arrival a :: pre, post, by rw [he]; rfl, hp⟩
    | tick =>
      cases n with
      | zero => exact ⟨[], es, rfl, rfl⟩
      | succ n =>
        obtain ⟨pre, post, he, hp⟩ := ih n (by simp only [work] at hn; omega)
        exact ⟨.tick :: pre, post, by rw [he]; rfl, by simp only [work, hp]⟩

theorem run_append (M : StructuredMachine Terminal Q (Fin k) t B) (hB : 0 < B)
    (enc : Terminal → Fin k) (decode : Fin k → Terminal) (as bs : List (Event Terminal))
    (x : SConfig (Control Q B) (Fin k) (4 + t)) :
    run M hB enc decode (as ++ bs) x = run M hB enc decode bs (run M hB enc decode as x) := by
  simp only [run, List.foldl_append]

/-- Cross the first actual recovery handoff in an arbitrary interleaved
event stream. All preceding arrivals become the preserved log, and the
remaining stream runs from the exact completed recovery state. -/
theorem recovery_handoff (M : StructuredMachine Terminal Q (Fin k) t B) (hB : 0 < B)
    (enc : Terminal → Fin k) (decode : Fin k → Terminal) (roles : Fin 4 ≃ Fin 4)
    (es : List (Event Terminal)) (log : STape (Fin k)) (x : SConfig Q (Fin k) t)
    (y : SConfig (Fin 3 → Fin 3) (Fin k) 3) (n : ℕ)
    (hdone : ∀ j, (HistoryRecover.run M.blank n y).state j = 2) (hn : n < work es) :
    ∃ pre post, es = pre ++ .tick :: post ∧ work pre ≤ n ∧
      run M hB enc decode es (ReplayLoopRecovery.lift roles log x y) =
        run M hB enc decode post
          ⟨(x.state, roles, .inr ⟨0, hB⟩),
            (ReplayLoopRecovery.lift (B := B) roles (appendLog M.blank enc (arrivals pre) log) x
              (HistoryRecover.run M.blank n y)).tape⟩ := by
  let P := fun i => ∀ j, (HistoryRecover.run M.blank i y).state j = 2
  have hex : ∃ i, P i := ⟨n, hdone⟩
  let d := Nat.find hex
  have hd : P d := Nat.find_spec hex
  have hdn : d ≤ n := Nat.find_min' hex hdone
  have hbefore : ∀ i, i < d → ¬ P i := fun i hi => Nat.find_min hex hi
  have he : HistoryRecover.run M.blank n y = HistoryRecover.run M.blank d y := by
    rw [show n = d + (n - d) by omega]
    simp only [HistoryRecover.run, List.replicate_add, List.foldl_append]
    exact ReplayLoopRecovery.stopped M.blank _ _ hd
  obtain ⟨pre, post, hes, hp⟩ := split_tick es d (by omega)
  refine ⟨pre, post, hes, by omega, ?_⟩
  rw [hes, run_append]
  have hi := recovery_interleaved M hB enc decode roles pre log x y
    (by intro i hi; exact hbefore i (by omega))
  rw [hi]
  change run M hB enc decode post
    ((worker M hB decode).sMicroStep
      (ReplayLoopRecovery.lift roles (appendLog M.blank enc (arrivals pre) log) x
        (HistoryRecover.run M.blank (work pre) y)) none) = _
  rw [hp, ReplayLoopRecovery.switch_tick M hB decode roles _ x _ hd, he]

theorem replay_switch (M : StructuredMachine Terminal Q (Fin k) t B) (hB : 0 < B)
    (decode : Fin k → Terminal) (roles : Fin 4 ≃ Fin 4) (F : Fin 4 → STape (Fin k))
    (x : SConfig (Q × Fin B) (Fin k) (1 + t))
    (h : x.state.2.val = 0 ∧ (x.tape TapeReplay.sourceAddr).focus = M.blank) :
    (worker M hB decode).sMicroStep (ReplayLoopReplay.lift roles F x) none =
      ⟨(x.state.1, rotate.trans roles, .inl (fun _ => 0)), (ReplayLoopReplay.lift roles F x).tape⟩ := by
  simp only [StructuredMachine.sMicroStep, worker, ReplayLoopReplay.lift, buf,
    Equiv.symm_apply_apply, ↓reduceIte, h.1, h.2]
  rfl

/-- Cross the first replay handoff despite arbitrarily interleaved arrivals.
The accumulated log becomes the next frozen batch at the exact rotation. -/
theorem replay_handoff (M : StructuredMachine Terminal Q (Fin k) t B) (hB : 0 < B)
    (enc : Terminal → Fin k) (decode : Fin k → Terminal) (roles : Fin 4 ≃ Fin 4)
    (es : List (Event Terminal)) (F : Fin 4 → STape (Fin k))
    (x : SConfig (Q × Fin B) (Fin k) (1 + t)) (n : ℕ)
    (hdone : (TapeReplay.run M hB decode n x).state.2.val = 0 ∧
      ((TapeReplay.run M hB decode n x).tape TapeReplay.sourceAddr).focus = M.blank)
    (hn : n < work es) :
    ∃ pre post, es = pre ++ .tick :: post ∧ work pre ≤ n ∧
      let F' := appendBuffers M.blank enc roles (arrivals pre) F
      let z := TapeReplay.run M hB decode n x
      run M hB enc decode es (ReplayLoopReplay.lift roles F x) =
        run M hB enc decode post
          (ReplayLoopRecovery.lift (rotate.trans roles) (F' (roles 0))
            (ReplayLoopRotation.matcher z) ⟨fun _ => 0, ReplayLoopRotation.nextBuffers roles F' z⟩) := by
  let P := fun i => (TapeReplay.run M hB decode i x).state.2.val = 0 ∧
    ((TapeReplay.run M hB decode i x).tape TapeReplay.sourceAddr).focus = M.blank
  have hex : ∃ i, P i := ⟨n, hdone⟩
  let d := Nat.find hex
  have hd : P d := Nat.find_spec hex
  have hdn : d ≤ n := Nat.find_min' hex hdone
  have hbefore : ∀ i, i < d → ¬ P i := fun i hi => Nat.find_min hex hi
  have he : TapeReplay.run M hB decode n x = TapeReplay.run M hB decode d x := by
    rw [show n = d + (n - d) by omega, TapeReplay.run_add]
    exact ReplayLoopReplay.stopped M hB decode _ _ hd
  obtain ⟨pre, post, hes, hp⟩ := split_tick es d (by omega)
  refine ⟨pre, post, hes, by omega, ?_⟩
  dsimp only
  rw [hes, run_append]
  have hi := replay_interleaved M hB enc decode roles pre F x
    (by intro i hi; exact hbefore i (by omega))
  rw [hi]
  change run M hB enc decode post
    ((worker M hB decode).sMicroStep
      (ReplayLoopReplay.lift roles (appendBuffers M.blank enc roles (arrivals pre) F)
        (TapeReplay.run M hB decode (work pre) x)) none) = _
  rw [hp, replay_switch M hB decode roles _ _ hd,
    ReplayLoopRotation.replay_to_recovery, he]

theorem cut_accounting (pre post : List (Event Terminal)) :
    arrivals (pre ++ .tick :: post) = arrivals pre ++ arrivals post ∧
    work (pre ++ .tick :: post) = work pre + 1 + work post := by
  constructor
  · simp only [arrivals, List.filterMap_append, List.filterMap_cons]
  · rw [work_append]
    simp only [work]
    omega

theorem work_ticks (n : ℕ) : work (List.replicate n (Event.tick : Event Terminal)) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, work, ih]

theorem work_events (C : ℕ) (w : List Terminal) : work (events C w) = w.length * C := by
  induction w with
  | nil => simp [events, work]
  | cons a w ih =>
    change work ((.arrival a :: List.replicate C .tick) ++ events C w) = _
    rw [work_append]
    simp only [work, work_ticks, ih, List.length_cons, Nat.succ_mul]
    omega

/-- A completed phase's cut cannot consume more worker budget than its
proved bound; the rest of the real-input trace retains the remainder. -/
theorem remaining_budget (es pre post : List (Event Terminal)) (n : ℕ)
    (he : es = pre ++ .tick :: post) (hn : work pre ≤ n) :
    work es - (n + 1) ≤ work post := by
  rw [he]
  have hh := (cut_accounting pre post).2
  omega

/-- info: 'PalPeg.ReplayLoopEventCut.replay_handoff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms replay_handoff

/-- info: 'PalPeg.ReplayLoopEventCut.recovery_handoff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms recovery_handoff

end PalPeg.ReplayLoopEventCut
