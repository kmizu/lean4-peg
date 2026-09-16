import PalPeg.ReplayLoopRecovery

set_option autoImplicit false
namespace PalPeg.ReplayLoopRotation
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ReplayLoop
variable {Q : Type} {k t B : ℕ}

def matcher (x : SConfig (Q × Fin B) (Fin k) (1 + t)) : SConfig Q (Fin k) t :=
  ⟨x.state.1, fun i => x.tape (TapeReplay.targetAddr i)⟩

def nextBuffers (roles : Fin 4 ≃ Fin 4) (F : Fin 4 → STape (Fin k))
    (x : SConfig (Q × Fin B) (Fin k) (1 + t)) : Fin 3 → STape (Fin k) :=
  ![x.tape TapeReplay.sourceAddr, F (roles 1), F (roles 3)]

/-- The actual replay handoff has exactly the next recovery layout:
consumed source, spare, frozen log; the former free buffer is the new log.
This is only a change of finite roles, with no tape copying. -/
theorem replay_to_recovery (roles : Fin 4 ≃ Fin 4) (F : Fin 4 → STape (Fin k))
    (x : SConfig (Q × Fin B) (Fin k) (1 + t)) :
    (⟨(x.state.1, rotate.trans roles, .inl (fun _ => 0)),
      (ReplayLoopReplay.lift roles F x).tape⟩ : SConfig (Control Q B) (Fin k) (4 + t)) =
    ReplayLoopRecovery.lift (rotate.trans roles) (F (roles 0)) (matcher x)
      ⟨fun _ => 0, nextBuffers roles F x⟩ := by
  unfold ReplayLoopRecovery.lift ReplayLoopReplay.lift matcher
  dsimp only
  congr 1
  funext j
  cases hj : (finSumFinEquiv.symm j : Fin 4 ⊕ Fin t) with
  | inl i =>
    obtain ⟨r, rfl⟩ := roles.surjective i
    fin_cases r <;>
      simp [rotate, nextBuffers, Equiv.apply_eq_iff_eq]
  | inr i => rfl

/-- Once recovery finishes, its source and matcher are precisely a replay
configuration; the other physical buffers retain their recovered values. -/
def recoveredBuffers (roles : Fin 4 ≃ Fin 4) (log : STape (Fin k))
    (T : Fin 3 → STape (Fin k)) : Fin 4 → STape (Fin k) := fun i =>
  let r := roles.symm i
  if h : r.val < 3 then T ⟨r.val, h⟩ else log

theorem recovery_to_replay (roles : Fin 4 ≃ Fin 4) (log : STape (Fin k))
    (x : SConfig Q (Fin k) t) (T : Fin 3 → STape (Fin k)) (p : Fin B) :
    (⟨(x.state, roles, .inr p),
      (ReplayLoopRecovery.lift (B := B) roles log x ⟨fun _ => 2, T⟩).tape⟩ :
        SConfig (Control Q B) (Fin k) (4 + t)) =
      ReplayLoopReplay.lift roles (recoveredBuffers roles log T) (TapeReplay.pack p (T 2) x) := by
  unfold ReplayLoopRecovery.lift ReplayLoopReplay.lift TapeReplay.pack
  simp only [TapeReplay.sourceAddr, TapeReplay.targetAddr, Equiv.symm_apply_apply]
  congr 1
  funext j
  cases hj : (finSumFinEquiv.symm j : Fin 4 ⊕ Fin t) with
  | inl i =>
    by_cases hi : i = roles 2
    · subst i
      simp only [Equiv.symm_apply_apply, ↓reduceIte, show (2 : Fin 4).val < 3 by decide, ↓reduceDIte]
      rfl
    · simp only [hi, ↓reduceIte, recoveredBuffers]
  | inr i => rfl

/-- info: 'PalPeg.ReplayLoopRotation.replay_to_recovery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms replay_to_recovery

/-- info: 'PalPeg.ReplayLoopRotation.recovery_to_replay' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms recovery_to_replay

variable {Terminal : Type} [Fintype Q] [DecidableEq Q]

theorem batch_to_recovery (M : StructuredMachine Terminal Q (Fin k) t B) (hB : 0 < B)
    (enc : Terminal → Fin k) (decode : Fin k → Terminal)
    (hdec : ∀ a, decode (enc a) = a) (henc : ∀ a, enc a ≠ M.blank)
    (roles : Fin 4 ≃ Fin 4) (F : Fin 4 → STape (Fin k))
    (w : List Terminal) (junk : List (Fin k)) (x : SConfig Q (Fin k) t) :
    ∃ d, d ≤ w.length * B + 1 ∧
      ReplayLoopReplay.run M hB decode d (ReplayLoopReplay.lift roles F
        (TapeReplay.pack ⟨0, hB⟩ (TapeReplay.source M.blank (w.map enc) junk) x)) =
      ReplayLoopRecovery.lift (rotate.trans roles) (F (roles 0)) (w.foldl M.sRound x)
        ⟨fun _ => 0, ![TapeReplay.source M.blank [] ((w.map enc).reverse ++ junk),
          F (roles 1), F (roles 3)]⟩ := by
  obtain ⟨d, hd, hr⟩ := ReplayLoopReplay.batch_handoff M hB enc decode hdec henc roles F w junk x
  refine ⟨d, hd, ?_⟩
  rw [hr]
  have hh := replay_to_recovery roles F (TapeReplay.pack ⟨0, hB⟩
    (TapeReplay.source M.blank [] ((w.map enc).reverse ++ junk)) (w.foldl M.sRound x))
  simpa only [matcher, nextBuffers, TapeReplay.pack, TapeReplay.sourceAddr,
    TapeReplay.targetAddr, Equiv.symm_apply_apply] using hh

theorem source_lift_blankEq (blank : Fin k) (roles : Fin 4 ≃ Fin 4)
    (F : Fin 4 → STape (Fin k)) (p : Fin B) (x : SConfig Q (Fin k) t)
    (S U : STape (Fin k)) (h : STape.BlankEq blank S U) :
    ConfigBlankEq blank (ReplayLoopReplay.lift roles F (TapeReplay.pack p S x))
      (ReplayLoopReplay.lift roles F (TapeReplay.pack p U x)) := by
  refine ⟨rfl, ?_⟩
  intro j
  simp only [ReplayLoopReplay.lift, TapeReplay.pack, TapeReplay.sourceAddr,
    TapeReplay.targetAddr, Equiv.symm_apply_apply]
  cases hj : (finSumFinEquiv.symm j : Fin 4 ⊕ Fin t) with
  | inl i =>
    by_cases hi : i = roles 2
    · simpa only [hi, ↓reduceIte] using h
    · simp only [hi, ↓reduceIte]
      exact STape.BlankEq.refl _ _
  | inr i => exact STape.BlankEq.refl _ _

/-- The actual padded source returned by recovery can be replayed directly;
all next-cycle tapes satisfy the same observational contract. -/
theorem padded_batch_to_recovery (M : StructuredMachine Terminal Q (Fin k) t B) (hB : 0 < B)
    (enc : Terminal → Fin k) (decode : Fin k → Terminal)
    (hdec : ∀ a, decode (enc a) = a) (henc : ∀ a, enc a ≠ M.blank)
    (roles : Fin 4 ≃ Fin 4) (F : Fin 4 → STape (Fin k))
    (w : List Terminal) (junk : List (Fin k)) (x : SConfig Q (Fin k) t)
    (S : STape (Fin k)) (hS : STape.BlankEq M.blank S (TapeReplay.source M.blank (w.map enc) junk)) :
    ∃ d, d ≤ w.length * B + 1 ∧
      ConfigBlankEq M.blank
        (ReplayLoopReplay.run M hB decode d (ReplayLoopReplay.lift roles F (TapeReplay.pack ⟨0, hB⟩ S x)))
        (ReplayLoopRecovery.lift (rotate.trans roles) (F (roles 0)) (w.foldl M.sRound x)
          ⟨fun _ => 0, ![TapeReplay.source M.blank [] ((w.map enc).reverse ++ junk),
            F (roles 1), F (roles 3)]⟩) := by
  obtain ⟨d, hd, hr⟩ := batch_to_recovery M hB enc decode hdec henc roles F w junk x
  have hx := source_lift_blankEq M.blank roles F ⟨0, hB⟩ x S _ hS
  have hh := (worker M hB decode).microSteps_blankEq (List.replicate d none) hx
  change ConfigBlankEq M.blank (ReplayLoopReplay.run M hB decode d _)
    (ReplayLoopReplay.run M hB decode d _) at hh
  rw [hr] at hh
  exact ⟨d, hd, hh⟩

/-- One full recovery/replay/rotation cycle of the actual worker. The
next log is reusable, the next recovery buffers are correctly placed, and
the matcher has consumed the stored word in its original order. -/
theorem cycle (M : StructuredMachine Terminal Q (Fin k) t B) (hB : 0 < B)
    (enc : Terminal → Fin k) (decode : Fin k → Terminal)
    (hdec : ∀ a, decode (enc a) = a) (henc : ∀ a, enc a ≠ M.blank)
    (roles : Fin 4 ≃ Fin 4) (log : STape (Fin k)) (x : SConfig Q (Fin k) t)
    (old : List (Fin k)) (ho : M.blank ∉ old) (w : List Terminal)
    (T : Fin 3 → STape (Fin k))
    (h0 : T 0 = ⟨old.reverse ++ [M.blank], M.blank, []⟩)
    (h1 : T 1 = ⟨[M.blank], M.blank, []⟩)
    (h2 : T 2 = ⟨(w.map enc).reverse ++ [M.blank], M.blank, []⟩) :
    ∃ (d : ℕ) (U : Fin 3 → STape (Fin k)),
      d ≤ max old.length w.length + w.length * B + 4 ∧
      STape.BlankEq M.blank (U 0) ⟨[M.blank], M.blank, []⟩ ∧
      STape.BlankEq M.blank (U 1) ⟨[M.blank], M.blank, []⟩ ∧
      ConfigBlankEq M.blank
        (ReplayLoopReplay.run M hB decode d (ReplayLoopRecovery.lift roles log x ⟨fun _ => 0, T⟩))
        (ReplayLoopRecovery.lift (rotate.trans roles) (U 0) (w.foldl M.sRound x)
          ⟨fun _ => 0, ![TapeReplay.source M.blank [] ((w.map enc).reverse ++ [M.blank]), U 1, log]⟩) := by
  have hw : M.blank ∉ w.map enc := by
    intro h
    obtain ⟨a, _, ha⟩ := List.mem_map.mp h
    exact henc a ha
  obtain ⟨d₁, U, hd₁, hr₁, hU0, hU1, hU2⟩ :=
    ReplayLoopRecovery.buffers_handoff M hB decode roles log x old (w.map enc) ho hw T h0 h1 h2
  let F := recoveredBuffers roles log U
  obtain ⟨d₂, hd₂, hr₂⟩ := padded_batch_to_recovery M hB enc decode hdec henc
    roles F w [M.blank] x (U 2) hU2
  have hF0 : F (roles 0) = U 0 := by simp [F, recoveredBuffers]
  have hF1 : F (roles 1) = U 1 := by simp [F, recoveredBuffers]
  have hF3 : F (roles 3) = log := by simp [F, recoveredBuffers]
  rw [hF0, hF1, hF3] at hr₂
  simp only [List.length_map] at hd₁
  refine ⟨d₁ + d₂, U, by omega, hU0, hU1, ?_⟩
  have hadd (n m : ℕ) (z : SConfig (Control Q B) (Fin k) (4 + t)) :
      ReplayLoopReplay.run M hB decode (n + m) z =
        ReplayLoopReplay.run M hB decode m (ReplayLoopReplay.run M hB decode n z) := by
    simp only [ReplayLoopReplay.run, List.replicate_add, List.foldl_append]
  rw [hadd, hr₁, recovery_to_replay]
  exact hr₂

/-- info: 'PalPeg.ReplayLoopRotation.cycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cycle

/-- info: 'PalPeg.ReplayLoopRotation.padded_batch_to_recovery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms padded_batch_to_recovery

/-- info: 'PalPeg.ReplayLoopRotation.batch_to_recovery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms batch_to_recovery

end PalPeg.ReplayLoopRotation
