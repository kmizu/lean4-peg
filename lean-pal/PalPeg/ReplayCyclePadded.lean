import PalPeg.ReplayLoopRotation

set_option autoImplicit false
namespace PalPeg.ReplayCyclePadded
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ReplayLoop
variable {Terminal Q : Type} [Fintype Q] [DecidableEq Q] {k t B : ℕ}

theorem lift_blankEq (blank : Fin k) (roles : Fin 4 ≃ Fin 4) (log : STape (Fin k))
    (x : SConfig Q (Fin k) t) (T U : Fin 3 → STape (Fin k))
    (h : ∀ i, STape.BlankEq blank (T i) (U i)) :
    ConfigBlankEq blank (ReplayLoopRecovery.lift (B := B) roles log x ⟨fun _ => 0, T⟩)
      (ReplayLoopRecovery.lift roles log x ⟨fun _ => 0, U⟩) := by
  refine ⟨rfl, ?_⟩
  intro j
  simp only [ReplayLoopRecovery.lift]
  cases hj : (finSumFinEquiv.symm j : Fin 4 ⊕ Fin t) with
  | inl i =>
    by_cases hi : (roles.symm i).val < 3
    · simpa only [hi, ↓reduceDIte] using h ⟨(roles.symm i).val, hi⟩
    · simp only [hi, ↓reduceDIte]
      exact STape.BlankEq.refl _ _
  | inr i => exact STape.BlankEq.refl _ _

/-- Recovered buffers are used as they physically stand. No exact empty
tape or removal of trailing blanks is assumed at the next cycle's start. -/
theorem cycle (M : StructuredMachine Terminal Q (Fin k) t B) (hB : 0 < B)
    (enc : Terminal → Fin k) (decode : Fin k → Terminal)
    (hdec : ∀ a, decode (enc a) = a) (henc : ∀ a, enc a ≠ M.blank)
    (roles : Fin 4 ≃ Fin 4) (log : STape (Fin k)) (x : SConfig Q (Fin k) t)
    (old : List (Fin k)) (ho : M.blank ∉ old) (w : List Terminal)
    (T : Fin 3 → STape (Fin k))
    (h0 : STape.BlankEq M.blank (T 0) ⟨old.reverse ++ [M.blank], M.blank, []⟩)
    (h1 : STape.BlankEq M.blank (T 1) ⟨[M.blank], M.blank, []⟩)
    (h2 : STape.BlankEq M.blank (T 2) ⟨(w.map enc).reverse ++ [M.blank], M.blank, []⟩) :
    ∃ (d : ℕ) (U : Fin 3 → STape (Fin k)),
      d ≤ max old.length w.length + w.length * B + 4 ∧
      STape.BlankEq M.blank (U 0) ⟨[M.blank], M.blank, []⟩ ∧
      STape.BlankEq M.blank (U 1) ⟨[M.blank], M.blank, []⟩ ∧
      ConfigBlankEq M.blank
        (ReplayLoopReplay.run M hB decode d (ReplayLoopRecovery.lift roles log x ⟨fun _ => 0, T⟩))
        (ReplayLoopRecovery.lift (rotate.trans roles) (U 0) (w.foldl M.sRound x)
          ⟨fun _ => 0, ![TapeReplay.source M.blank [] ((w.map enc).reverse ++ [M.blank]), U 1, log]⟩) := by
  let A : Fin 3 → STape (Fin k) := ![⟨old.reverse ++ [M.blank], M.blank, []⟩,
    ⟨[M.blank], M.blank, []⟩, ⟨(w.map enc).reverse ++ [M.blank], M.blank, []⟩]
  have ha : ∀ i, STape.BlankEq M.blank (T i) (A i) := by
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  obtain ⟨d, U, hd, hu0, hu1, hr⟩ :=
    ReplayLoopRotation.cycle M hB enc decode hdec henc roles log x old ho w A rfl rfl rfl
  have hh := (worker M hB decode).microSteps_blankEq (List.replicate d none)
    (lift_blankEq (B := B) M.blank roles log x T A ha)
  refine ⟨d, U, hd, hu0, hu1, hh.1.trans hr.1, ?_⟩
  intro j
  exact (hh.2 j).trans (hr.2 j)

/-- info: 'PalPeg.ReplayCyclePadded.cycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cycle

end PalPeg.ReplayCyclePadded
