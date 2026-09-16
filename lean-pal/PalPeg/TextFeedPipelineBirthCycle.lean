import PalPeg.TextFeedPipelineBirthRestore

set_option autoImplicit false
namespace PalPeg.TextFeedPipelineBirthCycle
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.TextFeedControl PalPeg.TextFeedInit
variable {k : ℕ}
abbrev Control := Fin 3 ⊕ Fin 3

/-- Source termination automatically hands the borrowed head to restoration.
The accepting bit denotes seed readiness, not PAL acceptance. -/
noncomputable def machine (e : Env k) (leftSym : Fin k) :
    StructuredMachine Unit Control (Fin k) 40 1 where
  tapeCount_pos := by decide
  blank := e.blank
  initial := .inl 0
  accepting := fun q => q == .inr 2
  micro := fun q a σ => match q with
    | .inl p => if p = 2 then (.inr 0, fun j => (σ j, .stay)) else
        let d := (TextFeedPipelineBirthSource.machine e leftSym).micro p a σ
        (.inl d.1, d.2)
    | .inr p =>
        let d := (TextFeedPipelineBirthRestore.machine e.blank).micro p a σ
        (.inr d.1, d.2)

noncomputable def run (e : Env k) (l : Fin k) (n : ℕ) (x : SConfig Control (Fin k) 40) :=
  (List.replicate n ()).foldl (machine e l).sRound x
def copying (x : SConfig (Fin 3) (Fin k) 40) : SConfig Control (Fin k) 40 := ⟨.inl x.state, x.tape⟩
def restoring (x : SConfig (Fin 3) (Fin k) 40) : SConfig Control (Fin k) 40 := ⟨.inr x.state, x.tape⟩

theorem run_add (e : Env k) (l : Fin k) (n m : ℕ) (x : SConfig Control (Fin k) 40) :
    run e l (n + m) x = run e l m (run e l n x) := by
  simp only [run, List.replicate_add, List.foldl_append]

theorem copy_round (e : Env k) (l : Fin k) (x : SConfig (Fin 3) (Fin k) 40) (h : x.state ≠ 2) :
    (machine e l).sRound (copying x) () = copying ((TextFeedPipelineBirthSource.machine e l).sRound x ()) := by
  simp only [StructuredMachine.sRound, Speedup.MultiStepMachine.roundInputs,
    Nat.sub_self, List.replicate_zero, List.foldl_cons, List.foldl_nil,
    StructuredMachine.sMicroStep, machine, copying, h, ↓reduceIte]
  rfl

theorem switch_round (e : Env k) (l : Fin k) (T : Fin 40 → STape (Fin k)) :
    (machine e l).sRound (copying ⟨2, T⟩) () = restoring ⟨0, T⟩ := by
  simp only [StructuredMachine.sRound, Speedup.MultiStepMachine.roundInputs,
    Nat.sub_self, List.replicate_zero, List.foldl_cons, List.foldl_nil,
    StructuredMachine.sMicroStep, machine, copying, restoring, ↓reduceIte]
  rfl

theorem restore_round (e : Env k) (l : Fin k) (x : SConfig (Fin 3) (Fin k) 40) :
    (machine e l).sRound (restoring x) () = restoring ((TextFeedPipelineBirthRestore.machine e.blank).sRound x ()) := by
  simp only [StructuredMachine.sRound, Speedup.MultiStepMachine.roundInputs,
    Nat.sub_self, List.replicate_zero, List.foldl_cons, List.foldl_nil,
    StructuredMachine.sMicroStep, machine, restoring]
  rfl

theorem restore_run (e : Env k) (l : Fin k) (n : ℕ) (x : SConfig (Fin 3) (Fin k) 40) :
    run e l n (restoring x) = restoring (TextFeedPipelineBirthRestore.run e.blank n x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    change run e l n ((machine e l).sRound (restoring x) ()) = _
    rw [restore_round, ih]
    rfl

theorem copy_run (e : Env k) (l : Fin k) (n : ℕ) (x : SConfig (Fin 3) (Fin k) 40)
    (h : ∀ i, i < n → (TextFeedPipelineBirthSource.run e l i x).state ≠ 2) :
    run e l n (copying x) = copying (TextFeedPipelineBirthSource.run e l n x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    change run e l n ((machine e l).sRound (copying x) ()) = _
    rw [copy_round e l x (h 0 (by omega)), ih]
    · rfl
    · intro i hi
      exact h (i + 1) (by omega)

theorem handoff (e : Env k) (l : Fin k) (n : ℕ) (x : SConfig (Fin 3) (Fin k) 40)
    (h : (TextFeedPipelineBirthSource.run e l n x).state = 2) :
    ∃ t, t ≤ n ∧ run e l (t + 1) (copying x) =
      restoring ⟨0, (TextFeedPipelineBirthSource.run e l n x).tape⟩ := by
  have hex : ∃ t, (TextFeedPipelineBirthSource.run e l t x).state = 2 := ⟨n, h⟩
  let t := Nat.find hex
  have ht : (TextFeedPipelineBirthSource.run e l t x).state = 2 := Nat.find_spec hex
  have hn : t ≤ n := Nat.find_min' hex h
  have hp : ∀ i, i < t → (TextFeedPipelineBirthSource.run e l i x).state ≠ 2 := by
    intro i hi
    exact Nat.find_min hex hi
  have he : TextFeedPipelineBirthSource.run e l n x = TextFeedPipelineBirthSource.run e l t x := by
    rw [show n = t + (n - t) by omega, TextFeedPipelineBirthSource.run_add]
    have hx : TextFeedPipelineBirthSource.run e l t x = ⟨2, (TextFeedPipelineBirthSource.run e l t x).tape⟩ := by rw [← ht]
    rw [hx]
    have hd (m : ℕ) (T : Fin 40 → STape (Fin k)) :
        TextFeedPipelineBirthSource.run e l m ⟨2, T⟩ = ⟨2, T⟩ := by
      induction m with
      | zero => rfl
      | succ m ih =>
        change TextFeedPipelineBirthSource.run e l m
          ((TextFeedPipelineBirthSource.machine e l).sRound ⟨2, T⟩ ()) = _
        have hr : (TextFeedPipelineBirthSource.machine e l).sRound ⟨2, T⟩ () = ⟨2, T⟩ := by
          simp only [StructuredMachine.sRound, Speedup.MultiStepMachine.roundInputs,
            Nat.sub_self, List.replicate_zero, List.foldl_cons, List.foldl_nil,
            StructuredMachine.sMicroStep, TextFeedPipelineBirthSource.machine, ↓reduceIte]
          rfl
        rw [hr, ih]
    exact hd _ _
  refine ⟨t, hn, ?_⟩
  rw [run_add, copy_run e l t x hp, he]
  have hx : TextFeedPipelineBirthSource.run e l t x = ⟨2, (TextFeedPipelineBirthSource.run e l t x).tape⟩ := by rw [← ht]
  rw [hx]
  exact switch_round e l _

/-- A complete autonomous copy/restore pass terminates within twice the
prefix length plus five ticks, with both the seed and history preserved. -/
theorem ready (e : Env k) (l : Fin k) (w : List (Fin k)) (hw : e.blank ∉ w) :
    ∃ n, n ≤ 2 * w.length + 5 ∧
      run e l n (copying (TextFeedPipelineBirthSource.pack 0
        (HistoryConcat.source e.blank w [e.blank]) (blankBundle e.blank 39))) =
      restoring (TextFeedPipelineBirthSource.pack 2
        (HistoryConcat.source e.blank (w ++ [e.blank]) [e.blank])
        (TextFeedPipelineOutputBirth.seed e l w w.length 0)) := by
  let x := TextFeedPipelineBirthSource.pack 0
    (HistoryConcat.source e.blank w [e.blank]) (blankBundle e.blank 39)
  have hc := TextFeedPipelineBirthSource.seed_from_source e l w [e.blank] hw
  have hs : (TextFeedPipelineBirthSource.run e l (w.length + 2) x).state = 2 := by
    rw [hc]
    rfl
  obtain ⟨t, ht, hh⟩ := handoff e l (w.length + 2) x hs
  refine ⟨(t + 1) + (w.length + 2), by omega, ?_⟩
  change run e l ((t + 1) + (w.length + 2)) (copying x) = _
  rw [run_add, hh, hc, restore_run]
  change restoring (TextFeedPipelineBirthRestore.run e.blank (w.length + 2)
    (TextFeedPipelineBirthSource.pack 0
      (HistoryConcat.source e.blank [] (w.reverse ++ [e.blank]))
      (TextFeedPipelineOutputBirth.seed e l w w.length 0))) = _
  rw [TextFeedPipelineBirthRestore.restored e.blank w hw]

theorem done_run (e : Env k) (l : Fin k) (n : ℕ) (T : Fin 40 → STape (Fin k)) :
    run e l n (restoring ⟨2, T⟩) = restoring ⟨2, T⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change run e l n ((machine e l).sRound (restoring ⟨2, T⟩) ()) = _
    have hr : (machine e l).sRound (restoring ⟨2, T⟩) () = restoring ⟨2, T⟩ := by
      rw [restore_round]
      simp only [StructuredMachine.sRound, Speedup.MultiStepMachine.roundInputs,
        Nat.sub_self, List.replicate_zero, List.foldl_cons, List.foldl_nil,
        StructuredMachine.sMicroStep, TextFeedPipelineBirthRestore.machine,
        HistoryRewind.machine, show (2 : Fin 3) ≠ 0 by decide, ↓reduceIte]
      congr 1
      congr 1
      funext j
      cases h : (finSumFinEquiv.symm j : Fin 1 ⊕ Fin 39) with
      | inl a =>
        have ha : a = 0 := Subsingleton.elim _ _
        have hj : j = TextFeedPipelineBirthSource.sourceAddr := by
          apply (finSumFinEquiv : Fin 1 ⊕ Fin 39 ≃ Fin 40).symm.injective
          simpa [TextFeedPipelineBirthSource.sourceAddr, ha] using h
        subst j
        rfl
      | inr a => rfl
    rw [hr, ih]

theorem ready_at (e : Env k) (l : Fin k) (w : List (Fin k)) (hw : e.blank ∉ w)
    (n : ℕ) (hn : 2 * w.length + 5 ≤ n) :
    run e l n (copying (TextFeedPipelineBirthSource.pack 0
      (HistoryConcat.source e.blank w [e.blank]) (blankBundle e.blank 39))) =
    restoring (TextFeedPipelineBirthSource.pack 2
      (HistoryConcat.source e.blank (w ++ [e.blank]) [e.blank])
      (TextFeedPipelineOutputBirth.seed e l w w.length 0)) := by
  obtain ⟨t, ht, hr⟩ := ready e l w hw
  rw [show n = t + (n - t) by omega, run_add, hr]
  exact done_run e l (n - t) _

/-- info: 'PalPeg.TextFeedPipelineBirthCycle.ready_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ready_at

/-- info: 'PalPeg.TextFeedPipelineBirthCycle.ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ready

end PalPeg.TextFeedPipelineBirthCycle
