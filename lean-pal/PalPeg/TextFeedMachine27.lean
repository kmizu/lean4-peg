import PalPeg.TextFeedUnpadded

/-! Execute the feeder on the same 27 physical tapes as preparation.
The seven remaining preprocessing/verifier tapes are never touched. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPrepare
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang
open PalPeg.TextFeedControl PalPeg.TextFeedInput PalPeg.TextFeedSchedule

variable {k B : ℕ} {Q Terminal : Type} [Fintype Q] [DecidableEq Q]

noncomputable def on27 (M : StructuredMachine Terminal Q (Fin k) 20 B) :
    StructuredMachine Terminal Q (Fin k) 27 B where
  tapeCount_pos := by omega
  blank := M.blank
  initial := M.initial
  accepting := M.accepting
  micro q a σ :=
    let r := M.micro q a (fun i => σ (feedSlot i))
    (r.1, fun j => match proj feedSlot j with
      | some i => r.2 i
      | none => (σ j, .stay))

def viewConfig (x : SConfig Q (Fin k) 27) : SConfig Q (Fin k) 20 :=
  ⟨x.state, feedView x.tape⟩

/-- One physical transition is exactly the existing feeder transition
on its selected tapes. The clock bound and finite control are unchanged. -/
theorem on27_micro_view (M : StructuredMachine Terminal Q (Fin k) 20 B)
    (x : SConfig Q (Fin k) 27) (a : Option Terminal) :
    viewConfig ((on27 M).sMicroStep x a) = M.sMicroStep (viewConfig x) a := by
  unfold viewConfig StructuredMachine.sMicroStep on27 feedView
  dsimp only
  congr 1
  funext i
  simp only [proj_ι]

theorem on27_micro_rest (M : StructuredMachine Terminal Q (Fin k) 20 B)
    (x : SConfig Q (Fin k) 27) (a : Option Terminal) (j : Fin 27)
    (hj : ∀ i, feedSlot i ≠ j) :
    ((on27 M).sMicroStep x a).tape j = x.tape j := by
  have hp := proj_eq_none feedSlot hj
  simp only [StructuredMachine.sMicroStep, on27, hp]
  rfl

theorem on27_microSteps_view (M : StructuredMachine Terminal Q (Fin k) 20 B)
    (l : List (Option Terminal)) (x : SConfig Q (Fin k) 27) :
    viewConfig (l.foldl (on27 M).sMicroStep x) = l.foldl M.sMicroStep (viewConfig x) := by
  induction l generalizing x with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldl_cons, ih, on27_micro_view]

theorem on27_microSteps_rest (M : StructuredMachine Terminal Q (Fin k) 20 B)
    (l : List (Option Terminal)) (x : SConfig Q (Fin k) 27) (j : Fin 27)
    (hj : ∀ i, feedSlot i ≠ j) :
    (l.foldl (on27 M).sMicroStep x).tape j = x.tape j := by
  induction l generalizing x with
  | nil => rfl
  | cons a l ih =>
    exact (ih _).trans (on27_micro_rest M x a j hj)

theorem on27_round_view (M : StructuredMachine Terminal Q (Fin k) 20 B)
    (x : SConfig Q (Fin k) 27) (a : Terminal) :
    viewConfig ((on27 M).sRound x a) = M.sRound (viewConfig x) a :=
  on27_microSteps_view M _ x

theorem on27_run_view (M : StructuredMachine Terminal Q (Fin k) 20 B)
    (input : List Terminal) (x : SConfig Q (Fin k) 27) :
    viewConfig (input.foldl (on27 M).sRound x) = input.foldl M.sRound (viewConfig x) := by
  induction input generalizing x with
  | nil => rfl
  | cons a input ih => simp only [List.foldl_cons, ih, on27_round_view]

/-- All seven auxiliary tapes survive an arbitrarily long input stream. -/
theorem on27_run_aux (M : StructuredMachine Terminal Q (Fin k) 20 B)
    (input : List Terminal) (x : SConfig Q (Fin k) 27) (j : Fin 27)
    (hlo : 19 ≤ j.val) (hhi : j.val < 26) :
    (input.foldl (on27 M).sRound x).tape j = x.tape j := by
  have hj : ∀ i, feedSlot i ≠ j := by
    intro i he
    have hh := congrArg Fin.val he
    by_cases hi : i.val < 19 <;> simp [feedSlot, hi] at hh <;> omega
  induction input generalizing x with
  | nil => rfl
  | cons a input ih =>
    exact (ih _).trans (on27_microSteps_rest M _ x j hj)

noncomputable local instance : DecidableEq (AP k ⊕ Empty) := Classical.decEq _
noncomputable local instance : DecidableEq (CT k ⊕ Fin k) := Classical.decEq _
noncomputable local instance (R rate : ℕ) : DecidableEq (Outer R rate) := Classical.decEq _

/-- The actual feeder on the preparation layout: no tape copy or reset. -/
noncomputable def feeder27 (e : Env k) (enc : Terminal → Fin k) (R rate : ℕ) :=
  on27 (TextFeedSchedule.machine e enc R rate)

noncomputable def run27 (e : Env k) (enc : Terminal → Fin k) (R rate : ℕ)
    (T : Fin 27 → STape (Fin k)) (input : List Terminal) :=
  input.foldl (feeder27 e enc R rate).sRound
    { state := ((TextFeedInit.initialCtrl e R rate, ⟨0, by omega⟩), ⟨0, by omega⟩), tape := T }

/-- The real 27-tape run inherits the previously proved continuous feeder
semantics, with precisely the prepared physical tapes as its starting point. -/
theorem run27_view (e : Env k) (enc : Terminal → Fin k) (R rate : ℕ)
    (T : Fin 27 → STape (Fin k)) (input : List Terminal) :
    viewConfig (run27 e enc R rate T input) =
      TextFeedRefine.preparedRun e enc R rate (TextFeedInit.initialCtrl e R rate, feedView T) input :=
  on27_run_view (TextFeedSchedule.machine e enc R rate) input _

/-- The unpadded output of prepare_unpadded can be used directly on the
27-tape machine; its view agrees observationally with the certified feeder. -/
theorem run27_blank_view (e : Env k) (enc : Terminal → Fin k) (R rate : ℕ)
    {T U : Fin 27 → STape (Fin k)} (h : ∀ j, STape.BlankEq e.blank (T j) (U j))
    (input : List Terminal) :
    ConfigBlankEq e.blank (viewConfig (run27 e enc R rate T input))
      (TextFeedRefine.preparedRun e enc R rate (TextFeedInit.initialCtrl e R rate, feedView U) input) := by
  rw [run27_view]
  exact future_blankEq e enc R rate h input []

theorem run27_aux (e : Env k) (enc : Terminal → Fin k) (R rate : ℕ)
    (T : Fin 27 → STape (Fin k)) (input : List Terminal) (j : Fin 27)
    (hlo : 19 ≤ j.val) (hhi : j.val < 26) :
    (run27 e enc R rate T input).tape j = T j :=
  on27_run_aux (TextFeedSchedule.machine e enc R rate) input _ j hlo hhi

/-- info: 'PalPeg.TextFeedPrepare.on27_run_view' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms on27_run_view

/-- info: 'PalPeg.TextFeedPrepare.on27_run_aux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms on27_run_aux

/-- info: 'PalPeg.TextFeedPrepare.run27_blank_view' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run27_blank_view

end PalPeg.TextFeedPrepare
