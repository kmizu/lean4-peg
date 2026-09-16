import PalPeg.TextFeedPipelineCoupled

/-! Identify the coupled ideal state with the existing 11-tape GS
interpreter. Its direction tape is the real persistent direction tape. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelineIdealEngine
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.TextFeedControl
open PalPeg.TextFeedPipelineFrames PalPeg.TextFeedPipelineCoupled
open PalPeg.TextFeedPipelineGuardAgreement PalPeg.VerifierFeedRefinement
variable {k : ℕ}

noncomputable def engine (e : Env k) : Interp Unit A C (Fin k) 11 :=
  GSVProgZLoop.interp e.blank e.endSym e.mark e.startSym

def bundle (I : GSVTapes.VTapes' k) (dir : STape (Fin k)) : Fin 11 → STape (Fin k) :=
  Fin.append (GSVProg.vTS I) (fun _ : Fin 1 => dir)

theorem eval_bundle (e : Env k) (I : GSVTapes.VTapes' k) (dir : STape (Fin k)) :
    evalConds (engine e) (fun j => (bundle I dir j).focus) = idealEval e I dir := by
  funext c
  cases c with
  | inl c =>
    change GSVProg.condOf10 e.endSym e.mark e.startSym c
      (fun j => (bundle I dir ((Fin.castAddEmb 1) j)).focus) = _
    apply congrArg (GSVProg.condOf10 e.endSym e.mark e.startSym c)
    funext j
    change (Fin.append (GSVProg.vTS I) (fun _ : Fin 1 => dir) (Fin.castAdd 1 j)).focus = _
    rw [Fin.append_left]
  | inr c => cases c <;> rfl

theorem bundle_action (e : Env k) (I : GSVTapes.VTapes' k) (dir : STape (Fin k)) (a : A) :
    (fun j => (bundle I dir j).applyAction e.blank
      ((engine e).actOf a none (fun j => (bundle I dir j).focus) j)) =
      bundle (idealNext e (.instruction a) I) (dirNext e (.instruction a) dir) := by
  cases a with
  | inl a =>
    have hv := actOf_transport (Fin.castAddEmb 1)
      (GSVProg.I10 (Terminal := Unit) e.blank e.endSym e.mark e.startSym) a none
      (GSVProg.vTS I) (bundle I dir)
    simp only [bundle, extend_castAdd_append] at hv
    have ht := applyAction_extend (Fin.castAddEmb 1) e.blank (GSVProg.vTS I) (bundle I dir)
      (actVec (GSVProg.I10 (Terminal := Unit) e.blank e.endSym e.mark e.startSym) a (GSVProg.vTS I))
    simp only [bundle, extend_castAdd_append] at ht
    change (fun j => (bundle I dir j).applyAction e.blank
      (((GSVProg.I10 (Terminal := Unit) e.blank e.endSym e.mark e.startSym).transport (Fin.castAddEmb 1)).actOf
        a none (fun j => (bundle I dir j).focus) j)) = _
    rw [show ((GSVProg.I10 (Terminal := Unit) e.blank e.endSym e.mark e.startSym).transport (Fin.castAddEmb 1)).actOf
      a none (fun j => (bundle I dir j).focus) = _ from hv]
    simp only [bundle, actVec] at ht ⊢
    rw [ht]
    simp only [idealNext, dirNext, stepTapes, VerifierFeedPrimitive.vTS_fromTapes]
    rfl
  | inr up =>
    have hv := actOf_transport (Fin.natAddEmb 10)
      (GSVProgZLoop.dirInterp (Terminal := Unit) e.blank e.mark) up none
      (fun _ : Fin 1 => dir) (bundle I dir)
    simp only [bundle, extend_natAdd_append] at hv
    have ht := applyAction_extend (Fin.natAddEmb 10) e.blank (fun _ : Fin 1 => dir) (bundle I dir)
      (actVec (GSVProgZLoop.dirInterp (Terminal := Unit) e.blank e.mark) up (fun _ : Fin 1 => dir))
    simp only [bundle, extend_natAdd_append] at ht
    change (fun j => (bundle I dir j).applyAction e.blank
      (((GSVProgZLoop.dirInterp (Terminal := Unit) e.blank e.mark).transport (Fin.natAddEmb 10)).actOf
        up none (fun j => (bundle I dir j).focus) j)) = _
    rw [show ((GSVProgZLoop.dirInterp (Terminal := Unit) e.blank e.mark).transport (Fin.natAddEmb 10)).actOf
      up none (fun j => (bundle I dir j).focus) = _ from hv]
    simp only [bundle, actVec] at ht ⊢
    rw [ht]
    rfl

theorem instruction_step (e : Env k) {u v : Snapshot k} (a : A)
    (h : Advance e u v (.instruction a)) :
    microStep (engine e) e.blank none (erase u.frames, bundle u.ideal u.dir) =
      (erase v.frames, bundle v.ideal v.dir) := by
  have hc : stepStack (idealEval e u.ideal u.dir) (erase u.frames) = (erase v.frames, some a) :=
    (ProgLangControlSteps.selected_iff _ _ _ _).mpr h.control
  simp only [microStep, eval_bundle, hc]
  rw [bundle_action, h.ideal, h.direction]

theorem silent_step (e : Env k) {u v : Snapshot k} (w : Event)
    (hw : ∀ a, w ≠ .instruction a) (h : Advance e u v w) :
    bundle u.ideal u.dir = bundle v.ideal v.dir ∧
      SEqAt (engine e) (bundle u.ideal u.dir) (erase u.frames) (erase v.frames) := by
  cases w with
  | instruction a => exact False.elim (hw a rfl)
  | feed1 | feed2 | idle | halt =>
    constructor
    · rw [h.ideal, h.direction]; rfl
    · unfold SEqAt
      rw [eval_bundle]
      exact h.control.dispatch

/-- Only genuine GS instructions consume an ideal interpreter step. -/
def semanticInputs : List Event → List (Option Unit)
  | [] => []
  | .instruction _ :: ws => none :: semanticInputs ws
  | _ :: ws => semanticInputs ws

/-- Endpoints allow only unexecuted pure control, exactly as the existing
GS Exec/RunsTo interface does. The final tapes must be equal, not equivalent. -/
def Ends (e : Env k) (l : List (Option Unit)) (s : Stack A C) (T : Fin 11 → STape (Fin k))
    (t : Stack A C) (U : Fin 11 → STape (Fin k)) : Prop :=
  ∃ r, runInputs (engine e) e.blank l (s, T) = (r, U) ∧ SEqAt (engine e) U r t

theorem Ends.congr_start {e : Env k} {l : List (Option Unit)} {s t r : Stack A C}
    {T U : Fin 11 → STape (Fin k)} (h : SEqAt (engine e) T s t)
    (hr : Ends e l t T r U) : Ends e l s T r U := by
  obtain ⟨s', he, hs⟩ := hr
  cases l with
  | nil =>
    change (t, T) = (s', U) at he
    obtain ⟨ht, hT⟩ := Prod.mk.inj he
    subst s'
    subst U
    exact ⟨s, rfl, h.trans hs⟩
  | cons x l =>
    exact ⟨s', (runInputs_congr h x l).trans he, hs⟩

/-- Erasing all queue and idle events yields a run of the original GS
interpreter with precisely the coupled final tapes and equivalent control. -/
theorem follows_engine (e : Env k) {u v : Snapshot k} {ws : List Event}
    (h : Follows e u ws v) :
    Ends e (semanticInputs ws) (erase u.frames) (bundle u.ideal u.dir)
      (erase v.frames) (bundle v.ideal v.dir) := by
  induction h with
  | nil u => exact ⟨erase u.frames, rfl, SEqAt.rfl' _ _ _⟩
  | stutter hf hi hd _ ih => simpa only [hf, hi, hd] using ih
  | @step u v z w ws had ht ih =>
    cases w with
    | instruction a =>
      obtain ⟨r, he, hr⟩ := ih
      refine ⟨r, ?_, hr⟩
      rw [semanticInputs, runInputs_cons, instruction_step e a had]
      exact he
    | feed1 | feed2 | idle | halt =>
      have hs := silent_step e _ (by intro a ha; cases ha) had
      apply Ends.congr_start hs.2
      rw [hs.1]
      exact ih

private theorem render_nil {fs : List Frame} (h : render (k := k) fs = []) : fs = [] := by
  cases fs with
  | nil => rfl
  | cons f fs => cases f <;> simp [render, renderFrame] at h

theorem next_halt_nil (ev : TextFeedPipelineControl.TaskCond k → Bool) (fs : List Frame)
    (h : (next ev fs).2 = .halt) : (next ev fs).1 = [] := by
  have he := next_render ev fs
  have hn : (stepStack ev (render fs)).2 = none := by rw [he, h]; rfl
  have ht := stepStack_snd_eq_none ev (render fs) hn
  rw [he] at ht
  exact render_nil ht

/-- A real return observation means the coupled ideal verifier is also
finished. The caller has not yet been dispatched by this theorem. -/
theorem halted_control {e : Env k} (leftSym : Fin k) (R rate : ℕ)
    {Text : List (Fin k)} {n : ℕ} (x : Config e leftSym R rate) (v : Snapshot k)
    (caller : Stack (TextFeedPipelineControl.TaskAct k) (TextFeedPipelineControl.TaskCond k))
    (hv : Valid e leftSym R rate Text n x v caller)
    (hmb : e.mark ≠ e.blank) (hb : e.blank ∉ Text) (hm : e.mark ∉ Text) (hn : n ≤ Text.length)
    (hw : (next (TextFeedPipelineControl.taskEval e (fun j => (x.2 j).focus)) v.frames).2 = .halt) :
    SEqAt (engine e) (bundle v.ideal v.dir) (erase v.frames) [] := by
  have hi := next_erase_physical v.qt1 v.mode1 v.qt2 v.mode2 v.aux v.old v.dir
    hv.refines hmb hb hm hn v.frames
  dsimp only at hi
  rw [← hv.physical, hw, next_halt_nil _ _ hw] at hi
  unfold SEqAt
  rw [eval_bundle]
  exact hi.dispatch

theorem follows_halted {e : Env k} (leftSym : Fin k) (R rate : ℕ)
    {Text : List (Fin k)} {n : ℕ} (x : Config e leftSym R rate) (u v : Snapshot k)
    (caller : Stack (TextFeedPipelineControl.TaskAct k) (TextFeedPipelineControl.TaskCond k))
    (hv : Valid e leftSym R rate Text n x v caller)
    (hmb : e.mark ≠ e.blank) (hb : e.blank ∉ Text) (hm : e.mark ∉ Text) (hn : n ≤ Text.length)
    {ws : List Event} (h : Follows e u ws v)
    (hw : (next (TextFeedPipelineControl.taskEval e (fun j => (x.2 j).focus)) v.frames).2 = .halt) :
    Ends e (semanticInputs ws) (erase u.frames) (bundle u.ideal u.dir) [] (bundle v.ideal v.dir) := by
  obtain ⟨r, he, hr⟩ := follows_engine e h
  exact ⟨r, he, hr.trans (halted_control leftSym R rate x v caller hv hmb hb hm hn hw)⟩

theorem semanticInputs_replicate (ws : List Event) :
    semanticInputs ws = List.replicate (semanticInputs ws).length none := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    cases w <;> simp [semanticInputs, List.replicate_succ, ← ih]

private theorem run_empty (e : Env k) (l : List (Option Unit)) (T : Fin 11 → STape (Fin k)) :
    runInputs (engine e) e.blank l ([], T) = ([], T) := by
  induction l with
  | nil => rfl
  | cons x l ih => simpa only [runInputs_cons, microStep_nil] using ih

theorem halted_preserves (e : Env k) (l : List (Option Unit))
    (s : Stack A C) (T : Fin 11 → STape (Fin k)) (h : SEqAt (engine e) T s []) :
    (runInputs (engine e) e.blank l (s, T)).2 = T := by
  cases l with
  | nil => rfl
  | cons x l =>
    have hm : microStep (engine e) e.blank x (s, T) = ([], T) := by
      unfold SEqAt at h
      simp only [microStep, h, stepStack_nil]
    rw [runInputs_cons, hm, run_empty]

/-- Two terminating runs of the same old interpreter have exactly the
same final tapes, even if their step-count descriptions differ. -/
theorem Ends.unique {e : Env k} {m n : ℕ} {s : Stack A C}
    {T U V : Fin 11 → STape (Fin k)}
    (hu : Ends e (List.replicate m none) s T [] U)
    (hv : Ends e (List.replicate n none) s T [] V) : U = V := by
  obtain ⟨su, hru, hsu⟩ := hu
  obtain ⟨sv, hrv, hsv⟩ := hv
  have hU : (runInputs (engine e) e.blank (List.replicate (m + n) none) (s, T)).2 = U := by
    rw [List.replicate_add, runInputs_append, hru]
    exact halted_preserves e _ su U hsu
  have hV : (runInputs (engine e) e.blank (List.replicate (m + n) none) (s, T)).2 = V := by
    rw [Nat.add_comm m n, List.replicate_add, runInputs_append, hrv]
    exact halted_preserves e _ sv V hsv
  exact hU.symm.trans hV

/-- Connect the compiled endpoint to an existing GS RunsTo theorem. This
does not assume that queue/wait overhead equals the old GS step count. -/
theorem Ends.result_of_runsTo {e : Env k} {p : GSVProgZLoop.DProg}
    {T U V : Fin 11 → STape (Fin k)} {m cost : ℕ}
    (h : Ends e (List.replicate m none) [p] T [] V)
    (hr : GSVProgZLoop.RunsTo (engine e) e.blank p T U cost) : V = U := by
  obtain ⟨acts, he, hU, hc⟩ := hr
  obtain ⟨_, r, hrun, hctrl⟩ := he [] (List.replicate cost none) (by simp only [List.length_replicate, hc])
  rw [hU] at hrun hctrl
  have hu : Ends e (List.replicate cost none) [p] T [] U := ⟨r, by simpa using hrun, hctrl⟩
  exact h.unique hu

/-- info: 'PalPeg.TextFeedPipelineIdealEngine.instruction_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms instruction_step

/-- info: 'PalPeg.TextFeedPipelineIdealEngine.follows_engine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms follows_engine

/-- info: 'PalPeg.TextFeedPipelineIdealEngine.follows_halted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms follows_halted

/-- info: 'PalPeg.TextFeedPipelineIdealEngine.Ends.result_of_runsTo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Ends.result_of_runsTo

end PalPeg.TextFeedPipelineIdealEngine
