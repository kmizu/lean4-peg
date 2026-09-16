import PalPeg.TextFeedPipelineOutputBudget

/-! The direction cell has no moving head, even outside reachable source
states. Its empty left and right sides are an implementation invariant. -/
set_option autoImplicit false
namespace PalPeg.TextFeedPipelineDirection
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang
open PalPeg.ProgLangPersist PalPeg.ProgLangPersist2 PalPeg.ProgLangBank
open PalPeg.TextFeedControl PalPeg.TextFeedPipelineBank
variable {k : ℕ} {Terminal : Type}

noncomputable local instance : DecidableEq (TextFeedPipelineControl.TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineControl.TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (TextFeedPipelineControl.Outer e leftSym R rate) := Classical.decEq _

theorem prep_omits : proj prepSlot (38 : Fin 39) = none := by
  apply proj_eq_none
  intro i hi
  have hh := congrArg Fin.val hi
  change 11 + i.val = 38 at hh
  have := i.isLt
  omega

theorem verify_omits : proj verifySlot (38 : Fin 39) = none := by
  apply proj_eq_none
  intro i hi
  have hh := congrArg Fin.val hi
  have := i.isLt
  change (if h : i.val < 11 then (⟨i.val + 27, by omega⟩ : Fin 39) else ⟨i.val, by omega⟩).val = 38 at hh
  split_ifs at hh <;> dsimp at hh <;> omega

theorem prefix_omits : proj (Fin.castAddEmb 19 : Fin 20 ↪ Fin 39) 38 = none := by
  apply proj_eq_none
  intro i hi
  have hh := congrArg Fin.val hi
  change i.val = 38 at hh
  have := i.isLt
  omega

theorem act_stay (e : Env k) (a : TextFeedPipelineBank.Act k)
    (input : Option Terminal) (σ : Fin 39 → Fin k) :
    ((interp e).actOf a input σ 38).2 = .stay := by
  rcases a with (a | a) | (a | (a | up))
  · simp only [interp, TextFeedPrefixBank.interp, DualQueueShared.interp,
      Interp.transport, DualQueueShared.reserved_omitted (j := 38) (Or.inr rfl)]
  · simp only [interp, TextFeedPrefixBank.interp, TextFeedPrefixReady.interp,
      Interp.transport, prefix_omits]
  · simp only [interp, Interp.transport, prep_omits]
  · simp only [interp, Interp.transport, verify_omits]
  · have hp : proj dirSlot (38 : Fin 39) = some 0 := proj_ι dirSlot 0
    simp only [interp, Interp.transport, hp, GSVProgZLoop.dirInterp]

def Cell (T : STape (Fin k)) : Prop := ∃ a, T = ⟨[], a, []⟩

theorem cell_action (e : Env k) {T : STape (Fin k)} (h : Cell T)
    (v : Fin k × Move) (hv : v.2 = .stay) : Cell (T.applyAction e.blank v) := by
  obtain ⟨a, rfl⟩ := h
  obtain ⟨b, m⟩ := v
  cases hv
  exact ⟨b, rfl⟩

theorem cell_dir (e : Env k) {T : STape (Fin k)} (h : Cell T) :
    T.applyAction e.blank (e.mark, .stay) = GSVProgZLoop.dirTape e.blank e.mark true 0 := by
  obtain ⟨a, rfl⟩ := h
  rfl

theorem micro_cell (e : Env k) (input : Option Terminal)
    (x : Stack (TextFeedPipelineBank.Act k) (TextFeedPipelineBank.Cond k) × (Fin 39 → STape (Fin k)))
    (h : Cell (x.2 38)) : Cell ((microStep (interp e) e.blank input x).2 38) := by
  dsimp only [microStep]
  cases ha : (stepStack (evalConds (interp (Terminal := Terminal) e) (fun j => (x.2 j).focus)) x.1).2
  · exact h
  · exact cell_action e h _ (act_stay e _ input _)

open TextFeedPipelineControl (Index programs)

theorem chunk_cell (e : Env k) (i : Index k) (inputs : List (Option Terminal))
    (x : (Bank (programs e) × Bool) × (Fin 39 → STape (Fin k)))
    (h : Cell (x.2 38)) :
    Cell ((runChunk (programs e) (fun _ => TextFeedPipelineControl.interp e) e.blank i inputs x).2 38) := by
  induction inputs generalizing x with
  | nil => exact h
  | cons a inputs ih => exact ih _ (micro_cell e a ((x.1.1 i).val, x.2) h)

theorem run_cell (e : Env k) (leftSym : Fin k) (R rate : ℕ)
    (x : TextFeedPipelineOutput.Core e leftSym R rate × (Fin 39 → STape (Fin k)))
    (h : Cell (x.2 38)) :
    Cell ((TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x).2 38) := by
  dsimp only [TextFeedPipelineControl.run, callRun]
  apply chunk_cell
  unfold restartDone
  split <;> exact h

theorem sample_cell (e : Env k) (leftSym : Fin k) (R rate : ℕ)
    (x : TextFeedPipelineOutput.State e leftSym R rate × (Fin 39 → STape (Fin k)))
    (h : Cell (x.2 38)) :
    Cell ((TextFeedPipelineOutput.sample e leftSym R rate x).2 38) := by
  have hn : ∀ ρ, (38 : Fin 39) ≠ TextFeedPipelineReport.frontIdx ρ := by
    intro ρ hh
    have he := congrArg Fin.val hh
    have hl : (TextFeedPipelineReport.frontIdx ρ).val < 10 := (PalPeg.RTQueueProg.ridx ρ).isLt
    omega
  unfold TextFeedPipelineOutput.sample
  split
  · simpa only [TextFeedPipelineReport.reader_round, TextFeedPipelineReport.restore,
      TextFeedPipelineReport.probe, if_neg (hn _)] using h
  · exact h

theorem step_cell (e : Env k) (leftSym : Fin k) (R rate : ℕ)
    (x : TextFeedPipelineOutput.State e leftSym R rate × (Fin 39 → STape (Fin k)))
    (h : Cell (x.2 38)) :
    Cell ((TextFeedPipelineOutput.step (Terminal := Terminal) e leftSym R rate x).2 38) := by
  apply sample_cell
  exact run_cell e leftSym R rate _ h

theorem steps_cell (e : Env k) (leftSym : Fin k) (R rate N : ℕ)
    (x : TextFeedPipelineOutput.State e leftSym R rate × (Fin 39 → STape (Fin k)))
    (h : Cell (x.2 38)) :
    Cell (((TextFeedPipelineOutput.step (Terminal := Terminal) e leftSym R rate)^[N] x).2 38) := by
  induction N with
  | zero => exact h
  | succ N ih =>
    rw [Function.iterate_succ_apply']
    exact step_cell e leftSym R rate _ ih

theorem capture_cell (e : Env k) (enc : Terminal → Fin k) (a : Option Terminal)
    (T : Fin 39 → STape (Fin k)) (h : Cell (T 38)) :
    Cell (arriveA e.blank (DualQueueShared.capture enc) a T 38) := by
  change Cell ((T 38).applyAction e.blank _)
  apply cell_action e h
  simp only [DualQueueShared.capture, Interp.transport,
    DualQueueShared.reserved_omitted (j := 38) (Or.inr rfl)]

theorem rounds_cell (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k) (R rate : ℕ)
    (word : List Terminal) (q : TextFeedPipelineOutput.State e leftSym R rate)
    (T : Fin 39 → STape (Fin k)) (h : Cell (T 38)) :
    let y := word.foldl (TextFeedPipelineOutput.machine e leftSym enc R rate).sRound ⟨((q, 0), 0), T⟩
    y.state.1.2 = 0 ∧ y.state.2 = 0 ∧ Cell (y.tape 38) := by
  induction word generalizing q T with
  | nil => exact ⟨rfl, rfl, h⟩
  | cons a word ih =>
    simp only [List.foldl_cons, TextFeedPipelineOutput.machine_round]
    exact ih _ _ (steps_cell e leftSym R rate (R + 1) _ (capture_cell e enc (some a) T h))

/-- Every real preparation/prefix endpoint has a canonical one-cell
direction tape after the fixed direction write; no extra premise is needed. -/
theorem finishAt_dir (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k)
    (R rate J : ℕ) (hJ : J ≤ R)
    (q : TextFeedPipelineOutput.State e leftSym R rate) (T : Fin 39 → STape (Fin k)) (h : Cell (T 38))
    (word : List Terminal) (a : Terminal) :
    ((TextFeedPipelineOutputPrepFinish.finishAt e leftSym enc R rate word a J
      ⟨((q, 0), 0), T⟩).tape 38).applyAction e.blank (e.mark, .stay) =
      GSVProgZLoop.dirTape e.blank e.mark true 0 := by
  apply cell_dir
  let y := word.foldl (TextFeedPipelineOutput.machine e leftSym enc R rate).sRound
    ⟨((q, 0), 0), T⟩
  obtain ⟨h₁, h₂, hs⟩ := rounds_cell e leftSym enc R rate word q T h
  have hy : y = ⟨((y.state.1.1, 0), 0), y.tape⟩ := by
    have he : y.state = ((y.state.1.1, 0), 0) := Prod.ext (Prod.ext rfl h₁) h₂
    rw [← he]
  change Cell (((some a :: List.replicate ((J + 1) * 96) none).foldl
    (TextFeedPipelineOutput.machine e leftSym enc R rate).sMicroStep y).tape 38)
  rw [hy, TextFeedPipelineOutputPrepFinish.machine_partial e leftSym enc R rate J hJ]
  exact steps_cell e leftSym R rate (J + 1) _ (capture_cell e enc (some a) y.tape hs)

/-- info: 'PalPeg.TextFeedPipelineDirection.finishAt_dir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finishAt_dir
end PalPeg.TextFeedPipelineDirection
