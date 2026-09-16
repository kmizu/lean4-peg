import PalPeg.TextFeedPipelinePrepFrames
import PalPeg.ProgLangCallFramePrefix

/-! Physical completion of preparation at an internal frame boundary.
The pipeline is not required to idle for the unused part of that frame. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelinePrepFinish
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangPersist2 PalPeg.ProgLangBank PalPeg.TextFeedControl PalPeg.PrepInstance
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.TextFeedPipelineBank PalPeg.TextFeedPipelineControl PalPeg.TextFeedPipelinePrepWindow
open PalPeg.TextFeedPipelinePrepInput PalPeg.TextFeedPipelinePrepFrames
open PalPeg.TextFeedPrepResume (source)

variable {k : ℕ} {Terminal : Type}

noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (Outer e leftSym R rate) := Classical.decEq _

abbrev Config (e : Env k) (leftSym : Fin k) (R rate : ℕ) :=
  SConfig ((CallCtrl (programs e) (Outer e leftSym R rate) × Fin 94) × Fin ((R + 1) * 94 + 1)) (Fin k) 39

def phase (R J : ℕ) : Fin ((R + 1) * 94 + 1) := nextPhase^[(J + 1) * 94 + 1] 0

noncomputable def finishAt (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k) (R rate : ℕ)
    (word : List Terminal) (a : Terminal) (J : ℕ) (x : Config e leftSym R rate) : Config e leftSym R rate :=
  (some a :: List.replicate ((J + 1) * 94) none).foldl (machine e leftSym enc R rate).sMicroStep
    (word.foldl (machine e leftSym enc R rate).sRound x)

theorem machine_partial (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k) (R rate J : ℕ) (hJ : J ≤ R)
    (c : CallCtrl (programs e) (Outer e leftSym R rate)) (T : Fin 39 → STape (Fin k)) (a : Terminal) :
    (some a :: List.replicate ((J + 1) * 94) none).foldl (machine e leftSym enc R rate).sMicroStep
      { state := ((c, 0), 0), tape := T } =
      let y := (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[J + 1]
        (c, arriveA e.blank (DualQueueShared.capture enc) (some a) T)
      { state := ((y.1, 0), phase R J), tape := y.2 } :=
  callFrameMachine_prefix (programs e) (fun _ => TextFeedPipelineControl.interp e) (choose e leftSym R rate)
    93 (R + 1) (J + 1) (by omega) e.blank (by omega) (0, true, startCtrlS (task e leftSym rate))
    (encode (.prefix .idle)) (DualQueueShared.capture enc) a c T

/-- Given any finite source execution, the actual arrival-bearing machine
reaches its exact endpoint after full frames plus one partial frame.
Both FIFO words include every input so far, including the final arrival. -/
theorem finish_at {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (enc : Terminal → Fin k) (R rate J : ℕ) (hJ : J ≤ R)
    (c : CallCtrl (programs e) (Outer e leftSym R rate)) (T : Fin 39 → STape (Fin k))
    (hb : AtBoundary (programs e) c.2.2.1) (hc0 : c.1.1 = 0)
    {q₁ q₂ : Queue (Fin k)} {old : Fin k} (h : QueuesAt e c.1.2.1 T q₁ q₂ old)
    (p : Prog (PrepAct k) (PrepCond k)) (r : Stack (TaskAct k) (TaskCond k))
    (P : Fin 15 → STape (Fin k)) (hv : prepView T = P) (hs : ControlEq c.1.2.2.val [p] r)
    (tr : List (Fin 15 → Fin k × Move)) (he : Exec (source e) e.blank p P tr)
    (word : List Terminal) (a : Terminal) (hlen : tr.length = word.length * R + J)
    (hall : ∀ b ∈ word ++ [a], enc b ≠ e.mark) :
    ∃ c' T', finishAt e leftSym enc R rate word a J { state := ((c, 0), 0), tape := T } =
        { state := ((c', 0), phase R J), tape := T' } ∧
      prepView T' = applyTrace e.blank P tr ∧ AtBoundary (programs e) c'.2.2.1 ∧
      ReadyAt e T' (snoc (word.foldl (fun q b => snoc q (enc b)) q₁) (enc a))
        (snoc (word.foldl (fun q b => snoc q (enc b)) q₂) (enc a)) (enc a) ∧ c'.1.2.1 = false ∧
      stepStack (taskEval e (fun j => (T' j).focus)) c'.1.2.2.val =
        stepStack (taskEval e (fun j => (T' j).focus)) r := by
  have hlive := TextFeedPrepHandoff.exec_live_prefix e p P tr he tr.length (Nat.le_refl _)
  rw [hlen] at hlive
  obtain ⟨hpre, htail⟩ := TextFeedPrepFrames.live_split e [p] P (word.length * R) J hlive
  obtain ⟨c1, T1, hz1, hv1, hb1, hr1, hs1, hc1⟩ := busy_frames hc hmb leftSym enc R rate word c T hb hc0 h
    [p] r P hv hs hpre (fun b hb => hall b (List.mem_append_left _ hb))
  obtain ⟨c2, T2, hz2, hv2, hb2, hr2, hs2, _, hf2⟩ := busy_calls hc hmb leftSym enc R rate J hJ c1 T1 hb1 hc1 hr1
    a (hall a (List.mem_append_right _ List.mem_cons_self))
    (runInputs (source e) e.blank (List.replicate (word.length * R) none) ([p], P)).1 r
    (runInputs (source e) e.blank (List.replicate (word.length * R) none) ([p], P)).2 hv1 hs1 htail
  have hcomp : runInputs (source e) e.blank (List.replicate J none)
      (runInputs (source e) e.blank (List.replicate (word.length * R) none) ([p], P)) =
      runInputs (source e) e.blank (List.replicate tr.length none) ([p], P) := by
    rw [hlen, List.replicate_add, runInputs_append]
  simp only [Prod.mk.eta] at hv2 hs2
  rw [hcomp] at hv2 hs2
  obtain ⟨hout, hreturn⟩ := TextFeedPrepHandoff.exec_endpoint e p P tr he
  refine ⟨c2, T2, ?_, hv2.trans hout, hb2, hr2, hf2, ?_⟩
  · rw [finishAt, hz1, machine_partial e leftSym enc R rate J hJ, hz2]
  · have hreturn' : (stepStack (evalConds (source e) (fun j => (prepView T2 j).focus))
        (runInputs (source e) e.blank (List.replicate tr.length none) ([p], P)).1).2 = none := by
      rw [hv2]
      exact hreturn
    have hmap : stepStack (taskEval e (fun j => (T2 j).focus))
        ((runInputs (source e) e.blank (List.replicate tr.length none) ([p], P)).1.map liftPrep ++ r) =
        stepStack (taskEval e (fun j => (T2 j).focus)) r :=
      (step_sim_map Sum.inl Sum.inl (evalConds (source e) (fun j => (prepView T2 j).focus))
        (taskEval e (fun j => (T2 j).focus)) (fun _ => rfl) _ r).2 hreturn'
    exact (hs2 _).trans hmap

/-- info: 'PalPeg.TextFeedPipelinePrepFinish.finish_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finish_at

end PalPeg.TextFeedPipelinePrepFinish
