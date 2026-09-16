import PalPeg.TextFeedPipelinePrepFinish

/-! Instantiate physical preparation completion with the actual finite
decomposition/setup program and its scanner/verifier representation. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelinePrepSetup
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangBank PalPeg.TextFeedControl PalPeg.PrepInstance PalPeg.PatternTapes PalPeg.PatternProg
open PalPeg.RTQueue
open PalPeg.TextFeedPipelineBank PalPeg.TextFeedPipelineControl PalPeg.TextFeedPipelinePrepWindow
open PalPeg.TextFeedPipelinePrepInput PalPeg.TextFeedPipelinePrepFinish

variable {k : ℕ} {Terminal : Type}

noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (Outer e leftSym R rate) := Classical.decEq _

/-- The source cost is linear in the stage length. Any actual arrival
word covering that many preparation calls reaches the proved setup tapes
and the prefix continuation, without assuming an externally prepared state. -/
theorem setup_finishes {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (enc : Terminal → Fin k) (R rate : ℕ)
    (c : CallCtrl (programs e) (Outer e leftSym R rate)) (T : Fin 39 → STape (Fin k))
    (hb : AtBoundary (programs e) c.2.2.1) (hc0 : c.1.1 = 0)
    {q₁ q₂ : Queue (Fin k)} {old : Fin k} (h : QueuesAt e c.1.2.1 T q₁ q₂ old)
    (hs : c.1.2.2.val = [task e leftSym rate]) {S : PatternTapes.Tapes k}
    (hv : prepView T = TSg S) {w Text : List (Fin k)} {L : ℕ}
    (hpre : StageTapes.PrepPre e.blank e.mark leftSym L w Text S)
    (hstart : e.startSym ∉ PrepInstances.stagePat w L)
    (hend : e.endSym ∉ PrepInstances.stagePat w L) (hne : e.startSym ≠ e.endSym) :
    let d := PrepInstances.prepRes w L
    ∃ ticks S', ticks ≤ (GSPreProg.preprocessSlope + 25 + 7 * rate) * L +
        GSPreProg.preprocessOffset + 37 + 11 * rate ∧
      GSVTapes.VEncodes' e.blank e.startSym e.endSym e.mark
        ((w.take L).reverse.take d.1) ((w.take L).reverse.drop d.1)
        (TextFeed.padW e.blank Text 0) rate d.2.1 d.2.2 (toGS S', toVExt S') (⟨0, 0⟩, 0) ∧
      ∀ (word : List Terminal) (a : Terminal) (J : ℕ), J ≤ R → ticks = word.length * R + J →
        (∀ b ∈ word ++ [a], enc b ≠ e.mark) →
        ∃ c' T', finishAt e leftSym enc R rate word a J { state := ((c, 0), 0), tape := T } =
            { state := ((c', 0), phase R J), tape := T' } ∧
          prepView T' = TSg S' ∧ AtBoundary (programs e) c'.2.2.1 ∧
          ReadyAt e T' (snoc (word.foldl (fun q b => snoc q (enc b)) q₁) (enc a))
            (snoc (word.foldl (fun q b => snoc q (enc b)) q₂) (enc a)) (enc a) ∧ c'.1.2.1 = false ∧
          stepStack (taskEval e (fun j => (T' j).focus)) c'.1.2.2.val =
            stepStack (taskEval e (fun j => (T' j).focus)) [liftPrefix TextFeedPrefixAtomic.source, afterPrefix rate] := by
  dsimp only
  obtain ⟨tr, S', he, ht, hv', hn⟩ := finitePrepSetup_exec (Terminal := Unit) rate hmb hpre hstart hend hne
  refine ⟨tr.length, S', hn, hv', ?_⟩
  intro word a J hJ hlen hall
  have hs' : ControlEq c.1.2.2.val
      [finitePrepSetup e.blank e.startSym e.endSym leftSym e.mark rate] [afterPrep rate] := by
    rw [hs]
    exact control_initial e leftSym rate
  obtain ⟨c', T', hz, hp, hb', hq, hf, hctrl⟩ := finish_at hc hmb leftSym enc R rate J hJ c T hb hc0 h
    (finitePrepSetup e.blank e.startSym e.endSym leftSym e.mark rate) [afterPrep rate] (TSg S) hv hs' tr he word a hlen hall
  refine ⟨c', T', hz, hp.trans ht, hb', hq, hf, ?_⟩
  rw [afterPrep, stepStack_seq] at hctrl
  exact hctrl

/-- info: 'PalPeg.TextFeedPipelinePrepSetup.setup_finishes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms setup_finishes

end PalPeg.TextFeedPipelinePrepSetup
