import PalPeg.TextFeedPipelineOutputPrefixFrames

/-! Concrete preparation through the observed prefix deadline, retaining
the actual captures, observer state, tapes and both machine clocks. -/
set_option autoImplicit false
namespace PalPeg.TextFeedPipelineOutputPrefixSetup
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangBank PalPeg.TextFeedControl
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.PatternTapes PalPeg.PatternProg
open PalPeg.TextFeedPipelineBank PalPeg.TextFeedPipelineControl PalPeg.TextFeedPipelinePrepInput
open PalPeg.TextFeedPipelineOutputPrepFinish
open PalPeg.TextFeedPipelineOutputPrefixFrames

variable {k : ℕ} {Terminal : Type}
noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (Outer e leftSym R rate) := Classical.decEq _

theorem setup_reaches {e : Env k} (leftSym : Fin k) (enc : Terminal → Fin k) (R rate : ℕ)
    (c : TextFeedPipelineOutput.Core e leftSym R rate) (T : Fin 39 → STape (Fin k))
    (hb : AtBoundary (programs e) c.2.2.1) (hz : c.1.1 = 0)
    {q₁ q₂ : Queue (Fin k)} {old : Fin k} (hq : QueuesAt e c.1.2.1 T q₁ q₂ old)
    (hs : c.1.2.2.val = [task e leftSym rate]) {S : PatternTapes.Tapes k}
    (hv : prepView T = TSg S) {w Text : List (Fin k)} {L n : ℕ}
    (hpre : StageTapes.PrepPre e.blank e.mark leftSym L w Text S)
    (h : TextFeedPipelinePrefixWindow.Safe e (PrepInstances.stagePat w L) Text)
    (hi₁ : Inv q₁) (hl₁ : toList q₁ = Text.take n)
    (hi₂ : Inv q₂) (hl₂ : toList q₂ = Text.take n) (ρ : Role) (bit : Bool) (hR : 0 < R) :
    let d := PrepInstances.prepRes w L
    let u := (w.take L).reverse.take d.1
    let v := (w.take L).reverse.drop d.1
    ∃ ticks, ticks ≤ (GSPreProg.preprocessSlope + 25 + 7 * rate) * L +
        GSPreProg.preprocessOffset + 37 + 11 * rate ∧
      ∀ (before : List Terminal) (a : Terminal) (J : ℕ), J ≤ R → ticks = before.length * R + J →
        TextFeedPrefixDeadline.Valid Text n ((before ++ [a]).map enc) →
        ∀ (waiting running : List Terminal),
          n + before.length + 1 + waiting.length + running.length ≤ Text.length →
          (∀ j b, waiting[j]? = some b → Text[n + before.length + 1 + j]? = some (enc b)) →
          (∀ j b, running[j]? = some b →
            Text[n + before.length + 1 + waiting.length + j]? = some (enc b)) →
          u.length ≤ n + before.length + 1 + waiting.length + 1 →
          5 * u.length + 2 ≤ running.length * R →
          Reached e leftSym enc R rate u v Text rate d.2.1 d.2.2 n
            (before ++ a :: (waiting ++ running)) ⟨(((c, ρ, bit), 0), 0), T⟩ := by
  dsimp only
  obtain ⟨ticks, ht, hfinish⟩ := setup_prefix leftSym enc R rate c T hb hz hq hs hv hpre
    h hi₁ hl₁ hi₂ hl₂ ρ bit
  refine ⟨ticks, ht, ?_⟩
  intro before a J hJ he hvalid waiting running hn hw ha hroom hbudget
  obtain ⟨z, hl, hg, hr, _, _⟩ := hfinish before a J hJ he hvalid
  obtain ⟨hz', h96, hout⟩ := rounds_clocks enc before
    (⟨(((c, ρ, bit), 0), 0), T⟩ : Config e leftSym R rate) hz rfl rfl
  apply prepend before (a :: (waiting ++ running))
  exact reaches_from_partial enc _
    (TextFeedPipelinePrefixSetup.safe_take h (PrepInstances.prepRes w L).1)
    hz' h96 hout a J hJ hl hg hr hR waiting running hn hw ha hroom hbudget

/-- info: 'PalPeg.TextFeedPipelineOutputPrefixSetup.setup_reaches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms setup_reaches
end PalPeg.TextFeedPipelineOutputPrefixSetup
