import PalPeg.TextFeedPipelinePrefixSetup
import PalPeg.TextFeedPipelinePrefixFedPhysical

/-! Actual initial prep through the verifier-ready physical prefix return. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelinePrefixFedSetup
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangBank PalPeg.TextFeedControl
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.PatternTapes PalPeg.PatternProg
open PalPeg.TextFeedPipelineBank PalPeg.TextFeedPipelineControl PalPeg.TextFeedPipelinePrepInput
open PalPeg.TextFeedPipelinePrefixLink PalPeg.TextFeedPipelinePrefixWindow
open PalPeg.TextFeedPipelinePrefixPrepared PalPeg.TextFeedPipelinePrefixSetup
open PalPeg.TextFeedPipelinePrefixReserve PalPeg.TextFeedPipelinePrefixFedHit
open PalPeg.TextFeedPrefixDeadline (Valid)

variable {k : ℕ} {Terminal : Type}

theorem setup_ready {e : Env k} (leftSym : Fin k) (enc : Terminal → Fin k) (R rate : ℕ)
    (x : Phys e leftSym R rate) (hb : AtBoundary (programs e) x.1.2.2.1) (hz : x.1.1.1 = 0)
    {q₁ q₂ : Queue (Fin k)} {old : Fin k} (hq : QueuesAt e x.1.1.2.1 x.2 q₁ q₂ old)
    (hs : x.1.1.2.2.val = [task e leftSym rate]) {S : PatternTapes.Tapes k}
    (hv : prepView x.2 = TSg S) {w Text : List (Fin k)} {L n : ℕ}
    (hpre : StageTapes.PrepPre e.blank e.mark leftSym L w Text S)
    (h : Safe e (PrepInstances.stagePat w L) Text)
    (hi₁ : Inv q₁) (hl₁ : toList q₁ = Text.take n) (hi₂ : Inv q₂) (hl₂ : toList q₂ = Text.take n)
    (hR : 0 < R) :
    let d := PrepInstances.prepRes w L
    let u := (w.take L).reverse.take d.1
    let v := (w.take L).reverse.drop d.1
    ∃ ticks, ticks ≤ (GSPreProg.preprocessSlope + 25 + 7 * rate) * L +
        GSPreProg.preprocessOffset + 37 + 11 * rate ∧
      ∀ (before : List Terminal) (a : Terminal) (J : ℕ), J ≤ R → ticks = before.length * R + J →
        Valid Text n ((before ++ [a]).map enc) →
        ∀ (waiting running : List Terminal),
          Valid Text (n + before.length + 1) (waiting.map enc) →
          Valid Text (n + before.length + 1 + waiting.length) (running.map enc) →
          u.length ≤ n + before.length + 1 + waiting.length →
          5 * u.length + 2 ≤ running.length * R →
          TextFeedPipelinePrefixFedPhysical.Witness e enc leftSym R rate u v Text rate d.2.1 d.2.2 n
            (before ++ a :: (waiting ++ running)) x := by
  dsimp only
  obtain ⟨ticks, S', ht, hve, hfinish⟩ := TextFeedPipelinePrepSetup.setup_finishes h.code h.mark_blank
    leftSym enc R rate x.1 x.2 hb hz hq hs hv hpre h.start_u h.end_u h.start_end
  refine ⟨ticks, ht, ?_⟩
  intro before a J hJ he hvalid waiting running hw hr hroom hbudget
  have hall : ∀ b ∈ before ++ [a], enc b ≠ e.mark := by
    intro b hmem heq
    exact h.mark_text (heq ▸ valid_mem hvalid (enc b) (List.mem_map.mpr ⟨b, hmem, rfl⟩))
  obtain ⟨c', T', hf, hp, hb', hq', hfirst, hctrl⟩ := hfinish before a J hJ he hall
  have hlist₁ := TextFeedPipelinePrepReady.arrivals_contents enc hi₁ hl₁ before a hvalid
  have hlist₂ := TextFeedPipelinePrepReady.arrivals_contents enc hi₂ hl₂ before a hvalid
  obtain ⟨z, hlink, hg, hQ, hX⟩ := TextFeedPipelinePrefixEndpoint.ready_to_prefix
    (x := (c', T')) hp hq' hlist₁ hb' hfirst hctrl hve
  have hreserve : Reserve e Text (n + before.length + 1) z := by
    obtain ⟨_, _, _, _, _, _, _, _, h₂, _⟩ := hlink
    exact ⟨h₂.inv, hQ ▸ hlist₂, hX⟩
  have hy := endpoint_eq (y := (c', T')) enc before a J hJ hf
  rw [← hy] at hlink
  apply TextFeedPipelinePrefixFedPhysical.hit_witness
  apply TextFeedPipelinePrefixFedHit.prepend before (a :: (waiting ++ running))
  exact TextFeedPipelinePrefixFedHit.reach_from_partial enc (safe_take h (PrepInstances.prepRes w L).1)
    (rounds_counter enc before x hz) a J hJ hlink hg hreserve hR waiting running hw hr hroom hbudget

/-- info: 'PalPeg.TextFeedPipelinePrefixFedSetup.setup_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms setup_ready

end PalPeg.TextFeedPipelinePrefixFedSetup
