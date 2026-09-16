import PalPeg.TextFeedPipelinePrefixPrepared

/-! Initial preparation through physical prefix return on one pipeline. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelinePrefixSetup
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangBank PalPeg.TextFeedControl
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.PatternTapes PalPeg.PatternProg
open PalPeg.TextFeedPipelineBank PalPeg.TextFeedPipelineControl PalPeg.TextFeedPipelinePrepInput
open PalPeg.TextFeedPipelinePrefixLink PalPeg.TextFeedPipelinePrefixWindow
open PalPeg.TextFeedPipelinePrefixPhysical PalPeg.TextFeedPipelinePrefixPrepared
open PalPeg.TextFeedPrefixDeadline (Valid)

variable {k : ℕ} {Terminal : Type}

theorem valid_mem {Text w : List (Fin k)} {n : ℕ} (h : Valid Text n w) :
    ∀ a ∈ w, a ∈ Text := by
  induction h with
  | nil _ => simp
  | cons ha ht ih =>
    intro a hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact List.mem_of_getElem? ha
    · exact ih a hm

theorem safe_take {e : Env k} {u Text : List (Fin k)} (h : Safe e u Text) (N : ℕ) :
    Safe e (u.take N) Text :=
  ⟨h.code, h.mark_blank, h.blank_text, h.mark_text,
    fun hm => h.end_u (List.mem_of_mem_take hm),
    fun hm => h.start_u (List.mem_of_mem_take hm), h.start_end⟩

theorem setup_prefix {e : Env k} (leftSym : Fin k) (enc : Terminal → Fin k) (R rate : ℕ)
    (x : Phys e leftSym R rate) (hb : AtBoundary (programs e) x.1.2.2.1) (hz : x.1.1.1 = 0)
    {q₁ q₂ : Queue (Fin k)} {old : Fin k} (hq : QueuesAt e x.1.1.2.1 x.2 q₁ q₂ old)
    (hs : x.1.1.2.2.val = [task e leftSym rate]) {S : PatternTapes.Tapes k}
    (hv : prepView x.2 = TSg S) {w Text : List (Fin k)} {L n : ℕ}
    (hpre : StageTapes.PrepPre e.blank e.mark leftSym L w Text S)
    (h : Safe e (PrepInstances.stagePat w L) Text) (hi : Inv q₁) (hl : toList q₁ = Text.take n)
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
          Witness e enc leftSym R rate u v Text rate d.2.1 d.2.2 n
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
  have hlist := TextFeedPipelinePrepReady.arrivals_contents enc hi hl before a hvalid
  exact prepared_deadline (y := (c', T')) enc (safe_take h (PrepInstances.prepRes w L).1) hz before a J hJ hf hp hq' hlist hb' hfirst hctrl hve
    hR waiting running hw hr hroom hbudget

/-- info: 'PalPeg.TextFeedPipelinePrefixSetup.setup_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms setup_prefix

end PalPeg.TextFeedPipelinePrefixSetup
