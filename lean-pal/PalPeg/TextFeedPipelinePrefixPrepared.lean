import PalPeg.TextFeedPipelinePrefixPartial

/-! The physical prep endpoint is enough to invoke the prefix deadline,
including all earlier prep inputs and the partially used final frame. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelinePrefixPrepared
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangPersist2 PalPeg.ProgLangBank PalPeg.TextFeedControl
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.PatternTapes PalPeg.PatternProg
open PalPeg.TextFeedPipelineBank PalPeg.TextFeedPipelineControl PalPeg.TextFeedPipelinePrepInput
open PalPeg.TextFeedPipelinePrefixLink PalPeg.TextFeedPipelinePrefixWindow
open PalPeg.TextFeedPipelinePrefixFrames PalPeg.TextFeedPipelinePrefixHit PalPeg.TextFeedPrefixRank
open PalPeg.TextFeedPipelinePrefixPhysical PalPeg.TextFeedPipelinePrefixPartial
open PalPeg.TextFeedPipelinePrepFinish (phase finishAt)

variable {k : ℕ} {Terminal : Type}

noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (Outer e leftSym R rate) := Classical.decEq _

theorem rounds_pack (e : Env k) (enc : Terminal → Fin k) (leftSym : Fin k) (R rate : ℕ)
    (word : List Terminal) (x : Phys e leftSym R rate) :
    word.foldl (machine e leftSym enc R rate).sRound (pack x 0) =
      pack (word.foldl (fun x a => frame e enc leftSym R rate a x) x) 0 := by
  induction word generalizing x with
  | nil => rfl
  | cons a w ih => simpa only [List.foldl_cons, round_pack] using ih (frame e enc leftSym R rate a x)

theorem rounds_counter {e : Env k} (enc : Terminal → Fin k) {leftSym : Fin k} {R rate : ℕ}
    (word : List Terminal) (x : Phys e leftSym R rate) (hz : x.1.1.1 = 0) :
    (word.foldl (fun x a => frame e enc leftSym R rate a x) x).1.1.1 = 0 := by
  induction word generalizing x with
  | nil => exact hz
  | cons a w ih => exact ih _ (frame_counter enc hz a)

theorem endpoint_eq {e : Env k} (enc : Terminal → Fin k) {leftSym : Fin k} {R rate : ℕ}
    (before : List Terminal) (a : Terminal) (J : ℕ) (hJ : J ≤ R) {x y : Phys e leftSym R rate}
    (he : finishAt e leftSym enc R rate before a J (pack x 0) = pack y (phase R J)) :
    (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[J]
      (input e enc leftSym R rate a (before.foldl (fun x a => frame e enc leftSym R rate a x) x)) = y := by
  have hh := partial_pack e enc leftSym R rate J hJ a
    (before.foldl (fun x a => frame e enc leftSym R rate a x) x)
  rw [finishAt, rounds_pack] at he
  change finishAt e leftSym enc R rate [] a J
    (pack (before.foldl (fun x a => frame e enc leftSym R rate a x) x) 0) = _ at he
  rw [hh] at he
  exact congrArg (fun c => (c.state.1.1, c.tape)) he

theorem prepared_deadline {e : Env k} {u v Text : List (Fin k)} {n p r R rate : ℕ}
    (enc : Terminal → Fin k) {leftSym : Fin k} {x y : Phys e leftSym R rate}
    (h : Safe e u Text) (hz : x.1.1.1 = 0) (before : List Terminal) (a : Terminal) (J : ℕ) (hJ : J ≤ R)
    (he : finishAt e leftSym enc R rate before a J (pack x 0) = pack y (phase R J))
    {S : PatternTapes.Tapes k} {q₁ q₂ : Queue (Fin k)} {old : Fin k}
    (hp : prepView y.2 = TSg S) (hq : ReadyAt e y.2 q₁ q₂ old)
    (hl : toList q₁ = Text.take (n + before.length + 1))
    (hb : AtBoundary (programs e) y.1.2.2.1) (hf : y.1.1.2.1 = false)
    (hs : stepStack (taskEval e (fun j => (y.2 j).focus)) y.1.1.2.2.val =
      stepStack (taskEval e (fun j => (y.2 j).focus)) [liftPrefix TextFeedPrefixAtomic.source, afterPrefix rate])
    (hv : GSVTapes.VEncodes' e.blank e.startSym e.endSym e.mark u v (TextFeed.padW e.blank Text 0)
      rate p r (toGS S, toVExt S) (⟨0, 0⟩, 0))
    (hR : 0 < R) (waiting running : List Terminal)
    (hw : TextFeedPrefixDeadline.Valid Text (n + before.length + 1) (waiting.map enc))
    (hr : TextFeedPrefixDeadline.Valid Text (n + before.length + 1 + waiting.length) (running.map enc))
    (hroom : u.length ≤ n + before.length + 1 + waiting.length)
    (hbudget : 5 * u.length + 2 ≤ running.length * R) :
    Witness e enc leftSym R rate u v Text rate p r n (before ++ a :: (waiting ++ running)) x := by
  obtain ⟨z, hlink, hg, _, _⟩ := TextFeedPipelinePrefixEndpoint.ready_to_prefix hp hq hl hb hf hs hv
  have hy := endpoint_eq enc before a J hJ he
  rw [← hy] at hlink
  apply hit_witness
  apply prepend before (a :: (waiting ++ running))
  exact reach_from_partial enc h (rounds_counter enc before x hz) a J hJ hlink hg hR waiting running hw hr hroom hbudget

/-- info: 'PalPeg.TextFeedPipelinePrefixPrepared.prepared_deadline' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prepared_deadline

end PalPeg.TextFeedPipelinePrefixPrepared
