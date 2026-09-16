import PalPeg.TextFeedPipelinePrefixResume

/-! A prefix beginning midway through a real frame reaches a physical
return event without restarting the frame or resetting either clock. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelinePrefixPartial
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangPersist2 PalPeg.ProgLangBank PalPeg.TextFeedControl
open PalPeg.TextFeedPipelineBank PalPeg.TextFeedPipelineControl
open PalPeg.TextFeedPipelinePrefixLink PalPeg.TextFeedPipelinePrefixWindow
open PalPeg.TextFeedPipelinePrefixFrames PalPeg.TextFeedPipelinePrefixHit PalPeg.TextFeedPrefixRank
open PalPeg.TextFeedPipelinePrefixResume PalPeg.TextFeedPipelinePrefixPhysical

variable {k : ℕ} {Terminal : Type}

noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (Outer e leftSym R rate) := Classical.decEq _

theorem reach_from_partial {e : Env k} {u v Text : List (Fin k)} {d p r n fuel : ℕ}
    (enc : Terminal → Fin k) {leftSym : Fin k} {R rate : ℕ} {z : State k} {x : Phys e leftSym R rate}
    (h : Safe e u Text) (hz : x.1.1.1 = 0) (a : Terminal) (J : ℕ) (hJ : J ≤ R)
    (hl : Link e leftSym R rate z ((TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[J]
      (input e enc leftSym R rate a x)))
    (hg : Good e u v Text d p r (n + 1) fuel (erase z))
    (hR : 0 < R) (waiting running : List Terminal)
    (hw : TextFeedPrefixDeadline.Valid Text (n + 1) (waiting.map enc))
    (hr : TextFeedPrefixDeadline.Valid Text (n + 1 + waiting.length) (running.map enc))
    (hroom : u.length ≤ n + 1 + waiting.length) (hbudget : 5 * u.length + 2 ≤ running.length * R) :
    Hit e enc leftSym R rate u v Text d p r n (a :: (waiting ++ running)) x := by
  have hrem := after_input_remaining enc hz a J hJ
  rcases resume_after_wait enc h hl hg hR waiting running hw hr hroom hbudget with
    ⟨K, hK, hl', hg'⟩ | hh
  · rw [hrem] at hK
    apply Hit.within (J := K + J) (by omega)
    · simpa only [Function.iterate_add_apply] using hl'
    · exact hg'
  · apply Hit.next
    rw [hrem] at hh
    simpa only [← Function.iterate_add_apply, Nat.sub_add_cancel hJ, frame] using hh

theorem physical_from_partial {e : Env k} {u v Text : List (Fin k)} {d p r n fuel : ℕ}
    (enc : Terminal → Fin k) {leftSym : Fin k} {R rate : ℕ} {z : State k} {x : Phys e leftSym R rate}
    (h : Safe e u Text) (hz : x.1.1.1 = 0) (a : Terminal) (J : ℕ) (hJ : J ≤ R)
    (hl : Link e leftSym R rate z ((TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[J]
      (input e enc leftSym R rate a x)))
    (hg : Good e u v Text d p r (n + 1) fuel (erase z))
    (hR : 0 < R) (waiting running : List Terminal)
    (hw : TextFeedPrefixDeadline.Valid Text (n + 1) (waiting.map enc))
    (hr : TextFeedPrefixDeadline.Valid Text (n + 1 + waiting.length) (running.map enc))
    (hroom : u.length ≤ n + 1 + waiting.length) (hbudget : 5 * u.length + 2 ≤ running.length * R) :
    Witness e enc leftSym R rate u v Text d p r n (a :: (waiting ++ running)) x :=
  hit_witness (reach_from_partial enc h hz a J hJ hl hg hR waiting running hw hr hroom hbudget)

/-- info: 'PalPeg.TextFeedPipelinePrefixPartial.physical_from_partial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms physical_from_partial

end PalPeg.TextFeedPipelinePrefixPartial
