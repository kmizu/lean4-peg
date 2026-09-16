import PalPeg.TextFeedPipelinePrefixEndpoint

/-! Consume only the remaining calls of a partially completed input frame. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelinePrefixResume
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangPersist2 PalPeg.ProgLangBank PalPeg.TextFeedControl
open PalPeg.TextFeedPipelineBank PalPeg.TextFeedPipelineControl
open PalPeg.TextFeedPipelinePrefixLink PalPeg.TextFeedPipelinePrefixWindow
open PalPeg.TextFeedPipelinePrefixFrames PalPeg.TextFeedPipelinePrefixHit PalPeg.TextFeedPrefixRank

variable {k : ℕ} {Terminal : Type}

theorem nextPhase_finish {B : ℕ} (N : ℕ) (p : Fin B) (hs : p.val + N = B) :
    nextPhase^[N] p = ⟨0, Nat.zero_lt_of_lt p.isLt⟩ := by
  induction N generalizing p with
  | zero => have := p.isLt; omega
  | succ N ih =>
    rw [Function.iterate_succ_apply]
    by_cases hN : N = 0
    · subst N
      simp only [Function.iterate_zero, id_eq]
      simp [nextPhase, show ¬ p.val + 1 < B by omega]
    · apply ih
      have hp : p.val + 1 < B := by omega
      simp only [nextPhase, dif_pos hp]
      omega

def remaining {e : Env k} {leftSym : Fin k} {R rate : ℕ} (x : Phys e leftSym R rate) : ℕ :=
  if x.1.1.1 = 0 then 0 else R + 1 - x.1.1.1.val

noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (Outer e leftSym R rate) := Classical.decEq _

theorem remaining_window {e : Env k} {leftSym : Fin k} {R rate : ℕ} (x : Phys e leftSym R rate) :
    (remaining x ≠ 0 → 0 < x.1.1.1.val) ∧ x.1.1.1.val + remaining x ≤ R + 1 ∧
      ((TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[remaining x] x).1.1.1 = 0 := by
  by_cases hz : x.1.1.1 = 0
  · simp [remaining, hz]
  · have hp := x.1.1.1.isLt
    have hv : x.1.1.1.val ≠ 0 := by exact fun h => hz (Fin.ext h)
    simp only [remaining, if_neg hz]
    refine ⟨by omega, by omega, ?_⟩
    rw [run_counter_iterate]
    exact nextPhase_finish _ _ (by omega)

theorem resume_or_hit {e : Env k} {u v Text : List (Fin k)} {d p r n fuel : ℕ}
    {leftSym : Fin k} {R rate : ℕ} {z : State k} {x : Phys e leftSym R rate}
    (h : Safe e u Text) (hl : Link e leftSym R rate z x) (hg : Good e u v Text d p r n fuel (erase z))
    (hn : n ≤ Text.length) :
    (∃ J ≤ remaining x, Link e leftSym R rate ((work e)^[J] z)
        ((TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[J] x) ∧
      Good e u v Text d p r n 0 (erase ((work e)^[J] z))) ∨
    (∃ f, Link e leftSym R rate ((work e)^[remaining x] z)
        ((TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[remaining x] x) ∧
      Good e u v Text d p r n f (erase ((work e)^[remaining x] z)) ∧
      ((TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[remaining x] x).1.1.1 = 0) := by
  obtain ⟨hp, hlen, hz⟩ := remaining_window (Terminal := Terminal) x
  rcases window_preserve_or_hit (Terminal := Terminal) h hl hg hn (remaining x) hp hlen with hh | ⟨f, hl', hg'⟩
  · exact Or.inl hh
  · exact Or.inr ⟨f, hl', hg', hz⟩

theorem after_input_remaining {e : Env k} (enc : Terminal → Fin k) {leftSym : Fin k} {R rate : ℕ}
    {x : Phys e leftSym R rate} (hz : x.1.1.1 = 0) (a : Terminal) (J : ℕ) (hJ : J ≤ R) :
    remaining ((TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[J]
      (input e enc leftSym R rate a x)) = R - J := by
  by_cases he : J = R
  · subst J
    have hc := frame_counter enc hz a
    change remaining (frame e enc leftSym R rate a x) = R - R
    simp only [remaining, hc, if_pos, Nat.sub_self]
  · have hlt : J + 1 < R + 1 := by omega
    have hc : ((TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[J]
        (input e enc leftSym R rate a x)).1.1.1 = ⟨J + 1, hlt⟩ := by
      change (((TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[J + 1])
        (x.1, arriveA e.blank (DualQueueShared.capture enc) (some a) x.2)).1.1.1 = _
      rw [run_counter_iterate, hz]
      exact nextPhase_iterate (Nat.zero_lt_succ R) (J + 1) hlt
    have hn : (⟨J + 1, hlt⟩ : Fin (R + 1)) ≠ 0 := by intro hh; have := congrArg Fin.val hh; simp at this
    simp only [remaining, hc, if_neg hn]
    omega

theorem resume_after_wait {e : Env k} {u v Text : List (Fin k)} {d p r n fuel : ℕ}
    (enc : Terminal → Fin k) {leftSym : Fin k} {R rate : ℕ} {z : State k} {x : Phys e leftSym R rate}
    (h : Safe e u Text) (hl : Link e leftSym R rate z x) (hg : Good e u v Text d p r n fuel (erase z))
    (hR : 0 < R) (waiting running : List Terminal)
    (hw : TextFeedPrefixDeadline.Valid Text n (waiting.map enc))
    (hr : TextFeedPrefixDeadline.Valid Text (n + waiting.length) (running.map enc))
    (hroom : u.length ≤ n + waiting.length) (hbudget : 5 * u.length + 2 ≤ running.length * R) :
    (∃ J ≤ remaining x, Link e leftSym R rate ((work e)^[J] z)
        ((TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[J] x) ∧
      Good e u v Text d p r n 0 (erase ((work e)^[J] z))) ∨
    Hit e enc leftSym R rate u v Text d p r n (waiting ++ running)
      ((TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[remaining x] x) := by
  have hb := hw.bound
  rcases resume_or_hit (Terminal := Terminal) h hl hg (by omega) with hh | ⟨f, hl', hg', hz⟩
  · exact Or.inl hh
  · exact Or.inr (reach_after_wait enc h hl' hg' hz hR waiting running hw hr hroom hbudget)

/-- info: 'PalPeg.TextFeedPipelinePrefixResume.resume_after_wait' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resume_after_wait

/-- info: 'PalPeg.TextFeedPipelinePrefixResume.resume_or_hit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resume_or_hit

end PalPeg.TextFeedPipelinePrefixResume
