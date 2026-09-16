import PalPeg.TextFeedPipelinePrefixLink

/-! Rank descent up to, but not beyond, the physical prefix return.
The following GS phase is never replaced by an artificial idle loop. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelinePrefixWindow
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangBank PalPeg.TextFeedControl
open PalPeg.TextFeedPipelineBank PalPeg.TextFeedPipelineControl
open PalPeg.TextFeedPrefixRank PalPeg.TextFeedPipelinePrefixLink

variable {k : ℕ} {Terminal : Type}

structure Safe (e : Env k) (u Text : List (Fin k)) : Prop where
  code : Function.Injective e.code
  mark_blank : e.mark ≠ e.blank
  blank_text : e.blank ∉ Text
  mark_text : e.mark ∉ Text
  end_u : e.endSym ∉ u
  start_u : e.startSym ∉ u
  start_end : e.startSym ≠ e.endSym

theorem Safe.symbol {e : Env k} {u Text : List (Fin k)} (h : Safe e u Text)
    {n : ℕ} {a : Fin k} (ha : Text[n]? = some a) : a ≠ e.mark := by
  intro he
  exact h.mark_text (he ▸ List.mem_of_getElem? ha)

noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (Outer e leftSym R rate) := Classical.decEq _

theorem step_progress {e : Env k} {u v Text : List (Fin k)} {d p r n fuel : ℕ}
    {leftSym : Fin k} {R rate : ℕ} {z : State k} {x : Phys e leftSym R rate}
    (h : Safe e u Text) (hl : Link e leftSym R rate z x) (hg : Good e u v Text d p r n fuel (erase z))
    (hf : 0 < fuel) (hz : x.1.1.1 ≠ 0) (hn : n ≤ Text.length) (hroom : u.length ≤ n) :
    Link e leftSym R rate (work e z) (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x) ∧
      Good e u v Text d p r n (fuel - 1) (erase (work e z)) := by
  obtain ⟨a, ha⟩ := has_action hg hf h.end_u h.start_end
  exact ⟨hl.step h.code h.mark_blank hz ha,
    hg.progress h.mark_blank h.blank_text h.mark_text h.end_u h.start_u h.start_end hn hroom⟩

theorem step_preserve {e : Env k} {u v Text : List (Fin k)} {d p r n fuel : ℕ}
    {leftSym : Fin k} {R rate : ℕ} {z : State k} {x : Phys e leftSym R rate}
    (h : Safe e u Text) (hl : Link e leftSym R rate z x) (hg : Good e u v Text d p r n fuel (erase z))
    (hf : 0 < fuel) (hz : x.1.1.1 ≠ 0) (hn : n ≤ Text.length) :
    ∃ fuel', Link e leftSym R rate (work e z) (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x) ∧
      Good e u v Text d p r n fuel' (erase (work e z)) := by
  obtain ⟨a, ha⟩ := has_action hg hf h.end_u h.start_end
  obtain ⟨f, hh⟩ := hg.preserve h.mark_blank h.blank_text h.mark_text h.end_u h.start_u h.start_end hn
  exact ⟨f, hl.step h.code h.mark_blank hz ha, hh⟩

theorem next_window {e : Env k} {leftSym : Fin k} {R rate N : ℕ} {x : Phys e leftSym R rate}
    (hlen : x.1.1.1.val + (N + 1) ≤ R + 1) :
    (N ≠ 0 → 0 < (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x).1.1.1.val) ∧
      (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x).1.1.1.val + N ≤ R + 1 := by
  have hnext (hn : N ≠ 0) : x.1.1.1.val + 1 < R + 1 := by omega
  constructor
  · intro hn
    rw [run_counter]
    simp only [nextPhase, dif_pos (hnext hn)]
    omega
  · by_cases hn : N = 0
    · have hh := (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x).1.1.1.isLt
      omega
    · rw [run_counter]
      simp only [nextPhase, dif_pos (hnext hn)]
      omega

/-- Only N≤fuel calls are executed: at N=fuel the source has just
returned, before the next real call can initialize/start GS. -/
theorem window_progress {e : Env k} {u v Text : List (Fin k)} {d p r n fuel : ℕ}
    {leftSym : Fin k} {R rate : ℕ} {z : State k} {x : Phys e leftSym R rate}
    (h : Safe e u Text) (hl : Link e leftSym R rate z x) (hg : Good e u v Text d p r n fuel (erase z))
    (hn : n ≤ Text.length) (hroom : u.length ≤ n) (N : ℕ) (hN : N ≤ fuel)
    (hpos : N ≠ 0 → 0 < x.1.1.1.val) (hlen : x.1.1.1.val + N ≤ R + 1) :
    Link e leftSym R rate ((work e)^[N] z) ((TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[N] x) ∧
      Good e u v Text d p r n (fuel - N) (erase ((work e)^[N] z)) := by
  induction N generalizing z x fuel with
  | zero => exact ⟨hl, hg⟩
  | succ N ih =>
    have hz : x.1.1.1 ≠ 0 := by
      have hh := hpos (Nat.succ_ne_zero N)
      intro hz
      rw [hz] at hh
      simp at hh
    obtain ⟨hl', hg'⟩ := step_progress (Terminal := Terminal) h hl hg (by omega) hz hn hroom
    obtain ⟨hp, hlen'⟩ := next_window (Terminal := Terminal) hlen
    have hh := ih hl' hg' (by omega) hp hlen'
    simpa only [Function.iterate_succ_apply, Nat.sub_sub, Nat.add_comm] using hh

/-- During input waiting, either the prefix returns inside this window
or the entire window preserves the invariant, with its new bounded rank. -/
theorem window_preserve_or_hit {e : Env k} {u v Text : List (Fin k)} {d p r n fuel : ℕ}
    {leftSym : Fin k} {R rate : ℕ} {z : State k} {x : Phys e leftSym R rate}
    (h : Safe e u Text) (hl : Link e leftSym R rate z x) (hg : Good e u v Text d p r n fuel (erase z))
    (hn : n ≤ Text.length) (N : ℕ)
    (hpos : N ≠ 0 → 0 < x.1.1.1.val) (hlen : x.1.1.1.val + N ≤ R + 1) :
    (∃ J ≤ N, Link e leftSym R rate ((work e)^[J] z)
        ((TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[J] x) ∧
      Good e u v Text d p r n 0 (erase ((work e)^[J] z))) ∨
    (∃ f, Link e leftSym R rate ((work e)^[N] z)
        ((TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[N] x) ∧
      Good e u v Text d p r n f (erase ((work e)^[N] z))) := by
  induction N generalizing z x fuel with
  | zero => exact Or.inr ⟨fuel, hl, hg⟩
  | succ N ih =>
    by_cases hf : fuel = 0
    · subst fuel
      exact Or.inl ⟨0, Nat.zero_le _, hl, hg⟩
    have hz : x.1.1.1 ≠ 0 := by
      have hh := hpos (Nat.succ_ne_zero N)
      intro hz
      rw [hz] at hh
      simp at hh
    obtain ⟨f, hl', hg'⟩ := step_preserve (Terminal := Terminal) h hl hg (by omega) hz hn
    obtain ⟨hp, hlen'⟩ := next_window (Terminal := Terminal) hlen
    rcases ih hl' hg' hp hlen' with ⟨J, hJ, hL, hG⟩ | ⟨f', hL, hG⟩
    · left
      refine ⟨J + 1, by omega, ?_⟩
      simpa only [Function.iterate_succ_apply] using And.intro hL hG
    · right
      refine ⟨f', ?_⟩
      simpa only [Function.iterate_succ_apply] using And.intro hL hG

/-- info: 'PalPeg.TextFeedPipelinePrefixWindow.window_progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms window_progress

/-- info: 'PalPeg.TextFeedPipelinePrefixWindow.window_preserve_or_hit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms window_preserve_or_hit

end PalPeg.TextFeedPipelinePrefixWindow
