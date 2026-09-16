import PalPeg.TextFeedPipelinePrefixStart

/-! Arrival plus a bounded productive prefix window on the actual pipeline. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelinePrefixFrames
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangBank PalPeg.TextFeedControl
open PalPeg.RTQueueClosed
open PalPeg.ProgLangPersist2
open PalPeg.TextFeedPipelineBank PalPeg.TextFeedPipelineControl
open PalPeg.TextFeedPipelinePrefixLink PalPeg.TextFeedPipelinePrefixWindow
open PalPeg.TextFeedPrefixRank

variable {k : ℕ} {Terminal : Type}

noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (Outer e leftSym R rate) := Classical.decEq _

noncomputable def input (e : Env k) (enc : Terminal → Fin k) (leftSym : Fin k) (R rate : ℕ)
    (a : Terminal) (x : Phys e leftSym R rate) : Phys e leftSym R rate :=
  TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate
    (x.1, arriveA e.blank (DualQueueShared.capture enc) (some a) x.2)

noncomputable def frame (e : Env k) (enc : Terminal → Fin k) (leftSym : Fin k) (R rate : ℕ)
    (a : Terminal) (x : Phys e leftSym R rate) : Phys e leftSym R rate :=
  (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[R]
    (input e enc leftSym R rate a x)

theorem input_counter {e : Env k} (enc : Terminal → Fin k) {leftSym : Fin k} {R rate : ℕ}
    {x : Phys e leftSym R rate} (hz : x.1.1.1 = 0) (hR : 0 < R) (a : Terminal) :
    (input e enc leftSym R rate a x).1.1.1.val = 1 := by
  simp only [input, run_counter, hz, nextPhase]
  simp [hR]

theorem input_good {e : Env k} {u v Text : List (Fin k)} {d p r n fuel : ℕ}
    (enc : Terminal → Fin k) {leftSym : Fin k} {R rate : ℕ} {z : State k} {x : Phys e leftSym R rate}
    (h : Safe e u Text) (hl : Link e leftSym R rate z x) (hg : Good e u v Text d p r n fuel (erase z))
    (hz : x.1.1.1 = 0) (hn : n < Text.length) (a : Terminal) (ha : Text[n]? = some (enc a)) :
    Link e leftSym R rate (arrival (enc a) z) (input e enc leftSym R rate a x) ∧
      Good e u v Text d p r (n + 1) fuel (erase (arrival (enc a) z)) :=
  ⟨hl.arrival h.code h.mark_blank enc hz a (h.symbol ha), hg.arrive h.mark_blank hn ha⟩

theorem arrival_window {e : Env k} {u v Text : List (Fin k)} {d p r n fuel : ℕ}
    (enc : Terminal → Fin k) {leftSym : Fin k} {R rate : ℕ} {z : State k} {x : Phys e leftSym R rate}
    (h : Safe e u Text) (hl : Link e leftSym R rate z x) (hg : Good e u v Text d p r n fuel (erase z))
    (hz : x.1.1.1 = 0) (hR : 0 < R) (hn : n < Text.length) (hroom : u.length ≤ n + 1)
    (a : Terminal) (ha : Text[n]? = some (enc a)) (N : ℕ) (hN : N ≤ fuel) (hNR : N ≤ R) :
    Link e leftSym R rate ((work e)^[N] (arrival (enc a) z))
        ((TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[N] (input e enc leftSym R rate a x)) ∧
      Good e u v Text d p r (n + 1) (fuel - N) (erase ((work e)^[N] (arrival (enc a) z))) := by
  obtain ⟨hl', hg'⟩ := input_good enc h hl hg hz hn a ha
  have hc := input_counter enc hz hR a
  exact window_progress h hl' hg' (by omega) hroom N hN (by intro _; omega) (by omega)

theorem frame_progress {e : Env k} {u v Text : List (Fin k)} {d p r n fuel : ℕ}
    (enc : Terminal → Fin k) {leftSym : Fin k} {R rate : ℕ} {z : State k} {x : Phys e leftSym R rate}
    (h : Safe e u Text) (hl : Link e leftSym R rate z x) (hg : Good e u v Text d p r n fuel (erase z))
    (hz : x.1.1.1 = 0) (hR : 0 < R) (hn : n < Text.length) (hroom : u.length ≤ n + 1)
    (a : Terminal) (ha : Text[n]? = some (enc a)) (hf : R ≤ fuel) :
    Link e leftSym R rate ((work e)^[R] (arrival (enc a) z)) (frame e enc leftSym R rate a x) ∧
      Good e u v Text d p r (n + 1) (fuel - R) (erase ((work e)^[R] (arrival (enc a) z))) :=
  arrival_window enc h hl hg hz hR hn hroom a ha R hf (Nat.le_refl R)

theorem frame_complete {e : Env k} {u v Text : List (Fin k)} {d p r n fuel : ℕ}
    (enc : Terminal → Fin k) {leftSym : Fin k} {R rate : ℕ} {z : State k} {x : Phys e leftSym R rate}
    (h : Safe e u Text) (hl : Link e leftSym R rate z x) (hg : Good e u v Text d p r n fuel (erase z))
    (hz : x.1.1.1 = 0) (hR : 0 < R) (hn : n < Text.length) (hroom : u.length ≤ n + 1)
    (a : Terminal) (ha : Text[n]? = some (enc a)) (hf : fuel ≤ R) :
    Link e leftSym R rate ((work e)^[fuel] (arrival (enc a) z))
        ((TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[fuel] (input e enc leftSym R rate a x)) ∧
      Good e u v Text d p r (n + 1) 0 (erase ((work e)^[fuel] (arrival (enc a) z))) := by
  simpa only [Nat.sub_self] using arrival_window enc h hl hg hz hR hn hroom a ha fuel (Nat.le_refl fuel) hf

theorem frame_counter {e : Env k} (enc : Terminal → Fin k) {leftSym : Fin k} {R rate : ℕ}
    {x : Phys e leftSym R rate} (hz : x.1.1.1 = 0) (a : Terminal) :
    (frame e enc leftSym R rate a x).1.1.1 = 0 := by
  change (((TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[R + 1])
    (x.1, arriveA e.blank (DualQueueShared.capture enc) (some a) x.2)).1.1.1 = 0
  rw [run_counter_iterate, hz]
  exact nextPhase_iterate_round (Nat.zero_lt_succ R)

theorem frame_wait {e : Env k} {u v Text : List (Fin k)} {d p r n fuel : ℕ}
    (enc : Terminal → Fin k) {leftSym : Fin k} {R rate : ℕ} {z : State k} {x : Phys e leftSym R rate}
    (h : Safe e u Text) (hl : Link e leftSym R rate z x) (hg : Good e u v Text d p r n fuel (erase z))
    (hz : x.1.1.1 = 0) (hR : 0 < R) (hn : n < Text.length)
    (a : Terminal) (ha : Text[n]? = some (enc a)) :
    (∃ J ≤ R, Link e leftSym R rate ((work e)^[J] (arrival (enc a) z))
        ((TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[J] (input e enc leftSym R rate a x)) ∧
      Good e u v Text d p r (n + 1) 0 (erase ((work e)^[J] (arrival (enc a) z)))) ∨
    (∃ f, Link e leftSym R rate ((work e)^[R] (arrival (enc a) z)) (frame e enc leftSym R rate a x) ∧
      Good e u v Text d p r (n + 1) f (erase ((work e)^[R] (arrival (enc a) z)))) := by
  obtain ⟨hl', hg'⟩ := input_good enc h hl hg hz hn a ha
  have hc := input_counter enc hz hR a
  exact window_preserve_or_hit h hl' hg' (by omega) R (by intro _; omega) (by omega)

/-- info: 'PalPeg.TextFeedPipelinePrefixFrames.frame_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms frame_complete

/-- info: 'PalPeg.TextFeedPipelinePrefixFrames.frame_wait' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms frame_wait

end PalPeg.TextFeedPipelinePrefixFrames
