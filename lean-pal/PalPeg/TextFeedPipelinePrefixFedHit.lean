import PalPeg.TextFeedPipelinePrefixReserve

/-! Prefix deadlines retain the second FIFO and untouched text head. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelinePrefixFedHit
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangBank PalPeg.TextFeedControl
open PalPeg.TextFeedPipelineBank PalPeg.TextFeedPipelineControl
open PalPeg.TextFeedPipelinePrefixLink PalPeg.TextFeedPipelinePrefixWindow
open PalPeg.TextFeedPipelinePrefixFrames PalPeg.TextFeedPrefixRank
open PalPeg.TextFeedPipelinePrefixReserve
open PalPeg.TextFeedPrefixDeadline (Valid)

variable {k : ℕ} {Terminal : Type}

noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (Outer e leftSym R rate) := Classical.decEq _

inductive FedHit (e : Env k) (enc : Terminal → Fin k) (leftSym : Fin k) (R rate : ℕ)
    (u v Text : List (Fin k)) (d p r : ℕ) : ℕ → List Terminal → Phys e leftSym R rate → Prop
  | now {n w x z} (hl : Link e leftSym R rate z x) (hg : Good e u v Text d p r n 0 (erase z))
      (hr : Reserve e Text n z) : FedHit e enc leftSym R rate u v Text d p r n w x
  | within {n a w x z J} (hJ : J ≤ R)
      (hl : Link e leftSym R rate z
        ((TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[J] (input e enc leftSym R rate a x)))
      (hg : Good e u v Text d p r (n + 1) 0 (erase z)) (hr : Reserve e Text (n + 1) z) :
      FedHit e enc leftSym R rate u v Text d p r n (a :: w) x
  | next {n a w x}
      (h : FedHit e enc leftSym R rate u v Text d p r (n + 1) w (frame e enc leftSym R rate a x)) :
      FedHit e enc leftSym R rate u v Text d p r n (a :: w) x

theorem reach_of_budget {e : Env k} {u v Text : List (Fin k)} {d p r n fuel : ℕ}
    (enc : Terminal → Fin k) {leftSym : Fin k} {R rate : ℕ} {z : State k} {x : Phys e leftSym R rate}
    (h : Safe e u Text) (hl : Link e leftSym R rate z x) (hg : Good e u v Text d p r n fuel (erase z))
    (hq : Reserve e Text n z) (hz : x.1.1.1 = 0) (hR : 0 < R) (hroom : u.length ≤ n)
    (w : List Terminal) (hw : Valid Text n (w.map enc)) (hbudget : fuel ≤ w.length * R) :
    FedHit e enc leftSym R rate u v Text d p r n w x := by
  induction w generalizing n fuel z x with
  | nil =>
    have hf : fuel = 0 := by simpa only [List.length_nil, Nat.zero_mul, Nat.le_zero] using hbudget
    exact FedHit.now hl (hf ▸ hg) hq
  | cons a w ih =>
    cases hw with
    | cons ha ht =>
      have hb := ht.bound
      have hn : n < Text.length := by omega
      have hq' := hq.arrival hn ha
      by_cases hf : fuel ≤ R
      · obtain ⟨hl', hg'⟩ := frame_complete enc h hl hg hz hR hn (by omega) a ha hf
        exact FedHit.within hf hl' hg' (hq'.works fuel)
      · obtain ⟨hl', hg'⟩ := frame_progress enc h hl hg hz hR hn (by omega) a ha (by omega)
        apply FedHit.next
        apply ih hl' hg' (hq'.works R) (frame_counter enc hz a) (by omega) ht
        simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at hbudget
        omega

theorem FedHit.append {e : Env k} {enc : Terminal → Fin k} {leftSym : Fin k} {R rate : ℕ}
    {u v Text : List (Fin k)} {d p r n : ℕ} {w : List Terminal} {x : Phys e leftSym R rate}
    (h : FedHit e enc leftSym R rate u v Text d p r n w x) (extra : List Terminal) :
    FedHit e enc leftSym R rate u v Text d p r n (w ++ extra) x := by
  induction h with
  | now hl hg hr => exact FedHit.now hl hg hr
  | within hJ hl hg hr => exact FedHit.within hJ hl hg hr
  | next _ ih => exact FedHit.next ih

theorem prepend {e : Env k} {enc : Terminal → Fin k} {leftSym : Fin k} {R rate : ℕ}
    {u v Text : List (Fin k)} {d p r n : ℕ} (before rest : List Terminal) {x : Phys e leftSym R rate}
    (h : FedHit e enc leftSym R rate u v Text d p r (n + before.length) rest
      (before.foldl (fun x a => frame e enc leftSym R rate a x) x)) :
    FedHit e enc leftSym R rate u v Text d p r n (before ++ rest) x := by
  induction before generalizing n x with
  | nil => exact h
  | cons a w ih =>
    apply FedHit.next
    apply ih
    simpa only [List.length_cons, List.foldl_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem wait_or_hit {e : Env k} {u v Text : List (Fin k)} {d p r n fuel : ℕ}
    (enc : Terminal → Fin k) {leftSym : Fin k} {R rate : ℕ} {z : State k} {x : Phys e leftSym R rate}
    (h : Safe e u Text) (hl : Link e leftSym R rate z x) (hg : Good e u v Text d p r n fuel (erase z))
    (hq : Reserve e Text n z) (hz : x.1.1.1 = 0) (hR : 0 < R)
    (w : List Terminal) (hw : Valid Text n (w.map enc)) :
    FedHit e enc leftSym R rate u v Text d p r n w x ∨
      ∃ z' f, Link e leftSym R rate z' (w.foldl (fun x a => frame e enc leftSym R rate a x) x) ∧
        Good e u v Text d p r (n + w.length) f (erase z') ∧ Reserve e Text (n + w.length) z' ∧
        (w.foldl (fun x a => frame e enc leftSym R rate a x) x).1.1.1 = 0 := by
  induction w generalizing n fuel z x with
  | nil => exact Or.inr ⟨z, fuel, hl, hg, hq, hz⟩
  | cons a w ih =>
    cases hw with
    | cons ha ht =>
      have hb := ht.bound
      have hn : n < Text.length := by omega
      have hq' := hq.arrival hn ha
      rcases frame_wait enc h hl hg hz hR hn a ha with ⟨J, hJ, hl', hg'⟩ | ⟨f, hl', hg'⟩
      · exact Or.inl (FedHit.within hJ hl' hg' (hq'.works J))
      · rcases ih hl' hg' (hq'.works R) (frame_counter enc hz a) ht with hh | ⟨z', f', hl'', hg'', hq'', hz'⟩
        · exact Or.inl (FedHit.next hh)
        · right
          refine ⟨z', f', hl'', ?_, ?_, hz'⟩
          · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hg''
          · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hq''

theorem reach_after_wait {e : Env k} {u v Text : List (Fin k)} {d p r n fuel : ℕ}
    (enc : Terminal → Fin k) {leftSym : Fin k} {R rate : ℕ} {z : State k} {x : Phys e leftSym R rate}
    (h : Safe e u Text) (hl : Link e leftSym R rate z x) (hg : Good e u v Text d p r n fuel (erase z))
    (hq : Reserve e Text n z) (hz : x.1.1.1 = 0) (hR : 0 < R) (waiting running : List Terminal)
    (hw : Valid Text n (waiting.map enc)) (hr : Valid Text (n + waiting.length) (running.map enc))
    (hroom : u.length ≤ n + waiting.length) (hbudget : 5 * u.length + 2 ≤ running.length * R) :
    FedHit e enc leftSym R rate u v Text d p r n (waiting ++ running) x := by
  rcases wait_or_hit enc h hl hg hq hz hR waiting hw with hh | ⟨z', f, hl', hg', hq', hz'⟩
  · exact hh.append running
  · apply prepend waiting running
    exact reach_of_budget enc h hl' hg' hq' hz' hR hroom running hr (le_trans hg'.bound hbudget)

theorem reach_from_partial {e : Env k} {u v Text : List (Fin k)} {d p r n fuel : ℕ}
    (enc : Terminal → Fin k) {leftSym : Fin k} {R rate : ℕ} {z : State k} {x : Phys e leftSym R rate}
    (h : Safe e u Text) (hz : x.1.1.1 = 0) (a : Terminal) (J : ℕ) (hJ : J ≤ R)
    (hl : Link e leftSym R rate z ((TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[J]
      (input e enc leftSym R rate a x)))
    (hg : Good e u v Text d p r (n + 1) fuel (erase z)) (hq : Reserve e Text (n + 1) z)
    (hR : 0 < R) (waiting running : List Terminal)
    (hw : Valid Text (n + 1) (waiting.map enc))
    (hr : Valid Text (n + 1 + waiting.length) (running.map enc))
    (hroom : u.length ≤ n + 1 + waiting.length) (hbudget : 5 * u.length + 2 ≤ running.length * R) :
    FedHit e enc leftSym R rate u v Text d p r n (a :: (waiting ++ running)) x := by
  have hrem := TextFeedPipelinePrefixResume.after_input_remaining enc hz a J hJ
  have hb := hw.bound
  rcases TextFeedPipelinePrefixResume.resume_or_hit (Terminal := Terminal) h hl hg (by omega) with
    ⟨K, hK, hl', hg'⟩ | ⟨f, hl', hg', hz'⟩
  · rw [hrem] at hK
    apply FedHit.within (J := K + J) (by omega)
    · simpa only [Function.iterate_add_apply] using hl'
    · exact hg'
    · exact hq.works K
  · have hh := reach_after_wait enc h hl' hg' (hq.works _) hz' hR waiting running hw hr hroom hbudget
    apply FedHit.next
    rw [hrem] at hh
    simpa only [← Function.iterate_add_apply, Nat.sub_add_cancel hJ, frame] using hh

/-- info: 'PalPeg.TextFeedPipelinePrefixFedHit.reach_from_partial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reach_from_partial

/-- info: 'PalPeg.TextFeedPipelinePrefixFedHit.reach_after_wait' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reach_after_wait

end PalPeg.TextFeedPipelinePrefixFedHit
