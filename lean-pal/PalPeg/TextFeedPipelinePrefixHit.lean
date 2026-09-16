import PalPeg.TextFeedPipelinePrefixFrames

/-! A prefix-return event along real input frames, stopping before GS. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelinePrefixHit
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangPersist2 PalPeg.ProgLangBank PalPeg.TextFeedControl
open PalPeg.TextFeedPipelineBank PalPeg.TextFeedPipelineControl
open PalPeg.TextFeedPipelinePrefixLink PalPeg.TextFeedPipelinePrefixWindow
open PalPeg.TextFeedPipelinePrefixFrames PalPeg.TextFeedPrefixRank
open PalPeg.TextFeedPrefixDeadline (Valid)

variable {k : ℕ} {Terminal : Type}

noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (Outer e leftSym R rate) := Classical.decEq _

inductive Hit (e : Env k) (enc : Terminal → Fin k) (leftSym : Fin k) (R rate : ℕ)
    (u v Text : List (Fin k)) (d p r : ℕ) : ℕ → List Terminal → Phys e leftSym R rate → Prop
  | now {n w x z} (hl : Link e leftSym R rate z x) (hg : Good e u v Text d p r n 0 (erase z)) :
      Hit e enc leftSym R rate u v Text d p r n w x
  | within {n a w x z J} (hJ : J ≤ R)
      (hl : Link e leftSym R rate z
        ((TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[J] (input e enc leftSym R rate a x)))
      (hg : Good e u v Text d p r (n + 1) 0 (erase z)) :
      Hit e enc leftSym R rate u v Text d p r n (a :: w) x
  | next {n a w x}
      (h : Hit e enc leftSym R rate u v Text d p r (n + 1) w (frame e enc leftSym R rate a x)) :
      Hit e enc leftSym R rate u v Text d p r n (a :: w) x

theorem reach_of_budget {e : Env k} {u v Text : List (Fin k)} {d p r n fuel : ℕ}
    (enc : Terminal → Fin k) {leftSym : Fin k} {R rate : ℕ} {z : State k} {x : Phys e leftSym R rate}
    (h : Safe e u Text) (hl : Link e leftSym R rate z x) (hg : Good e u v Text d p r n fuel (erase z))
    (hz : x.1.1.1 = 0) (hR : 0 < R) (hroom : u.length ≤ n)
    (w : List Terminal) (hw : Valid Text n (w.map enc)) (hbudget : fuel ≤ w.length * R) :
    Hit e enc leftSym R rate u v Text d p r n w x := by
  induction w generalizing n fuel z x with
  | nil =>
    have hf : fuel = 0 := by simpa only [List.length_nil, Nat.zero_mul, Nat.le_zero] using hbudget
    exact Hit.now hl (hf ▸ hg)
  | cons a w ih =>
    cases hw with
    | cons ha ht =>
      have hb := ht.bound
      have hn : n < Text.length := by omega
      by_cases hf : fuel ≤ R
      · obtain ⟨hl', hg'⟩ := frame_complete enc h hl hg hz hR hn (by omega) a ha hf
        exact Hit.within hf hl' hg'
      · obtain ⟨hl', hg'⟩ := frame_progress enc h hl hg hz hR hn (by omega) a ha (by omega)
        apply Hit.next
        apply ih hl' hg' (frame_counter enc hz a) (by omega) ht
        simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at hbudget
        omega

theorem Hit.append {e : Env k} {enc : Terminal → Fin k} {leftSym : Fin k} {R rate : ℕ}
    {u v Text : List (Fin k)} {d p r n : ℕ} {w : List Terminal} {x : Phys e leftSym R rate}
    (h : Hit e enc leftSym R rate u v Text d p r n w x) (extra : List Terminal) :
    Hit e enc leftSym R rate u v Text d p r n (w ++ extra) x := by
  induction h with
  | now hl hg => exact Hit.now hl hg
  | within hJ hl hg => exact Hit.within hJ hl hg
  | next _ ih => exact Hit.next ih

theorem wait_or_hit {e : Env k} {u v Text : List (Fin k)} {d p r n fuel : ℕ}
    (enc : Terminal → Fin k) {leftSym : Fin k} {R rate : ℕ} {z : State k} {x : Phys e leftSym R rate}
    (h : Safe e u Text) (hl : Link e leftSym R rate z x) (hg : Good e u v Text d p r n fuel (erase z))
    (hz : x.1.1.1 = 0) (hR : 0 < R)
    (w : List Terminal) (hw : Valid Text n (w.map enc)) :
    Hit e enc leftSym R rate u v Text d p r n w x ∨
      ∃ z' f, Link e leftSym R rate z' (w.foldl (fun x a => frame e enc leftSym R rate a x) x) ∧
        Good e u v Text d p r (n + w.length) f (erase z') ∧
        (w.foldl (fun x a => frame e enc leftSym R rate a x) x).1.1.1 = 0 := by
  induction w generalizing n fuel z x with
  | nil => exact Or.inr ⟨z, fuel, hl, hg, hz⟩
  | cons a w ih =>
    cases hw with
    | cons ha ht =>
      have hb := ht.bound
      rcases frame_wait enc h hl hg hz hR (by omega) a ha with ⟨J, hJ, hl', hg'⟩ | ⟨f, hl', hg'⟩
      · exact Or.inl (Hit.within hJ hl' hg')
      · rcases ih hl' hg' (frame_counter enc hz a) ht with hh | ⟨z', f', hl'', hg'', hz'⟩
        · exact Or.inl (Hit.next hh)
        · right
          refine ⟨z', f', hl'', ?_, hz'⟩
          simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hg''

theorem prepend {e : Env k} {enc : Terminal → Fin k} {leftSym : Fin k} {R rate : ℕ}
    {u v Text : List (Fin k)} {d p r n : ℕ} (before rest : List Terminal) {x : Phys e leftSym R rate}
    (h : Hit e enc leftSym R rate u v Text d p r (n + before.length) rest
      (before.foldl (fun x a => frame e enc leftSym R rate a x) x)) :
    Hit e enc leftSym R rate u v Text d p r n (before ++ rest) x := by
  induction before generalizing n x with
  | nil => exact h
  | cons a w ih =>
    apply Hit.next
    apply ih
    simpa only [List.length_cons, List.foldl_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem reach_after_wait {e : Env k} {u v Text : List (Fin k)} {d p r n fuel : ℕ}
    (enc : Terminal → Fin k) {leftSym : Fin k} {R rate : ℕ} {z : State k} {x : Phys e leftSym R rate}
    (h : Safe e u Text) (hl : Link e leftSym R rate z x) (hg : Good e u v Text d p r n fuel (erase z))
    (hz : x.1.1.1 = 0) (hR : 0 < R) (waiting running : List Terminal)
    (hw : Valid Text n (waiting.map enc)) (hr : Valid Text (n + waiting.length) (running.map enc))
    (hroom : u.length ≤ n + waiting.length) (hbudget : 5 * u.length + 2 ≤ running.length * R) :
    Hit e enc leftSym R rate u v Text d p r n (waiting ++ running) x := by
  rcases wait_or_hit enc h hl hg hz hR waiting hw with hh | ⟨z', f, hl', hg', hz'⟩
  · exact hh.append running
  · apply prepend waiting running
    exact reach_of_budget enc h hl' hg' hz' hR hroom running hr (le_trans hg'.bound hbudget)

/-- info: 'PalPeg.TextFeedPipelinePrefixHit.reach_after_wait' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reach_after_wait

/-- info: 'PalPeg.TextFeedPipelinePrefixHit.reach_of_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reach_of_budget

end PalPeg.TextFeedPipelinePrefixHit
