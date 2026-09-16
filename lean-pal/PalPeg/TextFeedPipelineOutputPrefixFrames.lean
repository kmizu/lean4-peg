import PalPeg.TextFeedPipelineOutputPrefix

/-! Alignment across actual input words on the observation-enabled machine. -/
set_option autoImplicit false
namespace PalPeg.TextFeedPipelineOutputPrefixFrames
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.TextFeedControl
open PalPeg.TextFeedPipelineControl PalPeg.TextFeedPipelinePrefixLink
open PalPeg.TextFeedPipelineOutputPrepFinish (Config finishAt)
open PalPeg.TextFeedPipelinePrefixFedPhysical (Complete)
open PalPeg.TextFeedPrefixRank (Good)
open PalPeg.TextFeedPipelinePrefixReserve (Reserve)

variable {k : ℕ} {Terminal : Type}
noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (Outer e leftSym R rate) := Classical.decEq _

private theorem canonical {e : Env k} {leftSym : Fin k} {R rate : ℕ}
    (x : Config e leftSym R rate) (h96 : x.state.1.2 = 0) (hout : x.state.2 = 0) :
    x = ⟨(((x.state.1.1.1, x.state.1.1.2.1, x.state.1.1.2.2), 0), 0), x.tape⟩ := by
  rcases x with ⟨⟨⟨q, ph⟩, out⟩, T⟩
  change ph = 0 at h96
  change out = 0 at hout
  subst ph
  subst out
  rfl

def Reached (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k) (R rate : ℕ)
    (u v Text : List (Fin k)) (d p r n : ℕ) (word : List Terminal) (x : Config e leftSym R rate) : Prop :=
  ∃ before a after J, word = before ++ a :: after ∧ J ≤ R ∧
    let y := finishAt e leftSym enc R rate before a J x
    Complete e leftSym R rate u v Text d p r (n + before.length + 1) (y.state.1.1.1, y.tape)

theorem rounds_clocks {e : Env k} (enc : Terminal → Fin k) {leftSym : Fin k} {R rate : ℕ}
    (word : List Terminal) (x : Config e leftSym R rate)
    (hz : x.state.1.1.1.1.1 = 0) (h96 : x.state.1.2 = 0) (hout : x.state.2 = 0) :
    let y := word.foldl (TextFeedPipelineOutput.machine e leftSym enc R rate).sRound x
    y.state.1.1.1.1.1 = 0 ∧ y.state.1.2 = 0 ∧ y.state.2 = 0 := by
  induction word generalizing x with
  | nil => exact ⟨hz, h96, hout⟩
  | cons a word ih =>
    apply ih
    · rw [canonical x h96 hout, TextFeedPipelineOutput.machine_round]
      change ((TextFeedPipelineOutput.step (Terminal := Terminal) e leftSym R rate)^[R + 1] _).1.1.1.1 = 0
      rw [TextFeedPipelineOutput.step_counter_iterate]
      change nextPhase^[R + 1] x.state.1.1.1.1.1 = 0
      rw [hz]
      exact nextPhase_iterate_round (Nat.zero_lt_succ R)
    · rw [canonical x h96 hout, TextFeedPipelineOutput.machine_round]
    · rw [canonical x h96 hout, TextFeedPipelineOutput.machine_round]

theorem prepend {e : Env k} {enc : Terminal → Fin k} {leftSym : Fin k} {R rate : ℕ}
    {u v Text : List (Fin k)} {d p r n : ℕ} (before rest : List Terminal)
    (x : Config e leftSym R rate)
    (h : Reached e leftSym enc R rate u v Text d p r (n + before.length) rest
      (before.foldl (TextFeedPipelineOutput.machine e leftSym enc R rate).sRound x)) :
    Reached e leftSym enc R rate u v Text d p r n (before ++ rest) x := by
  obtain ⟨mid, a, after, J, he, hJ, hc⟩ := h
  refine ⟨before ++ mid, a, after, J, ?_, hJ, ?_⟩
  · rw [he, List.append_assoc]
  · simpa only [finishAt, List.foldl_append, List.length_append, Nat.add_assoc] using hc

theorem frames_cases {e : Env k} {u v Text : List (Fin k)} {d p r n fuel : ℕ}
    (enc : Terminal → Fin k) {leftSym : Fin k} {R rate : ℕ} {z : State k}
    (x : Config e leftSym R rate) (h : TextFeedPipelinePrefixWindow.Safe e u Text)
    (hl : Link e leftSym R rate z (x.state.1.1.1, x.tape))
    (hg : Good e u v Text d p r n fuel (erase z)) (hr : Reserve e Text n z)
    (hz : x.state.1.1.1.1.1 = 0) (h96 : x.state.1.2 = 0) (hout : x.state.2 = 0)
    (hR : 0 < R) (word : List Terminal) (hn : n + word.length ≤ Text.length)
    (has : ∀ j a, word[j]? = some a → Text[n + j]? = some (enc a)) :
    Reached e leftSym enc R rate u v Text d p r n word x ∨
    (∃ z' f,
      let y := word.foldl (TextFeedPipelineOutput.machine e leftSym enc R rate).sRound x
      Link e leftSym R rate z' (y.state.1.1.1, y.tape) ∧
      Good e u v Text d p r (n + word.length) f (erase z') ∧
      Reserve e Text (n + word.length) z' ∧
      y.state.1.1.1.1.1 = 0 ∧ y.state.1.2 = 0 ∧ y.state.2 = 0) := by
  induction word generalizing x z n fuel with
  | nil =>
    right
    simpa only [List.foldl_nil, List.length_nil, Nat.add_zero] using
      (show ∃ z' f, Link e leftSym R rate z' (x.state.1.1.1, x.tape) ∧
        Good e u v Text d p r n f (erase z') ∧ Reserve e Text n z' ∧
        x.state.1.1.1.1.1 = 0 ∧ x.state.1.2 = 0 ∧ x.state.2 = 0 from
        ⟨z, fuel, hl, hg, hr, hz, h96, hout⟩)
  | cons a word ih =>
    have hframe := TextFeedPipelineOutputPrefix.frame_cases enc h hl hg hr hz hR
      (by simp only [List.length_cons] at hn; omega) a (by simpa using has 0 a rfl)
      x.state.1.1.2.1 x.state.1.1.2.2
    rw [← canonical x h96 hout] at hframe
    rcases hframe with ⟨J, hJ, hc⟩ | ⟨z1, f1, hl1, hg1, hr1, hz1, h961, hout1⟩
    · left
      exact ⟨[], a, word, J, rfl, hJ, hc⟩
    · let x1 := (TextFeedPipelineOutput.machine e leftSym enc R rate).sRound x a
      have htail : ∀ j b, word[j]? = some b → Text[(n + 1) + j]? = some (enc b) := by
        intro j b hj
        have hh := has (j + 1) b (by simpa using hj)
        simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hh
      have hnext := ih x1 hl1 hg1 hr1 hz1 h961 hout1
        (by simp only [List.length_cons] at hn; omega) htail
      rcases hnext with ⟨before, b, after, J, hw, hJ, hc⟩ | hc
      · left
        refine ⟨a :: before, b, after, J, by simp only [List.cons_append, hw], hJ, ?_⟩
        simpa only [finishAt, List.foldl_cons, List.length_cons, x1,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hc
      · right
        simpa only [List.foldl_cons, List.length_cons, x1,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hc

/-- Once the alignment input is available, enough actual worker slots
force Complete inside the supplied nonempty input word. -/
theorem productive_reaches {e : Env k} {u v Text : List (Fin k)} {d p r n fuel : ℕ}
    (enc : Terminal → Fin k) {leftSym : Fin k} {R rate : ℕ} {z : State k}
    (x : Config e leftSym R rate) (h : TextFeedPipelinePrefixWindow.Safe e u Text)
    (hl : Link e leftSym R rate z (x.state.1.1.1, x.tape))
    (hg : Good e u v Text d p r n fuel (erase z)) (hr : Reserve e Text n z)
    (hz : x.state.1.1.1.1.1 = 0) (h96 : x.state.1.2 = 0) (hout : x.state.2 = 0)
    (hR : 0 < R) (word : List Terminal) (hne : word ≠ [])
    (hn : n + word.length ≤ Text.length) (hroom : u.length ≤ n + 1)
    (has : ∀ j a, word[j]? = some a → Text[n + j]? = some (enc a))
    (hbudget : fuel ≤ word.length * R) :
    Reached e leftSym enc R rate u v Text d p r n word x := by
  induction word generalizing x z n fuel with
  | nil => exact False.elim (hne rfl)
  | cons a word ih =>
    have hframe := TextFeedPipelineOutputPrefix.productive_cases enc h hl hg hr hz hR
      (by simp only [List.length_cons] at hn; omega) hroom a (by simpa using has 0 a rfl)
      x.state.1.1.2.1 x.state.1.1.2.2
    rw [← canonical x h96 hout] at hframe
    rcases hframe with ⟨J, hJ, hc⟩ | ⟨hmore, z1, hl1, hg1, hr1, hz1, h961, hout1⟩
    · exact ⟨[], a, word, J, rfl, hJ, hc⟩
    · let x1 := (TextFeedPipelineOutput.machine e leftSym enc R rate).sRound x a
      have hbudget' : fuel - R ≤ word.length * R := by
        simp only [List.length_cons, Nat.succ_mul] at hbudget
        omega
      have hne' : word ≠ [] := by
        intro he
        simp only [he, List.length_nil, Nat.zero_mul] at hbudget'
        omega
      have htail : ∀ j b, word[j]? = some b → Text[(n + 1) + j]? = some (enc b) := by
        intro j b hj
        have hh := has (j + 1) b (by simpa using hj)
        simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hh
      obtain ⟨before, b, after, J, hw, hJ, hc⟩ := ih x1 hl1 hg1 hr1 hz1 h961 hout1 hne'
        (by simp only [List.length_cons] at hn; omega) (by omega) htail hbudget'
      refine ⟨a :: before, b, after, J, by simp only [List.cons_append, hw], hJ, ?_⟩
      simpa only [finishAt, List.foldl_cons, List.length_cons, x1,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hc

/-- Waiting arrivals followed by enough productive frames reach Complete
on the actual machine. The uniform rank bound is derived from Good. -/
theorem reaches_after_wait {e : Env k} {u v Text : List (Fin k)} {d p r n fuel : ℕ}
    (enc : Terminal → Fin k) {leftSym : Fin k} {R rate : ℕ} {z : State k}
    (x : Config e leftSym R rate) (h : TextFeedPipelinePrefixWindow.Safe e u Text)
    (hl : Link e leftSym R rate z (x.state.1.1.1, x.tape))
    (hg : Good e u v Text d p r n fuel (erase z)) (hr : Reserve e Text n z)
    (hz : x.state.1.1.1.1.1 = 0) (h96 : x.state.1.2 = 0) (hout : x.state.2 = 0)
    (hR : 0 < R) (waiting running : List Terminal)
    (hn : n + waiting.length + running.length ≤ Text.length)
    (hw : ∀ j a, waiting[j]? = some a → Text[n + j]? = some (enc a))
    (ha : ∀ j a, running[j]? = some a → Text[n + waiting.length + j]? = some (enc a))
    (hroom : u.length ≤ n + waiting.length + 1)
    (hbudget : 5 * u.length + 2 ≤ running.length * R) :
    Reached e leftSym enc R rate u v Text d p r n (waiting ++ running) x := by
  rcases frames_cases enc x h hl hg hr hz h96 hout hR waiting (by omega) hw with
    ⟨before, a, after, J, he, hJ, hc⟩ | ⟨z1, f1, hl1, hg1, hr1, hz1, h961, hout1⟩
  · refine ⟨before, a, after ++ running, J, ?_, hJ, hc⟩
    rw [he, List.append_assoc, List.cons_append]
  · let x1 := waiting.foldl (TextFeedPipelineOutput.machine e leftSym enc R rate).sRound x
    have hne : running ≠ [] := by
      intro he
      simp only [he, List.length_nil, Nat.zero_mul] at hbudget
      omega
    obtain ⟨before, a, after, J, he, hJ, hc⟩ := productive_reaches enc x1 h hl1 hg1 hr1
      hz1 h961 hout1 hR running hne hn hroom ha (hg1.bound.trans hbudget)
    refine ⟨waiting ++ before, a, after, J, ?_, hJ, ?_⟩
    · rw [he, List.append_assoc]
    · simpa only [finishAt, List.foldl_append, List.length_append, Nat.add_assoc, x1] using hc

/-- A prefix invariant established inside the current real input frame
reaches completion within the remaining frame and the supplied deadline. -/
theorem reaches_from_partial {e : Env k} {u v Text : List (Fin k)} {d p r n fuel : ℕ}
    (enc : Terminal → Fin k) {leftSym : Fin k} {R rate : ℕ} {z : State k}
    (x : Config e leftSym R rate) (h : TextFeedPipelinePrefixWindow.Safe e u Text)
    (hz : x.state.1.1.1.1.1 = 0) (h96 : x.state.1.2 = 0) (hout : x.state.2 = 0)
    (a : Terminal) (J : ℕ) (hJ : J ≤ R)
    (hl : let y := finishAt e leftSym enc R rate [] a J x
      Link e leftSym R rate z (y.state.1.1.1, y.tape))
    (hg : Good e u v Text d p r (n + 1) fuel (erase z))
    (hr : Reserve e Text (n + 1) z) (hR : 0 < R) (waiting running : List Terminal)
    (hn : n + 1 + waiting.length + running.length ≤ Text.length)
    (hw : ∀ j b, waiting[j]? = some b → Text[n + 1 + j]? = some (enc b))
    (ha : ∀ j b, running[j]? = some b → Text[n + 1 + waiting.length + j]? = some (enc b))
    (hroom : u.length ≤ n + 1 + waiting.length + 1)
    (hbudget : 5 * u.length + 2 ≤ running.length * R) :
    Reached e leftSym enc R rate u v Text d p r n (a :: (waiting ++ running)) x := by
  let y := finishAt e leftSym enc R rate [] a J x
  have hc := canonical x h96 hout
  have hrem : TextFeedPipelinePrefixResume.remaining (y.state.1.1.1, y.tape) = R - J := by
    dsimp only [y]
    rw [hc]
    exact TextFeedPipelineOutputPrepFinish.partial_remaining e leftSym enc R rate J hJ _ _ a hz
  have hext (K : ℕ) (hK : J + K ≤ R) :
      finishAt e leftSym enc R rate [] a (J + K) x =
      let v := (TextFeedPipelineOutput.step (Terminal := Terminal) e leftSym R rate)^[K]
        (y.state.1.1, y.tape)
      ⟨((v.1, 0), TextFeedPipelineOutputPrepFinish.phase R (J + K)), v.2⟩ := by
    dsimp only [y]
    rw [hc]
    simp only [finishAt, List.foldl_nil,
      TextFeedPipelineOutputPrepFinish.machine_partial e leftSym enc R rate J hJ,
      TextFeedPipelineOutputPrepFinish.machine_partial e leftSym enc R rate (J + K) hK]
    rw [show J + K + 1 = K + (J + 1) by omega, Function.iterate_add_apply]
  have hcases := TextFeedPipelineOutputPrefix.resume_cases (Terminal := Terminal)
    h hl hg hr (by omega) y.state.1.1.2.1 y.state.1.1.2.2
  change (∃ K ≤ TextFeedPipelinePrefixResume.remaining (y.state.1.1.1, y.tape), _) ∨ _ at hcases
  rw [hrem] at hcases
  rcases hcases with ⟨K, hK, hcomplete⟩ | ⟨f, hl', hg', hr', hz'⟩
  · refine ⟨[], a, waiting ++ running, J + K, rfl, by omega, ?_⟩
    rw [hext K (by omega)]
    exact hcomplete
  · have he := hext (R - J) (by omega)
    rw [Nat.add_sub_of_le hJ, TextFeedPipelineOutputPrepFinish.phase_full] at he
    have hfull : finishAt e leftSym enc R rate [] a R x =
        (TextFeedPipelineOutput.machine e leftSym enc R rate).sRound x a := by
      rw [hc]
      exact TextFeedPipelineOutputPrepFinish.finishAt_full e leftSym enc R rate _ _ a
    rw [hfull] at he
    have hreach := reaches_after_wait enc
      ((TextFeedPipelineOutput.machine e leftSym enc R rate).sRound x a)
      h (he.symm ▸ hl') hg' hr' (he.symm ▸ hz')
      (by rw [he]) (by rw [he]) hR waiting running hn hw ha hroom hbudget
    obtain ⟨before, b, after, K, hw', hK, hcomplete⟩ := hreach
    refine ⟨a :: before, b, after, K, by simp only [List.cons_append, hw'], hK, ?_⟩
    simpa only [finishAt, List.foldl_cons, List.length_cons,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcomplete

/-- info: 'PalPeg.TextFeedPipelineOutputPrefixFrames.reaches_from_partial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms reaches_from_partial

/-- info: 'PalPeg.TextFeedPipelineOutputPrefixFrames.reaches_after_wait' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms reaches_after_wait

/-- info: 'PalPeg.TextFeedPipelineOutputPrefixFrames.productive_reaches' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms productive_reaches

/-- info: 'PalPeg.TextFeedPipelineOutputPrefixFrames.frames_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms frames_cases
end PalPeg.TextFeedPipelineOutputPrefixFrames
