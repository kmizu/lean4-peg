import PalPeg.TextFeedPipelineOutputResume

/-! Matcher parameters are supplied by the actual normalized GS result,
including the no-repetition branch whose raw period is zero. -/
set_option autoImplicit false
namespace PalPeg.TextFeedPipelineParameters
open PalPeg.TextFeedControl
open PalPeg.Program PalPeg.TextFeedPipelineService
open PalPeg.TextFeedPipelineOutputBudget (workerRate)
variable {k : ℕ} {Terminal : Type}

noncomputable local instance : DecidableEq (TextFeedPipelineControl.TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineControl.TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (TextFeedPipelineControl.Outer e leftSym R rate) := Classical.decEq _

theorem decomp (w : List (Fin k)) (L : ℕ) (hL : 0 < L) (hw : L ≤ w.length) :
    let x := PrepInstances.stagePat w L
    let d := PrepInstances.prepRes w L
    KSimple (x.drop d.1) 8 d.2.1 d.2.2 ∧ 0 < (x.drop d.1).length ∧
      GSVerifierZ.ZDeadline (x.take d.1) (x.drop d.1) 8 d.2.1 d.2.2 := by
  let x := PrepInstances.stagePat w L
  let d := PrepInstances.prepRes w L
  have H := PrepInstances.prep_gsDecomp w L
  have hlen : x.length = L := PrepInstances.stagePat_length hw
  have hcut : 7 * d.1 < L := PrepInstances.prep_cut_bound hL hw
  have hs : d.1 ≤ x.length := by omega
  have ht : (x.take d.1).length = d.1 := List.length_take_of_le hs
  have hv : (x.drop d.1).length = L - d.1 := by rw [List.length_drop, hlen]
  have hK : KSimple (x.drop d.1) 8 d.2.1 d.2.2 := (PrepInstances.prep_core w L).ksimple_eff
  refine ⟨hK, by rw [hv]; omega, ?_⟩
  apply GSVerifierZ.zdeadline_of_prefix (by decide) hK.period_pos
  · rw [List.take_append_drop, ht, hlen]
    exact hcut
  · rw [ht]
    by_cases hp : (PrepInstances.rawRes w L).2.1 = 0
    · have he : d.2.1 = (x.drop d.1).length + 1 := by
        simp only [d, x, PrepInstances.prepRes, effPeriod, hp, ↓reduceIte]
      rw [he, hv]
      omega
    · have he : d.2.1 = (PrepInstances.rawRes w L).2.1 := by
        simp only [d, PrepInstances.prepRes, effPeriod, if_neg hp]
      rw [he]
      exact H.cut_period_bound hp

theorem conditions (e : Env k) (w Text : List (Fin k)) (L : ℕ)
    (h : TextFeedPipelinePrefixWindow.Safe e (PrepInstances.stagePat w L) Text) :
    let x := PrepInstances.stagePat w L
    let d := PrepInstances.prepRes w L
    ∀ z, TextFeedPipelineInputMacro.Conditions e Text (x.take d.1) (x.drop d.1) 8 d.2.1 d.2.2 z := by
  intro x d z
  have hK : KSimple (x.drop d.1) 8 d.2.1 d.2.2 := (PrepInstances.prep_core w L).ksimple_eff
  exact ⟨h.mark_blank, h.blank_text, h.mark_text, by decide, hK.period_pos,
    fun hm => h.start_u (List.mem_of_mem_drop hm),
    fun hm => h.end_u (List.mem_of_mem_drop hm),
    fun hm => h.end_u (List.mem_of_mem_take hm),
    fun hm => h.start_u (List.mem_of_mem_take hm), h.start_end⟩

/-- Reassemble the two matcher pieces into the original full pattern. -/
theorem raw_full (u v Text : List (Fin k)) (n : ℕ) :
    TextFeedPipelineOutputSound.RawMatches (Text := Text) (leftPat := u) (rightPat := v) n ↔
      ∃ i, i + (u ++ v).length = n ∧ OccAt (u ++ v) Text i := by
  constructor
  · rintro ⟨i, hi, he, hv, hu⟩
    refine ⟨i - u.length, ?_, occAt_append_iff.mpr ⟨hu, ?_⟩⟩
    · simp only [List.length_append]; omega
    · simpa only [Nat.sub_add_cancel hi] using hv
  · rintro ⟨i, he, hm⟩
    obtain ⟨hu, hv⟩ := occAt_append_iff.mp hm
    refine ⟨i + u.length, by omega, ?_, hv, ?_⟩
    · simp only [List.length_append] at he; omega
    · simpa only [Nat.add_sub_cancel] using hu

/-- The concrete stage matcher recognizes suffix occurrences of its whole
pattern, at fixed service speed and with the GS premises derived internally. -/
theorem stage_resumed_iff (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k)
    (w Text : List (Fin k)) (L n : ℕ) (hL : 0 < L) (hw : L ≤ w.length)
    (h : TextFeedPipelinePrefixWindow.Safe e (PrepInstances.stagePat w L) Text) :
    let pat := PrepInstances.stagePat w L
    let d := PrepInstances.prepRes w L
    ∀ (x : TextFeedPipelineCoupled.Config e leftSym (workerRate 8) 8)
      (a : Macro e leftSym (workerRate 8) 8 Text (pat.take d.1) (pat.drop d.1) d.2.1 d.2.2 n x),
      a.z.1.pos = (pat.take d.1).length → a.z.1.q = 0 → a.z.2 = ⟨0, 0, 0, true⟩ →
      ∀ (as : List Terminal), as ≠ [] → n + as.length ≤ Text.length →
      (∀ j c, as[j]? = some c → Text[n + j]? = some (enc c)) →
      x.1.1.2.1 = false → target 8 (pat.drop d.1) n ≤ a.score →
      ∀ (ρ : RTQueueTapes.Role) (bit : Bool)
        (actual : TextFeedPipelineOutputPrepFinish.Config e leftSym (workerRate 8) 8),
      ConfigBlankEq e.blank actual (TextFeedPipelineOutputClock.embed (TextFeedPipelineObserved.pack x ρ bit)) →
      ((TextFeedPipelineOutput.machine e leftSym enc (workerRate 8) 8).accepting
        (as.foldl (TextFeedPipelineOutput.machine e leftSym enc (workerRate 8) 8).sRound
          ((List.replicate (TextFeedPipelinePrefixResume.remaining x * 96) none).foldl
            (TextFeedPipelineOutput.machine e leftSym enc (workerRate 8) 8).sMicroStep actual)).state = true ↔
        ∃ i, i + pat.length = n + as.length ∧ OccAt pat Text i) := by
  intro pat d x a hp hq hz as hne hn has hfirst hcredit ρ bit actual hsim
  obtain ⟨hK, hpat, hd⟩ := decomp w L hL hw
  have hh := TextFeedPipelineOutputResume.boot_resumed_iff h.code enc a (conditions e w Text L h)
    hK hpat hd hp hq hz as hne hn has hfirst (TextFeedPipelineOutputBudget.service_rate 8)
    hcredit ρ bit actual hsim
  have he := raw_full (pat.take d.1) (pat.drop d.1) Text (n + as.length)
  exact hh.trans (by simpa only [List.take_append_drop] using he)

/-- info: 'PalPeg.TextFeedPipelineParameters.stage_resumed_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stage_resumed_iff
/-- info: 'PalPeg.TextFeedPipelineParameters.decomp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms decomp
/-- info: 'PalPeg.TextFeedPipelineParameters.conditions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms conditions
end PalPeg.TextFeedPipelineParameters
