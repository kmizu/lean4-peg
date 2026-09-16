import PalPeg.TextFeedPipelineObserved

/-! The observer cannot sample inside a macro. Its only active service
phase is the real returned-loop boundary. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelineOutputSound
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.TextFeedControl
open PalPeg.TextFeedPipelineControl PalPeg.TextFeedPipelineFrames PalPeg.TextFeedPipelineCoupled
open PalPeg.TextFeedPipelineInputMacro PalPeg.TextFeedPipelineService PalPeg.TextFeedPipelineObserved
open PalPeg.TextFeedPipelineFrontier
open PalPeg.GSVerifierZ PalPeg.RTQueueTapes

variable {k : ℕ} {Terminal : Type} {e : Env k} {leftSym : Fin k} {R rate p r : ℕ}
variable {Text leftPat rightPat : List (Fin k)} {enc : Terminal → Fin k}

noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (Outer e leftSym R rate) := Classical.decEq _

private theorem before_ne (a : A) :
    beforeVerify (k := k) a ≠ feedHead ∧ beforeVerify (k := k) a ≠ verifyBody rate := by
  cases a with
  | inl a =>
    simp only [beforeVerify]
    split_ifs <;> simp [waitText1, waitText2, feedHead, verifyBody]
  | inr up => simp [beforeVerify, feedHead, verifyBody]

private theorem cond_ne (c : C) :
    beforeCond (k := k) c ≠ feedHead ∧ beforeCond (k := k) c ≠ verifyBody rate := by
  cases c with
  | inl c => cases c <;> simp [beforeCond, feedHead, verifyBody]
  | inr c => cases c <;> simp [beforeCond, feedHead, verifyBody]

private theorem lift_ne_feed (p : GSVProgZLoop.DProg) : liftVerify (k := k) p ≠ feedHead := by
  cases p <;> simp [liftVerify, verifyAct, feedHead]

private theorem seq_ne_body (p q : Task k) (hp : p ≠ feedHead) : .seq p q ≠ verifyBody rate := by
  intro h
  exact hp (Prog.seq.inj h).1

private theorem lift_ne_body (p : GSVProgZLoop.DProg) : liftVerify (k := k) p ≠ verifyBody rate := by
  cases p with
  | skip => simp [liftVerify, verifyBody]
  | act a => exact seq_ne_body _ _ (before_ne (rate := rate) a).1
  | seq p q => exact seq_ne_body _ _ (lift_ne_feed p)
  | ite c p q => exact seq_ne_body _ _ (cond_ne (rate := rate) c).1
  | loop c a b => exact seq_ne_body _ _ (cond_ne (rate := rate) c).1

private theorem after_ne (a : A) : afterVerify (k := k) a ≠ verifyBody rate := by
  cases a with
  | inl a => simp only [afterVerify]; split_ifs <;> simp [feedHead, verifyBody]
  | inr up => simp [afterVerify, verifyBody]

private theorem renderFrame_no_body (f : Frame) : verifyBody (k := k) rate ∉ renderFrame f := by
  cases f with
  | code p => simpa only [renderFrame, List.mem_singleton] using (lift_ne_body p).symm
  | pending a =>
    simp only [renderFrame, List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨(before_ne a).2.symm, (seq_ne_body _ _ (by simp [feedHead])).symm⟩
  | after a => simpa only [renderFrame, List.mem_singleton] using (after_ne a).symm
  | test c p q =>
    simp only [renderFrame, List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨(cond_ne c).2.symm, by simp [verifyBody]⟩
  | cycle c a b =>
    simp only [renderFrame, List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨(cond_ne c).2.symm, by simp [verifyBody, loopCore]⟩
  | body c a b =>
    simp only [renderFrame, List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨(seq_ne_body _ _ (by simp [verifyAct, feedHead])).symm, by simp [verifyBody, loopCore]⟩
  | bodyRest c a b =>
    simp only [renderFrame, List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨(seq_ne_body _ _ (lift_ne_feed b)).symm, by simp [verifyBody, loopCore]⟩
  | skip => simp [renderFrame, verifyBody]

theorem macro_gate {n : ℕ} {x : Config e leftSym R rate} {u : Snapshot k}
    (h : Valid e leftSym R rate Text n x u [verifyLoop rate]) :
    TextFeedPipelineOutput.atBoundary rate x.1 = false := by
  classical
  apply Bool.eq_false_iff.mpr
  intro hg
  have he : x.1.1.2.2.val = [verifyBody rate, verifyLoop rate] := of_decide_eq_true hg
  have hr : render (k := k) u.frames = [verifyBody rate] := List.append_cancel_right (h.control.symm.trans he)
  have hm : verifyBody (k := k) rate ∈ render u.frames := by rw [hr]; simp
  obtain ⟨f, _, hf⟩ := List.mem_flatMap.mp hm
  exact renderFrame_no_body f hf

theorem entry_gate {n : ℕ} {x : Config e leftSym R rate}
    (d : Entry e leftSym R rate Text leftPat rightPat p r n x)
    (h : TextFeedPipelineOutput.atBoundary rate x.1 = true) : d.rank = 2 := by
  classical
  have hp := d.positive
  have hr := d.rank_le
  by_cases h₂ : d.rank = 2
  · exact h₂
  by_cases h₁ : d.rank = 1
  · have hv := d.valid.1.control
    have hf : d.u.frames = [] := by simpa only [h₁] using d.valid.2
    have he : x.1.1.2.2.val = [verifyBody rate, verifyLoop rate] := of_decide_eq_true h
    simp only [h₁, TextFeedPipelineReentryInput.caller, hf, render, List.flatMap_nil, List.nil_append] at hv
    have hh := hv.symm.trans he
    simp [TextFeedPipelineReentry.second, verifyBody, feedHead, feedHead2] at hh
  · have h₃ : d.rank = 3 := by omega
    have hv : Valid e leftSym R rate Text n x d.u [verifyLoop rate] := by
      simpa only [h₃, TextFeedPipelineReentryInput.caller] using d.valid.1
    have he := macro_gate hv
    rw [h] at he
    contradiction

def Semantic (z : VStateZ) : Prop :=
  ScanInv rightPat (TextFeed.padW e.blank Text Text.length) z.1 ∧
    ZInv leftPat rightPat (TextFeed.padW e.blank Text Text.length) z

def Matches (n : ℕ) : Prop := ∃ i, leftPat.length ≤ i ∧ i + rightPat.length = n ∧
  OccAt rightPat (TextFeed.padW e.blank Text Text.length) i ∧
  MatchLen leftPat (TextFeed.padW e.blank Text Text.length) (i - leftPat.length) leftPat.length

theorem flag_sound {n : ℕ} {z : VStateZ}
    (hs : Semantic (e := e) (Text := Text) (leftPat := leftPat) (rightPat := rightPat) z)
    (hf : zReportFlag leftPat rightPat n z = true) :
    Matches (e := e) (Text := Text) (leftPat := leftPat) (rightPat := rightPat) n := by
  obtain ⟨hq, hn, hu⟩ := (zReportFlag_eq hs.2).mp hf
  refine ⟨z.1.pos, hs.2.1, hn, ?_, hu⟩
  change MatchLen rightPat (TextFeed.padW e.blank Text Text.length) z.1.pos rightPat.length
  simpa only [hq] using hs.1.1

theorem sample_sound {n : ℕ} {x : Config e leftSym R rate}
    (a : State e leftSym R rate Text leftPat rightPat p r n x)
    (hc : Function.Injective e.code) (hcond : ∀ z, Conditions e Text leftPat rightPat rate p r z)
    (hn : n ≤ Text.length)
    (hs : Semantic (e := e) (Text := Text) (leftPat := leftPat) (rightPat := rightPat) a.z)
    (ρ : Role) (bit : Bool)
    (ho : (TextFeedPipelineOutput.sample e leftSym R rate (pack x ρ bit)).1.2.2 = true) :
    bit = true ∨ Matches (e := e) (Text := Text) (leftPat := leftPat) (rightPat := rightPat) n := by
  cases a with
  | «macro» a =>
    have hg := macro_gate a.valid
    exact Or.inl (by simpa only [TextFeedPipelineOutput.sample, pack, hg, Bool.false_eq_true, ↓reduceIte] using ho)
  | entry a =>
    by_cases hg : TextFeedPipelineOutput.atBoundary rate x.1 = true
    · have hr := entry_gate a hg
      rw [entry_sample a hc hr (hcond a.z).blank_text hn (hcond a.z).mark_blank
        (hcond a.z).end_left (hcond a.z).end_right ρ bit] at ho
      simp only [Bool.or_eq_true] at ho
      rcases ho with hb | hf
      · exact Or.inl hb
      · exact Or.inr (flag_sound hs hf)
    · exact Or.inl (by simpa only [TextFeedPipelineOutput.sample, pack, if_neg hg] using ho)

theorem semantic_step (hK : KSimple rightPat rate p r) (hp : 0 < p)
    (hd : ZDeadline leftPat rightPat rate p r) {z : VStateZ}
    (h : Semantic (e := e) (Text := Text) (leftPat := leftPat) (rightPat := rightPat) z) :
    Semantic (e := e) (Text := Text) (leftPat := leftPat) (rightPat := rightPat)
      (vStepZ leftPat rightPat rate p r (TextFeed.padW e.blank Text Text.length) z) :=
  ⟨by simpa only [vStepZ_fst] using scanStep_inv hK h.1, vStepZ_inv hp hd h.1 h.2⟩

/-- A true bit either came from this frontier's verified report, or was
already true with no intervening input. Captures discard older bits. -/
theorem trace_sound {n₀ n₁ : ℕ} {x₀ x₁ : Config e leftSym R rate}
    {a : State e leftSym R rate Text leftPat rightPat p r n₀ x₀}
    {b : State e leftSym R rate Text leftPat rightPat p r n₁ x₁} {ops : List (Option Terminal)}
    (h : Trace e leftSym R rate enc Text leftPat rightPat p r a ops b)
    (hc : Function.Injective e.code) (hcond : ∀ z, Conditions e Text leftPat rightPat rate p r z)
    (hK : KSimple rightPat rate p r) (hd : ZDeadline leftPat rightPat rate p r)
    (hn : n₁ ≤ Text.length)
    (hs : Semantic (e := e) (Text := Text) (leftPat := leftPat) (rightPat := rightPat) a.z)
    (ρ : Role) (bit : Bool) :
    (opRun e leftSym R rate enc ops (pack x₀ ρ bit)).1.2.2 = true →
      (bit = true ∧ n₀ = n₁) ∨
        Matches (e := e) (Text := Text) (leftPat := leftPat) (rightPat := rightPat) n₁ := by
  induction h generalizing ρ bit with
  | refl => exact fun hh => Or.inl ⟨hh, rfl⟩
  | @worker n x a b hz he =>
    intro ho
    have hs' : Semantic (e := e) (Text := Text) (leftPat := leftPat) (rightPat := rightPat) b.z := by
      rcases he with he | ⟨he, _⟩
      · simpa only [he] using hs
      · simpa only [he] using semantic_step hK (hcond a.z).positive_p hd hs
    have ho' : (TextFeedPipelineOutput.sample e leftSym R rate
        (pack (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x) ρ bit)).1.2.2 = true := by
      simpa only [opRun, List.foldl_cons, List.foldl_nil, opStep, TextFeedPipelineOutput.step,
        pack, if_neg hz] using ho
    rcases sample_sound b hc hcond hn hs' ρ bit ho' with hb | hm
    · exact Or.inl ⟨hb, rfl⟩
    · exact Or.inr hm
  | @arrival n x c a b hz he =>
    intro ho
    have hs' : Semantic (e := e) (Text := Text) (leftPat := leftPat) (rightPat := rightPat) b.z := by
      simpa only [he] using hs
    have ho' : (TextFeedPipelineOutput.sample e leftSym R rate
        (pack (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate
          (TextFeedPipelineInputRun.captured e leftSym R rate enc c x)) ρ false)).1.2.2 = true := by
      simpa only [opRun, List.foldl_cons, List.foldl_nil, opStep, TextFeedPipelineOutput.step,
        pack, project, TextFeedPipelineInputRun.captured, hz, ↓reduceIte] using ho
    rcases sample_sound b hc hcond hn hs' ρ false ho' with hb | hm
    · contradiction
    · exact Or.inr hm
  | @trans n₀ n₁ n₂ x₀ x₁ x₂ xs ys a b c h h' ih ih' =>
    intro ho
    have hn' : n₁ ≤ Text.length := h'.frontier.trans hn
    have hs' := TextFeedPipelineDeadline.trace_invariant h _
      (fun z hz => semantic_step hK (hcond z).positive_p hd hz) hs
    obtain ⟨ρ₁, bit₁, hr⟩ := realize h hc ρ bit
    have ho' : (opRun e leftSym R rate enc ys (pack x₁ ρ₁ bit₁)).1.2.2 = true := by
      simp only [opRun, List.foldl_append] at ho
      change (opRun e leftSym R rate enc ys (opRun e leftSym R rate enc xs (pack x₀ ρ bit))).1.2.2 = true at ho
      rwa [hr] at ho
    rcases ih' hn hs' ρ₁ bit₁ ho' with ⟨hb, he⟩ | hm
    · have ho₁ : (opRun e leftSym R rate enc xs (pack x₀ ρ bit)).1.2.2 = true := by rw [hr]; exact hb
      rcases ih hn' hs ρ bit ho₁ with ⟨hb₀, he₀⟩ | hm₀
      · exact Or.inl ⟨hb₀, he₀.trans he⟩
      · exact Or.inr (he ▸ hm₀)
    · exact Or.inr hm

theorem frames_sound {n : ℕ} {x : Config e leftSym R rate}
    (hcode : Function.Injective e.code) (a : State e leftSym R rate Text leftPat rightPat p r n x)
    (hc : ∀ z, Conditions e Text leftPat rightPat rate p r z)
    (hK : KSimple rightPat rate p r) (hpat : 0 < rightPat.length)
    (hdeadline : ZDeadline leftPat rightPat rate p r)
    (as : List Terminal) (hne : as ≠ []) (hn : n + as.length ≤ Text.length)
    (has : ∀ j c, as[j]? = some c → Text[n + j]? = some (enc c))
    (hz : x.1.1.1 = 0) (hfirst : x.1.1.2.1 = false)
    (hR : progressRate rate * (rate + 1) ≤ R) (ha : target rate rightPat n ≤ a.score)
    (hs : Semantic (e := e) (Text := Text) (leftPat := leftPat) (rightPat := rightPat) a.z)
    (ρ : Role) (bit : Bool)
    (ho : (TextFeedPipelineOutput.machine e leftSym enc R rate).accepting
      (as.foldl (TextFeedPipelineOutput.machine e leftSym enc R rate).sRound
        (embed (pack x ρ bit))).state = true) :
    Matches (e := e) (Text := Text) (leftPat := leftPat) (rightPat := rightPat) (n + as.length) := by
  obtain ⟨b, ht, _⟩ := a.frames hcode leftSym R rate enc hc hpat as hn has hz hfirst hR ha
  rw [machine_output] at ho
  rcases trace_sound ht hcode hc hK hdeadline hn hs ρ bit ho with ⟨_, he⟩ | hm
  · have hl : 0 < as.length := by
      cases as with
      | nil => exact False.elim (hne rfl)
      | cons c cs => exact Nat.zero_lt_succ _
    omega
  · exact hm

/-- info: 'PalPeg.TextFeedPipelineOutputSound.frames_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms frames_sound

def RawMatches (n : ℕ) : Prop := ∃ i, leftPat.length ≤ i ∧ i + rightPat.length = n ∧
  OccAt rightPat Text i ∧ MatchLen leftPat Text (i - leftPat.length) leftPat.length

private theorem match_pad {pat : List (Fin k)} {i q : ℕ} (hbound : i + q ≤ Text.length) :
    MatchLen pat (TextFeed.padW e.blank Text Text.length) i q ↔ MatchLen pat Text i q := by
  have he (j : ℕ) (hj : j < q) := TextFeed.padW_getElem?_of_lt (blank := e.blank)
    (Text := Text) (Nat.le_refl Text.length) (by omega : i + j < Text.length)
  constructor
  · intro h j hj
    rw [← he j hj]
    exact h j hj
  · intro h j hj
    rw [he j hj]
    exact h j hj

theorem matches_raw {n : ℕ} (hn : n ≤ Text.length) :
    Matches (e := e) (Text := Text) (leftPat := leftPat) (rightPat := rightPat) n ↔
      RawMatches (Text := Text) (leftPat := leftPat) (rightPat := rightPat) n := by
  constructor
  · rintro ⟨i, hi, he, hv, hu⟩
    exact ⟨i, hi, he, (match_pad (e := e) (by omega)).mp hv,
      (match_pad (e := e) (by omega)).mp hu⟩
  · rintro ⟨i, hi, he, hv, hu⟩
    exact ⟨i, hi, he, (match_pad (e := e) (by omega)).mpr hv,
      (match_pad (e := e) (by omega)).mpr hu⟩

/-- Output correctness from an arbitrary startup phase. Only an actual
service trace and its final credit are needed; the first call need not be
an input arrival. At least one arrival excludes a stale initial bit. -/
theorem trace_iff {n₀ n₁ : ℕ} {x₀ x₁ : Config e leftSym R rate}
    {a : State e leftSym R rate Text leftPat rightPat p r n₀ x₀}
    {b : State e leftSym R rate Text leftPat rightPat p r n₁ x₁}
    {ops : List (Option Terminal)}
    (ht : Trace e leftSym R rate enc Text leftPat rightPat p r a ops b)
    (hcode : Function.Injective e.code) (hc : ∀ z, Conditions e Text leftPat rightPat rate p r z)
    (hK : KSimple rightPat rate p r) (hd : ZDeadline leftPat rightPat rate p r)
    (hn : n₁ ≤ Text.length) (hmore : n₀ < n₁)
    (hb : target rate rightPat n₁ ≤ b.score)
    (hs : Semantic (e := e) (Text := Text) (leftPat := leftPat) (rightPat := rightPat) a.z)
    (hstart : a.z.1.pos = leftPat.length) (ρ : Role) (bit : Bool) :
    (opRun e leftSym R rate enc ops (pack x₀ ρ bit)).1.2.2 = true ↔
      RawMatches (Text := Text) (leftPat := leftPat) (rightPat := rightPat) n₁ := by
  constructor
  · intro ho
    rcases trace_sound ht hcode hc hK hd hn hs ρ bit ho with hstale | hm
    · exact False.elim (by omega)
    · exact (matches_raw (e := e) hn).mp hm
  · intro hm
    obtain ⟨i, hi, he, hv, hu⟩ := (matches_raw (e := e) hn).mpr hm
    exact trace_output hcode ht hc hK hd hn hb hs.1 hs.2 hv hu
      (by rw [hstart]; exact hi) (by omega) he ρ bit

/-- Concrete finite-control matcher correctness at every nonempty input
prefix, from an initialized streaming state. No abstract-output oracle or
macro-termination premise remains. Startup itself is a separate obligation. -/
theorem frames_iff {n : ℕ} {x : Config e leftSym R rate}
    (hcode : Function.Injective e.code) (a : State e leftSym R rate Text leftPat rightPat p r n x)
    (hc : ∀ z, Conditions e Text leftPat rightPat rate p r z)
    (hK : KSimple rightPat rate p r) (hpat : 0 < rightPat.length)
    (hdeadline : ZDeadline leftPat rightPat rate p r)
    (as : List Terminal) (hne : as ≠ []) (hn : n + as.length ≤ Text.length)
    (has : ∀ j c, as[j]? = some c → Text[n + j]? = some (enc c))
    (hz : x.1.1.1 = 0) (hfirst : x.1.1.2.1 = false)
    (hR : progressRate rate * (rate + 1) ≤ R) (ha : target rate rightPat n ≤ a.score)
    (hs : Semantic (e := e) (Text := Text) (leftPat := leftPat) (rightPat := rightPat) a.z)
    (hstart : a.z.1.pos = leftPat.length) (ρ : Role) (bit : Bool) :
    (TextFeedPipelineOutput.machine e leftSym enc R rate).accepting
      (as.foldl (TextFeedPipelineOutput.machine e leftSym enc R rate).sRound
        (embed (pack x ρ bit))).state = true ↔
      RawMatches (Text := Text) (leftPat := leftPat) (rightPat := rightPat) (n + as.length) := by
  rw [machine_output]
  obtain ⟨b, ht, hb⟩ := a.frames hcode leftSym R rate enc hc hpat as hn has hz hfirst hR ha
  have hlen : 0 < as.length := by
    cases as with
    | nil => exact False.elim (hne rfl)
    | cons c cs => exact Nat.zero_lt_succ _
  exact trace_iff ht hcode hc hK hdeadline hn (by omega) hb hs hstart ρ bit

/-- info: 'PalPeg.TextFeedPipelineOutputSound.trace_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms trace_iff

/-- info: 'PalPeg.TextFeedPipelineOutputSound.frames_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms frames_iff

end PalPeg.TextFeedPipelineOutputSound
