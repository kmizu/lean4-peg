import PalPeg.TextFeedPipelineDeadline

/-! Realize the service trace with the integrated physical observer. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelineObserved
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.TextFeedControl
open PalPeg.TextFeedPipelineControl PalPeg.TextFeedPipelineCoupled PalPeg.TextFeedPipelineInputRun
open PalPeg.TextFeedPipelineInputMacro PalPeg.TextFeedPipelineService PalPeg.TextFeedPipelineFrontier
open PalPeg.TextFeedPipelineDeadline PalPeg.GSVerifierZ PalPeg.RTQueue PalPeg.RTQueueTapes

variable {k : ℕ} {Terminal : Type} {e : Env k} {leftSym : Fin k} {R rate p r : ℕ}
variable {Text leftPat rightPat : List (Fin k)} {enc : Terminal → Fin k}

noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (Outer e leftSym R rate) := Classical.decEq _

abbrev View (e : Env k) (leftSym : Fin k) (R rate : ℕ) :=
  TextFeedPipelineOutput.State e leftSym R rate × (Fin 39 → STape (Fin k))

def pack (x : Config e leftSym R rate) (ρ : Role) (b : Bool) : View e leftSym R rate :=
  ((x.1, ρ, b), x.2)

def project (y : View e leftSym R rate) : Config e leftSym R rate := (y.1.1, y.2)

noncomputable def opStep (e : Env k) (leftSym : Fin k) (R rate : ℕ) (enc : Terminal → Fin k)
    (y : View e leftSym R rate) : Option Terminal → View e leftSym R rate
  | none => TextFeedPipelineOutput.step (Terminal := Terminal) e leftSym R rate y
  | some c => TextFeedPipelineOutput.step (Terminal := Terminal) e leftSym R rate
      (pack (captured e leftSym R rate enc c (project y)) y.1.2.1 y.1.2.2)

noncomputable def opRun (e : Env k) (leftSym : Fin k) (R rate : ℕ) (enc : Terminal → Fin k)
    (ops : List (Option Terminal)) (y : View e leftSym R rate) : View e leftSym R rate :=
  ops.foldl (opStep e leftSym R rate enc) y

theorem pack_project (y : View e leftSym R rate) : pack (project y) y.1.2.1 y.1.2.2 = y := rfl

theorem project_pack (x : Config e leftSym R rate) (ρ : Role) (bit : Bool) :
    project (pack x ρ bit) = x := rfl

set_option maxRecDepth 2048 in
theorem realize {n₀ n₁ : ℕ} {x₀ x₁ : Config e leftSym R rate}
    {a : State e leftSym R rate Text leftPat rightPat p r n₀ x₀}
    {b : State e leftSym R rate Text leftPat rightPat p r n₁ x₁} {ops : List (Option Terminal)}
    (h : Trace e leftSym R rate enc Text leftPat rightPat p r a ops b)
    (hc : Function.Injective e.code) (ρ : Role) (bit : Bool) :
    ∃ ρ' bit', opRun e leftSym R rate enc ops (pack x₀ ρ bit) = pack x₁ ρ' bit' := by
  induction h generalizing ρ bit with
  | refl => exact ⟨ρ, bit, rfl⟩
  | @worker n x a b hz he =>
    obtain ⟨u, caller, hv⟩ := b.valid
    have hp := TextFeedPipelineOutput.step_preserves (Terminal := Terminal) hc (pack x ρ bit) hv
    let y := opRun e leftSym R rate enc [none] (pack x ρ bit)
    change project y = TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x at hp
    exact ⟨y.1.2.1, y.1.2.2, by rw [← hp]; exact (pack_project y).symm⟩
  | @arrival n x c a b hz he =>
    obtain ⟨u, caller, hv⟩ := b.valid
    have hp := TextFeedPipelineOutput.step_preserves (Terminal := Terminal) hc
      (pack (captured e leftSym R rate enc c x) ρ bit) hv
    let y := TextFeedPipelineOutput.step (Terminal := Terminal) e leftSym R rate
      (pack (captured e leftSym R rate enc c x) ρ bit)
    change project y = TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate
      (captured e leftSym R rate enc c x) at hp
    refine ⟨y.1.2.1, y.1.2.2, ?_⟩
    simp only [opRun, List.foldl_cons, List.foldl_nil, opStep, project_pack]
    rw [← hp]
    exact (pack_project y).symm
  | @trans n₀ n₁ n₂ x₀ x₁ x₂ xs ys a b c h h' ih ih' =>
    obtain ⟨ρ₁, b₁, h₁⟩ := ih ρ bit
    obtain ⟨ρ₂, b₂, h₂⟩ := ih' ρ₁ b₁
    refine ⟨ρ₂, b₂, ?_⟩
    simp only [opRun, List.foldl_append]
    change opRun e leftSym R rate enc ys (opRun e leftSym R rate enc xs (pack x₀ ρ bit)) = _
    rw [h₁, h₂]

theorem sample_sticky (y : View e leftSym R rate) (h : y.1.2.2 = true) :
    (TextFeedPipelineOutput.sample e leftSym R rate y).1.2.2 = true := by
  unfold TextFeedPipelineOutput.sample
  split <;> simp [h]

theorem sticky {n₀ n₁ : ℕ} {x₀ x₁ : Config e leftSym R rate}
    {a : State e leftSym R rate Text leftPat rightPat p r n₀ x₀}
    {b : State e leftSym R rate Text leftPat rightPat p r n₁ x₁} {ops : List (Option Terminal)}
    (h : Trace e leftSym R rate enc Text leftPat rightPat p r a ops b)
    (hc : Function.Injective e.code) (heq : n₀ = n₁) (ρ : Role) :
    (opRun e leftSym R rate enc ops (pack x₀ ρ true)).1.2.2 = true := by
  induction h generalizing ρ with
  | refl => rfl
  | worker hz he =>
    apply sample_sticky
    simpa only [pack, if_neg hz]
  | arrival c hz he => omega
  | trans h h' ih ih' =>
    have hf := h.frontier
    have hf' := h'.frontier
    obtain ⟨ρ₁, bit₁, hr⟩ := realize h hc ρ true
    have hb := ih (by omega) ρ
    rw [hr] at hb
    change bit₁ = true at hb
    subst bit₁
    simp only [opRun, List.foldl_append]
    change (opRun e leftSym R rate enc _ (opRun e leftSym R rate enc _ (pack _ ρ true))).1.2.2 = true
    rw [hr]
    exact ih' (by omega) ρ₁

theorem last_sample {n₀ n₁ : ℕ} {x₀ x₁ : Config e leftSym R rate}
    {a : State e leftSym R rate Text leftPat rightPat p r n₀ x₀}
    {b : State e leftSym R rate Text leftPat rightPat p r n₁ x₁} {ops : List (Option Terminal)}
    (h : Trace e leftSym R rate enc Text leftPat rightPat p r a ops b)
    (hc : Function.Injective e.code) (hne : ops ≠ []) (ρ : Role) (bit : Bool) :
    ∃ ρ' bit', opRun e leftSym R rate enc ops (pack x₀ ρ bit) =
      TextFeedPipelineOutput.sample e leftSym R rate (pack x₁ ρ' bit') := by
  induction h generalizing ρ bit with
  | refl => exact False.elim (hne rfl)
  | worker hz he => exact ⟨ρ, bit, by simp only [opRun, List.foldl_cons, List.foldl_nil,
      opStep, TextFeedPipelineOutput.step, pack, if_neg hz]⟩
  | arrival c hz he => exact ⟨ρ, false, by simp only [opRun, List.foldl_cons, List.foldl_nil,
      opStep, TextFeedPipelineOutput.step, pack, project, captured, hz, ↓reduceIte]⟩
  | @trans n₀ n₁ n₂ x₀ x₁ x₂ xs ys a b c h h' ih ih' =>
    by_cases hy : ys = []
    · have hx : xs ≠ [] := by simpa only [hy, List.append_nil] using hne
      obtain ⟨ρ₁, b₁, hs⟩ := ih hx ρ bit
      obtain ⟨ρ₂, b₂, hp⟩ := realize h' hc ρ₁ b₁
      have he : x₁ = x₂ := by
        have hh := congrArg project hp
        simpa only [hy, opRun, List.foldl_nil, project, pack] using hh
      refine ⟨ρ₁, b₁, ?_⟩
      simpa only [hy, List.append_nil, he] using hs
    · obtain ⟨ρ₁, b₁, hp⟩ := realize h hc ρ bit
      obtain ⟨ρ₂, b₂, hs⟩ := ih' hy ρ₁ b₁
      refine ⟨ρ₂, b₂, ?_⟩
      simp only [opRun, List.foldl_append]
      change opRun e leftSym R rate enc ys (opRun e leftSym R rate enc xs (pack x₀ ρ bit)) = _
      rw [hp, hs]

def embed (y : View e leftSym R rate) :
    SConfig ((TextFeedPipelineOutput.State e leftSym R rate × Fin 96) × Fin ((R + 1) * 96 + 1)) (Fin k) 39 :=
  ⟨((y.1, 0), 0), y.2⟩

theorem opRun_none (N : ℕ) (y : View e leftSym R rate) :
    opRun e leftSym R rate enc (List.replicate N none) y =
      (TextFeedPipelineOutput.step (Terminal := Terminal) e leftSym R rate)^[N] y := by
  induction N generalizing y with
  | zero => rfl
  | succ N ih =>
    rw [List.replicate_succ]
    change opRun e leftSym R rate enc (List.replicate N none)
      (TextFeedPipelineOutput.step (Terminal := Terminal) e leftSym R rate y) = _
    rw [ih, Function.iterate_succ_apply]

theorem opRun_frame (c : Terminal) (y : View e leftSym R rate) :
    opRun e leftSym R rate enc (some c :: List.replicate R none) y =
      (TextFeedPipelineOutput.step (Terminal := Terminal) e leftSym R rate)^[R + 1]
        (pack (captured e leftSym R rate enc c (project y)) y.1.2.1 y.1.2.2) := by
  change opRun e leftSym R rate enc (List.replicate R none)
    (TextFeedPipelineOutput.step (Terminal := Terminal) e leftSym R rate
      (pack (captured e leftSym R rate enc c (project y)) y.1.2.1 y.1.2.2)) = _
  rw [opRun_none, Function.iterate_succ_apply]

/-- The call word used by the proof is exactly the finite machine's
external-input execution, with both physical clocks restored each round. -/
theorem machine_frames (as : List Terminal) (y : View e leftSym R rate) :
    as.foldl (TextFeedPipelineOutput.machine e leftSym enc R rate).sRound (embed y) =
      embed (opRun e leftSym R rate enc (schedule R as) y) := by
  induction as generalizing y with
  | nil => rfl
  | cons c cs ih =>
    have hm : (TextFeedPipelineOutput.machine e leftSym enc R rate).sRound (embed y) c =
        embed ((TextFeedPipelineOutput.step (Terminal := Terminal) e leftSym R rate)^[R + 1]
          (pack (captured e leftSym R rate enc c (project y)) y.1.2.1 y.1.2.2)) := by
      simpa only [embed, pack, captured, project] using
        TextFeedPipelineOutput.machine_round e leftSym enc R rate y.1 y.2 c
    rw [List.foldl_cons, hm, ih]
    have he : opRun e leftSym R rate enc (schedule R (c :: cs)) y =
        opRun e leftSym R rate enc (schedule R cs)
          (opRun e leftSym R rate enc (some c :: List.replicate R none) y) := by
      simp only [schedule, List.flatMap_cons, opRun, List.foldl_append]
    rw [he, opRun_frame]

theorem machine_output (as : List Terminal) (y : View e leftSym R rate) :
    (TextFeedPipelineOutput.machine e leftSym enc R rate).accepting
      (as.foldl (TextFeedPipelineOutput.machine e leftSym enc R rate).sRound (embed y)).state =
      (opRun e leftSym R rate enc (schedule R as) y).1.2.2 := by
  rw [machine_frames]
  rfl

theorem entry_sample {n : ℕ} {x : Config e leftSym R rate}
    (d : Entry e leftSym R rate Text leftPat rightPat p r n x)
    (hc : Function.Injective e.code) (hr : d.rank = 2)
    (hb : e.blank ∉ Text) (hn : n ≤ Text.length) (hmb : e.mark ≠ e.blank)
    (hel : e.endSym ∉ leftPat) (her : e.endSym ∉ rightPat)
    (ρ : Role) (bit : Bool) :
    (TextFeedPipelineOutput.sample e leftSym R rate (pack x ρ bit)).1.2.2 =
      (bit || zReportFlag leftPat rightPat n d.z) := by
  have hv : Valid e leftSym R rate Text n x d.u [verifyBody rate, verifyLoop rate] := by
    simpa only [hr, TextFeedPipelineReentryInput.caller] using d.valid.1
  have hframes : d.u.frames = [] := by simpa only [hr] using d.valid.2
  obtain ⟨he, hq, hh, hp⟩ := TextFeedPipelineMacroResult.initial_encoding d.origin.refines d.feed d.ghost
  have he' := d.ideal.symm ▸ he
  have hfeed := (TextFeedPipelineMacroResult.feed_of_zencoding hv.refines he' hq hh hp).1
  have hsample := TextFeedPipelineOutput.sample_report hc
    (TextFeedPipelineMacroBoundary.annotate_valid hv d.z) hframes hfeed rfl
    (d.dir.trans d.direction) hb hn hmb hel her ρ bit
  rw [show pack x ρ bit = ((x.1, ρ, bit), x.2) from rfl, hsample]

/-- Actual output along arbitrary service traces, including a partial
startup frame. The queue observer is executed at the report node. -/
theorem trace_output {i n n' : ℕ} {x y : Config e leftSym R rate}
    (hcode : Function.Injective e.code) {a : State e leftSym R rate Text leftPat rightPat p r n x}
    {b : State e leftSym R rate Text leftPat rightPat p r n' y}
    {ops : List (Option Terminal)}
    (htotal : Trace e leftSym R rate enc Text leftPat rightPat p r a ops b)
    (hc : ∀ z, Conditions e Text leftPat rightPat rate p r z)
    (hK : KSimple rightPat rate p r)
    (hdeadline : ZDeadline leftPat rightPat rate p r)
    (hn : n' ≤ Text.length) (hb : target rate rightPat n' ≤ b.score)
    (hi : ScanInv rightPat (TextFeed.padW e.blank Text Text.length) a.z.1)
    (hzi : ZInv leftPat rightPat (TextFeed.padW e.blank Text Text.length) a.z)
    (ho : OccAt rightPat (TextFeed.padW e.blank Text Text.length) i)
    (hu : MatchLen leftPat (TextFeed.padW e.blank Text Text.length) (i - leftPat.length) leftPat.length)
    (hp : a.z.1.pos ≤ i) (hbefore : n < i + rightPat.length)
    (hd : i + rightPat.length = n') (ρ : Role) (bit : Bool) :
    (opRun e leftSym R rate enc ops (pack x ρ bit)).1.2.2 = true := by
  obtain ⟨m, y, d, pre, post, hsplit, ht, ht', hr, hhit⟩ :=
    TextFeedPipelineDeadline.trace_report htotal hc hK hb hi ho hp hbefore hd
  have hm : m = n' := by
    have hupper := ht'.frontier
    have hlower := (State.entry d).fits.1
    change d.z.1.pos + d.z.1.q ≤ m at hlower
    rw [hhit.1, hhit.2] at hlower
    omega
  have hpre : pre ≠ [] := by
    intro he
    have htime := ht.time_le
    simp only [he, List.length_nil, Nat.add_zero] at htime
    omega
  have hinv := trace_invariant ht
    (fun z => ScanInv rightPat (TextFeed.padW e.blank Text Text.length) z.1 ∧
      ZInv leftPat rightPat (TextFeed.padW e.blank Text Text.length) z)
    (by
      intro z hz
      exact ⟨by simpa only [vStepZ_fst] using scanStep_inv hK hz.1,
        vStepZ_inv (hc z).positive_p hdeadline hz.1 hz.2⟩) ⟨hi, hzi⟩
  have hfull : MatchLen leftPat (TextFeed.padW e.blank Text Text.length)
      (d.z.1.pos - leftPat.length) leftPat.length := by simpa only [hhit.1] using hu
  have hflag : zReportFlag leftPat rightPat m d.z = true :=
    zReportFlag_complete (z := d.z) hinv.2 hfull hhit.2 (by rw [hhit.1]; omega)
  obtain ⟨ρ₁, b₁, hsample⟩ := last_sample ht hcode hpre ρ bit
  have hb : (opRun e leftSym R rate enc pre (pack x ρ bit)).1.2.2 = true := by
    rw [hsample]
    simpa only [hflag, Bool.or_true] using entry_sample d hcode hr (hc d.z).blank_text (by omega)
      (hc d.z).mark_blank (hc d.z).end_left (hc d.z).end_right ρ₁ b₁
  obtain ⟨ρ₂, b₂, hreal⟩ := realize ht hcode ρ bit
  rw [hreal] at hb
  change b₂ = true at hb
  subst b₂
  rw [hsplit]
  simp only [opRun, List.foldl_append]
  change (opRun e leftSym R rate enc post (opRun e leftSym R rate enc pre (pack x ρ bit))).1.2.2 = true
  rw [hreal]
  exact sticky ht' hcode hm ρ₂

/-- Full input frames are an instance of the arbitrary-trace output theorem. -/
theorem frames_output {i n : ℕ} {x : Config e leftSym R rate}
    (hcode : Function.Injective e.code) (a : State e leftSym R rate Text leftPat rightPat p r n x)
    (hc : ∀ z, Conditions e Text leftPat rightPat rate p r z)
    (hK : KSimple rightPat rate p r) (hpat : 0 < rightPat.length)
    (hdeadline : ZDeadline leftPat rightPat rate p r)
    (as : List Terminal) (hn : n + as.length ≤ Text.length)
    (has : ∀ j c, as[j]? = some c → Text[n + j]? = some (enc c))
    (hz : x.1.1.1 = 0) (hfirst : x.1.1.2.1 = false)
    (hR : progressRate rate * (rate + 1) ≤ R) (ha : target rate rightPat n ≤ a.score)
    (hi : ScanInv rightPat (TextFeed.padW e.blank Text Text.length) a.z.1)
    (hzi : ZInv leftPat rightPat (TextFeed.padW e.blank Text Text.length) a.z)
    (ho : OccAt rightPat (TextFeed.padW e.blank Text Text.length) i)
    (hu : MatchLen leftPat (TextFeed.padW e.blank Text Text.length) (i - leftPat.length) leftPat.length)
    (hp : a.z.1.pos ≤ i) (hbefore : n < i + rightPat.length)
    (hd : i + rightPat.length = n + as.length) (ρ : Role) (bit : Bool) :
    (TextFeedPipelineOutput.machine e leftSym enc R rate).accepting
      (as.foldl (TextFeedPipelineOutput.machine e leftSym enc R rate).sRound
        (embed (pack x ρ bit))).state = true := by
  rw [machine_output]
  obtain ⟨b, ht, hb⟩ := a.frames hcode leftSym R rate enc hc hpat as hn has hz hfirst hR ha
  exact trace_output hcode ht hc hK hdeadline hn hb hi hzi ho hu hp hbefore hd ρ bit

/-- info: 'PalPeg.TextFeedPipelineObserved.trace_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms trace_output

/-- info: 'PalPeg.TextFeedPipelineObserved.frames_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms frames_output

end PalPeg.TextFeedPipelineObserved
