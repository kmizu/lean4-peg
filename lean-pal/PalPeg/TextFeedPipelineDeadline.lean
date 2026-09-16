import PalPeg.TextFeedPipelineService
import PalPeg.TextFeedPipelineOutput

/-! Occurrence deadlines for the real pipeline, including suspended
instructions and reentry. Reports are located in its actual call trace. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelineDeadline
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.TextFeedControl
open PalPeg.TextFeedPipelineControl PalPeg.TextFeedPipelineCoupled PalPeg.TextFeedPipelineInputRun
open PalPeg.TextFeedPipelineInputMacro PalPeg.TextFeedPipelineService PalPeg.TextFeedPipelineFrontier
open PalPeg.GSVerifierZ

variable {k : ℕ} {Terminal : Type} {e : Env k} {leftSym : Fin k} {R rate p r : ℕ}
variable {Text leftPat rightPat : List (Fin k)} {enc : Terminal → Fin k}

def Hit (i : ℕ) (z : VStateZ) : Prop := z.1.pos = i ∧ z.1.q = rightPat.length

def Visited (i : ℕ) {n₀ n₁ : ℕ} {x₀ x₁ : Config e leftSym R rate}
    (a : State e leftSym R rate Text leftPat rightPat p r n₀ x₀)
    (ops : List (Option Terminal)) (b : State e leftSym R rate Text leftPat rightPat p r n₁ x₁) : Prop :=
  ∃ m y, ∃ d : Entry e leftSym R rate Text leftPat rightPat p r m y, ∃ pre post,
    ops = pre ++ post ∧ Trace e leftSym R rate enc Text leftPat rightPat p r a pre (.entry d) ∧
    Trace e leftSym R rate enc Text leftPat rightPat p r (.entry d) post b ∧
    d.rank = 2 ∧ Hit (rightPat := rightPat) i d.z

theorem Visited.append_right {i n₀ n₁ n₂ : ℕ} {x₀ x₁ x₂ : Config e leftSym R rate}
    {a : State e leftSym R rate Text leftPat rightPat p r n₀ x₀}
    {b : State e leftSym R rate Text leftPat rightPat p r n₁ x₁}
    {c : State e leftSym R rate Text leftPat rightPat p r n₂ x₂} {xs ys : List (Option Terminal)}
    (h : Visited (enc := enc) i a xs b)
    (ht : Trace e leftSym R rate enc Text leftPat rightPat p r b ys c) :
    Visited (enc := enc) i a (xs ++ ys) c := by
  obtain ⟨m, y, d, pre, post, he, hp, hs, hr, hh⟩ := h
  exact ⟨m, y, d, pre, post ++ ys, by simp only [he, List.append_assoc], hp, hs.trans ht, hr, hh⟩

theorem Visited.append_left {i n₀ n₁ n₂ : ℕ} {x₀ x₁ x₂ : Config e leftSym R rate}
    {a : State e leftSym R rate Text leftPat rightPat p r n₀ x₀}
    {b : State e leftSym R rate Text leftPat rightPat p r n₁ x₁}
    {c : State e leftSym R rate Text leftPat rightPat p r n₂ x₂} {xs ys : List (Option Terminal)}
    (ht : Trace e leftSym R rate enc Text leftPat rightPat p r a xs b)
    (h : Visited (enc := enc) i b ys c) : Visited (enc := enc) i a (xs ++ ys) c := by
  obtain ⟨m, y, d, pre, post, he, hp, hs, hr, hh⟩ := h
  exact ⟨m, y, d, xs ++ pre, post, by simp only [he, List.append_assoc], ht.trans hp, hs, hr, hh⟩

theorem trace_invariant {n₀ n₁ : ℕ} {x₀ x₁ : Config e leftSym R rate}
    {a : State e leftSym R rate Text leftPat rightPat p r n₀ x₀}
    {b : State e leftSym R rate Text leftPat rightPat p r n₁ x₁} {ops : List (Option Terminal)}
    (h : Trace e leftSym R rate enc Text leftPat rightPat p r a ops b)
    (P : VStateZ → Prop)
    (hp : ∀ z, P z → P (vStepZ leftPat rightPat rate p r (TextFeed.padW e.blank Text Text.length) z)) :
    P a.z → P b.z := by
  induction h with
  | refl => exact id
  | worker hz he =>
    intro ha
    rcases he with he | ⟨he, _⟩
    · simpa only [he] using ha
    · simpa only [he] using hp _ ha
  | arrival c hz he => intro ha; simpa only [he] using ha
  | trans h h' ih ih' => exact fun ha => ih' (ih ha)

/-- Safe shifts preserve the candidate unless a real return has already
visited its matching state. -/
theorem no_skip_or_report {i n₀ n₁ : ℕ} {x₀ x₁ : Config e leftSym R rate}
    {a : State e leftSym R rate Text leftPat rightPat p r n₀ x₀}
    {b : State e leftSym R rate Text leftPat rightPat p r n₁ x₁} {ops : List (Option Terminal)}
    (h : Trace e leftSym R rate enc Text leftPat rightPat p r a ops b)
    (hK : KSimple rightPat rate p r) (hrate : 0 < rate)
    (ho : OccAt rightPat (TextFeed.padW e.blank Text Text.length) i) :
    ScanInv rightPat (TextFeed.padW e.blank Text Text.length) a.z.1 → a.z.1.pos ≤ i →
    ¬ Hit (rightPat := rightPat) i a.z →
    (ScanInv rightPat (TextFeed.padW e.blank Text Text.length) b.z.1 ∧ b.z.1.pos ≤ i ∧
      ¬ Hit (rightPat := rightPat) i b.z) ∨ Visited (enc := enc) i a ops b := by
  induction h with
  | refl a => exact fun hi hp hn => Or.inl ⟨hi, hp, hn⟩
  | @worker n x a b hz he =>
    intro hi hp hn
    rcases he with he | ⟨he, d, hb, hr⟩
    · exact Or.inl (by simpa only [he] using (show _ ∧ _ ∧ _ from ⟨hi, hp, hn⟩))
    · have hi' : ScanInv rightPat (TextFeed.padW e.blank Text Text.length) b.z.1 := by
        rw [he, vStepZ_fst]
        exact scanStep_inv hK hi
      have hp' : b.z.1.pos ≤ i := by
        rw [he, vStepZ_fst]
        exact scanStep_pos_le_of_occ hK hrate hi ho hp (fun hq heq => hn ⟨heq, hq⟩)
      by_cases hh : Hit (rightPat := rightPat) i b.z
      · subst b
        exact Or.inr ⟨n, _, d, [none], [], rfl,
          .worker hz (Or.inr ⟨he, d, rfl, hr⟩), .refl _, hr, hh⟩
      · exact Or.inl ⟨hi', hp', hh⟩
  | arrival c hz he =>
    intro hi hp hn
    exact Or.inl (by simpa only [he] using (show _ ∧ _ ∧ _ from ⟨hi, hp, hn⟩))
  | trans h h' ih ih' =>
    intro hi hp hn
    rcases ih hi hp hn with ⟨hi₁, hp₁, hn₁⟩ | hv
    · rcases ih' hi₁ hp₁ hn₁ with hh | hv
      · exact Or.inl hh
      · exact Or.inr (hv.append_left h)
    · exact Or.inr (hv.append_right h')

/-- At the exact deadline an unreported state is strictly short of the
required service, including partially executed macros and reentry. -/
theorem score_lt_deadline {i n : ℕ} {x : Config e leftSym R rate}
    (a : State e leftSym R rate Text leftPat rightPat p r n x)
    (hc : ∀ z, Conditions e Text leftPat rightPat rate p r z)
    (hK : KSimple rightPat rate p r)
    (hi : ScanInv rightPat (TextFeed.padW e.blank Text Text.length) a.z.1)
    (ho : OccAt rightPat (TextFeed.padW e.blank Text Text.length) i)
    (hp : a.z.1.pos ≤ i) (hh : ¬ Hit (rightPat := rightPat) i a.z)
    (hd : i + rightPat.length = n) : a.score < target rate rightPat n := by
  cases a with
  | «macro» a =>
    have hl := prefix_before_deadline a.waits a.origin.refines a.start (hc a.z)
      a.follows a.credit hK hi ho hp hh
    have hw := a.wait_le
    simp only [State.score, Macro.score, target]
    simp only [Nat.mul_add, hd] at hl
    omega
  | entry a =>
    have hq := a.feed.qle
    simp only [a.ghost] at hq
    have hm := Nat.mul_le_mul_left (rate + 1) hp
    simp only [State.z] at hm
    have hb : Phi rate a.z.1 + rate * rightPat.length ≤ (rate + 1) * n := by
      have heq := congrArg (fun j => (rate + 1) * j) hd
      simp only [Phi]
      nlinarith
    have hb' := Nat.mul_le_mul_left (progressRate rate) hb
    simp only [Nat.mul_add] at hb'
    have := a.paid
    have := a.positive
    simp only [State.score, Entry.score, target]
    omega

/-- Any actual call trace that reaches the deadline with enough service
credit must contain the report, even if it starts inside an input frame. -/
theorem trace_report {i n₀ n₁ : ℕ} {x₀ x₁ : Config e leftSym R rate}
    {a : State e leftSym R rate Text leftPat rightPat p r n₀ x₀}
    {b : State e leftSym R rate Text leftPat rightPat p r n₁ x₁}
    {ops : List (Option Terminal)}
    (ht : Trace e leftSym R rate enc Text leftPat rightPat p r a ops b)
    (hc : ∀ z, Conditions e Text leftPat rightPat rate p r z)
    (hK : KSimple rightPat rate p r) (hb : target rate rightPat n₁ ≤ b.score)
    (hi : ScanInv rightPat (TextFeed.padW e.blank Text Text.length) a.z.1)
    (ho : OccAt rightPat (TextFeed.padW e.blank Text Text.length) i)
    (hp : a.z.1.pos ≤ i) (hbefore : n₀ < i + rightPat.length)
    (hd : i + rightPat.length = n₁) : Visited (enc := enc) i a ops b := by
  have hno : ¬ Hit (rightPat := rightPat) i a.z := by
    rintro ⟨hpos, hq⟩
    have hh := a.fits.1
    rw [hpos, hq] at hh
    omega
  rcases no_skip_or_report ht hK (hc a.z).positive_rate ho hi hp hno with ⟨hi', hp', hh'⟩ | hv
  · exact False.elim ((Nat.not_lt_of_ge hb) (score_lt_deadline b hc hK hi' ho hp' hh' hd))
  · exact hv

/-- The full input-frame service theorem forces an actual report node,
not just an abstract interpreter state or a future-input promise. -/
theorem frames_report {i n : ℕ} {x : Config e leftSym R rate}
    (hcode : Function.Injective e.code) (a : State e leftSym R rate Text leftPat rightPat p r n x)
    (hc : ∀ z, Conditions e Text leftPat rightPat rate p r z)
    (hK : KSimple rightPat rate p r) (hpat : 0 < rightPat.length)
    (as : List Terminal) (hn : n + as.length ≤ Text.length)
    (has : ∀ j c, as[j]? = some c → Text[n + j]? = some (enc c))
    (hz : x.1.1.1 = 0) (hfirst : x.1.1.2.1 = false)
    (hR : progressRate rate * (rate + 1) ≤ R) (ha : target rate rightPat n ≤ a.score)
    (hi : ScanInv rightPat (TextFeed.padW e.blank Text Text.length) a.z.1)
    (ho : OccAt rightPat (TextFeed.padW e.blank Text Text.length) i) (hp : a.z.1.pos ≤ i)
    (hbefore : n < i + rightPat.length) (hd : i + rightPat.length = n + as.length) :
    ∃ b : State e leftSym R rate Text leftPat rightPat p r (n + as.length)
        (frames e leftSym R rate enc as x), Visited (enc := enc) i a (schedule R as) b := by
  obtain ⟨b, ht, hb⟩ := a.frames hcode leftSym R rate enc hc hpat as hn has hz hfirst hR ha
  exact ⟨b, trace_report ht hc hK hb hi ho hp hbefore hd⟩

/-- info: 'PalPeg.TextFeedPipelineDeadline.frames_report' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms frames_report

end PalPeg.TextFeedPipelineDeadline
