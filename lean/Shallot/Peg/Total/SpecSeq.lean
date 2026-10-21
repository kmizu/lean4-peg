import Shallot.Peg.Total.Spec

/-!
# The specification for sequence, choice and not-predicate

Each lemma takes the specifications of the parts and gives the one of the compound expression, by cases on the
behaviors of the parts. For a sequence, the second part runs with the same open set where the first part consumed
nothing, and with the empty set (at a shorter suffix) where it consumed.
-/

namespace Shallot

section Seq

variable {g G : Grammar} {S : Nat} {a b : PExp} {x : List Char} {ta tb tb0 : Tr}

/-- A sequence whose first part fails. -/
theorem spec_seq_fl (hB : Beh g S a x .fl) (hG : Good G ta x .fl) :
    Spec g G (seqT ta tb tb0) S (.seq a b) x := by
  obtain ⟨hz, hp, hl⟩ := hG
  exact ⟨.fl, .seqFail₁ _ _ _ _ hB, .seqFail₁ _ _ _ hz, .altFail _ _ _ (.seqFail₁ _ _ _ hz) (.seqFail₁ _ _ _ hp),
    .altFail _ _ _ hl (.altFail _ _ _ (.seqFail₁ _ _ _ hz) (.seqFail₁ _ _ _ hp))⟩

/-- A sequence whose first part loops. -/
theorem spec_seq_lp (hB : Beh g S a x .lp) (hG : Good G ta x .lp) :
    Spec g G (seqT ta tb tb0) S (.seq a b) x := by
  obtain ⟨hz, hp, r, t, hl⟩ := hG
  refine ⟨.lp, ?_, .seqFail₁ _ _ _ hz, .altFail _ _ _ (.seqFail₁ _ _ _ hz) (.seqFail₁ _ _ _ hp),
    r, _, .altL _ _ _ _ _ hl⟩
  intro o h
  cases h with
  | seqOk _ _ _ _ _ _ _ _ h₁ _ => exact hB _ h₁
  | seqFail₁ _ _ _ _ h₁ => exact hB _ h₁
  | seqFail₂ _ _ _ _ _ _ h₁ _ => exact hB _ h₁

/-- A sequence whose first part succeeds consuming nothing. -/
theorem spec_seq_okE (hB : Beh g S a x .okE) (hG : Good G ta x .okE) (hb : Spec g G tb S b x) :
    Spec g G (seqT ta tb tb0) S (.seq a b) x := by
  obtain ⟨t₁, h₁⟩ := hB
  obtain ⟨⟨tz, hz⟩, hp, hl⟩ := hG
  obtain ⟨cb, hBb, hGb⟩ := hb
  have lift : ∀ {o}, DS g S b x o → DS g (nx S x x) b x o := fun h => by rw [nx_eq]; exact h
  cases cb with
  | okE =>
    obtain ⟨t₂, h₂⟩ := hBb
    obtain ⟨⟨tz', hz'⟩, hp', hl'⟩ := hGb
    exact ⟨.okE, ⟨_, .seqOk _ _ _ _ _ _ _ _ h₁ (lift h₂)⟩, ⟨_, .seqOk _ _ _ _ _ _ _ hz hz'⟩,
      .altFail _ _ _ (.seqFail₂ _ _ _ _ _ hz hp') (.seqFail₁ _ _ _ hp),
      .altFail _ _ _ hl (.altFail _ _ _ (.seqFail₂ _ _ _ _ _ hz hl') (.seqFail₁ _ _ _ hp))⟩
  | okC r =>
    obtain ⟨hne, t₂, h₂⟩ := hBb
    obtain ⟨hz', ⟨tp', hp'⟩, hl'⟩ := hGb
    exact ⟨.okC r, ⟨hne, _, .seqOk _ _ _ _ _ _ _ _ h₁ (lift h₂)⟩, .seqFail₂ _ _ _ _ _ hz hz',
      ⟨_, .altL _ _ _ _ _ (.seqOk _ _ _ _ _ _ _ hz hp')⟩,
      .altFail _ _ _ hl (.altFail _ _ _ (.seqFail₂ _ _ _ _ _ hz hl') (.seqFail₁ _ _ _ hp))⟩
  | fl =>
    obtain ⟨hz', hp', hl'⟩ := hGb
    exact ⟨.fl, .seqFail₂ _ _ _ _ _ _ h₁ (lift hBb), .seqFail₂ _ _ _ _ _ hz hz',
      .altFail _ _ _ (.seqFail₂ _ _ _ _ _ hz hp') (.seqFail₁ _ _ _ hp),
      .altFail _ _ _ hl (.altFail _ _ _ (.seqFail₂ _ _ _ _ _ hz hl') (.seqFail₁ _ _ _ hp))⟩
  | lp =>
    obtain ⟨hz', hp', r', tl', hl'⟩ := hGb
    refine ⟨.lp, ?_, .seqFail₂ _ _ _ _ _ hz hz', .altFail _ _ _ (.seqFail₂ _ _ _ _ _ hz hp') (.seqFail₁ _ _ _ hp),
      r', _, .altR _ _ _ _ _ hl (.altL _ _ _ _ _ (.seqOk _ _ _ _ _ _ _ hz hl'))⟩
    intro o h
    cases h with
    | seqOk _ _ _ _ _ _ _ _ h₁' h₂' =>
      cases ds_det h₁ h₁'; rw [nx_eq] at h₂'; exact hBb _ h₂'
    | seqFail₁ _ _ _ _ h₁' => cases ds_det h₁ h₁'
    | seqFail₂ _ _ _ _ _ _ h₁' h₂' =>
      cases ds_det h₁ h₁'; rw [nx_eq] at h₂'; exact hBb _ h₂'

/-- A sequence whose first part consumes, reaching `r`. -/
theorem spec_seq_okC {r : List Char} (hB : Beh g S a x (.okC r)) (hG : Good G ta x (.okC r))
    (hb0 : Spec g G tb0 0 b r) : Spec g G (seqT ta tb tb0) S (.seq a b) x := by
  obtain ⟨hne, t₁, h₁⟩ := hB
  obtain ⟨hz, ⟨tp, hp⟩, hl⟩ := hG
  obtain ⟨cb, hBb, hGb⟩ := hb0
  have lift : ∀ {o}, DS g 0 b r o → DS g (nx S x r) b r o := fun h => by rw [nx_ne hne]; exact h
  have hlt := ds_lt h₁ hne
  cases cb with
  | okE =>
    obtain ⟨t₂, h₂⟩ := hBb
    obtain ⟨tr', hr'⟩ := r_okE hGb
    exact ⟨.okC r, ⟨hne, _, .seqOk _ _ _ _ _ _ _ _ h₁ (lift h₂)⟩, .seqFail₁ _ _ _ hz,
      ⟨_, .altR _ _ _ _ _ (.seqFail₁ _ _ _ hz) (.seqOk _ _ _ _ _ _ _ hp hr')⟩,
      .altFail _ _ _ hl (.altFail _ _ _ (.seqFail₁ _ _ _ hz) (.seqFail₂ _ _ _ _ _ hp hGb.2.2))⟩
  | okC r₂ =>
    obtain ⟨hne₂, t₂, h₂⟩ := hBb
    obtain ⟨tr', hr'⟩ := r_okC hGb
    have hne' : r₂ ≠ x := by
      intro h; subst h; have := ds_lt h₂ hne₂; omega
    exact ⟨.okC r₂, ⟨hne', _, .seqOk _ _ _ _ _ _ _ _ h₁ (lift h₂)⟩, .seqFail₁ _ _ _ hz,
      ⟨_, .altR _ _ _ _ _ (.seqFail₁ _ _ _ hz) (.seqOk _ _ _ _ _ _ _ hp hr')⟩,
      .altFail _ _ _ hl (.altFail _ _ _ (.seqFail₁ _ _ _ hz) (.seqFail₂ _ _ _ _ _ hp hGb.2.2))⟩
  | fl =>
    exact ⟨.fl, .seqFail₂ _ _ _ _ _ _ h₁ (lift hBb), .seqFail₁ _ _ _ hz,
      .altFail _ _ _ (.seqFail₁ _ _ _ hz) (.seqFail₂ _ _ _ _ _ hp (r_fl hGb)),
      .altFail _ _ _ hl (.altFail _ _ _ (.seqFail₁ _ _ _ hz) (.seqFail₂ _ _ _ _ _ hp hGb.2.2))⟩
  | lp =>
    obtain ⟨r', tl', hl'⟩ := hGb.2.2
    refine ⟨.lp, ?_, .seqFail₁ _ _ _ hz, .altFail _ _ _ (.seqFail₁ _ _ _ hz) (.seqFail₂ _ _ _ _ _ hp (r_lp hGb)),
      r', _, .altR _ _ _ _ _ hl (.altR _ _ _ _ _ (.seqFail₁ _ _ _ hz) (.seqOk _ _ _ _ _ _ _ hp hl'))⟩
    intro o h
    cases h with
    | seqOk _ _ _ _ _ _ _ _ h₁' h₂' =>
      cases ds_det h₁ h₁'; rw [nx_ne hne] at h₂'; exact hBb _ h₂'
    | seqFail₁ _ _ _ _ h₁' => cases ds_det h₁ h₁'
    | seqFail₂ _ _ _ _ _ _ h₁' h₂' =>
      cases ds_det h₁ h₁'; rw [nx_ne hne] at h₂'; exact hBb _ h₂'

/-- **Sequence.** -/
theorem spec_seq (ha : Spec g G ta S a x) (hb : Spec g G tb S b x)
    (hb0 : ∀ r, r.length < x.length → Spec g G tb0 0 b r) : Spec g G (seqT ta tb tb0) S (.seq a b) x := by
  obtain ⟨ca, hB, hG⟩ := ha
  cases ca with
  | okE => exact spec_seq_okE hB hG hb
  | okC r => exact spec_seq_okC hB hG (hb0 r (ds_lt hB.2.choose_spec hB.1))
  | fl => exact spec_seq_fl hB hG
  | lp => exact spec_seq_lp hB hG

end Seq

/-! ## Choice -/

section Alt

variable {g G : Grammar} {S : Nat} {a b : PExp} {x : List Char} {ta tb : Tr}

/-- Where the first alternative fails, the choice behaves as the second. -/
theorem good_alt_fl (hG : Good G ta x .fl) {c : Cl} (hb : Good G tb x c) : Good G (altT ta tb) x c := by
  obtain ⟨tF, hF⟩ := fl_ok hG
  obtain ⟨hz, hp, hl⟩ := hG
  have lok : ∀ {u v r}, FlD G u x → OkD G v x r → OkD G (.alt u (.seq ta.fl v)) x r :=
    fun hu ⟨t, hv⟩ => ⟨_, .altR _ _ _ _ _ hu (.seqOk _ _ _ _ _ _ _ hF hv)⟩
  have lfl : ∀ {u v}, FlD G u x → FlD G v x → FlD G (.alt u (.seq ta.fl v)) x :=
    fun hu hv => .altFail _ _ _ hu (.seqFail₂ _ _ _ _ _ hF hv)
  cases c with
  | okE => obtain ⟨a', b', d'⟩ := hb; exact ⟨lok hz a', lfl hp b', lfl hl d'⟩
  | okC r => obtain ⟨a', b', d'⟩ := hb; exact ⟨lfl hz a', lok hp b', lfl hl d'⟩
  | fl => obtain ⟨a', b', d'⟩ := hb; exact ⟨lfl hz a', lfl hp b', lfl hl d'⟩
  | lp => obtain ⟨a', b', r, d'⟩ := hb; exact ⟨lfl hz a', lfl hp b', r, lok hl d'⟩

/-- **Prioritized choice.** -/
theorem spec_alt (ha : Spec g G ta S a x) (hb : Spec g G tb S b x) : Spec g G (altT ta tb) S (.alt a b) x := by
  obtain ⟨ca, hB, hG⟩ := ha
  cases ca with
  | okE =>
    obtain ⟨t, h⟩ := hB
    obtain ⟨⟨tz, hz⟩, hp, hl⟩ := hG
    have hF := fl_fail (c := .okE) ⟨⟨tz, hz⟩, hp, hl⟩ (by simp)
    exact ⟨.okE, ⟨_, .altL _ _ _ _ _ _ h⟩, ⟨_, .altL _ _ _ _ _ hz⟩, .altFail _ _ _ hp (.seqFail₁ _ _ _ hF),
      .altFail _ _ _ hl (.seqFail₁ _ _ _ hF)⟩
  | okC r =>
    obtain ⟨hne, t, h⟩ := hB
    obtain ⟨hz, ⟨tp, hp⟩, hl⟩ := hG
    have hF := fl_fail (c := .okC r) ⟨hz, ⟨tp, hp⟩, hl⟩ (by simp)
    exact ⟨.okC r, ⟨hne, _, .altL _ _ _ _ _ _ h⟩, .altFail _ _ _ hz (.seqFail₁ _ _ _ hF), ⟨_, .altL _ _ _ _ _ hp⟩,
      .altFail _ _ _ hl (.seqFail₁ _ _ _ hF)⟩
  | lp =>
    have hF := fl_fail hG (by simp)
    obtain ⟨hz, hp, r, tl, hl⟩ := hG
    refine ⟨.lp, ?_, .altFail _ _ _ hz (.seqFail₁ _ _ _ hF), .altFail _ _ _ hp (.seqFail₁ _ _ _ hF),
      r, _, .altL _ _ _ _ _ hl⟩
    intro o h
    cases h with
    | altL _ _ _ _ _ _ h₁ => exact hB _ h₁
    | altR _ _ _ _ _ _ h₁ _ => exact hB _ h₁
    | altFail _ _ _ _ h₁ _ => exact hB _ h₁
  | fl =>
    obtain ⟨cb, hBb, hGb⟩ := hb
    refine ⟨cb, ?_, good_alt_fl hG hGb⟩
    cases cb with
    | okE => obtain ⟨t, h⟩ := hBb; exact ⟨_, .altR _ _ _ _ _ _ hB h⟩
    | okC r => obtain ⟨hne, t, h⟩ := hBb; exact ⟨hne, _, .altR _ _ _ _ _ _ hB h⟩
    | fl => exact .altFail _ _ _ _ hB hBb
    | lp =>
      intro o h
      cases h with
      | altL _ _ _ _ _ _ h₁ => cases ds_det hB h₁
      | altR _ _ _ _ _ _ _ h₂ => exact hBb _ h₂
      | altFail _ _ _ _ _ h₂ => exact hBb _ h₂

end Alt

/-! ## Not-predicate -/

/-- **Not-predicate.** -/
theorem spec_not {g G : Grammar} {S : Nat} {a : PExp} {x : List Char} {ta : Tr} (ha : Spec g G ta S a x) :
    Spec g G (notT ta) S (.notP a) x := by
  obtain ⟨ca, hB, hG⟩ := ha
  cases ca with
  | okE =>
    obtain ⟨t, h⟩ := hB
    exact ⟨.fl, .notOk _ _ _ _ _ h, fl_fail hG (by simp), fail0, hG.2.2⟩
  | okC r =>
    obtain ⟨hne, t, h⟩ := hB
    exact ⟨.fl, .notOk _ _ _ _ _ h, fl_fail hG (by simp), fail0, hG.2.2⟩
  | fl => exact ⟨.okE, ⟨_, .notFail _ _ _ hB⟩, fl_ok hG, fail0, hG.2.2⟩
  | lp =>
    refine ⟨.lp, ?_, fl_fail hG (by simp), fail0, hG.2.2⟩
    intro o h
    cases h with
    | notOk _ _ _ _ _ h₁ => exact hB _ h₁
    | notFail _ _ _ h₁ => exact hB _ h₁

end Shallot
