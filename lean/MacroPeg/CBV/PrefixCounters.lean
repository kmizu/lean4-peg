import MacroPeg.Properties.Strategy

namespace Shallot.MacroPeg.CBV.PrefixCounters

/-! Prefix-valued counters for Par. All calls execute at the original input
root. A counter k is the literal x.take k, rather than a repeated-character
encoding. Simultaneous extension compares counters without inspecting or
decomposing their literal values. -/

def atEnd (a : MExp) : MExp := .andP (.seq a (.notP .any))

def equalBody (self : Nat) : MExp :=
  .alt (.seq (atEnd (.param 0)) (atEnd (.param 1)))
    (.call self [.seq (.param 0) .any, .seq (.param 1) .any])

def equalCall (self : Nat) (x : List Char) (a b : Nat) : MExp :=
  .call self [.lit (x.take a), .lit (x.take b)]

theorem equalBody_firstOrder (self : Nat) : (equalBody self).FirstOrder := by
  simp [equalBody, atEnd, MExp.andP, MExp.FirstOrder, MExp.FirstOrderArgs]

private theorem strip_append (p r : List Char) :
    Shallot.stripPrefix? p (p ++ r) = some r := by
  induction p with
  | nil => rfl
  | cons c p ih => simpa [Shallot.stripPrefix?, Shallot.beqChar] using ih

theorem literal_take (g : MGrammar) (s : Strategy) (x : List Char) (k : Nat) :
    MDerives g s (.lit (x.take k)) x (.ok (.leaf (x.take k)) (x.drop k)) := by
  apply MDerives.litOk
  have h := strip_append (x.take k) (x.drop k)
  rw [List.take_append_drop] at h
  exact h

theorem prefix_eq (x : List Char) (k : Nat) :
    x = x.take k ++ x.drop k := (List.take_append_drop k x).symm

theorem end_obs (g : MGrammar) (x : List Char) (k : Nat) (hk : k ≤ x.length) :
    SObs g .callByValuePar (atEnd (.lit (x.take k))) x
      (if k = x.length then some x else none) := by
  have hl := literal_take g .callByValuePar x k
  by_cases he : k = x.length
  · subst k
    simp only [ite_true]
    have hd : MDerives g .callByValuePar
        (.seq (.lit (x.take x.length)) (.notP .any)) x
        (.ok (.seq (.leaf (x.take x.length)) .notT) []) :=
      .seqOk _ _ _ _ _ _ _ (by simpa using hl) (.notFail _ _ .anyFail)
    exact ⟨_, .notFail _ _ (.notOk _ _ _ _ hd), rfl⟩
  · simp only [if_neg he]
    have hn : x.drop k ≠ [] := by
      intro h
      have hh := congrArg List.length h
      simp only [List.length_drop, List.length_nil] at hh
      omega
    cases hdrop : x.drop k with
    | nil => exact False.elim (hn hdrop)
    | cons c cs =>
      have hd : MDerives g .callByValuePar
          (.seq (.lit (x.take k)) (.notP .any)) x .fail :=
        .seqFail₂ _ _ _ _ _ (by simpa [hdrop] using hl)
          (.notOk _ _ _ _ (.anyOk c cs))
      exact ⟨_, .notOk _ _ _ _ (.notFail _ _ hd), rfl⟩

theorem grow_obs (g : MGrammar) (x : List Char) (k : Nat) (hk : k < x.length) :
    ∃ t, MDerives g .callByValuePar (.seq (.lit (x.take k)) .any) x
      (.ok t (x.drop (k + 1))) := by
  have hn : x.drop k ≠ [] := by
    intro h
    have hh := congrArg List.length h
    simp only [List.length_drop, List.length_nil] at hh
    omega
  cases hdrop : x.drop k with
  | nil => exact False.elim (hn hdrop)
  | cons c cs =>
    have ht : x.drop (k + 1) = cs := by
      rw [List.drop_add_one_eq_tail_drop, hdrop]
      rfl
    exact ⟨_, .seqOk _ _ _ _ _ _ _
      (by simpa [hdrop] using literal_take g .callByValuePar x k)
      (by simpa [ht] using (MDerives.anyOk (g := g) (s := .callByValuePar) c cs))⟩

private theorem grow_fail (g : MGrammar) (x : List Char) :
    MDerives g .callByValuePar (.seq (.lit x) .any) x .fail :=
  .seqFail₂ _ _ _ [] _ (.litOk _ _ _ (by simpa using strip_append x [])) .anyFail

private theorem both_end (g : MGrammar) (x : List Char) (a b : Nat)
    (ha : a ≤ x.length) (hb : b ≤ x.length) :
    SObs g .callByValuePar (.seq (atEnd (.lit (x.take a))) (atEnd (.lit (x.take b)))) x
      (if a = x.length ∧ b = x.length then some x else none) := by
  have h₁ := end_obs g x a ha
  have h₂ := end_obs g x b hb
  by_cases hA : a = x.length
  · simp only [if_pos hA] at h₁
    obtain ⟨o, hd, ho⟩ := h₁
    cases o with
    | fail => cases ho
    | ok t r =>
      have hr := Option.some.inj ho
      subst r
      by_cases hB : b = x.length
      · simp only [if_pos hB] at h₂
        obtain ⟨o, hd₂, ho₂⟩ := h₂
        cases o with
        | fail => cases ho₂
        | ok t₂ r₂ =>
          have hr₂ := Option.some.inj ho₂
          subst r₂
          exact ⟨_, .seqOk _ _ _ _ _ _ _ hd hd₂, by simp [hA, hB, MOutcome.restOf]⟩
      · simp only [if_neg hB] at h₂
        obtain ⟨o, hd₂, ho₂⟩ := h₂
        cases o with
        | fail => exact ⟨_, .seqFail₂ _ _ _ _ _ hd hd₂, by simp [hB, MOutcome.restOf]⟩
        | ok _ _ => cases ho₂
  · simp only [if_neg hA] at h₁
    obtain ⟨o, hd, ho⟩ := h₁
    cases o with
    | fail => exact ⟨_, .seqFail₁ _ _ _ hd, by simp [hA, MOutcome.restOf]⟩
    | ok _ _ => cases ho

theorem par_call {g : MGrammar} {i : Nat} {rule : MRule}
    {args vals : List MExp} {x : List Char} {r : Option (List Char)}
    (hr : ruleAtM g.rules i = some rule) (ha : rule.arity = args.length)
    (hv : DerivesArgsPar g .callByValuePar x args vals)
    (hd : SObs g .callByValuePar (MExp.subst vals rule.body) x r) :
    SObs g .callByValuePar (.call i args) x r := by
  obtain ⟨o, hd, ho⟩ := hd
  cases o with
  | fail => exact ⟨_, .callParFail _ _ _ _ _ rfl hr ha hv hd, ho⟩
  | ok t y => exact ⟨_, .callParOk _ _ _ _ _ _ _ rfl hr ha hv hd, ho⟩

theorem par_args_unique {g : MGrammar} {s : Strategy} {x : List Char}
    {args vals vals' : List MExp}
    (h : DerivesArgsPar g s x args vals) (h' : DerivesArgsPar g s x args vals') :
    vals = vals' := by
  induction args generalizing vals vals' with
  | nil => cases h; cases h'; rfl
  | cons a args ih =>
    cases h with
    | cons _ _ _ p y t vs hd hp ht =>
      cases h' with
      | cons _ _ _ p' y' t' vs' hd' hp' ht' =>
        have ho := mderives_det hd hd'
        injection ho with _ hy
        subst y'
        have he : p ++ y = p' ++ y := hp.symm.trans hp'
        have hpq := List.append_cancel_right he
        rw [hpq, ih ht ht']

/-- Once the successful argument evaluation is known, a Par call has exactly
the observations of its body with the captured literals substituted. -/
theorem par_call_iff {g : MGrammar} {i : Nat} {rule : MRule}
    {args vals : List MExp} {x : List Char}
    (hr : ruleAtM g.rules i = some rule) (ha : rule.arity = args.length)
    (hv : DerivesArgsPar g .callByValuePar x args vals) (r : Option (List Char)) :
    SObs g .callByValuePar (.call i args) x r ↔
      SObs g .callByValuePar (MExp.subst vals rule.body) x r := by
  constructor
  · rintro ⟨o, hd, ho⟩
    cases hd with
    | callNameOk _ _ _ _ _ _ hs _ _ _ => cases hs
    | callNameFail _ _ _ _ hs _ _ _ => cases hs
    | callSeqOk _ _ _ _ _ _ _ _ hs _ _ _ _ => cases hs
    | callSeqFail _ _ _ _ _ _ hs _ _ _ _ => cases hs
    | callSeqArgFail _ _ _ _ _ _ _ _ hs _ _ _ _ => cases hs
    | callParOk _ _ rule' _ _ vals' _ _ hr' _ hv' hd' =>
      have he : rule' = rule := Option.some.inj (hr'.symm.trans hr)
      subst rule'
      have he := par_args_unique hv' hv
      subst vals'
      exact ⟨_, hd', ho⟩
    | callParFail _ _ rule' _ vals' _ hr' _ hv' hd' =>
      have he : rule' = rule := Option.some.inj (hr'.symm.trans hr)
      subst rule'
      have he := par_args_unique hv' hv
      subst vals'
      exact ⟨_, hd', ho⟩
    | callParArgFail _ pre bad post _ _ _ _ _ _ _ hf =>
      have hm : bad ∈ pre ++ bad :: post := by simp
      obtain ⟨t, y, hok⟩ := derivesArgsPar_mem_ok hv hm
      have he := mderives_det hf hok
      cases he
    | callMissing _ _ _ hmissing => rw [hr] at hmissing; cases hmissing
    | callArity _ _ rule' _ hr' ha' =>
      have he : rule' = rule := Option.some.inj (hr'.symm.trans hr)
      subst rule'
      exact False.elim (ha' ha)
  · exact par_call hr ha hv

private theorem alt_after_fail {g : MGrammar} {a b : MExp} {x : List Char}
    {r : Option (List Char)} (ha : SObs g .callByValuePar a x none)
    (hb : SObs g .callByValuePar b x r) :
    SObs g .callByValuePar (.alt a b) x r := by
  obtain ⟨o, hd, ho⟩ := ha
  cases o with
  | ok _ _ => cases ho
  | fail =>
    obtain ⟨o₂, hd₂, ho₂⟩ := hb
    cases o₂ with
    | fail => exact ⟨_, .altFail _ _ _ hd hd₂, ho₂⟩
    | ok t y => exact ⟨_, .altR _ _ _ _ _ hd hd₂, ho₂⟩

/-- The equality rule terminates on all valid prefix counters. Equality
returns zero-width success, and inequality returns explicit finite failure. -/
theorem equal_body_obs {g : MGrammar} {self : Nat}
    (hr : ruleAtM g.rules self = some ⟨2, equalBody self⟩)
    (x : List Char) (a b : Nat) (ha : a ≤ x.length) (hb : b ≤ x.length) :
    SObs g .callByValuePar
      (MExp.subst [.lit (x.take a), .lit (x.take b)] (equalBody self)) x
      (if a = b then some x else none) := by
  have aux : ∀ d a b, a + d = x.length → b ≤ x.length →
      SObs g .callByValuePar
        (MExp.subst [.lit (x.take a), .lit (x.take b)] (equalBody self)) x
        (if a = b then some x else none) := by
    intro d
    induction d with
    | zero =>
      intro a b h hb
      have hA : a = x.length := by omega
      change SObs g .callByValuePar
        (.alt (.seq (atEnd (.lit (x.take a))) (atEnd (.lit (x.take b))))
          (.call self [.seq (.lit (x.take a)) .any, .seq (.lit (x.take b)) .any])) x _
      by_cases hB : b = x.length
      · have hd := both_end g x a b (by omega) hb
        simp only [if_pos (show a = x.length ∧ b = x.length from ⟨hA, hB⟩)] at hd
        obtain ⟨o, hd, ho⟩ := hd
        cases o with
        | fail => cases ho
        | ok t y =>
          have hy := Option.some.inj ho
          subst y
          exact ⟨_, .altL _ _ _ _ _ hd, by simp [hA, hB, MOutcome.restOf]⟩
      · have hd := both_end g x a b (by omega) hb
        simp only [show ¬ (a = x.length ∧ b = x.length) from fun h => hB h.2, ite_false] at hd
        apply alt_after_fail hd
        have hf : MDerives g .callByValuePar
            (.call self [.seq (.lit (x.take a)) .any, .seq (.lit (x.take b)) .any]) x .fail :=
          .callParArgFail self [] _ [_] _ x [] rfl hr rfl (.nil x)
            (by simpa [hA] using grow_fail g x)
        exact ⟨_, hf, by simp [hA, hB, MOutcome.restOf, eq_comm]⟩
    | succ d ih =>
      intro a b h hb
      have hA : a < x.length := by omega
      change SObs g .callByValuePar
        (.alt (.seq (atEnd (.lit (x.take a))) (atEnd (.lit (x.take b))))
          (.call self [.seq (.lit (x.take a)) .any, .seq (.lit (x.take b)) .any])) x _
      have hd := both_end g x a b (by omega) hb
      simp only [show ¬ (a = x.length ∧ b = x.length) from fun h => by omega, ite_false] at hd
      apply alt_after_fail hd
      obtain ⟨ta, hga⟩ := grow_obs g x a hA
      by_cases hB : b = x.length
      · have hf : MDerives g .callByValuePar
            (.call self [.seq (.lit (x.take a)) .any, .seq (.lit (x.take b)) .any]) x .fail :=
          .callParArgFail self [_] _ [] _ x [.lit (x.take (a + 1))] rfl hr rfl
            (.cons _ _ _ _ _ _ _ hga (prefix_eq x (a + 1)) (.nil x))
            (by simpa [hB] using grow_fail g x)
        exact ⟨_, hf, by simp [show a ≠ b from by omega, MOutcome.restOf]⟩
      · obtain ⟨tb, hgb⟩ := grow_obs g x b (by omega)
        have hv : DerivesArgsPar g .callByValuePar x
            [.seq (.lit (x.take a)) .any, .seq (.lit (x.take b)) .any]
            [.lit (x.take (a + 1)), .lit (x.take (b + 1))] :=
          .cons _ _ _ _ _ _ _ hga (prefix_eq x (a + 1))
            (.cons _ _ _ _ _ _ _ hgb (prefix_eq x (b + 1)) (.nil x))
        have hh := ih (a + 1) (b + 1) (by omega) (by omega)
        have hc := par_call hr rfl hv hh
        simpa only [Nat.add_right_cancel_iff] using hc
  exact aux (x.length - a) a b (by omega) hb

/-- An actual first-order Par rule compares two bounded prefix lengths on
the unmodified original input, including empty input and either endpoint. -/
theorem equal_obs {g : MGrammar} {self : Nat}
    (hr : ruleAtM g.rules self = some ⟨2, equalBody self⟩)
    (x : List Char) (a b : Nat) (ha : a ≤ x.length) (hb : b ≤ x.length) :
    SObs g .callByValuePar (equalCall self x a b) x
      (if a = b then some x else none) := by
  apply par_call hr rfl _ (equal_body_obs hr x a b ha hb)
  exact .cons _ _ _ _ _ _ _ (literal_take g .callByValuePar x a) (prefix_eq x a)
    (.cons _ _ _ _ _ _ _ (literal_take g .callByValuePar x b) (prefix_eq x b) (.nil x))

theorem equal_obs_iff {g : MGrammar} {self : Nat}
    (hr : ruleAtM g.rules self = some ⟨2, equalBody self⟩)
    (x : List Char) (a b : Nat) (ha : a ≤ x.length) (hb : b ≤ x.length)
    (r : Option (List Char)) :
    SObs g .callByValuePar (equalCall self x a b) x r ↔
      r = if a = b then some x else none := by
  have ht := equal_obs hr x a b ha hb
  constructor
  · intro h
    exact sObs_unique h ht
  · rintro rfl
    exact ht

/-- Any terminating root expression can supply a prefix-valued counter;
the expression need not itself be a literal. -/
theorem capture_root {g : MGrammar} {e : MExp} {x : List Char} {k : Nat}
    (h : SObs g .callByValuePar e x (some (x.drop k))) :
    ∃ t, MDerives g .callByValuePar e x (.ok t (x.drop k)) := by
  obtain ⟨o, hd, ho⟩ := h
  cases o with
  | fail => cases ho
  | ok t y =>
    have hy := Option.some.inj ho
    subst y
    exact ⟨t, hd⟩

/-- Equality also accepts counters computed by actual argument expressions. -/
theorem equal_arguments_obs {g : MGrammar} {self : Nat}
    (hr : ruleAtM g.rules self = some ⟨2, equalBody self⟩)
    {x : List Char} {a b : Nat} (ha : a ≤ x.length) (hb : b ≤ x.length)
    {ea eb : MExp}
    (hA : SObs g .callByValuePar ea x (some (x.drop a)))
    (hB : SObs g .callByValuePar eb x (some (x.drop b))) :
    SObs g .callByValuePar (.call self [ea, eb]) x
      (if a = b then some x else none) := by
  obtain ⟨ta, hda⟩ := capture_root hA
  obtain ⟨tb, hdb⟩ := capture_root hB
  exact par_call hr rfl
    (.cons _ _ _ _ _ _ _ hda (prefix_eq x a)
      (.cons _ _ _ _ _ _ _ hdb (prefix_eq x b) (.nil x)))
    (equal_body_obs hr x a b ha hb)

end Shallot.MacroPeg.CBV.PrefixCounters
