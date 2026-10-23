import MacroPeg.Properties.Strategy

namespace Shallot.MacroPeg.CBV.RootObservation

theorem seq_ok {g : MGrammar} {s : Strategy} {a b : MExp} {x y : List Char}
    {r : Option (List Char)} (ha : SObs g s a x (some y)) (hb : SObs g s b y r) :
    SObs g s (.seq a b) x r := by
  obtain ⟨oa, hda, hra⟩ := ha
  cases oa with
  | fail => cases hra
  | ok ta ya =>
    have hy := Option.some.inj hra
    subst ya
    obtain ⟨ob, hdb, hrb⟩ := hb
    cases ob with
    | fail => exact ⟨_, .seqFail₂ _ _ _ _ _ hda hdb, hrb⟩
    | ok tb yb => exact ⟨_, .seqOk _ _ _ _ _ _ _ hda hdb, hrb⟩

theorem seq_fail {g : MGrammar} {s : Strategy} {a b : MExp} {x : List Char}
    (ha : SObs g s a x none) : SObs g s (.seq a b) x none := by
  obtain ⟨o, hd, ho⟩ := ha
  cases o with
  | fail => exact ⟨_, .seqFail₁ _ _ _ hd, rfl⟩
  | ok _ _ => cases ho

theorem not_ok {g : MGrammar} {s : Strategy} {a : MExp} {x y : List Char}
    (ha : SObs g s a x (some y)) : SObs g s (.notP a) x none := by
  obtain ⟨o, hd, ho⟩ := ha
  cases o with
  | fail => cases ho
  | ok _ _ => exact ⟨_, .notOk _ _ _ _ hd, rfl⟩

theorem not_fail {g : MGrammar} {s : Strategy} {a : MExp} {x : List Char}
    (ha : SObs g s a x none) : SObs g s (.notP a) x (some x) := by
  obtain ⟨o, hd, ho⟩ := ha
  cases o with
  | fail => exact ⟨_, .notFail _ _ hd, rfl⟩
  | ok _ _ => cases ho

theorem alt_right {g : MGrammar} {s : Strategy} {a b : MExp} {x : List Char}
    {r : Option (List Char)} (ha : SObs g s a x none) (hb : SObs g s b x r) :
    SObs g s (.alt a b) x r := by
  obtain ⟨oa, hda, hra⟩ := ha
  cases oa with
  | ok _ _ => cases hra
  | fail =>
    obtain ⟨ob, hdb, hrb⟩ := hb
    cases ob with
    | fail => exact ⟨_, .altFail _ _ _ hda hdb, hrb⟩
    | ok tb yb => exact ⟨_, .altR _ _ _ _ _ hda hdb, hrb⟩

theorem alt_left {g : MGrammar} {s : Strategy} {a b : MExp} {x y : List Char}
    (ha : SObs g s a x (some y)) : SObs g s (.alt a b) x (some y) := by
  obtain ⟨o, hd, ho⟩ := ha
  cases o with
  | fail => cases ho
  | ok _ _ => exact ⟨_, .altL _ _ _ _ _ hd, ho⟩

def branch (guard yes no : MExp) : MExp :=
  .alt (.seq guard yes) (.seq (.notP guard) no)

/-- The negative guard prevents failure of the selected continuation from
falling through to the other branch. All strategies satisfy this rule. -/
theorem branch_true {g : MGrammar} {s : Strategy} {guard yes no : MExp}
    {x : List Char} {r : Option (List Char)}
    (hg : SObs g s guard x (some x)) (hy : SObs g s yes x r) :
    SObs g s (branch guard yes no) x r := by
  have hl := seq_ok hg hy
  cases r with
  | some y => exact alt_left hl
  | none => exact alt_right hl (seq_fail (not_ok hg))

theorem branch_false {g : MGrammar} {s : Strategy} {guard yes no : MExp}
    {x : List Char} {r : Option (List Char)}
    (hg : SObs g s guard x none) (hn : SObs g s no x r) :
    SObs g s (branch guard yes no) x r :=
  alt_right (seq_fail hg) (seq_ok (not_fail hg) hn)

theorem seq_iff {g : MGrammar} {s : Strategy} {a b : MExp} {x : List Char}
    {r : Option (List Char)} :
    SObs g s (.seq a b) x r ↔
      (∃ y, SObs g s a x (some y) ∧ SObs g s b y r) ∨
      (r = none ∧ SObs g s a x none) := by
  constructor
  · rintro ⟨o, hd, ho⟩
    cases hd with
    | seqOk _ _ _ y _ _ _ ha hb => exact Or.inl ⟨y, ⟨_, ha, rfl⟩, ⟨_, hb, ho⟩⟩
    | seqFail₁ _ _ _ ha => exact Or.inr ⟨ho.symm, ⟨_, ha, rfl⟩⟩
    | seqFail₂ _ _ _ y _ ha hb => exact Or.inl ⟨y, ⟨_, ha, rfl⟩, ⟨_, hb, ho⟩⟩
  · rintro (⟨y, ha, hb⟩ | ⟨rfl, ha⟩)
    · exact seq_ok ha hb
    · exact seq_fail ha

theorem alt_iff {g : MGrammar} {s : Strategy} {a b : MExp} {x : List Char}
    {r : Option (List Char)} :
    SObs g s (.alt a b) x r ↔
      (∃ y, r = some y ∧ SObs g s a x (some y)) ∨
      (SObs g s a x none ∧ SObs g s b x r) := by
  constructor
  · rintro ⟨o, hd, ho⟩
    cases hd with
    | altL _ _ _ y _ ha => exact Or.inl ⟨y, ho.symm, ⟨_, ha, rfl⟩⟩
    | altR _ _ _ _ _ ha hb => exact Or.inr ⟨⟨_, ha, rfl⟩, ⟨_, hb, ho⟩⟩
    | altFail _ _ _ ha hb => exact Or.inr ⟨⟨_, ha, rfl⟩, ⟨_, hb, ho⟩⟩
  · rintro (⟨y, rfl, ha⟩ | ⟨ha, hb⟩)
    · exact alt_left ha
    · exact alt_right ha hb

theorem unique_iff {g : MGrammar} {s : Strategy} {a : MExp} {x : List Char}
    {r : Option (List Char)} (ha : SObs g s a x r) (r' : Option (List Char)) :
    SObs g s a x r' ↔ r' = r := by
  constructor
  · intro h
    exact sObs_unique h ha
  · rintro rfl
    exact ha

theorem seq_zero_iff {g : MGrammar} {s : Strategy} {a b : MExp} {x : List Char}
    (ha : SObs g s a x (some x)) (r : Option (List Char)) :
    SObs g s (.seq a b) x r ↔ SObs g s b x r := by
  rw [seq_iff]
  constructor
  · rintro (⟨y, hy, hb⟩ | ⟨_, hf⟩)
    · have he : y = x := Option.some.inj (sObs_unique hy ha)
      subst y
      exact hb
    · have he := sObs_unique hf ha
      cases he
  · intro hb
    exact Or.inl ⟨x, ha, hb⟩

theorem alt_fail_left_iff {g : MGrammar} {s : Strategy} {a b : MExp} {x : List Char}
    (ha : SObs g s a x none) (r : Option (List Char)) :
    SObs g s (.alt a b) x r ↔ SObs g s b x r := by
  rw [alt_iff]
  simp only [unique_iff ha, Option.some_ne_none, and_false, exists_const, false_or, true_and]

theorem alt_fail_right_iff {g : MGrammar} {s : Strategy} {a b : MExp} {x : List Char}
    (hb : SObs g s b x none) (r : Option (List Char)) :
    SObs g s (.alt a b) x r ↔ SObs g s a x r := by
  rw [alt_iff]
  simp only [unique_iff hb]
  cases r <;> simp

theorem branch_true_iff {g : MGrammar} {s : Strategy} {guard yes no : MExp}
    {x : List Char} (hg : SObs g s guard x (some x)) (r : Option (List Char)) :
    SObs g s (branch guard yes no) x r ↔ SObs g s yes x r := by
  unfold branch
  rw [alt_fail_right_iff (seq_fail (b := no) (not_ok hg))]
  exact seq_zero_iff hg r

theorem branch_false_iff {g : MGrammar} {s : Strategy} {guard yes no : MExp}
    {x : List Char} (hg : SObs g s guard x none) (r : Option (List Char)) :
    SObs g s (branch guard yes no) x r ↔ SObs g s no x r := by
  unfold branch
  rw [alt_fail_left_iff (seq_fail (b := yes) hg)]
  exact seq_zero_iff (not_fail hg) r

/-- A total Boolean test, with success always at the unchanged input root. -/
def Test (g : MGrammar) (s : Strategy) (e : MExp) (x : List Char) (b : Bool) : Prop :=
  SObs g s e x (if b then some x else none)

theorem test_seq {g : MGrammar} {s : Strategy} {a b : MExp} {x : List Char}
    {u v : Bool} (ha : Test g s a x u) (hb : Test g s b x v) :
    Test g s (.seq a b) x (u && v) := by
  cases u with
  | true => exact seq_ok ha hb
  | false => exact seq_fail ha

theorem test_alt {g : MGrammar} {s : Strategy} {a b : MExp} {x : List Char}
    {u v : Bool} (ha : Test g s a x u) (hb : Test g s b x v) :
    Test g s (.alt a b) x (u || v) := by
  cases u with
  | true => exact alt_left ha
  | false => exact alt_right ha hb

theorem test_not {g : MGrammar} {s : Strategy} {a : MExp} {x : List Char}
    {u : Bool} (ha : Test g s a x u) : Test g s (.notP a) x (!u) := by
  cases u with
  | true => exact not_ok ha
  | false => exact not_fail ha

def alternatives : List MExp → MExp
  | [] => MExp.failAlways
  | e :: es => .alt e (alternatives es)

theorem alternatives_subst (args : List MExp) (es : List MExp) :
    MExp.subst args (alternatives es) = alternatives (es.map (MExp.subst args)) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [alternatives, MExp.subst, ih]

theorem alternatives_firstOrder (es : List MExp)
    (h : ∀ e ∈ es, e.FirstOrder) : (alternatives es).FirstOrder := by
  induction es with
  | nil => trivial
  | cons e es ih => exact ⟨h e List.mem_cons_self, ih (fun a ha => h a (List.mem_cons_of_mem _ ha))⟩

theorem alternatives_test {α : Type} {g : MGrammar} {s : Strategy} {x : List Char}
    (es : List α) (f : α → MExp) (b : α → Bool)
    (h : ∀ a ∈ es, Test g s (f a) x (b a)) :
    Test g s (alternatives (es.map f)) x (es.any b) := by
  induction es with
  | nil => exact ⟨_, .notOk _ _ _ _ (.eps x), rfl⟩
  | cons a es ih =>
    exact test_alt (h a List.mem_cons_self)
      (ih (fun a ha => h a (List.mem_cons_of_mem _ ha)))

theorem peek_success {g : MGrammar} {s : Strategy} {e : MExp} {x y : List Char}
    (he : SObs g s e x (some y)) : Test g s (.andP e) x true :=
  not_fail (not_ok he)

theorem peek_failure {g : MGrammar} {s : Strategy} {e : MExp} {x : List Char}
    (he : SObs g s e x none) : Test g s (.andP e) x false :=
  not_ok (not_fail he)

/-- A total test for a proposition. The false case is finite failure. -/
def Predicate (g : MGrammar) (s : Strategy) (e : MExp) (x : List Char) (P : Prop) : Prop :=
  (P → SObs g s e x (some x)) ∧ (¬P → SObs g s e x none)

theorem Predicate.of_obs {g : MGrammar} {s : Strategy} {e : MExp} {x : List Char}
    {P : Prop} [Decidable P] (h : SObs g s e x (if P then some x else none)) :
    Predicate g s e x P := by
  constructor
  · intro hp
    simpa only [if_pos hp] using h
  · intro hp
    simpa only [if_neg hp] using h

theorem Predicate.obs {g : MGrammar} {s : Strategy} {e : MExp} {x : List Char}
    {P : Prop} [Decidable P] (h : Predicate g s e x P) :
    SObs g s e x (if P then some x else none) := by
  by_cases hp : P
  · simpa only [if_pos hp] using h.1 hp
  · simpa only [if_neg hp] using h.2 hp

theorem Predicate.congr {g : MGrammar} {s : Strategy} {e : MExp} {x : List Char}
    {P Q : Prop} (h : Predicate g s e x P) (he : P ↔ Q) : Predicate g s e x Q :=
  ⟨fun hq => h.1 (he.2 hq), fun hq => h.2 (fun hp => hq (he.1 hp))⟩

theorem Predicate.seq {g : MGrammar} {s : Strategy} {a b : MExp} {x : List Char}
    {P Q : Prop} (ha : Predicate g s a x P) (hb : Predicate g s b x Q) :
    Predicate g s (.seq a b) x (P ∧ Q) := by
  constructor
  · rintro ⟨hp, hq⟩
    exact seq_ok (ha.1 hp) (hb.1 hq)
  · intro hn
    by_cases hp : P
    · exact seq_ok (ha.1 hp) (hb.2 (fun hq => hn ⟨hp, hq⟩))
    · exact seq_fail (ha.2 hp)

theorem Predicate.alt {g : MGrammar} {s : Strategy} {a b : MExp} {x : List Char}
    {P Q : Prop} (ha : Predicate g s a x P) (hb : Predicate g s b x Q) :
    Predicate g s (.alt a b) x (P ∨ Q) := by
  constructor
  · intro h
    by_cases hp : P
    · exact alt_left (ha.1 hp)
    · exact alt_right (ha.2 hp) (hb.1 (h.resolve_left hp))
  · intro hn
    exact alt_right (ha.2 (fun hp => hn (Or.inl hp))) (hb.2 (fun hq => hn (Or.inr hq)))

theorem Predicate.notP {g : MGrammar} {s : Strategy} {e : MExp} {x : List Char}
    {P : Prop} (h : Predicate g s e x P) : Predicate g s (.notP e) x (¬P) := by
  constructor
  · intro hn
    exact not_fail (h.2 hn)
  · intro hn
    have hp : P := Classical.byContradiction hn
    exact not_ok (h.1 hp)

end Shallot.MacroPeg.CBV.RootObservation
