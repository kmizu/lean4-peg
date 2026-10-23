import MacroPeg.CBVtoCBN.Positions

namespace Shallot.MacroPeg.CBVtoCBN

theorem obs_seq_iff {g : MGrammar} {a b : MExp} {x : List Char} {r : Option (List Char)} :
    MacroObs g (.seq a b) x r ↔
      (∃ y, MacroObs g a x (some y) ∧ MacroObs g b y r) ∨ (r = none ∧ MacroObs g a x none) := by
  constructor
  · rintro ⟨o, hd, hr⟩
    cases hd with
    | seqOk _ _ _ y z ta tb ha hb => exact Or.inl ⟨y, ⟨_, ha, rfl⟩, ⟨_, hb, hr⟩⟩
    | seqFail₁ _ _ _ ha => exact Or.inr ⟨hr.symm, ⟨_, ha, rfl⟩⟩
    | seqFail₂ _ _ _ y ta ha hb => exact Or.inl ⟨y, ⟨_, ha, rfl⟩, ⟨_, hb, hr⟩⟩
  · rintro (⟨y, ha, hb⟩ | ⟨rfl, ha⟩)
    · exact obs_seq ha hb
    · exact obs_seq_none ha

theorem obs_alt_iff {g : MGrammar} {a b : MExp} {x : List Char} {r : Option (List Char)} :
    MacroObs g (.alt a b) x r ↔
      (∃ y, r = some y ∧ MacroObs g a x (some y)) ∨ (MacroObs g a x none ∧ MacroObs g b x r) := by
  constructor
  · rintro ⟨o, hd, hr⟩
    cases hd with
    | altL _ _ _ y ta ha => exact Or.inl ⟨y, hr.symm, ⟨_, ha, rfl⟩⟩
    | altR _ _ _ y tb ha hb => exact Or.inr ⟨⟨_, ha, rfl⟩, ⟨_, hb, hr⟩⟩
    | altFail _ _ _ ha hb => exact Or.inr ⟨⟨_, ha, rfl⟩, ⟨_, hb, hr⟩⟩
  · rintro (⟨y, rfl, ha⟩ | ⟨ha, hb⟩)
    · exact obs_alt_some ha
    · exact obs_alt_none ha hb

theorem seq_zero_iff {g : MGrammar} {guard body : MExp} {x : List Char}
    (hg : MacroObs g guard x (some x)) (r : Option (List Char)) :
    MacroObs g (.seq guard body) x r ↔ MacroObs g body x r := by
  rw [obs_seq_iff]
  constructor
  · rintro (⟨y, hy, hb⟩ | ⟨_, hf⟩)
    · have he : x = y := Option.some.inj (macroObs_unique hg hy)
      subst y
      exact hb
    · have he := macroObs_unique hg hf
      cases he
  · intro hb
    exact Or.inl ⟨x, hg, hb⟩

theorem obs_unique_iff {g : MGrammar} {e : MExp} {x : List Char} {r : Option (List Char)}
    (hr : MacroObs g e x r) (r' : Option (List Char)) : MacroObs g e x r' ↔ r' = r := by
  constructor
  · intro h; exact (macroObs_unique hr h).symm
  · rintro rfl; exact hr

theorem alt_fail_left_iff {g : MGrammar} {a b : MExp} {x : List Char}
    (ha : MacroObs g a x none) (r : Option (List Char)) :
    MacroObs g (.alt a b) x r ↔ MacroObs g b x r := by
  rw [obs_alt_iff]
  simp only [obs_unique_iff ha, Option.some_ne_none, and_false, exists_const, false_or, true_and]

theorem alt_fail_right_iff {g : MGrammar} {a b : MExp} {x : List Char}
    (hb : MacroObs g b x none) (r : Option (List Char)) :
    MacroObs g (.alt a b) x r ↔ MacroObs g a x r := by
  rw [obs_alt_iff]
  simp only [obs_unique_iff hb]
  cases r <;> simp

/-- A total zero-width guard selects one branch even when that branch explicitly fails. -/
def ifP (guard yes no : MExp) : MExp := .alt (.seq guard yes) (.seq (.notP guard) no)

theorem ifP_true_iff {g : MGrammar} {guard yes no : MExp} {x : List Char}
    (ht : MacroObs g guard x (some x)) (r : Option (List Char)) :
    MacroObs g (ifP guard yes no) x r ↔ MacroObs g yes x r := by
  unfold ifP
  rw [alt_fail_right_iff (obs_seq_none (b := no) (obs_not_some ht))]
  exact seq_zero_iff ht r

theorem ifP_false_iff {g : MGrammar} {guard yes no : MExp} {x : List Char}
    (hf : MacroObs g guard x none) (r : Option (List Char)) :
    MacroObs g (ifP guard yes no) x r ↔ MacroObs g no x r := by
  unfold ifP
  rw [alt_fail_left_iff (obs_seq_none (b := yes) hf)]
  exact seq_zero_iff (obs_not_none hf) r

theorem ifP_firstOrder {guard yes no : MExp} (hg : guard.FirstOrder) (hy : yes.FirstOrder) (hn : no.FirstOrder) :
    (ifP guard yes no).FirstOrder := ⟨⟨hg, hy⟩, ⟨hg, hn⟩⟩

theorem LenRep.equiv {g : MGrammar} {a b : MExp} {k : Nat} (ha : LenRep g a k) (hb : LenRep g b k) :
    ObsEquiv g a b := by
  intro x r
  rw [obs_unique_iff (ha x), obs_unique_iff (hb x)]

/-- The fixed-length representation can be substituted through any first-order CBN rule call. -/
theorem call_len_equiv {g : MGrammar} (hg : g.FirstOrder) (i : Nat) {a b : MExp} {k : Nat}
    (ha : LenRep g a k) (hb : LenRep g b k) : ObsEquiv g (.call i [a]) (.call i [b]) := by
  intro x r
  constructor
  · exact sim_obs hg (.node (.call i (.cons (.leaf (ha.equiv hb)) .nil)))
  · exact sim_obs hg (.node (.call i (.cons (.leaf (hb.equiv ha)) .nil)))

theorem obs_call_iff {g : MGrammar} {i : Nat} {args : List MExp} {rule : MRule}
    (hr : ruleAtM g.rules i = some rule) (ha : rule.arity = args.length) (x : List Char) (r : Option (List Char)) :
    MacroObs g (.call i args) x r ↔ MacroObs g (MExp.subst args rule.body) x r := by
  constructor
  · rintro ⟨o, hd, ho⟩
    cases hd with
    | callNameOk _ _ rule' _ rest t hs hr' ha' hb =>
      have he : rule' = rule := Option.some.inj (hr'.symm.trans hr)
      subst rule'
      exact ⟨_, hb, ho⟩
    | callNameFail _ _ rule' _ hs hr' ha' hb =>
      have he : rule' = rule := Option.some.inj (hr'.symm.trans hr)
      subst rule'
      exact ⟨_, hb, ho⟩
    | callParOk _ _ _ _ _ _ _ hs _ _ _ _ => cases hs
    | callParFail _ _ _ _ _ hs _ _ _ _ => cases hs
    | callParArgFail _ _ _ _ _ _ _ hs _ _ _ _ => cases hs
    | callSeqOk _ _ _ _ _ _ _ _ hs _ _ _ _ => cases hs
    | callSeqFail _ _ _ _ _ _ hs _ _ _ _ => cases hs
    | callSeqArgFail _ _ _ _ _ _ _ _ hs _ _ _ _ => cases hs
    | callMissing _ _ _ hr' => rw [hr] at hr'; cases hr'
    | callArity _ _ rule' _ hr' ha' =>
      have he : rule' = rule := Option.some.inj (hr'.symm.trans hr)
      subst rule'
      exact False.elim (ha' ha)
  · exact obs_call hr ha

end Shallot.MacroPeg.CBVtoCBN
