import MacroPeg.CBVtoCBN.Control

namespace Shallot.MacroPeg.CBVtoCBN

/-- A total zero-width test. False is explicit finite failure, never absence of an observation. -/
def RootTest (g : MGrammar) (e : MExp) (x : List Char) (P : Prop) : Prop :=
  (P → MacroObs g e x (some x)) ∧ (¬ P → MacroObs g e x none)

theorem RootTest.of_obs {g : MGrammar} {e : MExp} {x : List Char} {P : Prop} [Decidable P]
    (h : MacroObs g e x (if P then some x else none)) : RootTest g e x P := by
  constructor
  · intro hp; simpa only [if_pos hp] using h
  · intro hp; simpa only [if_neg hp] using h

theorem RootTest.obs {g : MGrammar} {e : MExp} {x : List Char} {P : Prop} [Decidable P]
    (h : RootTest g e x P) : MacroObs g e x (if P then some x else none) := by
  by_cases hp : P
  · simpa only [if_pos hp] using h.1 hp
  · simpa only [if_neg hp] using h.2 hp

theorem RootTest.congr {g : MGrammar} {e : MExp} {x : List Char} {P Q : Prop}
    (h : RootTest g e x P) (he : P ↔ Q) : RootTest g e x Q :=
  ⟨fun hq => h.1 (he.mpr hq), fun hn => h.2 (fun hp => hn (he.mp hp))⟩

theorem RootTest.success_iff {g : MGrammar} {e : MExp} {x : List Char} {P : Prop}
    (h : RootTest g e x P) : MacroObs g e x (some x) ↔ P := by
  classical
  exact test_success_iff P h.obs

theorem RootTest.failure_iff {g : MGrammar} {e : MExp} {x : List Char} {P : Prop}
    (h : RootTest g e x P) : MacroObs g e x none ↔ ¬ P := by
  constructor
  · intro hf hp; have he := macroObs_unique (h.1 hp) hf; cases he
  · exact h.2

theorem RootTest.seq {g : MGrammar} {a b : MExp} {x : List Char} {P Q : Prop}
    (ha : RootTest g a x P) (hb : RootTest g b x Q) : RootTest g (.seq a b) x (P ∧ Q) := by
  classical
  constructor
  · rintro ⟨hp, hq⟩; exact obs_seq (ha.1 hp) (hb.1 hq)
  · intro hn
    by_cases hp : P
    · exact obs_seq (ha.1 hp) (hb.2 (fun hq => hn ⟨hp, hq⟩))
    · exact obs_seq_none (ha.2 hp)

/-- A false guard prevents evaluation of the body; totality is needed only on the selected branch. -/
theorem RootTest.guarded {g : MGrammar} {guard body : MExp} {x : List Char} {P Q : Prop}
    (hg : RootTest g guard x P) (hb : P → RootTest g body x Q) :
    RootTest g (.seq guard body) x (P ∧ Q) := by
  classical
  constructor
  · rintro ⟨hp, hq⟩; exact obs_seq (hg.1 hp) ((hb hp).1 hq)
  · intro hn
    by_cases hp : P
    · exact obs_seq (hg.1 hp) ((hb hp).2 (fun hq => hn ⟨hp, hq⟩))
    · exact obs_seq_none (hg.2 hp)

theorem RootTest.alt {g : MGrammar} {a b : MExp} {x : List Char} {P Q : Prop}
    (ha : RootTest g a x P) (hb : RootTest g b x Q) : RootTest g (.alt a b) x (P ∨ Q) := by
  classical
  constructor
  · intro h
    by_cases hp : P
    · exact obs_alt_some (ha.1 hp)
    · exact obs_alt_none (ha.2 hp) (hb.1 (h.resolve_left hp))
  · intro hn
    exact obs_alt_none (ha.2 (fun hp => hn (Or.inl hp))) (hb.2 (fun hq => hn (Or.inr hq)))

theorem RootTest.notP {g : MGrammar} {a : MExp} {x : List Char} {P : Prop}
    (ha : RootTest g a x P) : RootTest g (.notP a) x (¬ P) := by
  classical
  exact ⟨fun hn => obs_not_none (ha.2 hn), fun hnn => obs_not_some (ha.1 (Classical.byContradiction hnn))⟩

theorem rootTest_call_iff {g : MGrammar} {i : Nat} {args : List MExp} {rule : MRule}
    (hr : ruleAtM g.rules i = some rule) (ha : rule.arity = args.length) (x : List Char) (P : Prop) :
    RootTest g (.call i args) x P ↔ RootTest g (MExp.subst args rule.body) x P := by
  constructor
  · intro h
    exact ⟨fun hp => (obs_call_iff hr ha x (some x)).mp (h.1 hp),
      fun hn => (obs_call_iff hr ha x none).mp (h.2 hn)⟩
  · intro h
    exact ⟨fun hp => (obs_call_iff hr ha x (some x)).mpr (h.1 hp),
      fun hn => (obs_call_iff hr ha x none).mpr (h.2 hn)⟩

theorem rootTest_eps (g : MGrammar) (x : List Char) : RootTest g .eps x True :=
  ⟨fun _ => obs_eps x, fun hn => False.elim (hn True.intro)⟩

theorem rootTest_fail (g : MGrammar) (x : List Char) : RootTest g MExp.failAlways x False :=
  ⟨False.elim, fun _ => obs_not_some (obs_eps x)⟩

end Shallot.MacroPeg.CBVtoCBN
