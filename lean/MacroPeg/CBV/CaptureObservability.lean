import MacroPeg.CBVtoCBN.SpanValues

namespace Shallot.MacroPeg.CBV.CaptureObservability

/-! Captured strings are opaque: they are observed only by replay against
the remaining input. Equal replay behavior at every suffix gives equal
observations in every first-order CBV continuation. This constrains a
residual interface; it is not a separation of language classes. -/

def parameterRest (x : List Char) (E : List (List Char)) (k p : Nat) : Option (List Char) :=
  (E[k]?).bind (fun w => Shallot.stripPrefix? w (sfx x p))

def EnvAgree (x : List Char) (E F : List (List Char)) : Prop :=
  ∀ k p, p ≤ x.length → parameterRest x E k p = parameterRest x F k p

theorem parameter_eval (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Nat → List (List Char) → Val) (E : List (List Char)) (k p : Nat) :
    evV g x s T E (.param k) p = some ((parameterRest x E k p).map List.length) := by
  simp only [evV, parameterRest]
  cases E[k]? with
  | none => rfl
  | some w =>
    simp only [Option.bind_some]
    cases Shallot.stripPrefix? w (sfx x p) <;> rfl

mutual
  theorem evaluator_eq {g : MGrammar} {x : List Char} {s : Strategy}
      {T : Nat → List (List Char) → Val} {E F : List (List Char)}
      (hT : OkTV x.length T) (hE : EnvAgree x E F) :
      ∀ e p, p ≤ x.length → evV g x s T E e p = evV g x s T F e p
    | .param k, p, hp => by rw [parameter_eval, parameter_eval, hE k p hp]
    | .eps, _, _ | .any, _, _ | .chr _, _, _ | .range _ _, _, _ | .lit _, _, _
    | .dbg _, _, _ | .lam _ _, _, _ | .callParam _ _, _, _ | .invoke _ _ _, _, _ => rfl
    | .call i args, p, hp => by
      simp only [evV]
      cases hr : ruleAtM g.rules i with
      | none => rfl
      | some rule =>
        by_cases ha : rule.arity = args.length
        · simp only [if_pos ha]
          cases s with
          | callByName | callByValuePar => rw [par_arguments_eq hT hE args p hp]
          | callByValueSeq => rw [seq_arguments_eq hT hE args p hp]
        · simp only [if_neg ha]
    | .seq a b, p, hp => by
      have heq := evaluator_eq (g := g) (s := s) hT hE a p hp
      cases hv : evV g x s T E a p with
      | none => rw [evV_seq_none hv, evV_seq_none (heq.symm.trans hv)]
      | some result =>
        cases result with
        | none => rw [evV_seq_fail hv, evV_seq_fail (heq.symm.trans hv)]
        | some q =>
          rw [evV_seq_ok hv, evV_seq_ok (heq.symm.trans hv)]
          exact evaluator_eq hT hE b q (evV_ok hT a p hp q hv)
    | .alt a b, p, hp => by
      have heq := evaluator_eq (g := g) (s := s) hT hE a p hp
      cases hv : evV g x s T E a p with
      | none => rw [evV_alt_none hv, evV_alt_none (heq.symm.trans hv)]
      | some result =>
        cases result with
        | none =>
          rw [evV_alt_fail hv, evV_alt_fail (heq.symm.trans hv)]
          exact evaluator_eq hT hE b p hp
        | some q => rw [evV_alt_ok hv, evV_alt_ok (heq.symm.trans hv)]
    | .notP a, p, hp => by simp only [evV]; rw [evaluator_eq hT hE a p hp]
    | .star a, p, hp => by
      rw [evV_star, evV_star]
      exact evStar_congr p (fun q hq => evaluator_eq hT hE a q (by omega))

  theorem par_arguments_eq {g : MGrammar} {x : List Char} {s : Strategy}
      {T : Nat → List (List Char) → Val} {E F : List (List Char)}
      (hT : OkTV x.length T) (hE : EnvAgree x E F) :
      ∀ args p, p ≤ x.length → evParArgs g x s T E args p = evParArgs g x s T F args p
    | [], _, _ => rfl
    | a :: args, p, hp => by
      simp only [evParArgs]
      rw [evaluator_eq hT hE a p hp, par_arguments_eq hT hE args p hp]

  theorem seq_arguments_eq {g : MGrammar} {x : List Char} {s : Strategy}
      {T : Nat → List (List Char) → Val} {E F : List (List Char)}
      (hT : OkTV x.length T) (hE : EnvAgree x E F) :
      ∀ args p, p ≤ x.length → evSeqArgs g x s T E args p = evSeqArgs g x s T F args p
    | [], _, _ => rfl
    | a :: args, p, hp => by
      have heq := evaluator_eq (g := g) (s := s) hT hE a p hp
      simp only [evSeqArgs]
      rw [← heq]
      cases hv : evV g x s T E a p with
      | none => rfl
      | some result =>
        cases result with
        | none => rfl
        | some q =>
          simp only []
          rw [seq_arguments_eq (g := g) (s := s) hT hE args q (evV_ok hT a p hp q hv)]
end

theorem decide_eq {g : MGrammar} {x : List Char} {s : Strategy} {E F : List (List Char)}
    (hE : EnvAgree x E F) (e : MExp) (he : e.FirstOrder) :
    decideObsV s g x (MExp.subst (E.map MExp.lit) e) =
      decideObsV s g x (MExp.subst (F.map MExp.lit) e) := by
  unfold decideObsV
  rw [evV_subst E e he, evV_subst F e he,
    evaluator_eq (tblV_ok g x s _) hE e x.length (Nat.le_refl _)]

/-- No continuation, even one using recursive rules, can distinguish two
environments whose literal replays agree on every remaining suffix. -/
theorem observations_iff {g : MGrammar} {x : List Char} {s : Strategy} {E F : List (List Char)}
    (hg : g.FirstOrder) (hs : s ≠ .callByName) (hE : EnvAgree x E F)
    (e : MExp) (he : e.FirstOrder) (r : Option (List Char)) :
    SObs g s (MExp.subst (E.map MExp.lit) e) x r ↔
      SObs g s (MExp.subst (F.map MExp.lit) e) x r := by
  rw [← decideObsV_iff hg hs (firstOrder_subst (firstOrderArgs_lits E) e he),
    ← decideObsV_iff hg hs (firstOrder_subst (firstOrderArgs_lits F) e he), decide_eq hE e he]

def Unreplayable (x w : List Char) : Prop :=
  ∀ p, p ≤ x.length → Shallot.stripPrefix? w (sfx x p) = none

/-- An environment consisting entirely of unmatchable literals behaves like
an unbound environment, regardless of the contents or lengths of its values. -/
theorem dead_environment {x : List Char} {E : List (List Char)}
    (h : ∀ w ∈ E, Unreplayable x w) : EnvAgree x E [] := by
  intro k p hp
  cases he : E[k]? with
  | none => simp [parameterRest, he]
  | some w => simp [parameterRest, he, h w (List.mem_of_getElem? he) p hp]

theorem absent_character {x : List Char} {c : Char} (hc : c ∉ x) : Unreplayable x [c] := by
  intro p hp
  cases hx : sfx x p with
  | nil => rfl
  | cons d rest =>
    obtain ⟨pre0, hroot⟩ := sfx_is_suffix x p
    have hd : d ∈ x := by rw [hroot, hx]; simp
    have hne : c ≠ d := by intro he; subst c; exact hc hd
    simp [Shallot.stripPrefix?, Shallot.beqChar, Char.toNat_inj, hne]

theorem dead_singletons_agree {x u v : List Char} (hu : Unreplayable x u)
    (hv : Unreplayable x v) : EnvAgree x [u] [v] := by
  intro k p hp
  cases k with
  | zero => simp [parameterRest, hu p hp, hv p hp]
  | succ k => simp [parameterRest]

/-- This regular expression's residual after consuming one character depends
on that consumed character, even when neither possible capture can replay. -/
def headDependent : MExp := .alt (.seq (.chr 'a') .any) (.chr 'b')

theorem headDependent_a (g : MGrammar) (s : Strategy) :
    SObs g s headDependent ['a', 'c'] (some []) := by
  refine ⟨_, .altL _ _ _ _ _ (.seqOk _ _ _ _ _ _ _
    (.chrOk 'a' 'a' ['c'] (by decide)) (.anyOk 'c' [])), rfl⟩

theorem headDependent_b (g : MGrammar) (s : Strategy) :
    SObs g s headDependent ['b', 'c'] (some ['c']) := by
  refine ⟨_, .altR _ _ _ _ _ (.seqFail₁ _ _ _
    (.chrFail 'a' 'b' ['c'] (by decide))) (.chrOk 'b' 'b' ['c'] (by decide)), rfl⟩

/-- There is no fixed residual body in any first-order CBV grammar that,
given just the first-character literal and the common suffix, reproduces
both residuals above. Prefix-dependent control before entry is not excluded. -/
theorem no_literal_residual (g : MGrammar) (hg : g.FirstOrder)
    (s : Strategy) (hs : s ≠ .callByName) :
    ¬ ∃ e : MExp, e.FirstOrder ∧
      SObs g s (MExp.subst [MExp.lit ['a']] e) ['c'] (some []) ∧
      SObs g s (MExp.subst [MExp.lit ['b']] e) ['c'] (some ['c']) := by
  rintro ⟨e, he, ha, hb⟩
  have hE : EnvAgree ['c'] [['a']] [['b']] :=
    dead_singletons_agree (absent_character (by simp)) (absent_character (by simp))
  have heq := observations_iff hg hs hE e he (some [])
  have hb' : SObs g s (MExp.subst [MExp.lit ['b']] e) ['c'] (some []) := heq.mp ha
  have hbad := sObs_unique hb' hb
  cases hbad

end Shallot.MacroPeg.CBV.CaptureObservability
