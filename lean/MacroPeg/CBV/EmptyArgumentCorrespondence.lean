import MacroPeg.CBV.EmptyArgumentEvaluation

namespace Shallot.MacroPeg.CBV.EmptyArgumentCorrespondence
open EmptyArgumentSpecialization

/-- Ordinary rows retain arbitrary dynamic environments. Nullary clone
rows correspond to the singleton empty source environment, independently
of the caller environment. Both relations use the actual iterated tables. -/
theorem tables_rows (g : MGrammar) (hg : g.FirstOrder) (x : List Char) (s : Strategy) (k : Nat) : Rows g x s k := by
  induction k with
  | zero => constructor <;> intro i r hr E p hp <;> rfl
  | succ k ih =>
    constructor
    · intro i r hr E p hp
      rw [valAt_tblV_succ hr E hp,valAt_tblV_succ (original_rule g i r hr) E hp]
      exact EmptyArgumentEvaluation.evaluator g x s k ih E r.body (hg r (ruleAtM_mem hr)) p hp
    · intro i r hr E p hp
      rw [valAt_tblV_succ hr [[]] hp,valAt_tblV_succ (clone_rule g i r hr) E hp]
      rw [←WordViewSubstitution.evaluator g x s (sourceTable g x s k) E (.lit []) True.intro [] rfl
        r.body (hg r (ruleAtM_mem hr)) p]
      exact EmptyArgumentEvaluation.evaluator g x s k ih E _
        (firstOrder_subst (args := [.lit []]) (by trivial) r.body (hg r (ruleAtM_mem hr))) p hp

theorem evaluator_eq (g : MGrammar) (hg : g.FirstOrder) (x : List Char) (s : Strategy) (k : Nat)
    (E : List (List Char)) (e : MExp) (he : e.FirstOrder) (p : Nat) (hp : p≤x.length) :
    evV g x s (sourceTable g x s k) E e p=evV (target g) x s (targetTable g x s k) E (render g e) p :=
  EmptyArgumentEvaluation.evaluator g x s k (tables_rows g hg x s k) E e he p hp

theorem zero_call_eq (g : MGrammar) (hg : g.FirstOrder) (x : List Char) (s : Strategy) (k i : Nat)
    (r : MRule) (hr : ruleAtM g.rules i=some r) (ha : r.arity=1) (A : MExp)
    (hA : A.FirstOrder) (hz : zeroCheck A=true) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV g x s (sourceTable g x s k) E (.call i [A]) p=
      evV (target g) x s (targetTable g x s k) E (.seq (render g A) (.call (g.rules.length+i) [])) p :=
  EmptyArgumentEvaluation.zero_call g x s k (tables_rows g hg x s k) i r hr ha A hz E p hp
    (evaluator_eq g hg x s k E A hA p hp)

theorem clone_body_eq (g : MGrammar) (hg : g.FirstOrder) (x : List Char) (s : Strategy) (k i : Nat)
    (r : MRule) (hr : ruleAtM g.rules i=some r) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV g x s (sourceTable g x s k) [[]] r.body p=
      evV (target g) x s (targetTable g x s k) E (render g (MExp.subst [.lit []] r.body)) p := by
  rw [←WordViewSubstitution.evaluator g x s (sourceTable g x s k) E (.lit []) True.intro [] rfl
    r.body (hg r (ruleAtM_mem hr)) p]
  exact evaluator_eq g hg x s k E _ (firstOrder_subst (args := [.lit []]) (by trivial) _ (hg r (ruleAtM_mem hr))) p hp

theorem clone_environment (g : MGrammar) (hg : g.FirstOrder) (x : List Char) (s : Strategy) (k i : Nat)
    (r : MRule) (hr : ruleAtM g.rules i=some r) (E F : List (List Char)) (p : Nat) (hp : p≤x.length) :
    valAt (targetTable g x s k (g.rules.length+i) E) p=
      valAt (targetTable g x s k (g.rules.length+i) F) p :=
  ((tables_rows g hg x s k).2 i r hr E p hp).symm.trans ((tables_rows g hg x s k).2 i r hr F p hp)

theorem decide_eq (g : MGrammar) (hg : g.FirstOrder) (s : Strategy) (e : MExp) (he : e.FirstOrder) (x : List Char) :
    decideObsV s g x e=decideObsV s (target g) x (render g e) := by
  unfold decideObsV
  rw [ScannerPairFusion.stable_result_eq g (target g) x s s e (render g e)
    (fun k => evaluator_eq g hg x s k [] e he x.length (Nat.le_refl _))]

theorem observations_iff (g : MGrammar) (hg : g.FirstOrder) (s : Strategy) (hs : s≠.callByName)
    (e : MExp) (he : e.FirstOrder) (x : List Char) (rest : Option (List Char)) :
    SObs g s e x rest ↔ SObs (target g) s (render g e) x rest := by
  rw [←decideObsV_iff hg hs he,←decideObsV_iff (target_firstOrder g) hs (render_firstOrder g e),decide_eq g hg s e he x]

theorem undefined_iff (g : MGrammar) (hg : g.FirstOrder) (x : List Char) (s : Strategy)
    (E : List (List Char)) (e : MExp) (he : e.FirstOrder) (p : Nat) (hp : p≤x.length) :
    (∀ k, evV g x s (sourceTable g x s k) E e p=none) ↔
      (∀ k, evV (target g) x s (targetTable g x s k) E (render g e) p=none) := by
  simp only [evaluator_eq g hg x s _ E e he p hp]

theorem language_preservation (g : MGrammar) (hg : g.FirstOrder) (s : Strategy) (hs : s≠.callByName)
    (e : MExp) (he : e.FirstOrder) :
    ∃ (out : MGrammar) (entry : MExp), out.FirstOrder ∧ entry.FirstOrder ∧
      ∀ x, SObs g s e x (some []) ↔ SObs out s entry x (some []) :=
  ⟨target g,render g e,target_firstOrder g,render_firstOrder g e,fun x => observations_iff g hg s hs e he x (some [])⟩

end Shallot.MacroPeg.CBV.EmptyArgumentCorrespondence
