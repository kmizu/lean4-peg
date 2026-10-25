import MacroPeg.CBV.SemanticBodyRewrite

namespace Shallot.MacroPeg.CBV.FiniteBodyRewrite

/-- Finite body expansion with an explicit uniform call-depth delay.
Both comparisons use actual source iterates. -/
def Related (g h : MGrammar) (s : Strategy) (delay : Nat) : Prop := ∀ i,
  match ruleAtM g.rules i,ruleAtM h.rules i with
  | none,none => True
  | some a,some b => a.arity=b.arity ∧ ∀ x k E p, p≤x.length →
      RLe (evV g x s (tblV g x s k) E a.body p) (evV g x s (tblV g x s k) E b.body p) ∧
      RLe (evV g x s (tblV g x s k) E b.body p) (evV g x s (tblV g x s (k+delay)) E a.body p)
  | _,_ => False

theorem arities {g h : MGrammar} {s : Strategy} {delay : Nat} (hr : Related g h s delay) : SemanticBodyRewrite.ArityEq g h := by
  intro i
  have hi := hr i
  cases hg : ruleAtM g.rules i <;> cases hh : ruleAtM h.rules i <;> simp only [hg,hh] at hi ⊢
  exact congrArg some hi.1

theorem forward_tables {g h : MGrammar} {s : Strategy} {delay : Nat} (hr : Related g h s delay) (x : List Char) (k : Nat) :
    TLeV (tblV g x s k) (tblV h x s k) := by
  induction k with
  | zero => exact TLeV.refl _
  | succ k ih =>
    intro i E p
    have hi := hr i
    cases hg : ruleAtM g.rules i <;> cases hh : ruleAtM h.rules i <;> simp only [hg,hh] at hi
    · simp only [tblV,hg,hh]; exact RLe.refl _
    · rename_i a b
      simp only [tblV,hg,hh,valAt_rangeMap]
      split
      · rename_i hp
        refine RLe.trans (hi.2 x k E p hp).1 ?_
        rw [←SemanticBodyRewrite.evaluator g h (arities hr) x s (tblV h x s k) E b.body p]
        exact evV_mono ih b.body p
      · exact RLe.refl _

theorem backward_tables {g h : MGrammar} {s : Strategy} {delay : Nat} (hr : Related g h s delay) (x : List Char) (k : Nat) :
    TLeV (tblV h x s k) (tblV g x s ((delay+1)*k)) := by
  induction k with
  | zero => exact TLeV.refl _
  | succ k ih =>
    intro i E p
    have hi := hr i
    cases hg : ruleAtM g.rules i <;> cases hh : ruleAtM h.rules i <;> simp only [hg,hh] at hi
    · rw [show (delay+1)*(k+1)=((delay+1)*k+delay)+1 by rw [Nat.mul_succ]; omega]
      simp only [tblV,hg,hh]; exact RLe.refl _
    · rename_i a b
      rw [show (delay+1)*(k+1)=((delay+1)*k+delay)+1 by rw [Nat.mul_succ]; omega]
      simp only [tblV,hg,hh,valAt_rangeMap]
      split
      · rename_i hp
        rw [←SemanticBodyRewrite.evaluator g h (arities hr) x s (tblV h x s k) E b.body p]
        exact RLe.trans (evV_mono ih b.body p) (hi.2 x ((delay+1)*k) E p hp).2
      · exact RLe.refl _

theorem defined_iff {g h : MGrammar} {s : Strategy} {delay : Nat} (hr : Related g h s delay)
    (x : List Char) (E : List (List Char)) (e : MExp) (p : Nat) (v : Option Nat) :
    (∃ k, evV g x s (tblV g x s k) E e p=some v) ↔
      ∃ k, evV h x s (tblV h x s k) E e p=some v := by
  constructor
  · rintro ⟨k,hk⟩
    refine ⟨k,?_⟩
    rw [←SemanticBodyRewrite.evaluator g h (arities hr) x s (tblV h x s k) E e p]
    exact (evV_mono (forward_tables hr x k) e p).eq_of_some hk
  · rintro ⟨k,hk⟩
    refine ⟨(delay+1)*k,?_⟩
    rw [←SemanticBodyRewrite.evaluator g h (arities hr) x s (tblV h x s k) E e p] at hk
    exact (evV_mono (backward_tables hr x k) e p).eq_of_some hk

theorem undefined_iff {g h : MGrammar} {s : Strategy} {delay : Nat} (hr : Related g h s delay)
    (x : List Char) (E : List (List Char)) (e : MExp) (p : Nat) :
    (∀ k, evV g x s (tblV g x s k) E e p=none) ↔
      ∀ k, evV h x s (tblV h x s k) E e p=none := by
  constructor
  · intro hs k
    cases hv : evV h x s (tblV h x s k) E e p with
    | none => rfl
    | some v =>
      obtain ⟨j,hj⟩ := (defined_iff hr x E e p v).mpr ⟨k,hv⟩
      rw [hs j] at hj
      cases hj
  · intro ht k
    cases hv : evV g x s (tblV g x s k) E e p with
    | none => rfl
    | some v =>
      obtain ⟨j,hj⟩ := (defined_iff hr x E e p v).mp ⟨k,hv⟩
      rw [ht j] at hj
      cases hj

theorem observations {g h : MGrammar} {s : Strategy} {delay : Nat} (hr : Related g h s delay)
    (hg : g.FirstOrder) (hh : h.FirstOrder) (hs : s≠.callByName) (e : MExp) (he : e.FirstOrder)
    (x : List Char) (rest : Option (List Char)) : SObs g s e x rest ↔ SObs h s e x rest := by
  have hc (v : Option Nat) :
      evV g x s (tblV g x s (iterBoundV g x)) [] e x.length=some v ↔
      evV h x s (tblV h x s (iterBoundV h x)) [] e x.length=some v :=
    (tblV_stable g x s (Nat.le_refl _)).symm.trans
      ((defined_iff hr x [] e x.length v).trans (tblV_stable h x s (Nat.le_refl _)))
  have eqv : evV g x s (tblV g x s (iterBoundV g x)) [] e x.length=
      evV h x s (tblV h x s (iterBoundV h x)) [] e x.length := by
    cases ha : evV g x s (tblV g x s (iterBoundV g x)) [] e x.length with
    | none =>
      cases hb : evV h x s (tblV h x s (iterBoundV h x)) [] e x.length with
      | none => rfl
      | some v => have hc := (hc v).mpr hb; rw [ha] at hc; cases hc
    | some v => exact ((hc v).mp ha).symm
  rw [←decideObsV_iff hg hs he,←decideObsV_iff hh hs he]
  unfold decideObsV
  rw [eqv]

end Shallot.MacroPeg.CBV.FiniteBodyRewrite
