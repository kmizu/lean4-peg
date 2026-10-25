import MacroPeg.CBV.SemanticBodyRewrite

namespace Shallot.MacroPeg.CBV.BoundedBodyRewrite

/-- A body expansion may remove one call layer. Both comparisons use
actual source tables; the reverse comparison spends one extra layer. -/
def Related (g h : MGrammar) (s : Strategy) : Prop := ∀ i,
  match ruleAtM g.rules i,ruleAtM h.rules i with
  | none,none => True
  | some a,some b => a.arity=b.arity ∧ ∀ x k E p, p≤x.length →
      RLe (evV g x s (tblV g x s k) E a.body p) (evV g x s (tblV g x s k) E b.body p) ∧
      RLe (evV g x s (tblV g x s k) E b.body p) (evV g x s (tblV g x s (k+1)) E a.body p)
  | _,_ => False

theorem arities {g h : MGrammar} {s : Strategy} (hr : Related g h s) : SemanticBodyRewrite.ArityEq g h := by
  intro i
  have hi := hr i
  cases hg : ruleAtM g.rules i <;> cases hh : ruleAtM h.rules i <;> simp only [hg,hh] at hi ⊢
  exact congrArg some hi.1

theorem forward_tables {g h : MGrammar} {s : Strategy} (hr : Related g h s) (x : List Char) (k : Nat) :
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

theorem backward_tables {g h : MGrammar} {s : Strategy} (hr : Related g h s) (x : List Char) (k : Nat) :
    TLeV (tblV h x s k) (tblV g x s (2*k)) := by
  induction k with
  | zero => exact TLeV.refl _
  | succ k ih =>
    intro i E p
    have hi := hr i
    cases hg : ruleAtM g.rules i <;> cases hh : ruleAtM h.rules i <;> simp only [hg,hh] at hi
    · rw [show 2*(k+1)=(2*k+1)+1 by omega]
      simp only [tblV,hg,hh]; exact RLe.refl _
    · rename_i a b
      rw [show 2*(k+1)=(2*k+1)+1 by omega]
      simp only [tblV,hg,hh,valAt_rangeMap]
      split
      · rename_i hp
        rw [←SemanticBodyRewrite.evaluator g h (arities hr) x s (tblV h x s k) E b.body p]
        exact RLe.trans (evV_mono ih b.body p) (hi.2 x (2*k) E p hp).2
      · exact RLe.refl _

theorem defined_iff {g h : MGrammar} {s : Strategy} (hr : Related g h s)
    (x : List Char) (E : List (List Char)) (e : MExp) (p : Nat) (v : Option Nat) :
    (∃ k, evV g x s (tblV g x s k) E e p=some v) ↔
      ∃ k, evV h x s (tblV h x s k) E e p=some v := by
  constructor
  · rintro ⟨k,hk⟩
    refine ⟨k,?_⟩
    rw [←SemanticBodyRewrite.evaluator g h (arities hr) x s (tblV h x s k) E e p]
    exact (evV_mono (forward_tables hr x k) e p).eq_of_some hk
  · rintro ⟨k,hk⟩
    refine ⟨2*k,?_⟩
    rw [←SemanticBodyRewrite.evaluator g h (arities hr) x s (tblV h x s k) E e p] at hk
    exact (evV_mono (backward_tables hr x k) e p).eq_of_some hk

theorem undefined_iff {g h : MGrammar} {s : Strategy} (hr : Related g h s)
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

theorem observations {g h : MGrammar} {s : Strategy} (hr : Related g h s)
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

theorem allclock_none_iff_no_observation (g : MGrammar) (hg : g.FirstOrder) (s : Strategy)
    (hs : s≠.callByName) (e : MExp) (he : e.FirstOrder) (x : List Char) :
    (∀ k, evV g x s (tblV g x s k) [] e x.length=none) ↔ ∀ rest, ¬SObs g s e x rest := by
  constructor
  · intro hn
    apply (decideObsV_none_iff hg hs he x).mp
    unfold decideObsV
    rw [hn]
  · intro hn k
    have hd := (decideObsV_none_iff hg hs he x).mpr hn
    cases hv : evV g x s (tblV g x s k) [] e x.length with
    | none => rfl
    | some v =>
      have hv' := (tblV_stable g x s (Nat.le_refl _)).mp ⟨k,hv⟩
      unfold decideObsV at hd
      rw [hv'] at hd
      cases v <;> cases hd

theorem undefined_of_observations (g h : MGrammar) (hg : g.FirstOrder) (hh : h.FirstOrder)
    (s t : Strategy) (hs : s≠.callByName) (ht : t≠.callByName)
    (e f : MExp) (he : e.FirstOrder) (hf : f.FirstOrder) (x : List Char)
    (ho : ∀ rest, SObs g s e x rest ↔ SObs h t f x rest) :
    (∀ k, evV g x s (tblV g x s k) [] e x.length=none) ↔
      ∀ k, evV h x t (tblV h x t k) [] f x.length=none := by
  rw [allclock_none_iff_no_observation g hg s hs e he x,
    allclock_none_iff_no_observation h hh t ht f hf x]
  exact forall_congr' (fun rest => not_congr (ho rest))

end Shallot.MacroPeg.CBV.BoundedBodyRewrite
