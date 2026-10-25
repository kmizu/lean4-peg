import MacroPeg.CBV.CanonicalProducerCompiler

namespace Shallot.MacroPeg.CBV.CanonicalProducerEvaluation
open CanonicalProducerCompiler
open ReplayControlFusion (Part)
open ExpressionContext (Context plug refinement)

def fork (choice : Bool) (a b : Context) := if choice then Context.alt a b else Context.seq a b

theorem binary (g : MGrammar) (x : List Char) (E : List (List Char)) (choice : Bool)
    (a a' b b' : MExp) (ca cb : Nat)
    (ha : ∀ k p, p≤x.length →
      RLe (evV g x .callByValuePar (tblV g x .callByValuePar k) E a p) (evV g x .callByValuePar (tblV g x .callByValuePar k) E a' p) ∧
      RLe (evV g x .callByValuePar (tblV g x .callByValuePar k) E a' p) (evV g x .callByValuePar (tblV g x .callByValuePar (k+ca)) E a p))
    (hb : ∀ k p, p≤x.length →
      RLe (evV g x .callByValuePar (tblV g x .callByValuePar k) E b p) (evV g x .callByValuePar (tblV g x .callByValuePar k) E b' p) ∧
      RLe (evV g x .callByValuePar (tblV g x .callByValuePar k) E b' p) (evV g x .callByValuePar (tblV g x .callByValuePar (k+cb)) E b p))
    (k p : Nat) (hp : p≤x.length) :
    RLe (evV g x .callByValuePar (tblV g x .callByValuePar k) E (if choice then .alt a b else .seq a b) p)
      (evV g x .callByValuePar (tblV g x .callByValuePar k) E (if choice then .alt a' b' else .seq a' b') p) ∧
    RLe (evV g x .callByValuePar (tblV g x .callByValuePar k) E (if choice then .alt a' b' else .seq a' b') p)
      (evV g x .callByValuePar (tblV g x .callByValuePar (k+(ca+cb))) E (if choice then .alt a b else .seq a b) p) := by
  have f1 := refinement g x .callByValuePar _ _ E (tblV_ok _ _ _ k) (TLeV.refl _) a a'
    (fun q hq => (ha k q hq).1) (fork choice .hole (.atom b)) p hp
  have f2 := refinement g x .callByValuePar _ _ E (tblV_ok _ _ _ k) (TLeV.refl _) b b'
    (fun q hq => (hb k q hq).1) (fork choice (.atom a') .hole) p hp
  have r1 := refinement g x .callByValuePar _ _ E (tblV_ok _ _ _ k) (tblV_le _ _ _ (by omega : k≤k+ca)) a' a
    (fun q hq => (ha k q hq).2) (fork choice .hole (.atom b')) p hp
  have r2 := refinement g x .callByValuePar _ _ E (tblV_ok _ _ _ (k+ca)) (tblV_le _ _ _ (by omega : k+ca≤k+ca+cb)) b' b
    (fun q hq => (hb (k+ca) q hq).2) (fork choice (.atom a) .hole) p hp
  cases choice <;> simpa [fork,plug,Nat.add_assoc] using And.intro (f1.trans f2) (r1.trans r2)

/-- Canonicalization is performed on the original real tables. The reverse
bound accounts for the earlier argument failure exposed at each changed call. -/
theorem bounds (ps : List Part) (es : List RecursiveProducedCompiler.Entry) (cores : List MExp)
    (hc : check ps es cores=true) (x : List Char) (E : List (List Char)) :
    ∀ e, e.FirstOrder → conforms ps es cores e=true → ∀ k p, p≤x.length →
    RLe (evV (source ps es) x .callByValuePar (tblV (source ps es) x .callByValuePar k) E e p)
      (evV (source ps es) x .callByValuePar (tblV (source ps es) x .callByValuePar k) E (render es e) p) ∧
    RLe (evV (source ps es) x .callByValuePar (tblV (source ps es) x .callByValuePar k) E (render es e) p)
      (evV (source ps es) x .callByValuePar (tblV (source ps es) x .callByValuePar (k+cost es e)) E e p)
  | .call i [a],he,hcon,k,p,hp => by
    have ha := (Bool.and_eq_true_iff.mp hcon).1
    cases hi : es[i]? with
    | none =>
      have hr : ruleAtM (source ps es).rules i=none := by rw [RecursiveProducedCompiler.source_rule,hi]; rfl
      simp only [render,cost,hi,Nat.add_zero]
      simp only [evV,hr]
      exact ⟨RLe.refl _,RLe.refl _⟩
    | some e =>
      have hr : ruleAtM (source ps es).rules i=some ⟨1,RecursiveProducedCompiler.body ps e⟩ := by
        rw [RecursiveProducedCompiler.source_rule,hi]; rfl
      have ih := bounds ps es cores hc x E a he.1 ha k p hp
      cases e with
      | growth r | origin P =>
        simp only [render,cost,hi,Nat.add_zero]
        exact ⟨ProducerArgumentRewrite.argument _ _ _ _ E (TLeV.refl _) i _ hr rfl a _ p ih.1,
          ProducerArgumentRewrite.argument _ _ _ _ E (tblV_le _ _ _ (by omega : k≤k+cost es a)) i _ hr rfl _ a p ih.2⟩
      | produced d b =>
        by_cases heq : MExp.beqE a d=true
        · simp only [render,cost,hi,if_pos heq,Nat.add_zero]
          exact ⟨ProducerArgumentRewrite.argument _ _ _ _ E (TLeV.refl _) i _ hr rfl a _ p ih.1,
            ProducerArgumentRewrite.argument _ _ _ _ E (tblV_le _ _ _ (by omega : k≤k+cost es a)) i _ hr rfl _ a p ih.2⟩
        · have hprod := checked_producer ps es cores hc i d b hi
          have hA := (Bool.and_eq_true_iff.mp hcon).2
          simp only [hi,heq,Bool.false_or] at hA
          have hforward := ProducerArgumentRewrite.forward _ (source_firstOrder ps es cores hc) i d b (core cores i d) a
            hr hprod.1 hprod.2.2.1 he.1 hA hprod.2.2.2 x k E p hp
          have hbackward := ProducerArgumentRewrite.backward _ (source_firstOrder ps es cores hc) i d b (core cores i d) a
            hr hprod.1 hprod.2.2.1 he.1 hA hprod.2.2.2 x (k+cost es a) E p hp
          let C : Context := .seq (.notP (.notP .hole)) (.atom (.call i [d]))
          have hf := refinement (source ps es) x .callByValuePar _ _ E (tblV_ok _ _ _ k) (TLeV.refl _) a (render es a)
            (fun q hq => (bounds ps es cores hc x E a he.1 ha k q hq).1) C p hp
          have hb := refinement (source ps es) x .callByValuePar _ _ E (tblV_ok _ _ _ k)
            (tblV_le _ _ _ (by omega : k≤k+cost es a)) (render es a) a
            (fun q hq => (bounds ps es cores hc x E a he.1 ha k q hq).2) C p hp
          simp only [C,plug] at hf hb
          simp only [render,cost,hi,if_neg heq,Nat.add_assoc]
          exact ⟨hforward.trans hf,hb.trans hbackward⟩
  | .seq a b,he,hcon,k,p,hp => by
    exact binary (source ps es) x E false a (render es a) b (render es b) (cost es a) (cost es b)
      (fun l q hq => bounds ps es cores hc x E a he.1 (Bool.and_eq_true_iff.mp hcon).1 l q hq)
      (fun l q hq => bounds ps es cores hc x E b he.2 (Bool.and_eq_true_iff.mp hcon).2 l q hq) k p hp
  | .alt a b,he,hcon,k,p,hp => by
    exact binary (source ps es) x E true a (render es a) b (render es b) (cost es a) (cost es b)
      (fun l q hq => bounds ps es cores hc x E a he.1 (Bool.and_eq_true_iff.mp hcon).1 l q hq)
      (fun l q hq => bounds ps es cores hc x E b he.2 (Bool.and_eq_true_iff.mp hcon).2 l q hq) k p hp
  | .notP a,he,hcon,k,p,hp => by
    exact ⟨refinement (source ps es) x .callByValuePar _ _ E (tblV_ok _ _ _ k) (TLeV.refl _) a (render es a)
        (fun q hq => (bounds ps es cores hc x E a he hcon k q hq).1) (.notP .hole) p hp,
      refinement (source ps es) x .callByValuePar _ _ E (tblV_ok _ _ _ k) (tblV_le _ _ _ (by omega : k≤k+cost es a)) (render es a) a
        (fun q hq => (bounds ps es cores hc x E a he hcon k q hq).2) (.notP .hole) p hp⟩
  | .star a,he,hcon,k,p,hp => by
    exact ⟨refinement (source ps es) x .callByValuePar _ _ E (tblV_ok _ _ _ k) (TLeV.refl _) a (render es a)
        (fun q hq => (bounds ps es cores hc x E a he hcon k q hq).1) (.star .hole) p hp,
      refinement (source ps es) x .callByValuePar _ _ E (tblV_ok _ _ _ k) (tblV_le _ _ _ (by omega : k≤k+cost es a)) (render es a) a
        (fun q hq => (bounds ps es cores hc x E a he hcon k q hq).2) (.star .hole) p hp⟩
  | .eps,_,_,_,_,_ | .any,_,_,_,_,_ | .chr _,_,_,_,_,_ | .range _ _,_,_,_,_,_ | .lit _,_,_,_,_,_ | .param _,_,_,_,_,_
  | .dbg _,_,_,_,_,_ | .lam _ _,_,_,_,_,_ | .invoke _ _ _,_,_,_,_,_ | .callParam _ _,_,_,_,_,_
  | .call _ [],_,_,_,_,_ | .call _ (_::_::_),_,_,_,_,_ => ⟨RLe.refl _,RLe.refl _⟩

end Shallot.MacroPeg.CBV.CanonicalProducerEvaluation
