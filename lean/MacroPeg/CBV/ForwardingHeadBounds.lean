import MacroPeg.CBV.ForwardingHeadExpansion

namespace Shallot.MacroPeg.CBV.ForwardingHeadExpansion
open MultiplyingPrefixCompiler
open ExpressionContext (plug)

/-- Finite head expansion advances the evaluator by at most its syntactic
depth. All comparisons use actual source tables and include finite failure. -/
theorem bounds (rs : List Spec) (hg : (source rs).FirstOrder) (fuel i : Nat) (seen : List Nat)
    (ht : ForwardingPrefixTrace.Trail rs seen i) (r : Spec) (hr : rs[i]?=some r)
    (x : List Char) (k : Nat) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    RLe (evV (source rs) x .callByValuePar (sourceTable rs x k) E (sourceBody r) p)
      (evV (source rs) x .callByValuePar (sourceTable rs x k) E (code rs fuel i seen) p) ∧
    RLe (evV (source rs) x .callByValuePar (sourceTable rs x k) E (code rs fuel i seen) p)
      (evV (source rs) x .callByValuePar (sourceTable rs x (k+fuel)) E (sourceBody r) p) := by
  induction fuel generalizing i seen r k E p with
  | zero => simp only [code,hr,Nat.add_zero]; exact ⟨RLe.refl _,RLe.refl _⟩
  | succ fuel ih =>
    have hmono := tblV_le (source rs) x .callByValuePar (m := k) (m' := k+(fuel+1)) (by omega)
    by_cases hi : i∈seen
    · have hclosed := ForwardingPrefixTrace.trail_closed rs seen i ht hi
      have he := ForwardingPrefixCycles.body_eq_dead rs seen hclosed i hi r hr x k E p hp
      simp only [code,if_pos hi]
      exact ⟨Or.inr he,by rw [←he]; exact evV_mono hmono _ _⟩
    · cases hf : decide (r.factor=1) with
      | false =>
        have hne : r.factor≠1 := of_decide_eq_false hf
        simp only [code,if_neg hi,hr,if_neg hne]
        exact ⟨RLe.refl _,evV_mono hmono _ _⟩
      | true =>
        have hfactor : r.factor=1 := of_decide_eq_true hf
        cases hc : rs[r.callee]? with
        | none =>
          simp only [code,if_neg hi,hr,if_pos hfactor,hc]
          exact ⟨RLe.refl _,evV_mono hmono _ _⟩
        | some child =>
          have hchildFO := source_body_firstOrder rs hg r.callee child hc
          have hcodeFO := code_firstOrder rs hg fuel r.callee (i::seen)
          have htrail := ForwardingPrefixTrace.trail_push rs seen i r ht hr hfactor
          have hcallee : ruleAtM (source rs).rules r.callee=some ⟨1,sourceBody child⟩ := by rw [source_rule,hc]; rfl
          simp only [code,if_neg hi,hr,if_pos hfactor,hc]
          constructor
          · rw [canonical_body rs x k i r child hr hfactor hc E p hp]
            refine RLe.trans (WordCallUnfolding.context_bounds (source rs) r.callee (sourceBody child)
              hcallee hchildFO (.param 0) True.intro (frame r) x k E p hp).1 ?_
            apply ExpressionContext.refinement (source rs) x .callByValuePar _ _ E (tblV_ok _ _ _ k)
              (TLeV.refl _) _ _ _ (frame r) p hp
            intro q hq
            exact WordExpansionRefinement.expanded (source rs) x _ _ (.param 0) (sourceBody child)
              (code rs fuel r.callee (i::seen)) True.intro hchildFO hcodeFO
              (fun w q hq => (ih r.callee (i::seen) htrail child hc k [w] q hq).1) E q hq
          · have hclock := tblV_le (source rs) x .callByValuePar (m := k) (m' := k+fuel) (by omega)
            have hinner : RLe
                (evV (source rs) x .callByValuePar (sourceTable rs x k) E
                  (plug (WordCallUnfolding.expanded (.param 0) (code rs fuel r.callee (i::seen))) (frame r)) p)
                (evV (source rs) x .callByValuePar (sourceTable rs x (k+fuel)) E
                  (plug (WordCallUnfolding.expanded (.param 0) (sourceBody child)) (frame r)) p) := by
              apply ExpressionContext.refinement (source rs) x .callByValuePar _ _ E (tblV_ok _ _ _ k)
                hclock _ _ _ (frame r) p hp
              intro q hq
              exact WordExpansionRefinement.expanded (source rs) x _ _ (.param 0)
                (code rs fuel r.callee (i::seen)) (sourceBody child) True.intro hcodeFO hchildFO
                (fun w q hq => (ih r.callee (i::seen) htrail child hc k [w] q hq).2) E q hq
            have hlast := (WordCallUnfolding.context_bounds (source rs) r.callee (sourceBody child)
              hcallee hchildFO (.param 0) True.intro (frame r) x (k+fuel) E p hp).2
            rw [←canonical_body rs x (k+fuel+1) i r child hr hfactor hc E p hp] at hlast
            simpa only [Nat.add_assoc] using RLe.trans hinner hlast

theorem expanded_bounds (rs : List Spec) (hg : (source rs).FirstOrder) (i : Nat) (r : Spec)
    (hr : rs[i]?=some r) (x : List Char) (k : Nat) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    RLe (evV (source rs) x .callByValuePar (sourceTable rs x k) E (sourceBody r) p)
      (evV (source rs) x .callByValuePar (sourceTable rs x k) E (expanded rs i) p) ∧
    RLe (evV (source rs) x .callByValuePar (sourceTable rs x k) E (expanded rs i) p)
      (evV (source rs) x .callByValuePar (sourceTable rs x (k+rs.length+1)) E (sourceBody r) p) := by
  simpa only [expanded,Nat.add_assoc] using bounds rs hg (rs.length+1) i [] (by simp [ForwardingPrefixTrace.Trail]) r hr x k E p hp

end Shallot.MacroPeg.CBV.ForwardingHeadExpansion
