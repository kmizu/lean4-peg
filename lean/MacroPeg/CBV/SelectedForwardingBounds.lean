import MacroPeg.CBV.SelectedForwardingCycles

namespace Shallot.MacroPeg.CBV.SelectedForwardingBounds
open SelectedForwardingContext
open MultiplyingPrefixCompiler (Spec sourceBody)
open ForwardingHeadExpansion (code expanded frame)
open ExpressionContext (plug)

theorem canonical_body (g : MGrammar) (x : List Char) (k : Nat) (r child : Spec) (hf : r.factor=1)
    (hc : ruleAtM g.rules r.callee=some ⟨1,sourceBody child⟩) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV g x .callByValuePar (tblV g x .callByValuePar k) E (sourceBody r) p=
      evV g x .callByValuePar (tblV g x .callByValuePar k) E (plug (.call r.callee [.param 0]) (frame r)) p := by
  change evV g x .callByValuePar (tblV g x .callByValuePar k) E
    (plug (.call r.callee [RepeatedWordArguments.expression (.param 0) r.factor]) (frame r)) p=_
  apply WordExpansionRefinement.context_eq _ _ _ _ _ (tblV_ok _ _ _ k) _ _ _ (frame r) p hp
  intro q hq
  rw [hf,evV_call_par hc rfl (by decide),evV_call_par hc rfl (by decide)]
  simp only [evParArgs,ForwardingPrefixCycles.expression_one]

theorem bounds (g : MGrammar) (hg : g.FirstOrder) (rs : List Spec) (ids : List Nat)
    (hv : Valid g rs ids) (fuel i : Nat) (seen : List Nat) (hseen : seen⊆ids) (hsel : i∈ids)
    (ht : ForwardingPrefixTrace.Trail rs seen i) (r : Spec) (hr : rs[i]?=some r)
    (x : List Char) (k : Nat) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    RLe (evV g x .callByValuePar (tblV g x .callByValuePar k) E (sourceBody r) p)
      (evV g x .callByValuePar (tblV g x .callByValuePar k) E (code rs fuel i seen) p) ∧
    RLe (evV g x .callByValuePar (tblV g x .callByValuePar k) E (code rs fuel i seen) p)
      (evV g x .callByValuePar (tblV g x .callByValuePar (k+fuel)) E (sourceBody r) p) := by
  induction fuel generalizing i seen r k E p with
  | zero => simp only [code,hr,Nat.add_zero]; exact ⟨RLe.refl _,RLe.refl _⟩
  | succ fuel ih =>
    have hmono := tblV_le g x .callByValuePar (m := k) (m' := k+(fuel+1)) (by omega)
    by_cases hvisit : i∈seen
    · have hclosed := ForwardingPrefixTrace.trail_closed rs seen i ht hvisit
      have he := SelectedForwardingCycles.body_eq_dead g rs ids hv seen hclosed hseen i hvisit r hr x k E p hp
      simp only [code,if_pos hvisit]
      exact ⟨Or.inr he,by rw [←he]; exact evV_mono hmono _ _⟩
    · cases hf : decide (r.factor=1) with
      | false =>
        have hne : r.factor≠1 := of_decide_eq_false hf
        simp only [code,if_neg hvisit,hr,if_neg hne]
        exact ⟨RLe.refl _,evV_mono hmono _ _⟩
      | true =>
        have hfactor : r.factor=1 := of_decide_eq_true hf
        cases hc : rs[r.callee]? with
        | none =>
          simp only [code,if_neg hvisit,hr,if_pos hfactor,hc]
          exact ⟨RLe.refl _,evV_mono hmono _ _⟩
        | some child =>
          have hchild := hv.edge i hsel r hr hfactor child hc
          have hsub : i::seen⊆ids := by
            intro a ha
            rcases List.mem_cons.mp ha with he|ha
            · exact he ▸ hsel
            · exact hseen ha
          have hchildFO := body_firstOrder g hg rs ids hv r.callee hchild child hc
          have hcodeFO := code_firstOrder g hg rs ids hv fuel r.callee (i::seen) hchild child hc
          have htrail := ForwardingPrefixTrace.trail_push rs seen i r ht hr hfactor
          have hcallee : ruleAtM g.rules r.callee=some ⟨1,sourceBody child⟩ := hv.rule r.callee hchild child hc
          simp only [code,if_neg hvisit,hr,if_pos hfactor,hc]
          constructor
          · rw [canonical_body g x k r child hfactor hcallee E p hp]
            refine RLe.trans (WordCallUnfolding.context_bounds g r.callee (sourceBody child)
              hcallee hchildFO (.param 0) True.intro (frame r) x k E p hp).1 ?_
            apply ExpressionContext.refinement g x .callByValuePar _ _ E (tblV_ok _ _ _ k)
              (TLeV.refl _) _ _ _ (frame r) p hp
            intro q hq
            exact WordExpansionRefinement.expanded g x _ _ (.param 0) (sourceBody child)
              (code rs fuel r.callee (i::seen)) True.intro hchildFO hcodeFO
              (fun w q hq => (ih r.callee (i::seen) hsub hchild htrail child hc k [w] q hq).1) E q hq
          · have hclock := tblV_le g x .callByValuePar (m := k) (m' := k+fuel) (by omega)
            have hinner : RLe
                (evV g x .callByValuePar (tblV g x .callByValuePar k) E
                  (plug (WordCallUnfolding.expanded (.param 0) (code rs fuel r.callee (i::seen))) (frame r)) p)
                (evV g x .callByValuePar (tblV g x .callByValuePar (k+fuel)) E
                  (plug (WordCallUnfolding.expanded (.param 0) (sourceBody child)) (frame r)) p) := by
              apply ExpressionContext.refinement g x .callByValuePar _ _ E (tblV_ok _ _ _ k)
                hclock _ _ _ (frame r) p hp
              intro q hq
              exact WordExpansionRefinement.expanded g x _ _ (.param 0)
                (code rs fuel r.callee (i::seen)) (sourceBody child) True.intro hcodeFO hchildFO
                (fun w q hq => (ih r.callee (i::seen) hsub hchild htrail child hc k [w] q hq).2) E q hq
            have hlast := (WordCallUnfolding.context_bounds g r.callee (sourceBody child)
              hcallee hchildFO (.param 0) True.intro (frame r) x (k+fuel) E p hp).2
            rw [←canonical_body g x (k+fuel+1) r child hfactor hcallee E p hp] at hlast
            simpa only [Nat.add_assoc] using RLe.trans hinner hlast

end Shallot.MacroPeg.CBV.SelectedForwardingBounds
