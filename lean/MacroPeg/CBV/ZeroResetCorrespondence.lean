import MacroPeg.CBV.ZeroResetOrigin
import MacroPeg.CBV.FiniteBodyRewrite
import MacroPeg.CBV.ForwardingHeadExpansion
import MacroPeg.CBV.WordExpansionRefinement

namespace Shallot.MacroPeg.CBV.ZeroResetCorrespondence
open ZeroResetOrigin
open MultiplyingPrefixCompiler (Spec source sourceBody source_rule)
open ForwardingHeadExpansion (frame)
open ExpressionContext (plug)

theorem body_bounds_of_zero (rs : List Spec) (hg : (source rs).FirstOrder)
    (r : Spec) (hz : ∀ child, rs[r.callee]?=some child → r.factor=0) (x : List Char) (k : Nat) (E : List (List Char))
    (p : Nat) (hp : p≤x.length) :
    RLe (evV (source rs) x .callByValuePar (tblV (source rs) x .callByValuePar k) E (sourceBody r) p)
      (evV (source rs) x .callByValuePar (tblV (source rs) x .callByValuePar k) E (normalizedBody rs r) p) ∧
    RLe (evV (source rs) x .callByValuePar (tblV (source rs) x .callByValuePar k) E (normalizedBody rs r) p)
      (evV (source rs) x .callByValuePar (tblV (source rs) x .callByValuePar (k+1)) E (sourceBody r) p) := by
  cases hn : rs[r.callee]? with
  | none =>
    have he : evV (source rs) x .callByValuePar (tblV (source rs) x .callByValuePar k) E (sourceBody r) p=
        evV (source rs) x .callByValuePar (tblV (source rs) x .callByValuePar k) E (normalizedBody rs r) p := by
      simp [sourceBody,normalizedBody,closedBranch,hn,evV,source_rule,MExp.failAlways]
    exact ⟨Or.inr he,by rw [←he]; exact evV_mono (tblV_step _ _ _ k) _ _⟩
  | some child =>
    have hf := hz child hn
    have hchild : ruleAtM (source rs).rules r.callee=some ⟨1,sourceBody child⟩ := by rw [source_rule,hn]; rfl
    have hchildFO := hg ⟨1,sourceBody child⟩ (ruleAtM_mem hchild)
    have hs : sourceBody r=plug (.call r.callee [.lit []]) (frame r) := by
      simp only [sourceBody,hf,RepeatedWordArguments.expression,frame,plug]
    have hsrc (j : Nat) := congrArg (fun e => evV (source rs) x .callByValuePar
      (tblV (source rs) x .callByValuePar j) E e p) hs
    have he : evV (source rs) x .callByValuePar (tblV (source rs) x .callByValuePar k) E
        (plug (WordCallUnfolding.expanded (.lit []) (sourceBody child)) (frame r)) p=
        evV (source rs) x .callByValuePar (tblV (source rs) x .callByValuePar k) E (normalizedBody rs r) p := by
      have hh : evV (source rs) x .callByValuePar (tblV (source rs) x .callByValuePar k) E
          (plug (WordCallUnfolding.expanded (.lit []) (sourceBody child)) (frame r)) p=
          evV (source rs) x .callByValuePar (tblV (source rs) x .callByValuePar k) E
          (plug (MExp.subst [.lit []] (sourceBody child)) (frame r)) p := by
        apply WordExpansionRefinement.context_eq _ _ _ _ _ (tblV_ok _ _ _ k) _ _ _ (frame r) p hp
        intro q hq
        have hg0 : evV (source rs) x .callByValuePar (tblV (source rs) x .callByValuePar k) E (.andP (.lit [])) q=some (some q) := by
          rw [CallLookahead.evV_peek]
          simp [evV,Shallot.stripPrefix?,length_sfx x hq,CallLookahead.peek]
        exact evV_seq_ok hg0
      simpa only [normalizedBody,closedBranch,hn,frame,plug] using hh
    have hb := WordCallUnfolding.context_bounds (source rs) r.callee (sourceBody child) hchild hchildFO
      (.lit []) True.intro (frame r) x k E p hp
    exact ⟨RLe.trans (Or.inr (hsrc k)) (RLe.trans hb.1 (Or.inr he)),
      RLe.trans (Or.inr he.symm) (RLe.trans hb.2 (Or.inr (hsrc (k+1)).symm))⟩

theorem body_bounds (rs : List Spec) (hg : (source rs).FirstOrder) (hc : check rs=true)
    (i : Nat) (r : Spec) (hr : rs[i]?=some r) (x : List Char) (k : Nat) (E : List (List Char))
    (p : Nat) (hp : p≤x.length) :
    RLe (evV (source rs) x .callByValuePar (tblV (source rs) x .callByValuePar k) E (sourceBody r) p)
      (evV (source rs) x .callByValuePar (tblV (source rs) x .callByValuePar k) E (normalizedBody rs r) p) ∧
    RLe (evV (source rs) x .callByValuePar (tblV (source rs) x .callByValuePar k) E (normalizedBody rs r) p)
      (evV (source rs) x .callByValuePar (tblV (source rs) x .callByValuePar (k+1)) E (sourceBody r) p) :=
  body_bounds_of_zero rs hg r (fun child hn => (head_checked rs hc r (List.mem_of_getElem? hr) child hn).1) x k E p hp

theorem related (rs : List Spec) (hg : (source rs).FirstOrder) (hc : check rs=true) :
    FiniteBodyRewrite.Related (source rs) (normalized rs) .callByValuePar 1 := by
  intro i
  cases hr : rs[i]? with
  | none => simp only [source_rule,normalized_rule,hr,Option.map_none]
  | some r =>
    simp only [source_rule,normalized_rule,hr,Option.map_some]
    exact ⟨True.intro,fun x k E p hp => body_bounds rs hg hc i r hr x k E p hp⟩

/-- Actual generated Seq execution refines source clock k and is refined
by source clock 2k. The result includes finite failure. -/
theorem physical_bounds (rs : List Spec) (hg : (source rs).FirstOrder) (hc : check rs=true)
    (e : MExp) (he : e.FirstOrder) (x : List Char) (k : Nat) (E : List (List Char))
    (p : Nat) (hp : p≤x.length) :
    RLe (evV (source rs) x .callByValuePar (tblV (source rs) x .callByValuePar k) E e p)
      (evV (target rs) x .callByValueSeq (tblV (target rs) x .callByValueSeq k) E (render rs e) p) ∧
    RLe (evV (target rs) x .callByValueSeq (tblV (target rs) x .callByValueSeq k) E (render rs e) p)
      (evV (source rs) x .callByValuePar (tblV (source rs) x .callByValuePar (2*k)) E e p) := by
  rw [←ReplayControlFusion.evaluator_eq (parts_valid rs hg hc) (plans_valid rs) x k E e he p hp]
  rw [←SemanticBodyRewrite.evaluator (source rs) (normalized rs)
    (FiniteBodyRewrite.arities (related rs hg hc)) x .callByValuePar (tblV (normalized rs) x .callByValuePar k) E e p]
  exact ⟨evV_mono (FiniteBodyRewrite.forward_tables (related rs hg hc) x k) e p,
    evV_mono (FiniteBodyRewrite.backward_tables (related rs hg hc) x k) e p⟩

theorem observations_iff (rs : List Spec) (hg : (source rs).FirstOrder) (hc : check rs=true)
    (e : MExp) (he : e.FirstOrder) (x : List Char) (rest : Option (List Char)) :
    SObs (source rs) .callByValuePar e x rest ↔ SObs (target rs) .callByValueSeq (render rs e) x rest :=
  (FiniteBodyRewrite.observations (related rs hg hc) hg
    (ReplayControlFusion.par_firstOrder (parts_valid rs hg hc) (plans rs)) (by decide) e he x rest).trans
    (ReplayControlFusion.observations_iff (parts_valid rs hg hc) (plans_valid rs) e he x rest)

theorem undefined_iff (rs : List Spec) (hg : (source rs).FirstOrder) (hc : check rs=true)
    (e : MExp) (he : e.FirstOrder) (x : List Char) :
    (∀ k, evV (source rs) x .callByValuePar (tblV (source rs) x .callByValuePar k) [] e x.length=none) ↔
      (∀ k, evV (target rs) x .callByValueSeq (tblV (target rs) x .callByValueSeq k) [] (render rs e) x.length=none) :=
  BoundedBodyRewrite.undefined_of_observations (source rs) (target rs) hg (ReplayControlFusion.seq_firstOrder _ _)
    .callByValuePar .callByValueSeq (by decide) (by decide) e (render rs e) he (ReplayControlFusion.render_firstOrder _ _ e) x
    (fun rest => observations_iff rs hg hc e he x rest)

theorem language_translation (rs : List Spec) (hg : (source rs).FirstOrder) (hc : check rs=true)
    (e : MExp) (he : e.FirstOrder) :
    ∃ (out : MGrammar) (entry : MExp), out.FirstOrder ∧ entry.FirstOrder ∧
      ∀ x, SObs (source rs) .callByValuePar e x (some []) ↔ SObs out .callByValueSeq entry x (some []) :=
  ⟨target rs,render rs e,ReplayControlFusion.seq_firstOrder _ _,ReplayControlFusion.render_firstOrder _ _ e,
    fun x => observations_iff rs hg hc e he x (some [])⟩

end Shallot.MacroPeg.CBV.ZeroResetCorrespondence
