import MacroPeg.CBV.CallLookahead
import MacroPeg.CBV.PrefixFamilyFusion

/-! Arbitrary-arity prefix fusion under body tests. Call-site lookahead keeps
the source caller position while Seq captures all adjacent runtime chunks. -/
namespace Shallot.MacroPeg.CBV.PrefixFamilyTestFusion
open PrefixFamilyFusion

theorem prefixExpr_render (n : Nat) :
    CallLookahead.render (CaptureViews.prefixExpr n) = CaptureViews.prefixExpr n := by
  induction n <;> simp_all [CaptureViews.prefixExpr,CallLookahead.render]

private theorem renderArgs_map_seq (a : MExp) (args : List MExp) :
    CallLookahead.renderArgs (args.map (.seq a)) =
      (CallLookahead.renderArgs args).map (.seq (CallLookahead.render a)) := by
  induction args <;> simp_all [CallLookahead.renderArgs,CallLookahead.render]

theorem parsers_render (args : List MExp) :
    CallLookahead.renderArgs (parsers args) = parsers (CallLookahead.renderArgs args) := by
  induction args <;> simp_all [parsers,CallLookahead.renderArgs,renderArgs_map_seq]

mutual
  theorem render_commute (parallel : Bool) (scope : Nat) : ∀ e, e.FirstOrder →
      CallLookahead.render (render parallel scope e) =
        render parallel scope (CallLookahead.render e)
    | .param k, _ => by
      by_cases hk : k < scope <;> cases parallel <;>
        simp [render,hk,CallLookahead.render,prefixExpr_render,MExp.failAlways]
    | .call i args, hf => by
      cases parallel <;>
        simp [render,CallLookahead.render,MExp.andP,parsers_render,
          renderArgs_commute _ scope args hf]
    | .seq a b, hf | .alt a b, hf => by
      simp only [render,CallLookahead.render]
      rw [render_commute parallel scope a hf.1,render_commute parallel scope b hf.2]
    | .star a, hf | .notP a, hf => by
      simp only [render,CallLookahead.render]
      rw [render_commute parallel scope a hf]
    | .eps, _ | .any, _ | .chr _, _ | .range _ _, _ | .lit _, _ => rfl
    | .dbg _, hf | .lam _ _, hf | .callParam _ _, hf | .invoke _ _ _, hf => False.elim hf
  theorem renderArgs_commute (parallel : Bool) (scope : Nat) :
      ∀ args, MExp.FirstOrderArgs args →
        CallLookahead.renderArgs (renderArgs parallel scope args) =
          renderArgs parallel scope (CallLookahead.renderArgs args)
    | [], _ => rfl
    | a::args, hf => by
      simp only [renderArgs,CallLookahead.renderArgs]
      rw [render_commute parallel scope a hf.1,renderArgs_commute parallel scope args hf.2]
end

def testedRules (rules : List MRule) : List MRule :=
  rules.map (fun r => ⟨r.arity,CallLookahead.render r.body⟩)

def parGrammar (rules : List MRule) : MGrammar :=
  CallLookahead.tested (PrefixFamilyFusion.parGrammar rules)
def seqGrammar (rules : List MRule) : MGrammar :=
  PrefixFamilyFusion.seqGrammar (testedRules rules)

theorem wrapped_family {rules : List MRule} (hf : ∀ r ∈ rules, r.body.FirstOrder) :
    CallLookahead.wrapped (PrefixFamilyFusion.parGrammar rules) =
      PrefixFamilyFusion.parGrammar (testedRules rules) := by
  unfold CallLookahead.wrapped PrefixFamilyFusion.parGrammar testedRules
  simp only [List.map_map,Function.comp_def]
  apply congrArg MGrammar.mk
  apply List.map_congr_left
  intro r hr
  simp only [CallLookahead.render]
  rw [render_commute true r.arity r.body (hf r hr)]
  have h : CallLookahead.render (replay r.arity) = replay r.arity := by
    cases r.arity <;> rfl
  rw [h]

/-- The fixed Seq target keeps all unbounded prefix values, evaluates the
tail at the common advanced position, and restores the caller after the test. -/
theorem observations_iff {rules : List MRule} (hf : ∀ r ∈ rules, r.body.FirstOrder)
    {e : MExp} (he : e.FirstOrder) (x : List Char) (r : Option (List Char)) :
    SObs (parGrammar rules) .callByValuePar (render true 0 e) x r ↔
      SObs (seqGrammar rules) .callByValueSeq (render false 0 (CallLookahead.render e)) x r := by
  have h := CallLookahead.observations_iff (PrefixFamilyFusion.par_firstOrder rules)
    (render true 0 e) (render_firstOrder true 0 e) x r
  rw [wrapped_family hf,render_commute true 0 e he] at h
  exact h.trans (PrefixFamilyFusion.observations_iff _ _ x r)

theorem language_translation {rules : List MRule} (hf : ∀ r ∈ rules, r.body.FirstOrder)
    {e : MExp} (he : e.FirstOrder) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧
      ∀ x, SObs (parGrammar rules) .callByValuePar (render true 0 e) x (some []) ↔
        SObs g .callByValueSeq start x (some []) :=
  ⟨seqGrammar rules,render false 0 (CallLookahead.render e),
    PrefixFamilyFusion.seq_firstOrder _,render_firstOrder _ _ _,
    fun x => observations_iff hf he x (some [])⟩

end Shallot.MacroPeg.CBV.PrefixFamilyTestFusion
