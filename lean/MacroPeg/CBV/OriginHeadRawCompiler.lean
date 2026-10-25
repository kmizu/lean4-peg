import MacroPeg.CBV.OriginHeadInlining

namespace Shallot.MacroPeg.CBV.OriginHeadRawCompiler
open MultiplyingPrefixCompiler (Spec source sourceBody source_rule)
open ReplayControlFusion (Part Plan)

abbrev parts := MixedForwardingReset.parts
abbrev entries := MixedForwardingReset.entries
abbrev prepared := MixedForwardingReset.normalized
abbrev target (rs : List Spec) (i : Nat) (r : Spec) (P : Plan) := OriginHeadInlining.target (parts rs) (entries rs) i r P
abbrev render (rs : List Spec) (i : Nat) (r : Spec) (P : Plan) := OriginHeadInlining.render (parts rs) (entries rs) i r P
abbrev check (rs : List Spec) (i : Nat) := OriginHeadInlining.check (parts rs) (entries rs) i

/-- Preparing zero heads is a Par rewrite independently of whether the
previous backend already accepts the resulting head-callee kinds. -/
theorem prepared_related (rs : List Spec) (hg : (source rs).FirstOrder) :
    FiniteBodyRewrite.Related (source rs) (prepared rs) .callByValuePar 1 := by
  intro i
  cases hr : rs[i]? with
  | none => simp only [source_rule,MixedForwardingReset.normalized_rule,hr,Option.map_none]
  | some r =>
    simp only [source_rule,MixedForwardingReset.normalized_rule,hr,Option.map_some]
    refine ⟨True.intro,?_⟩
    intro x k E p hp
    by_cases hf : 1≤r.factor
    · simp only [if_pos hf]
      exact ⟨RLe.refl _,evV_mono (tblV_step _ _ _ k) _ _⟩
    · simp only [if_neg hf]
      exact ZeroResetCorrespondence.body_bounds_of_zero rs hg r (fun _ _ => by omega) x k E p hp

theorem prepared_firstOrder (rs : List Spec) (hg : (source rs).FirstOrder) : (prepared rs).FirstOrder := by
  intro a ha
  obtain ⟨j,hj⟩ := List.getElem?_of_mem ha
  have hrule : ruleAtM (prepared rs).rules j=some a := by rw [ruleAtM_eq_getElem?]; exact hj
  rw [MixedForwardingReset.normalized_rule] at hrule
  cases hr : rs[j]? with
  | none => simp [hr] at hrule
  | some r =>
    simp only [hr,Option.map_some,Option.some.injEq] at hrule
    subst a
    have hb := hg ⟨1,sourceBody r⟩ (List.mem_map.mpr ⟨r,List.mem_of_getElem? hr,rfl⟩)
    by_cases hf : 1≤r.factor
    · simpa only [if_pos hf] using hb
    · simp only [if_neg hf,ZeroResetOrigin.normalizedBody,MExp.FirstOrder]
      refine ⟨?_,True.intro,hb.2.2⟩
      cases hc : rs[r.callee]? with
      | none => simp only [ZeroResetOrigin.closedBranch,hc]; trivial
      | some child =>
        simp only [ZeroResetOrigin.closedBranch,hc]
        have hchild := hg ⟨1,sourceBody child⟩ (List.mem_map.mpr ⟨child,List.mem_of_getElem? hc,rfl⟩)
        exact ⟨firstOrder_subst (args := [.lit []]) (by trivial) _ hchild,hb.1.2⟩

theorem observations_iff (rs : List Spec) (i : Nat) (r : Spec) (P : Plan)
    (hi : (entries rs)[i]?=some (.growth r)) (hj : (entries rs)[r.callee]?=some (.origin P))
    (hg : (source rs).FirstOrder) (hc : check rs i=true)
    (e : MExp) (he : e.FirstOrder) (x : List Char) (rest : Option (List Char)) :
    SObs (source rs) .callByValuePar e x rest ↔
      SObs (target rs i r P) .callByValueSeq (render rs i r P e) x rest :=
  (FiniteBodyRewrite.observations (prepared_related rs hg) hg (prepared_firstOrder rs hg) (by decide) e he x rest).trans
    (OriginHeadInlining.observations_iff _ _ i r P hi hj (prepared_firstOrder rs hg) hc e he x rest)

theorem undefined_iff (rs : List Spec) (i : Nat) (r : Spec) (P : Plan)
    (hi : (entries rs)[i]?=some (.growth r)) (hj : (entries rs)[r.callee]?=some (.origin P))
    (hg : (source rs).FirstOrder) (hc : check rs i=true) (e : MExp) (he : e.FirstOrder) (x : List Char) :
    (∀ k, evV (source rs) x .callByValuePar (tblV (source rs) x .callByValuePar k) [] e x.length=none) ↔
      (∀ k, evV (target rs i r P) x .callByValueSeq (tblV (target rs i r P) x .callByValueSeq k) [] (render rs i r P e) x.length=none) :=
  (FiniteBodyRewrite.undefined_iff (prepared_related rs hg) x [] e x.length).trans
    (OriginHeadInlining.undefined_iff _ _ i r P hi hj (prepared_firstOrder rs hg) hc e he x)

theorem language_translation (rs : List Spec) (i : Nat) (r : Spec) (P : Plan)
    (hi : (entries rs)[i]?=some (.growth r)) (hj : (entries rs)[r.callee]?=some (.origin P))
    (hg : (source rs).FirstOrder) (hc : check rs i=true) (e : MExp) (he : e.FirstOrder) :
    ∃ (g : MGrammar) (entry : MExp), g.FirstOrder ∧ entry.FirstOrder ∧
      ∀ x, SObs (source rs) .callByValuePar e x (some []) ↔ SObs g .callByValueSeq entry x (some []) :=
  ⟨target rs i r P,render rs i r P e,MixedForwardingCompiler.target_firstOrder _ _,MixedForwardingCompiler.render_firstOrder _ _ e,
    fun x => observations_iff rs i r P hi hj hg hc e he x (some [])⟩

end Shallot.MacroPeg.CBV.OriginHeadRawCompiler
