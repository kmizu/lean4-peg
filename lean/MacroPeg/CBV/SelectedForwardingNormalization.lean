import MacroPeg.CBV.SelectedForwardingBounds
import MacroPeg.CBV.FiniteBodyRewrite

namespace Shallot.MacroPeg.CBV.SelectedForwardingNormalization
open SelectedForwardingContext
open MultiplyingPrefixCompiler (Spec sourceBody)

def body (rs : List Spec) (ids : List Nat) (i : Nat) (old : MExp) :=
  if i∈ids then ForwardingHeadExpansion.expanded rs i else old
def normalized (g : MGrammar) (rs : List Spec) (ids : List Nat) : MGrammar :=
  ⟨g.rules.mapIdx (fun i r => ⟨r.arity,body rs ids i r.body⟩)⟩

theorem rule (g : MGrammar) (rs : List Spec) (ids : List Nat) (i : Nat) :
    ruleAtM (normalized g rs ids).rules i=(ruleAtM g.rules i).map (fun r => ⟨r.arity,body rs ids i r.body⟩) := by
  simp [normalized,ruleAtM_eq_getElem?]
theorem rule_count (g : MGrammar) (rs : List Spec) (ids : List Nat) : (normalized g rs ids).rules.length=g.rules.length := by
  simp [normalized]
theorem arities (g : MGrammar) (rs : List Spec) (ids : List Nat) : SemanticBodyRewrite.ArityEq g (normalized g rs ids) := by
  intro i
  cases hr : ruleAtM g.rules i <;> simp [rule,hr]

theorem firstOrder (g : MGrammar) (hg : g.FirstOrder) (rs : List Spec) (ids : List Nat) (hv : Valid g rs ids) :
    (normalized g rs ids).FirstOrder := by
  intro r hr
  obtain ⟨i,hi,he⟩ := List.mem_mapIdx.mp hr
  subst r
  have hs : ruleAtM g.rules i=some g.rules[i] := by
    rw [ruleAtM_eq_getElem?]
    exact List.getElem?_eq_getElem hi
  by_cases hsel : i∈ids
  · obtain ⟨s,hspec⟩ := metadata_exists g rs ids hv i g.rules[i] hs
    simp only [body,if_pos hsel]
    exact code_firstOrder g hg rs ids hv (rs.length+1) i [] hsel s hspec
  · simp only [body,if_neg hsel]
    exact hg g.rules[i] (List.getElem_mem hi)

theorem related (g : MGrammar) (hg : g.FirstOrder) (rs : List Spec) (ids : List Nat) (hv : Valid g rs ids) :
    FiniteBodyRewrite.Related g (normalized g rs ids) .callByValuePar (rs.length+1) := by
  intro i
  cases hr : ruleAtM g.rules i with
  | none => simp only [rule,hr,Option.map_none]
  | some r =>
    simp only [rule,hr,Option.map_some]
    refine ⟨True.intro,?_⟩
    intro x k E p hp
    by_cases hsel : i∈ids
    · obtain ⟨s,hspec⟩ := metadata_exists g rs ids hv i r hr
      have he : r=⟨1,sourceBody s⟩ := Option.some.inj (hr.symm.trans (hv.rule i hsel s hspec))
      subst r
      simpa only [body,if_pos hsel,ForwardingHeadExpansion.expanded] using
        SelectedForwardingBounds.bounds g hg rs ids hv (rs.length+1) i [] (by simp) hsel
          (by simp [ForwardingPrefixTrace.Trail]) s hspec x k E p hp
    · simp only [body,if_neg hsel]
      exact ⟨RLe.refl _,evV_mono (tblV_le g x .callByValuePar (by omega)) _ _⟩

theorem physical_bounds (g : MGrammar) (hg : g.FirstOrder) (rs : List Spec) (ids : List Nat)
    (hv : Valid g rs ids) (x : List Char) (k : Nat) :
    TLeV (tblV g x .callByValuePar k) (tblV (normalized g rs ids) x .callByValuePar k) ∧
      TLeV (tblV (normalized g rs ids) x .callByValuePar k) (tblV g x .callByValuePar ((g.rules.length+2)*k)) := by
  refine ⟨FiniteBodyRewrite.forward_tables (related g hg rs ids hv) x k,?_⟩
  simpa only [hv.length] using FiniteBodyRewrite.backward_tables (related g hg rs ids hv) x k

theorem checked_observations (g : MGrammar) (hg : g.FirstOrder) (rs : List Spec) (ids : List Nat)
    (hc : check g rs ids=true) (e : MExp) (he : e.FirstOrder) (x : List Char) (rest : Option (List Char)) :
    SObs g .callByValuePar e x rest ↔ SObs (normalized g rs ids) .callByValuePar e x rest :=
  FiniteBodyRewrite.observations (related g hg rs ids (checked g rs ids hc)) hg
    (firstOrder g hg rs ids (checked g rs ids hc)) (by decide) e he x rest

theorem checked_undefined (g : MGrammar) (hg : g.FirstOrder) (rs : List Spec) (ids : List Nat)
    (hc : check g rs ids=true) (x : List Char) (E : List (List Char)) (e : MExp) (p : Nat) :
    (∀ k, evV g x .callByValuePar (tblV g x .callByValuePar k) E e p=none) ↔
      (∀ k, evV (normalized g rs ids) x .callByValuePar (tblV (normalized g rs ids) x .callByValuePar k) E e p=none) :=
  FiniteBodyRewrite.undefined_iff (related g hg rs ids (checked g rs ids hc)) x E e p

end Shallot.MacroPeg.CBV.SelectedForwardingNormalization
