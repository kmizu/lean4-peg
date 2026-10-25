import MacroPeg.CBV.ForwardingHeadBounds
import MacroPeg.CBV.FiniteBodyRewrite

namespace Shallot.MacroPeg.CBV.ForwardingHeadNormalization
open MultiplyingPrefixCompiler

def normalized (rs : List Spec) : MGrammar :=
  ⟨rs.mapIdx (fun i _ => ⟨1,ForwardingHeadExpansion.expanded rs i⟩)⟩

theorem rule (rs : List Spec) (i : Nat) :
    ruleAtM (normalized rs).rules i=(rs[i]?).map (fun _ => ⟨1,ForwardingHeadExpansion.expanded rs i⟩) := by
  simp [normalized,ruleAtM_eq_getElem?]

theorem firstOrder (rs : List Spec) (hg : (source rs).FirstOrder) : (normalized rs).FirstOrder := by
  intro r hr
  obtain ⟨i,hi,he⟩ := List.mem_mapIdx.mp hr
  subst r
  exact ForwardingHeadExpansion.code_firstOrder rs hg (rs.length+1) i []

theorem related (rs : List Spec) (hg : (source rs).FirstOrder) :
    FiniteBodyRewrite.Related (source rs) (normalized rs) .callByValuePar (rs.length+1) := by
  intro i
  cases hr : rs[i]? with
  | none => simp only [source_rule,rule,hr,Option.map_none]
  | some r =>
    simp only [source_rule,rule,hr,Option.map_some]
    refine ⟨True.intro,?_⟩
    intro x k E p hp
    simpa only [Nat.add_assoc] using ForwardingHeadExpansion.expanded_bounds rs hg i r hr x k E p hp

/-- Source clock k is simulated at target clock k; target clock k is
simulated at source clock (n+2)k, where n is the number of source rules. -/
theorem physical_bounds (rs : List Spec) (hg : (source rs).FirstOrder) (x : List Char) (k : Nat) :
    TLeV (sourceTable rs x k) (tblV (normalized rs) x .callByValuePar k) ∧
      TLeV (tblV (normalized rs) x .callByValuePar k) (sourceTable rs x ((rs.length+2)*k)) :=
  ⟨FiniteBodyRewrite.forward_tables (related rs hg) x k,
    FiniteBodyRewrite.backward_tables (related rs hg) x k⟩

theorem observations_iff (rs : List Spec) (hg : (source rs).FirstOrder) (e : MExp) (he : e.FirstOrder)
    (x : List Char) (rest : Option (List Char)) :
    SObs (source rs) .callByValuePar e x rest ↔ SObs (normalized rs) .callByValuePar e x rest :=
  FiniteBodyRewrite.observations (related rs hg) hg (firstOrder rs hg) (by decide) e he x rest

theorem undefined_iff (rs : List Spec) (hg : (source rs).FirstOrder) (x : List Char)
    (E : List (List Char)) (e : MExp) (p : Nat) :
    (∀ k, evV (source rs) x .callByValuePar (sourceTable rs x k) E e p=none) ↔
      (∀ k, evV (normalized rs) x .callByValuePar (tblV (normalized rs) x .callByValuePar k) E e p=none) :=
  FiniteBodyRewrite.undefined_iff (related rs hg) x E e p

end Shallot.MacroPeg.CBV.ForwardingHeadNormalization
