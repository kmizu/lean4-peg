import MacroPeg.CBV.ForwardingPrefixTrace
import MacroPeg.CBV.SemanticBodyRewrite

namespace Shallot.MacroPeg.CBV.ForwardingCycleElimination
open MultiplyingPrefixCompiler

def body (rs : List Spec) (i : Nat) (r : Spec) : MExp :=
  match ForwardingPrefixTrace.classify rs i with
  | .cycle _ => ForwardingPrefixCycles.deadBody
  | _ => sourceBody r

/-- Closed factor-1 head components, including paths entering them, are
replaced by checked argument preflight followed by non-consuming divergence. -/
def normalized (rs : List Spec) : MGrammar := ⟨rs.mapIdx (fun i r => ⟨1,body rs i r⟩)⟩

theorem rule (rs : List Spec) (i : Nat) :
    ruleAtM (normalized rs).rules i=(rs[i]?).map (fun r => ⟨1,body rs i r⟩) := by
  simp [normalized,ruleAtM_eq_getElem?]

theorem arities (rs : List Spec) : SemanticBodyRewrite.ArityEq (source rs) (normalized rs) := by
  intro i
  cases hr : rs[i]? <;> simp [source_rule,rule,hr]

theorem body_eq (rs : List Spec) (i : Nat) (r : Spec) (hr : rs[i]?=some r)
    (x : List Char) (k : Nat) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV (source rs) x .callByValuePar (sourceTable rs x k) E (sourceBody r) p=
      evV (source rs) x .callByValuePar (sourceTable rs x k) E (body rs i r) p := by
  cases hc : ForwardingPrefixTrace.classify rs i with
  | terminal j path => simp only [body,hc]
  | exhausted => simp only [body,hc]
  | cycle ids =>
    obtain ⟨hcheck,hi⟩ := ForwardingPrefixTrace.classify_cycle rs i ids hc
    rw [body,hc]
    exact ForwardingPrefixCycles.body_eq_dead rs ids ((ForwardingPrefixCycles.checked_iff rs ids).mp hcheck)
      i hi r hr x k E p hp

/-- Equality is required only for actual source iterates. The recursive
table equality is derived after rewriting, not assumed for the new grammar. -/
theorem tables (rs : List Spec) (x : List Char) (k : Nat) :
    sourceTable rs x k=tblV (normalized rs) x .callByValuePar k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext i E
    cases hr : rs[i]? with
    | none => simp only [tblV,source_rule,rule,hr,Option.map_none]
    | some r =>
      have hs : ruleAtM (source rs).rules i=some ⟨1,sourceBody r⟩ := by rw [source_rule,hr]; rfl
      have ht : ruleAtM (normalized rs).rules i=some ⟨1,body rs i r⟩ := by rw [rule,hr]; rfl
      simp only [sourceTable,tblV,hs,ht,←ih]
      apply List.map_congr_left
      intro p hp
      have hbound : p≤x.length := by have := List.mem_range.mp hp; omega
      exact (body_eq rs i r hr x k E p hbound).trans
        (SemanticBodyRewrite.evaluator (source rs) (normalized rs) (arities rs) x .callByValuePar
          (sourceTable rs x k) E (body rs i r) p)

theorem evaluator_eq (rs : List Spec) (x : List Char) (k : Nat) (E : List (List Char)) (e : MExp) (p : Nat) :
    evV (source rs) x .callByValuePar (sourceTable rs x k) E e p=
      evV (normalized rs) x .callByValuePar (tblV (normalized rs) x .callByValuePar k) E e p := by
  rw [tables rs x k]
  exact SemanticBodyRewrite.evaluator (source rs) (normalized rs) (arities rs) x .callByValuePar _ E e p

theorem normalized_firstOrder (rs : List Spec) (hg : (source rs).FirstOrder) : (normalized rs).FirstOrder := by
  intro r hr
  obtain ⟨i,hi,he⟩ := List.mem_mapIdx.mp hr
  subst r
  have hs : (sourceBody rs[i]).FirstOrder := hg ⟨1,sourceBody rs[i]⟩ (List.mem_map.mpr
    ⟨rs[i],List.getElem_mem hi,rfl⟩)
  cases hc : ForwardingPrefixTrace.classify rs i with
  | cycle ids => simp only [body,hc]; trivial
  | terminal j path => simpa only [body,hc] using hs
  | exhausted => simpa only [body,hc] using hs

theorem decide_eq (rs : List Spec) (e : MExp) (x : List Char) :
    decideObsV .callByValuePar (source rs) x e=decideObsV .callByValuePar (normalized rs) x e := by
  unfold decideObsV
  rw [ScannerPairFusion.stable_result_eq (source rs) (normalized rs) x .callByValuePar .callByValuePar
    e e (fun k => evaluator_eq rs x k [] e x.length)]

theorem observations_iff (rs : List Spec) (hg : (source rs).FirstOrder) (e : MExp) (he : e.FirstOrder)
    (x : List Char) (rest : Option (List Char)) :
    SObs (source rs) .callByValuePar e x rest ↔ SObs (normalized rs) .callByValuePar e x rest := by
  rw [←decideObsV_iff hg (by decide) he,←decideObsV_iff (normalized_firstOrder rs hg) (by decide) he,decide_eq rs e x]

theorem undefined_iff (rs : List Spec) (x : List Char) (E : List (List Char)) (e : MExp) (p : Nat) :
    (∀ k, evV (source rs) x .callByValuePar (sourceTable rs x k) E e p=none) ↔
      (∀ k, evV (normalized rs) x .callByValuePar (tblV (normalized rs) x .callByValuePar k) E e p=none) := by
  simp only [evaluator_eq rs x _ E e p]

end Shallot.MacroPeg.CBV.ForwardingCycleElimination
