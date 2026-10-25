import MacroPeg.CBV.MixedGrowthChecks
import MacroPeg.CBV.ZeroResetCorrespondence

namespace Shallot.MacroPeg.CBV.MixedResetCompiler
open MultiplyingPrefixCompiler (Spec source sourceBody source_rule)
open ReplayControlFusion (Part Plan)

def closedBranch (rs : List Spec) (r : Spec) : MExp :=
  if 2≤r.factor then MExp.failAlways else ZeroResetOrigin.closedBranch rs r

def parts (rs : List Spec) : List Part := rs.flatMap (fun r => [⟨false,closedBranch rs r⟩,⟨true,r.fallback⟩])
def entries (rs : List Spec) : List MixedGrowthCompiler.Entry := rs.mapIdx (fun i r =>
  if 2≤r.factor then .growth r else .origin (.alt (.leaf (2*i)) (.leaf (2*i+1))))
def normalized (rs : List Spec) := MixedGrowthCompiler.source (parts rs) (entries rs)
def target (rs : List Spec) := MixedGrowthCompiler.target (parts rs) (entries rs)
abbrev render (rs : List Spec) := MixedGrowthCompiler.render (parts rs) (entries rs)
def check (rs : List Spec) : Bool := MixedGrowthChecks.check (parts rs) (entries rs) &&
  rs.all (fun r => if 2≤r.factor then true else match rs[r.callee]? with
    | none => true | some _ => decide (r.factor=0))

theorem pair_lookup (rs : List Spec) (closed : Bool) (i : Nat) :
    (parts rs)[2*i+(if closed then 0 else 1)]?=
      (rs[i]?).map (fun r => if closed then ⟨false,closedBranch rs r⟩ else ⟨true,r.fallback⟩) := by
  have hh (entries : List Spec) :
      (entries.flatMap (fun r => [({ replay := false,body := closedBranch rs r } : Part),⟨true,r.fallback⟩]))[2*i+(if closed then 0 else 1)]?=
      (entries[i]?).map (fun r => if closed then ⟨false,closedBranch rs r⟩ else ⟨true,r.fallback⟩) := by
    induction entries generalizing i with
    | nil => simp
    | cons r entries ih =>
      cases i with
      | zero => cases closed <;> rfl
      | succ i =>
        have hn : 2*(i+1)+(if closed then 0 else 1)=(2*i+(if closed then 0 else 1))+2 := by omega
        rw [hn]
        simpa only [List.flatMap_cons,List.cons_append,List.nil_append,List.getElem?_cons_succ,
          List.getElem?_cons_zero,Nat.add_succ,Nat.add_zero] using ih i
  exact hh rs

theorem normalized_rule (rs : List Spec) (i : Nat) :
    ruleAtM (normalized rs).rules i=(rs[i]?).map (fun r =>
      ⟨1,if 2≤r.factor then sourceBody r else ZeroResetOrigin.normalizedBody rs r⟩) := by
  rw [normalized,MixedGrowthCompiler.source_rule]
  simp only [entries,List.getElem?_mapIdx]
  cases hr : rs[i]? with
  | none => rfl
  | some r =>
    simp only [Option.map_some]
    by_cases hf : 2≤r.factor
    · simp only [if_pos hf,MixedGrowthCompiler.body]
    · simp only [if_neg hf,MixedGrowthCompiler.body,Plan.exp,ZeroResetOrigin.normalizedBody]
      have h0 := pair_lookup rs true i
      have h1 := pair_lookup rs false i
      simp only [if_true,Bool.false_eq_true,if_false,Nat.add_zero,hr,Option.map_some] at h0 h1
      simp only [ReplayControlFusion.sourceLeaf,h0,h1,Bool.false_eq_true,if_false,if_true,closedBranch,if_neg hf]

theorem valid (rs : List Spec) (hc : check rs=true) : MixedGrowthCompiler.Valid (parts rs) (entries rs) :=
  MixedGrowthChecks.checked _ _ (Bool.and_eq_true_iff.mp hc).1

theorem related (rs : List Spec) (hg : (source rs).FirstOrder) (hc : check rs=true) :
    FiniteBodyRewrite.Related (source rs) (normalized rs) .callByValuePar 1 := by
  intro i
  cases hr : rs[i]? with
  | none => simp only [source_rule,normalized_rule,hr,Option.map_none]
  | some r =>
    simp only [source_rule,normalized_rule,hr,Option.map_some]
    refine ⟨True.intro,?_⟩
    intro x k E p hp
    by_cases hf : 2≤r.factor
    · simp only [if_pos hf]
      exact ⟨RLe.refl _,evV_mono (tblV_step _ _ _ k) _ _⟩
    · simp only [if_neg hf]
      apply ZeroResetCorrespondence.body_bounds_of_zero rs hg r _ x k E p hp
      intro child hn
      have h := (List.all_eq_true.mp (Bool.and_eq_true_iff.mp hc).2) r (List.mem_of_getElem? hr)
      simp only [if_neg hf,hn] at h
      exact of_decide_eq_true h

theorem physical_bounds (rs : List Spec) (hg : (source rs).FirstOrder) (hc : check rs=true)
    (e : MExp) (he : e.FirstOrder) (x : List Char) (k : Nat) (E : List (List Char))
    (p : Nat) (hp : p≤x.length) :
    RLe (evV (source rs) x .callByValuePar (tblV (source rs) x .callByValuePar k) E e p)
      (evV (target rs) x .callByValueSeq (tblV (target rs) x .callByValueSeq k) E (render rs e) p) ∧
    RLe (evV (target rs) x .callByValueSeq (tblV (target rs) x .callByValueSeq k) E (render rs e) p)
      (evV (source rs) x .callByValuePar (tblV (source rs) x .callByValuePar (2*k)) E e p) := by
  have heq : evV (normalized rs) x .callByValuePar (tblV (normalized rs) x .callByValuePar k) E e p=
      evV (target rs) x .callByValueSeq (tblV (target rs) x .callByValueSeq k) E (render rs e) p :=
    MixedGrowthCorrespondence.evaluator_eq _ _ (valid rs hc) x k E e he p hp
  rw [←heq]
  rw [←SemanticBodyRewrite.evaluator (source rs) (normalized rs)
    (FiniteBodyRewrite.arities (related rs hg hc)) x .callByValuePar (tblV (normalized rs) x .callByValuePar k) E e p]
  exact ⟨evV_mono (FiniteBodyRewrite.forward_tables (related rs hg hc) x k) e p,
    evV_mono (FiniteBodyRewrite.backward_tables (related rs hg hc) x k) e p⟩

theorem rule_count (rs : List Spec) : (target rs).rules.length=rs.length*(rs.length+3) := by
  have hh : (rs.map (fun _ => 2)).sum=2*rs.length := by
    induction rs with
    | nil => rfl
    | cons r rs ih => simp [ih,Nat.mul_succ,Nat.add_comm]
  have hp : (parts rs).length=2*rs.length := by simpa [parts,List.length_flatMap] using hh
  simp only [target,MixedGrowthCompiler.rule_count,entries,List.length_mapIdx,hp]
  simp only [Nat.mul_add,Nat.mul_one]
  omega

theorem observations_iff (rs : List Spec) (hg : (source rs).FirstOrder) (hc : check rs=true)
    (e : MExp) (he : e.FirstOrder) (x : List Char) (rest : Option (List Char)) :
    SObs (source rs) .callByValuePar e x rest ↔ SObs (target rs) .callByValueSeq (render rs e) x rest :=
  (FiniteBodyRewrite.observations (related rs hg hc) hg
    (MixedGrowthCompiler.source_firstOrder _ _ (valid rs hc)) (by decide) e he x rest).trans
    (MixedGrowthCorrespondence.observations_iff _ _ (valid rs hc) e he x rest)

theorem undefined_iff (rs : List Spec) (hg : (source rs).FirstOrder) (hc : check rs=true)
    (e : MExp) (he : e.FirstOrder) (x : List Char) :
    (∀ k, evV (source rs) x .callByValuePar (tblV (source rs) x .callByValuePar k) [] e x.length=none) ↔
      (∀ k, evV (target rs) x .callByValueSeq (tblV (target rs) x .callByValueSeq k) [] (render rs e) x.length=none) :=
  BoundedBodyRewrite.undefined_of_observations (source rs) (target rs) hg (MixedGrowthCompiler.target_firstOrder _ _)
    .callByValuePar .callByValueSeq (by decide) (by decide) e (render rs e) he (MixedGrowthCompiler.render_firstOrder _ _ e) x
    (fun rest => observations_iff rs hg hc e he x rest)

theorem language_translation (rs : List Spec) (hg : (source rs).FirstOrder) (hc : check rs=true)
    (e : MExp) (he : e.FirstOrder) :
    ∃ (out : MGrammar) (entry : MExp), out.FirstOrder ∧ entry.FirstOrder ∧
      ∀ x, SObs (source rs) .callByValuePar e x (some []) ↔ SObs out .callByValueSeq entry x (some []) :=
  ⟨target rs,render rs e,MixedGrowthCompiler.target_firstOrder _ _,MixedGrowthCompiler.render_firstOrder _ _ e,
    fun x => observations_iff rs hg hc e he x (some [])⟩

end Shallot.MacroPeg.CBV.MixedResetCompiler
