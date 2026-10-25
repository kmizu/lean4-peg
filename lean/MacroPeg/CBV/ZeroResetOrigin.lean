import MacroPeg.CBV.ReplayControlFusion
import MacroPeg.CBV.MultiplyingPrefixCompiler
import MacroPeg.CBV.WordCallUnfolding

namespace Shallot.MacroPeg.CBV.ZeroResetOrigin
open MultiplyingPrefixCompiler (Spec source sourceBody source_rule)
open ReplayControlFusion (Part Plan)

mutual
  theorem literal_subst_closed : ∀ e, e.FirstOrder → ReplayFallbackFusion.Closed (MExp.subst [.lit []] e)
    | .param k,_ => by cases k <;> simp [MExp.subst,argAt,MExp.failAlways,ReplayFallbackFusion.Closed]
    | .call i args,h => literal_args_closed args h
    | .seq a b,h | .alt a b,h => ⟨literal_subst_closed a h.1,literal_subst_closed b h.2⟩
    | .notP a,h | .star a,h => literal_subst_closed a h
    | .eps,_ | .any,_ | .chr _,_ | .range _ _,_ | .lit _,_ => trivial
    | .dbg _,h | .lam _ _,h | .callParam _ _,h | .invoke _ _ _,h => False.elim h
  termination_by e => sizeOf e
  decreasing_by all_goals simp_wf; all_goals omega
  theorem literal_args_closed : ∀ args, MExp.FirstOrderArgs args → ReplayFallbackFusion.ClosedArgs (MExp.substArgs [.lit []] args)
    | [],_ => True.intro
    | a::args,h => ⟨literal_subst_closed a h.1,literal_args_closed args h.2⟩
  termination_by args => sizeOf args
  decreasing_by all_goals simp_wf; all_goals omega
end

mutual
  def closedCheck : MExp → Bool
    | .call _ args => closedArgsCheck args
    | .seq a b | .alt a b => closedCheck a && closedCheck b
    | .notP a | .star a => closedCheck a
    | .eps | .any | .chr _ | .range _ _ | .lit _ => true
    | _ => false
  def closedArgsCheck : List MExp → Bool
    | [] => true
    | a::args => closedCheck a && closedArgsCheck args
end
mutual
  theorem closed_checked : ∀ e, closedCheck e=true → ReplayFallbackFusion.Closed e
    | .call _ args,h => args_closed_checked args h
    | .seq a b,h | .alt a b,h => ⟨closed_checked a (Bool.and_eq_true_iff.mp h).1,closed_checked b (Bool.and_eq_true_iff.mp h).2⟩
    | .notP a,h | .star a,h => closed_checked a h
    | .eps,_ | .any,_ | .chr _,_ | .range _ _,_ | .lit _,_ => trivial
    | .param _,h | .dbg _,h | .lam _ _,h | .callParam _ _,h | .invoke _ _ _,h => by cases h
  theorem args_closed_checked : ∀ args, closedArgsCheck args=true → ReplayFallbackFusion.ClosedArgs args
    | [],_ => True.intro
    | a::args,h => ⟨closed_checked a (Bool.and_eq_true_iff.mp h).1,args_closed_checked args (Bool.and_eq_true_iff.mp h).2⟩
end

def check (rs : List Spec) := rs.all (fun r => match rs[r.callee]? with
  | none => true
  | some _ => decide (r.factor=0) && closedCheck r.tail)
def closedBranch (rs : List Spec) (r : Spec) : MExp := match rs[r.callee]? with
  | none => MExp.failAlways
  | some child => .seq (MExp.subst [.lit []] (sourceBody child)) r.tail
def normalizedBody (rs : List Spec) (r : Spec) : MExp := .alt (closedBranch rs r) (.seq (.param 0) r.fallback)
def parts (rs : List Spec) : List Part := rs.flatMap (fun r => [⟨false,closedBranch rs r⟩,⟨true,r.fallback⟩])
def plans (rs : List Spec) : List Plan := rs.mapIdx (fun i _ => .alt (.leaf (2*i)) (.leaf (2*i+1)))
abbrev normalized (rs : List Spec) := ReplayControlFusion.parGrammar (parts rs) (plans rs)
abbrev target (rs : List Spec) := ReplayControlFusion.seqGrammar (parts rs) (plans rs)
abbrev render (rs : List Spec) := ReplayControlFusion.render (parts rs) (plans rs)

theorem rule_count (rs : List Spec) : (target rs).rules.length=2*rs.length := by
  have hh : (rs.map (fun _ => 2)).sum=2*rs.length := by
    induction rs with
    | nil => rfl
    | cons r rs ih => simp [ih,Nat.mul_succ,Nat.add_comm]
  simpa [target,ReplayControlFusion.seqGrammar,parts,List.length_flatMap] using hh

theorem head_checked (rs : List Spec) (hc : check rs=true) (r : Spec) (hr : r∈rs) (child : Spec)
    (hn : rs[r.callee]?=some child) : r.factor=0 ∧ ReplayFallbackFusion.Closed r.tail := by
  have h := (List.all_eq_true.mp hc) r hr
  simp only [hn,Bool.and_eq_true_iff] at h
  exact ⟨of_decide_eq_true h.1,closed_checked _ h.2⟩

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
    ruleAtM (normalized rs).rules i=(rs[i]?).map (fun r => ⟨1,normalizedBody rs r⟩) := by
  rw [ReplayControlFusion.par_rule]
  simp only [plans,List.getElem?_mapIdx]
  cases hr : rs[i]? with
  | none => rfl
  | some r =>
    simp only [Option.map_some,Plan.exp,normalizedBody]
    have h0 := pair_lookup rs true i
    have h1 := pair_lookup rs false i
    simp only [if_true,Bool.false_eq_true,if_false,Nat.add_zero,hr,Option.map_some] at h0 h1
    simp only [ReplayControlFusion.sourceLeaf,h0,h1,Bool.false_eq_true,if_false,if_true]

theorem parts_valid (rs : List Spec) (hg : (source rs).FirstOrder) (hc : check rs=true) :
    ∀ r∈parts rs, ReplayControlFusion.ValidPart r := by
  intro p hp
  obtain ⟨r,hr,hp⟩ := List.mem_flatMap.mp hp
  have hbody := hg ⟨1,sourceBody r⟩ (List.mem_map.mpr ⟨r,hr,rfl⟩)
  have hclosed : ReplayFallbackFusion.Closed (closedBranch rs r) := by
    cases hn : rs[r.callee]? with
    | none => simp only [closedBranch,hn]; trivial
    | some child =>
      simp only [closedBranch,hn]
      exact ⟨literal_subst_closed _ (hg ⟨1,sourceBody child⟩ (List.mem_map.mpr ⟨child,List.mem_of_getElem? hn,rfl⟩)),
        (head_checked rs hc r hr child hn).2⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl
  · exact ⟨ReplayFallbackFusion.closed_firstOrder _ hclosed,fun _ => hclosed⟩
  · exact ⟨hbody.2.2,by intro h; cases h⟩

theorem plans_valid (rs : List Spec) : ∀ p∈plans rs, ReplayControlFusion.ValidPlan (parts rs) p := by
  intro p hp
  obtain ⟨i,hi,he⟩ := List.mem_mapIdx.mp hp
  subst p
  have hr : rs[i]?=some rs[i] := List.getElem?_eq_getElem hi
  constructor
  · exact ⟨⟨false,closedBranch rs rs[i]⟩,by simpa only [if_true,Nat.add_zero,hr,Option.map_some] using pair_lookup rs true i⟩
  · exact ⟨⟨true,rs[i].fallback⟩,by simpa only [Bool.false_eq_true,if_false,hr,Option.map_some] using pair_lookup rs false i⟩

end Shallot.MacroPeg.CBV.ZeroResetOrigin
