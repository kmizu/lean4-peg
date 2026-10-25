import MacroPeg.CBV.OriginHeadParts

namespace Shallot.MacroPeg.CBV.OriginHeadEvaluation
open OriginHeadPlan
open OriginHeadParts
open ReplayControlFusion (Part Plan sourceLeaf)
open MultiplyingPrefixCompiler (Spec)

def unfolded (parts : List Part) (r : Spec) (P : Plan) : MExp :=
  .alt (.seq (.andP (power r.factor)) (.seq (MExp.subst [power r.factor] (P.exp (sourceLeaf parts))) r.tail))
    (.seq (.param 0) r.fallback)

theorem after_expression (parts : List Part) (r : Spec) (P : Plan)
    (hp : ∀ a∈parts, ReplayControlFusion.ValidPart a) (hv : ReplayControlFusion.ValidPlan parts P)
    (hm : 1≤r.factor) (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table)
    (E : List (List Char)) (p : Nat) :
    evV g x s T E ((after parts.length (2*parts.length) (3*parts.length) P).exp (sourceLeaf (extended parts r))) p=
      evV g x s T E (.seq (MExp.subst [power r.factor] (P.exp (sourceLeaf parts))) r.tail) p := by
  rw [Plan.exp_eval]
  have ht : evV g x s T E (sourceLeaf (extended parts r) (3*parts.length)) p=evV g x s T E r.tail p := by
    simp only [sourceLeaf,tail_lookup,Bool.false_eq_true,if_false]
  have hleaves : Plan.All (fun i =>
      evV g x s T E (sourceLeaf (extended parts r) (parts.length+i)) p=
        evV g x s T E (MExp.subst [power r.factor] (sourceLeaf parts i)) p ∧
      evV g x s T E (sourceLeaf (extended parts r) (2*parts.length+i)) p=
        follow (evV g x s T E (MExp.subst [power r.factor] (sourceLeaf parts i)) p)
          (fun q => evV g x s T E r.tail q)) P := by
    apply Plan.all_imp (t := P) _ hv
    intro i hi
    obtain ⟨a,ha⟩ := hi
    have hsingle : sourceLeaf parts i=sourceLeaf [a] 0 := by simp only [sourceLeaf,ha,List.getElem?_cons_zero]
    have hb : sourceLeaf (extended parts r) (parts.length+i)=sourceLeaf [rebased r.factor a] 0 := by
      simp only [sourceLeaf,base_lookup parts r i a ha,List.getElem?_cons_zero]
    have hd : sourceLeaf (extended parts r) (2*parts.length+i)=sourceLeaf [attached r.tail (rebased r.factor a)] 0 := by
      simp only [sourceLeaf,done_lookup parts r i a ha,List.getElem?_cons_zero]
    constructor
    · rw [hb,hsingle]; exact rebased_eval g x s T E r.factor hm a (hp a (List.mem_of_getElem? ha)) p
    · rw [hd,attached_eval,hsingle,rebased_eval g x s T E r.factor hm a (hp a (List.mem_of_getElem? ha)) p]
  rw [after_eval parts.length (2*parts.length) (3*parts.length)
    (fun i => evV g x s T E (sourceLeaf (extended parts r) i) p)
    (fun i => evV g x s T E (MExp.subst [power r.factor] (sourceLeaf parts i)) p)
    (fun q => evV g x s T E r.tail q) p ht P hleaves,subst_plan]
  change follow (P.eval (fun i => evV g x s T E (MExp.subst [power r.factor] (sourceLeaf parts i)) p) p)
    (fun q => evV g x s T E r.tail q)=
    follow (evV g x s T E (P.exp (fun i => MExp.subst [power r.factor] (sourceLeaf parts i))) p)
      (fun q => evV g x s T E r.tail q)
  rw [Plan.exp_eval]

theorem plan_expression (parts : List Part) (r : Spec) (P : Plan)
    (hp : ∀ a∈parts, ReplayControlFusion.ValidPart a) (hv : ReplayControlFusion.ValidPlan parts P)
    (hm : 1≤r.factor) (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table)
    (E : List (List Char)) (p : Nat) :
    evV g x s T E ((plan parts r P).exp (sourceLeaf (extended parts r))) p=evV g x s T E (unfolded parts r P) p := by
  have hg : evV g x s T E (.andP (sourceLeaf (extended parts r) (3*parts.length+1))) p=
      evV g x s T E (.andP (power r.factor)) p := by
    have he : sourceLeaf (extended parts r) (3*parts.length+1)=sourceLeaf [⟨true,.andP (power (r.factor-1))⟩] 0 := by
      simp only [sourceLeaf,gate_lookup,List.getElem?_cons_zero]
    rw [he]; exact gate_eval g x s T E r.factor hm p
  have hf : sourceLeaf (extended parts r) (3*parts.length+2)=.seq (.param 0) r.fallback := by
    simp only [sourceLeaf,fallback_lookup,if_true]
  have ha (q : Nat) := after_expression parts r P hp hv hm g x s T E q
  change ReplayFallbackFusion.orElse
    (follow (evV g x s T E (.andP (sourceLeaf (extended parts r) (3*parts.length+1))) p)
      (fun q => evV g x s T E ((after parts.length (2*parts.length) (3*parts.length) P).exp (sourceLeaf (extended parts r))) q))
    (evV g x s T E (sourceLeaf (extended parts r) (3*parts.length+2)) p)=_
  simp only [hg,hf,ha]
  rfl

theorem unfolded_context (parts : List Part) (r : Spec) (P : Plan)
    (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table) (E : List (List Char)) (p : Nat) :
    evV g x s T E (unfolded parts r P) p=
      evV g x s T E (ExpressionContext.plug (WordCallUnfolding.expanded (power r.factor) (P.exp (sourceLeaf parts)))
        (ForwardingHeadExpansion.frame r)) p := by
  have hs : evV g x s T E (.seq (.andP (power r.factor))
      (.seq (MExp.subst [power r.factor] (P.exp (sourceLeaf parts))) r.tail)) p=
      evV g x s T E (.seq (.seq (.andP (power r.factor)) (MExp.subst [power r.factor] (P.exp (sourceLeaf parts)))) r.tail) p := by
    simp only [evV]
    cases evV g x s T E (.andP (power r.factor)) p with
    | none => rfl
    | some v => cases v <;> rfl
  exact congrArg (fun res => ReplayFallbackFusion.orElse res (evV g x s T E (.seq (.param 0) r.fallback) p)) hs

end Shallot.MacroPeg.CBV.OriginHeadEvaluation
