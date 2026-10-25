import MacroPeg.CBV.OriginTailParts

namespace Shallot.MacroPeg.CBV.OriginTailEvaluation
open OriginHeadPlan (follow)
open OriginTailPlan
open OriginTailParts
open ReplayControlFusion (Part Plan sourceLeaf)
open MultiplyingPrefixCompiler (Spec)
export OriginHeadEvaluation (unfolded unfolded_context)

theorem base_expression (parts : List Part) (r : Spec) (i : Nat) (a : Part) (hi : parts[i]?=some a)
    (ha : ReplayControlFusion.ValidPart a) (hm : 1≤r.factor) (g : MGrammar) (x : List Char) (s : Strategy)
    (T : ClockFreezing.Table) (E : List (List Char)) (p : Nat) :
    evV g x s T E (sourceLeaf (extended parts r) (parts.length+i)) p=
      evV g x s T E (MExp.subst [power r.factor] (sourceLeaf parts i)) p := by
  have hb : sourceLeaf (extended parts r) (parts.length+i)=sourceLeaf [rebased r.factor a] 0 := by
    simp only [sourceLeaf,base_lookup parts r i a hi,List.getElem?_cons_zero]
  have hs : sourceLeaf parts i=sourceLeaf [a] 0 := by simp only [sourceLeaf,hi,List.getElem?_cons_zero]
  rw [hb,hs]
  exact OriginHeadParts.rebased_eval g x s T E r.factor hm a ha p

theorem tail_slot (parts : List Part) (r : Spec) (ht : tailSupported r.tail=true) :
    sourceLeaf (extended parts r) (3*parts.length)=r.tail := by
  have he : sourceLeaf (extended parts r) (3*parts.length)=sourceLeaf [tailPart r.tail] 0 := by
    simp only [sourceLeaf,tail_lookup,List.getElem?_cons_zero]
  exact he.trans (tail_expression r.tail ht)

theorem done_expression (parts : List Part) (r : Spec) (i : Nat) (a : Part) (hi : parts[i]?=some a)
    (ha : ReplayControlFusion.ValidPart a) (hm : 1≤r.factor) (hc : doneCheck r.tail a=true)
    (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV g x s T E ((donePlan parts r i).exp (sourceLeaf (extended parts r))) p=
      follow (evV g x s T E (MExp.subst [power r.factor] (sourceLeaf parts i)) p) (fun q => evV g x s T E r.tail q) := by
  have hs : sourceLeaf parts i=sourceLeaf [a] 0 := by simp only [sourceLeaf,hi,List.getElem?_cons_zero]
  by_cases hb : (a.replay || ZeroResetOrigin.closedCheck r.tail)=true
  · simp only [donePlan,partAt,hi,Option.getD_some,hb,if_true,Plan.exp]
    have hd : sourceLeaf (extended parts r) (2*parts.length+i)=sourceLeaf [attached r.tail (rebased r.factor a)] 0 := by
      simp only [sourceLeaf,done_lookup parts r i a hi,donePart,hb,if_true,List.getElem?_cons_zero]
    rw [hd,OriginHeadParts.attached_eval,hs,OriginHeadParts.rebased_eval g x s T E r.factor hm a ha p]
  · have hf : (a.replay || ZeroResetOrigin.closedCheck r.tail)=false := Bool.eq_false_iff.mpr hb
    obtain ⟨hr,hB⟩ := Bool.or_eq_false_iff.mp hf
    have hchecks : EmptyArgumentSpecialization.zeroCheck a.body=true ∧ tailSupported r.tail=true := by
      simpa only [doneCheck,hr,hB,Bool.false_or,Bool.and_eq_true_iff] using hc
    simp only [donePlan,partAt,hi,Option.getD_some,hf,Bool.false_eq_true,if_false,Plan.exp]
    have hq : evV g x s T E (.andP (sourceLeaf (extended parts r) (parts.length+i))) p=
        CallLookahead.peek p (evV g x s T E (MExp.subst [power r.factor] (sourceLeaf parts i)) p) := by
      rw [CallLookahead.evV_peek,base_expression parts r i a hi ha hm g x s T E p]
    have htail := tail_slot parts r hchecks.2
    have hsource : MExp.subst [power r.factor] (sourceLeaf parts i)=a.body := by
      simp only [sourceLeaf,hi,hr,Bool.false_eq_true,if_false,ReplayFallbackFusion.subst_closed _ _ (ha.2 hr)]
    change follow (evV g x s T E (.andP (sourceLeaf (extended parts r) (parts.length+i))) p)
      (fun q => evV g x s T E (sourceLeaf (extended parts r) (3*parts.length)) q)=_
    rw [hq]
    simp only [htail]
    cases hv : evV g x s T E (MExp.subst [power r.factor] (sourceLeaf parts i)) p with
    | none => rfl
    | some v => cases v with
      | none => rfl
      | some q =>
        have hpos := EmptyArgumentSpecialization.zero_success g x s T E a.body hchecks.1 p q hp (by simpa only [hsource] using hv)
        subst q
        rfl

theorem after_expression (parts : List Part) (r : Spec) (P : Plan)
    (hparts : ∀ a∈parts, ReplayControlFusion.ValidPart a) (hv : ReplayControlFusion.ValidPlan parts P)
    (hm : 1≤r.factor) (hc : flowCheck parts r.tail P=true)
    (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV g x s T E ((append parts.length (3*parts.length) (donePlan parts r) P).exp (sourceLeaf (extended parts r))) p=
      evV g x s T E (.seq (MExp.subst [power r.factor] (P.exp (sourceLeaf parts))) r.tail) p := by
  rw [Plan.exp_eval]
  have hb : Plan.All (fun i => evV g x s T E (sourceLeaf (extended parts r) (parts.length+i)) p=
      evV g x s T E (MExp.subst [power r.factor] (sourceLeaf parts i)) p) P := by
    apply Plan.all_imp (t := P) _ hv
    intro i hi
    obtain ⟨a,ha⟩ := hi
    exact base_expression parts r i a ha (hparts a (List.mem_of_getElem? ha)) hm g x s T E p
  have hx : Exits (fun i => (donePlan parts r i).eval
      (fun j => evV g x s T E (sourceLeaf (extended parts r) j) p) p=
      follow (evV g x s T E (MExp.subst [power r.factor] (sourceLeaf parts i)) p) (fun q => evV g x s T E r.tail q))
      (evV g x s T E (sourceLeaf (extended parts r) (3*parts.length)) p=evV g x s T E r.tail p) P := by
    apply exits_imp (P := P) _ _ (flow_checked parts r.tail P hc)
    · intro i hi
      obtain ⟨a,ha,hc⟩ := hi
      simpa only [Plan.exp_eval] using done_expression parts r i a ha (hparts a (List.mem_of_getElem? ha)) hm hc g x s T E p hp
    · intro ht; rw [tail_slot parts r ht]
  rw [append_eval parts.length (3*parts.length) (donePlan parts r)
    (fun i => evV g x s T E (sourceLeaf (extended parts r) i) p)
    (fun i => evV g x s T E (MExp.subst [power r.factor] (sourceLeaf parts i)) p)
    (fun q => evV g x s T E r.tail q) p P hb hx,OriginHeadParts.subst_plan]
  change follow (P.eval (fun i => evV g x s T E (MExp.subst [power r.factor] (sourceLeaf parts i)) p) p)
    (fun q => evV g x s T E r.tail q)=
    follow (evV g x s T E (P.exp (fun i => MExp.subst [power r.factor] (sourceLeaf parts i))) p) (fun q => evV g x s T E r.tail q)
  rw [Plan.exp_eval]

theorem plan_expression (parts : List Part) (r : Spec) (P : Plan)
    (hparts : ∀ a∈parts, ReplayControlFusion.ValidPart a) (hv : ReplayControlFusion.ValidPlan parts P)
    (hm : 1≤r.factor) (hc : flowCheck parts r.tail P=true)
    (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV g x s T E ((plan parts r P).exp (sourceLeaf (extended parts r))) p=evV g x s T E (unfolded parts r P) p := by
  have hg : evV g x s T E (.andP (sourceLeaf (extended parts r) (3*parts.length+1))) p=
      evV g x s T E (.andP (power r.factor)) p := by
    have he : sourceLeaf (extended parts r) (3*parts.length+1)=sourceLeaf [⟨true,.andP (power (r.factor-1))⟩] 0 := by
      simp only [sourceLeaf,gate_lookup,List.getElem?_cons_zero]
    rw [he]; exact OriginHeadParts.gate_eval g x s T E r.factor hm p
  have hf : sourceLeaf (extended parts r) (3*parts.length+2)=.seq (.param 0) r.fallback := by
    simp only [sourceLeaf,fallback_lookup,if_true]
  have ha := after_expression parts r P hparts hv hm hc g x s T E p hp
  change ReplayFallbackFusion.orElse
    (follow (evV g x s T E (.andP (sourceLeaf (extended parts r) (3*parts.length+1))) p)
      (fun q => evV g x s T E ((append parts.length (3*parts.length) (donePlan parts r) P).exp (sourceLeaf (extended parts r))) q))
    (evV g x s T E (sourceLeaf (extended parts r) (3*parts.length+2)) p)=
    ReplayFallbackFusion.orElse (follow (evV g x s T E (.andP (power r.factor)) p)
      (fun q => evV g x s T E (.seq (MExp.subst [power r.factor] (P.exp (sourceLeaf parts))) r.tail) q))
      (evV g x s T E (.seq (.param 0) r.fallback) p)
  rw [hg,hf,CallLookahead.evV_peek]
  cases evV g x s T E (power r.factor) p with
  | none => rfl
  | some v => cases v with
    | none => rfl
    | some q =>
      change ReplayFallbackFusion.orElse
        (evV g x s T E ((append parts.length (3*parts.length) (donePlan parts r) P).exp (sourceLeaf (extended parts r))) p)
        (evV g x s T E (.seq (.param 0) r.fallback) p)=_
      rw [ha]
      rfl

end Shallot.MacroPeg.CBV.OriginTailEvaluation
