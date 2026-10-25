import MacroPeg.CBV.ForwardingCycleElimination
import MacroPeg.CBV.WordExpansionRefinement

namespace Shallot.MacroPeg.CBV.ForwardingHeadExpansion
open MultiplyingPrefixCompiler
open ExpressionContext (Context plug)

def frame (r : Spec) : Context := .alt (.seq .hole (.atom r.tail)) (.atom (.seq (.param 0) r.fallback))

/-- Calls are expanded only along the unique forwarding head path. Each
callee is rebound to its own singleton environment. The original PEG choice
parentheses are retained rather than distributing choice through sequence. -/
def code (rs : List Spec) : Nat → Nat → List Nat → MExp
  | 0,i,_ => match rs[i]? with | none => MExp.failAlways | some r => sourceBody r
  | fuel+1,i,seen =>
    if i∈seen then ForwardingPrefixCycles.deadBody else
    match rs[i]? with
    | none => MExp.failAlways
    | some r =>
      if r.factor=1 then
        match rs[r.callee]? with
        | none => sourceBody r
        | some _ => plug (WordCallUnfolding.expanded (.param 0) (code rs fuel r.callee (i::seen))) (frame r)
      else sourceBody r

def complete (rs : List Spec) : Nat → Nat → List Nat → Bool
  | 0,_,_ => false
  | fuel+1,i,seen =>
    if i∈seen then true else
    match rs[i]? with
    | none => true
    | some r => if r.factor=1 then
        match rs[r.callee]? with
        | none => true
        | some _ => complete rs fuel r.callee (i::seen)
      else true

def expanded (rs : List Spec) (i : Nat) := code rs (rs.length+1) i []

theorem complete_of_trace (rs : List Spec) (fuel i : Nat) (seen : List Nat)
    (h : ForwardingPrefixTrace.trace rs fuel i seen≠.exhausted) : complete rs fuel i seen=true := by
  induction fuel generalizing i seen with
  | zero => exact False.elim (h rfl)
  | succ fuel ih =>
    by_cases hi : i∈seen
    · simp [complete,hi]
    · cases hr : rs[i]? with
      | none => simp [complete,hi,hr]
      | some r =>
        by_cases hf : r.factor=1
        · cases hc : rs[r.callee]? with
          | none => simp [complete,hi,hr,hf,hc]
          | some child =>
            simp only [complete,if_neg hi,hr,if_pos hf,hc]
            apply ih r.callee (i::seen)
            simpa only [ForwardingPrefixTrace.trace,if_neg hi,hr,if_pos hf] using h
        · simp [complete,hi,hr,hf]

theorem expanded_complete (rs : List Spec) (i : Nat) : complete rs (rs.length+1) i []=true :=
  complete_of_trace rs (rs.length+1) i [] (ForwardingPrefixTrace.classify_total rs i)

theorem source_body_firstOrder (rs : List Spec) (hg : (source rs).FirstOrder) (i : Nat) (r : Spec)
    (hr : rs[i]?=some r) : (sourceBody r).FirstOrder :=
  hg ⟨1,sourceBody r⟩ (List.mem_map.mpr ⟨r,List.mem_of_getElem? hr,rfl⟩)

theorem code_firstOrder (rs : List Spec) (hg : (source rs).FirstOrder) (fuel i : Nat) (seen : List Nat) :
    (code rs fuel i seen).FirstOrder := by
  induction fuel generalizing i seen with
  | zero => cases hr : rs[i]? <;> simp only [code,hr]
            · trivial
            · exact source_body_firstOrder rs hg i _ hr
  | succ fuel ih =>
    by_cases hi : i∈seen
    · simp only [code,if_pos hi]; trivial
    · cases hr : rs[i]? with
      | none => simp only [code,if_neg hi,hr]; trivial
      | some r =>
        have hs := source_body_firstOrder rs hg i r hr
        by_cases hf : r.factor=1
        · cases hc : rs[r.callee]? with
          | none => simpa only [code,if_neg hi,hr,if_pos hf,hc] using hs
          | some child =>
            simp only [code,if_neg hi,hr,if_pos hf,hc,frame,plug]
            exact ⟨⟨⟨by trivial,firstOrder_subst (args := [.param 0]) (by trivial) _ (ih r.callee (i::seen))⟩,
              hs.1.2⟩,hs.2⟩
        · simpa only [code,if_neg hi,hr,if_neg hf] using hs

theorem canonical_body (rs : List Spec) (x : List Char) (k : Nat) (i : Nat) (r child : Spec)
    (_hr : rs[i]?=some r) (hf : r.factor=1) (hc : rs[r.callee]?=some child)
    (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV (source rs) x .callByValuePar (sourceTable rs x k) E (sourceBody r) p=
      evV (source rs) x .callByValuePar (sourceTable rs x k) E (plug (.call r.callee [.param 0]) (frame r)) p := by
  have hs : ruleAtM (source rs).rules r.callee=some ⟨1,sourceBody child⟩ := by rw [source_rule,hc]; rfl
  change evV (source rs) x .callByValuePar (sourceTable rs x k) E
    (plug (.call r.callee [RepeatedWordArguments.expression (.param 0) r.factor]) (frame r)) p=_
  apply WordExpansionRefinement.context_eq _ _ _ _ _ (tblV_ok _ _ _ k) _ _ _ (frame r) p hp
  intro q hq
  rw [hf,evV_call_par hs rfl (by decide),evV_call_par hs rfl (by decide)]
  simp only [evParArgs,ForwardingPrefixCycles.expression_one]

end Shallot.MacroPeg.CBV.ForwardingHeadExpansion
