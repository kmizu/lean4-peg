import MacroPeg.CBV.ForwardingHeadExpansion
import MacroPeg.Properties.MExpEq

namespace Shallot.MacroPeg.CBV.SelectedForwardingContext
open MultiplyingPrefixCompiler (Spec sourceBody)

/-- Metadata describes selected heads only. Other actual rule bodies may
contain origin control or arbitrary first-order code. -/
structure Valid (g : MGrammar) (rs : List Spec) (ids : List Nat) : Prop where
  length : g.rules.length=rs.length
  rule : ∀ i∈ids, ∀ r, rs[i]?=some r → ruleAtM g.rules i=some ⟨1,sourceBody r⟩
  edge : ∀ i∈ids, ∀ r, rs[i]?=some r → r.factor=1 → ∀ child, rs[r.callee]?=some child → r.callee∈ids

def check (g : MGrammar) (rs : List Spec) (ids : List Nat) : Bool :=
  decide (g.rules.length=rs.length) && ids.all (fun i => match rs[i]? with
    | none => true
    | some r => match ruleAtM g.rules i with
      | none => false
      | some a => (decide (a.arity=1) && MExp.beqE a.body (sourceBody r)) &&
        (if r.factor=1 then if r.callee<rs.length then ids.contains r.callee else true else true))

theorem checked_entry (g : MGrammar) (rs : List Spec) (ids : List Nat) (h : check g rs ids=true)
    (i : Nat) (hi : i∈ids) (r : Spec) (hr : rs[i]?=some r) :
    ruleAtM g.rules i=some ⟨1,sourceBody r⟩ ∧ (r.factor=1 → r.callee<rs.length → r.callee∈ids) := by
  have hh := (List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).2) i hi
  simp only [hr] at hh
  cases ha : ruleAtM g.rules i with
  | none => simp [ha] at hh
  | some a =>
    simp only [ha,Bool.and_eq_true_iff] at hh
    have harity : a.arity=1 := of_decide_eq_true hh.1.1
    have hbody : a.body=sourceBody r := (MExp.beqE_iff _ _).mp hh.1.2
    have hab : a=⟨1,sourceBody r⟩ := by cases a; cases harity; cases hbody; rfl
    refine ⟨congrArg some hab,?_⟩
    intro hf hn
    simpa only [if_pos hf,if_pos hn,List.contains_iff_mem] using hh.2

theorem checked (g : MGrammar) (rs : List Spec) (ids : List Nat) (h : check g rs ids=true) : Valid g rs ids := by
  refine ⟨of_decide_eq_true (Bool.and_eq_true_iff.mp h).1,?_,?_⟩
  · intro i hi r hr
    exact (checked_entry g rs ids h i hi r hr).1
  · intro i hi r hr hf child hc
    exact (checked_entry g rs ids h i hi r hr).2 hf (List.getElem?_eq_some_iff.mp hc).1

theorem metadata_exists (g : MGrammar) (rs : List Spec) (ids : List Nat) (hv : Valid g rs ids)
    (i : Nat) (r : MRule) (hr : ruleAtM g.rules i=some r) : ∃ s, rs[i]?=some s := by
  have hi : i<g.rules.length := by
    rw [ruleAtM_eq_getElem?] at hr
    exact (List.getElem?_eq_some_iff.mp hr).1
  rw [hv.length] at hi
  exact ⟨rs[i],List.getElem?_eq_getElem hi⟩

theorem body_firstOrder (g : MGrammar) (hg : g.FirstOrder) (rs : List Spec) (ids : List Nat)
    (hv : Valid g rs ids) (i : Nat) (hi : i∈ids) (r : Spec) (hr : rs[i]?=some r) : (sourceBody r).FirstOrder :=
  hg ⟨1,sourceBody r⟩ (ruleAtM_mem (hv.rule i hi r hr))

theorem code_firstOrder (g : MGrammar) (hg : g.FirstOrder) (rs : List Spec) (ids : List Nat)
    (hv : Valid g rs ids) (fuel i : Nat) (seen : List Nat) (hi : i∈ids) (r : Spec) (hr : rs[i]?=some r) :
    (ForwardingHeadExpansion.code rs fuel i seen).FirstOrder := by
  induction fuel generalizing i seen r with
  | zero => simpa only [ForwardingHeadExpansion.code,hr] using body_firstOrder g hg rs ids hv i hi r hr
  | succ fuel ih =>
    have hs := body_firstOrder g hg rs ids hv i hi r hr
    by_cases hseen : i∈seen
    · simp only [ForwardingHeadExpansion.code,if_pos hseen]; trivial
    · by_cases hf : r.factor=1
      · cases hc : rs[r.callee]? with
        | none => simpa only [ForwardingHeadExpansion.code,if_neg hseen,hr,if_pos hf,hc] using hs
        | some child =>
          simp only [ForwardingHeadExpansion.code,if_neg hseen,hr,if_pos hf,hc,
            ForwardingHeadExpansion.frame,ExpressionContext.plug]
          exact ⟨⟨⟨by trivial,firstOrder_subst (args := [.param 0]) (by trivial) _
            (ih r.callee (i::seen) (hv.edge i hi r hr hf child hc) child hc)⟩,hs.1.2⟩,hs.2⟩
      · simpa only [ForwardingHeadExpansion.code,if_neg hseen,hr,if_neg hf] using hs

end Shallot.MacroPeg.CBV.SelectedForwardingContext
