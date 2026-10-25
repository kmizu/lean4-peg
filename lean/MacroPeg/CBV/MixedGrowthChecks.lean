import MacroPeg.CBV.MixedGrowthCorrespondence
import MacroPeg.CBV.ZeroResetOrigin

namespace Shallot.MacroPeg.CBV.MixedGrowthChecks
open MixedGrowthCompiler
open ReplayControlFusion (Part Plan)

mutual
  def firstOrderCheck : MExp → Bool
    | .call _ args => argsCheck args
    | .seq a b | .alt a b => firstOrderCheck a && firstOrderCheck b
    | .notP a | .star a => firstOrderCheck a
    | .eps | .any | .chr _ | .range _ _ | .lit _ | .param _ => true
    | _ => false
  def argsCheck : List MExp → Bool
    | [] => true
    | a::args => firstOrderCheck a && argsCheck args
end
mutual
  theorem firstOrder_checked : ∀ e, firstOrderCheck e=true → e.FirstOrder
    | .call _ args,h => args_checked args h
    | .seq a b,h | .alt a b,h => ⟨firstOrder_checked a (Bool.and_eq_true_iff.mp h).1,firstOrder_checked b (Bool.and_eq_true_iff.mp h).2⟩
    | .notP a,h | .star a,h => firstOrder_checked a h
    | .eps,_ | .any,_ | .chr _,_ | .range _ _,_ | .lit _,_ | .param _,_ => trivial
    | .dbg _,h | .lam _ _,h | .callParam _ _,h | .invoke _ _ _,h => by cases h
  theorem args_checked : ∀ args, argsCheck args=true → MExp.FirstOrderArgs args
    | [],_ => True.intro
    | a::args,h => ⟨firstOrder_checked a (Bool.and_eq_true_iff.mp h).1,args_checked args (Bool.and_eq_true_iff.mp h).2⟩
end

def planCheck (parts : List Part) : Plan → Bool
  | .leaf i => decide (i<parts.length)
  | .alt a b | .guard a b => planCheck parts a && planCheck parts b
  | .notP a => planCheck parts a

theorem plan_checked (parts : List Part) : ∀ P, planCheck parts P=true → ReplayControlFusion.ValidPlan parts P
  | .leaf i,h => by
    have hi : i<parts.length := of_decide_eq_true h
    exact ⟨parts[i],List.getElem?_eq_getElem hi⟩
  | .alt a b,h | .guard a b,h => ⟨plan_checked parts a (Bool.and_eq_true_iff.mp h).1,plan_checked parts b (Bool.and_eq_true_iff.mp h).2⟩
  | .notP a,h => plan_checked parts a h

def check (parts : List Part) (es : List Entry) : Bool :=
  parts.all (fun r => firstOrderCheck r.body && (r.replay || ZeroResetOrigin.closedCheck r.body)) &&
  es.all (fun e => match e with
    | .growth r => ((decide (2≤r.factor) && firstOrderCheck r.tail) && firstOrderCheck r.fallback) &&
        (match es[r.callee]? with | none | some (.growth _) => true | _ => false)
    | .origin P => planCheck parts P)

theorem checked (parts : List Part) (es : List Entry) (hc : check parts es=true) : Valid parts es := by
  obtain ⟨hp,he⟩ := Bool.and_eq_true_iff.mp hc
  constructor
  · intro r hr
    obtain ⟨hf,hc⟩ := Bool.and_eq_true_iff.mp ((List.all_eq_true.mp hp) r hr)
    refine ⟨firstOrder_checked r.body hf,?_⟩
    intro hb
    simp only [hb,Bool.false_or] at hc
    exact ZeroResetOrigin.closed_checked _ hc
  · intro e hh
    have h := (List.all_eq_true.mp he) e hh
    cases e with
    | origin P => exact plan_checked parts P h
    | growth r =>
      obtain ⟨h,hcl⟩ := Bool.and_eq_true_iff.mp h
      obtain ⟨h,hfall⟩ := Bool.and_eq_true_iff.mp h
      obtain ⟨hfactor,htail⟩ := Bool.and_eq_true_iff.mp h
      refine ⟨of_decide_eq_true hfactor,firstOrder_checked _ htail,firstOrder_checked _ hfall,?_⟩
      intro child hchild
      cases child with
      | growth r => exact ⟨r,rfl⟩
      | origin P => simp only [hchild] at hcl; cases hcl

theorem observations_iff (parts : List Part) (es : List Entry) (hc : check parts es=true)
    (e : MExp) (he : e.FirstOrder) (x : List Char) (rest : Option (List Char)) :
    SObs (source parts es) .callByValuePar e x rest ↔
      SObs (target parts es) .callByValueSeq (render parts es e) x rest :=
  MixedGrowthCorrespondence.observations_iff parts es (checked parts es hc) e he x rest

end Shallot.MacroPeg.CBV.MixedGrowthChecks
