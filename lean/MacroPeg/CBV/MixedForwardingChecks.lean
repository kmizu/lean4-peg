import MacroPeg.CBV.MixedForwardingCorrespondence

namespace Shallot.MacroPeg.CBV.MixedForwardingChecks
open MixedForwardingCompiler
open ReplayControlFusion (Part Plan)
open MixedGrowthChecks (firstOrderCheck firstOrder_checked planCheck plan_checked)

def check (parts : List Part) (es : List Entry) : Bool :=
  parts.all (fun r => firstOrderCheck r.body && (r.replay || ZeroResetOrigin.closedCheck r.body)) &&
  es.all (fun e => match e with
    | .growth r => ((decide (1≤r.factor) && firstOrderCheck r.tail) && firstOrderCheck r.fallback) &&
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
    SObs (original parts es) .callByValuePar e x rest ↔
      SObs (target parts es) .callByValueSeq (render parts es e) x rest :=
  MixedForwardingCorrespondence.observations_iff parts es (checked parts es hc) e he x rest


end Shallot.MacroPeg.CBV.MixedForwardingChecks
