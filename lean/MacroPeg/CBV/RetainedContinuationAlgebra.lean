import MacroPeg.CBV.RetainedContinuationSyntax

namespace Shallot.MacroPeg.CBV.RetainedContinuationAlgebra
open RetainedContinuationSyntax
open ReplayControlFusion (Plan)
open TypedFieldSyntax (Header)
open ClockFreezing (Table)

theorem seq_assoc (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (a b c : MExp) (p : Nat) :
    evV g x s T E (.seq (.seq a b) c) p=evV g x s T E (.seq a (.seq b c)) p := by
  cases ha : evV g x s T E a p with
  | none => simp [evV,ha]
  | some v => cases v <;> simp [evV,ha]

theorem guard_congr (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (q a b : MExp) (p : Nat)
    (h : evV g x s T E a p=evV g x s T E b p) :
    evV g x s T E (.seq (.andP q) a) p=evV g x s T E (.seq (.andP q) b) p := by
  change (match evV g x s T E (.andP q) p with
    | some (some j) => evV g x s T E a j | other => other)=
    (match evV g x s T E (.andP q) p with
    | some (some j) => evV g x s T E b j | other => other)
  simp only [CallLookahead.evV_peek]
  cases hq : evV g x s T E q p with
  | none => rfl
  | some v => cases v with
    | none => rfl
    | some j => exact h

theorem committed_suffix (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (a b c : MExp) (p : Nat) :
    evV g x s T E (.alt (.seq (.andP a) (.seq a c))
      (.seq (.andP (.notP a)) (.seq b c))) p=evV g x s T E (.seq (.alt a b) c) p := by
  cases ha : evV g x s T E a p with
  | none => simp [MExp.andP,evV,ha]
  | some v => cases v with
    | none => simp [MExp.andP,evV,ha]
    | some q =>
      cases hc : evV g x s T E c q with
      | none => simp [MExp.andP,evV,ha,hc]
      | some r => cases r <;> simp [MExp.andP,evV,ha,hc]

theorem negative_guard (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (a c : MExp) (p : Nat) :
    evV g x s T E (.seq (.andP (.notP a)) c) p=evV g x s T E (.seq (.notP a) c) p := by
  cases ha : evV g x s T E a p with
  | none => simp [MExp.andP,evV,ha]
  | some v => cases v <;> simp [MExp.andP,evV,ha]

theorem base_exp (parts : List Header) (specs : List Spec) : ∀ (P : Plan),
    P.All (fun j => ∃ r, parts[j]?=some r) →
    P.exp (FieldPlanSyntax.sourceLeaf (normalizedParts parts specs))=P.exp (FieldPlanSyntax.sourceLeaf parts)
  | .leaf j,h => by
    obtain ⟨r,hr⟩ := h
    simp only [Plan.exp,FieldPlanSyntax.sourceLeaf,original_part parts specs j r hr,hr]
  | .alt a b,h | .guard a b,h => by
    simp only [Plan.exp,base_exp parts specs a h.1,base_exp parts specs b h.2]
  | .notP a,h => by simp only [Plan.exp,base_exp parts specs a h]

/-- The suffix is evaluated at the source plan's actual result position.
Actuals are never re-evaluated there; their environment stays in the copied
leaf entry. This local equality holds under arbitrary tables/strategies. -/
theorem fusion (parts : List Header) (specs : List Spec) (i : Nat) (spec : Spec) (hs : specs[i]?=some spec)
    (g : MGrammar) (x : List Char) (s : Strategy) (T : Table) (E : List (List Char)) :
    ∀ P, P.All (fun j => ∃ r, parts[j]?=some r) →
    (∀ key∈selected i P, key∈keys specs) → ∀ p,
    evV g x s T E ((normalizePlan parts specs i P).exp (FieldPlanSyntax.sourceLeaf (normalizedParts parts specs))) p=
      evV g x s T E (.seq (P.exp (FieldPlanSyntax.sourceLeaf parts)) spec.continuation.body) p
  | .leaf j,h,hkeys,p => by
    obtain ⟨r,hr⟩ := h
    have hk := hkeys (i,some j) (by simp [selected])
    have ha := added_part parts specs (i,some j) hk
    simp only [keyHeader,hs,hr] at ha
    change evV g x s T E (FieldPlanSyntax.sourceLeaf (normalizedParts parts specs) (address parts specs (i,some j))) p=_
    simp only [FieldPlanSyntax.sourceLeaf,ha,hr,Plan.exp]
    exact (seq_assoc g x s T E _ r.body spec.continuation.body p).symm
  | .alt a b,h,hkeys,p => by
    have ha := fusion parts specs i spec hs g x s T E a h.1
      (by intro key hk; exact hkeys key (List.mem_append_left _ hk)) p
    have hb := fusion parts specs i spec hs g x s T E b h.2
      (by intro key hk; exact hkeys key (List.mem_append_right _ hk)) p
    simp only [normalizePlan,Plan.exp,base_exp parts specs a h.1]
    have hl := guard_congr g x s T E (a.exp (FieldPlanSyntax.sourceLeaf parts)) _ _ p ha
    have hr := guard_congr g x s T E (.notP (a.exp (FieldPlanSyntax.sourceLeaf parts))) _ _ p hb
    change (match evV g x s T E (.seq (.andP (a.exp (FieldPlanSyntax.sourceLeaf parts)))
        ((normalizePlan parts specs i a).exp (FieldPlanSyntax.sourceLeaf (normalizedParts parts specs)))) p with
      | some none => evV g x s T E (.seq (.andP (.notP (a.exp (FieldPlanSyntax.sourceLeaf parts))))
          ((normalizePlan parts specs i b).exp (FieldPlanSyntax.sourceLeaf (normalizedParts parts specs)))) p
      | other => other)=_
    rw [hl,hr]
    exact committed_suffix g x s T E _ _ spec.continuation.body p
  | .guard a b,h,hkeys,p => by
    have hb := fusion parts specs i spec hs g x s T E b h.2 hkeys p
    simp only [normalizePlan,Plan.exp,base_exp parts specs a h.1]
    rw [seq_assoc]
    exact guard_congr g x s T E _ _ _ p hb
  | .notP a,h,hkeys,p => by
    have hk := hkeys (i,none) (by simp [selected])
    have ha := added_part parts specs (i,none) hk
    simp only [keyHeader,hs] at ha
    simp only [normalizePlan,Plan.exp,base_exp parts specs a h,FieldPlanSyntax.sourceLeaf,ha]
    exact negative_guard g x s T E _ spec.continuation.body p

/-- Syntax-generated continuation copies supply the rulewise rewrite;
there is no semantic row oracle among the caller's premises. -/
theorem related (parts : List Header) (specs : List Spec) (hc : check parts specs=true) :
    SemanticBodyRewrite.Related (source parts specs) (normalized parts specs) .callByValuePar := by
  obtain ⟨hv,hc⟩ := checked parts specs hc
  intro i
  rw [source_rule,normalized_rule]
  cases hs : specs[i]? with
  | none => trivial
  | some spec =>
    refine ⟨rfl,?_⟩
    intro x T E p hp
    have hplan := hv.specs ⟨spec.continuation.parameters.length,spec.plan⟩
      (List.mem_map.mpr ⟨spec,List.mem_of_getElem? hs,rfl⟩)
    have hsimple : spec.plan.All (fun j => ∃ r, parts[j]?=some r) :=
      Plan.all_imp (fun j ⟨r,hr,hl⟩ => ⟨r,hr⟩) spec.plan hplan
    exact (fusion parts specs i spec hs (source parts specs) x .callByValuePar T E spec.plan hsimple
      (selected_global specs i spec hs) p).symm

theorem physical (parts : List Header) (specs : List Spec) (hc : check parts specs=true)
    (x : List Char) (k : Nat) (E : List (List Char)) (e : MExp) (p : Nat) :
    evV (source parts specs) x .callByValuePar (tblV (source parts specs) x .callByValuePar k) E e p=
      evV (normalized parts specs) x .callByValuePar (tblV (normalized parts specs) x .callByValuePar k) E e p :=
  SemanticBodyRewrite.physical (related parts specs hc) x k E e p

end Shallot.MacroPeg.CBV.RetainedContinuationAlgebra
