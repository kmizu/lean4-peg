import MacroPeg.CBV.StablePar

namespace Shallot.MacroPeg.CBV.RecursiveProducedCompiler
open ReplayControlFusion (Part Plan)
export ProducedPrefixCompiler (Entry body source parts entries normalized target render normalizedBody conforms callCheck
  source_rule old_lookup produced_lookup old_plan_eq rule_count)

def entryCheck (ps : List Part) : Entry → Bool
  | .produced D _ => ZeroResetOrigin.closedCheck D
  | .origin P => MixedGrowthChecks.planCheck ps P
  | .growth _ => true

/-- Producers may contain real recursive user calls. Their actual arguments
must still be the very same closed parser used in the consuming prefix. -/
def check (ps : List Part) (es : List Entry) : Bool :=
  es.all (fun e => (entryCheck ps e && conforms es (body ps e)) && MixedGrowthChecks.firstOrderCheck (body ps e)) &&
    MixedForwardingChecks.check (parts ps es) (entries ps es)

theorem valid (ps : List Part) (es : List Entry) (hc : check ps es=true) :
    MixedForwardingCompiler.Valid (parts ps es) (entries ps es) :=
  MixedForwardingChecks.checked _ _ (Bool.and_eq_true_iff.mp hc).2

theorem entry_checked (ps : List Part) (es : List Entry) (hc : check ps es=true) (e : Entry) (he : e∈es) :
    match e with
    | .produced D _ => ReplayFallbackFusion.Closed D
    | .origin P => ReplayControlFusion.ValidPlan ps P
    | .growth _ => True := by
  have h := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
    (List.all_eq_true.mp (Bool.and_eq_true_iff.mp hc).1 e he)).1).1
  cases e with
  | produced D B => exact ZeroResetOrigin.closed_checked D h
  | origin P => exact MixedGrowthChecks.plan_checked ps P h
  | growth r => trivial

theorem conforms_body (ps : List Part) (es : List Entry) (hc : check ps es=true) (e : Entry) (he : e∈es) :
    conforms es (body ps e)=true :=
  (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
    (List.all_eq_true.mp (Bool.and_eq_true_iff.mp hc).1 e he)).1).2

theorem source_firstOrder (ps : List Part) (es : List Entry) (hc : check ps es=true) : (source ps es).FirstOrder := by
  intro r hr
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hr
  exact MixedGrowthChecks.firstOrder_checked _
    (Bool.and_eq_true_iff.mp (List.all_eq_true.mp (Bool.and_eq_true_iff.mp hc).1 e he)).2

theorem normalized_rule (ps : List Part) (es : List Entry) (hc : check ps es=true) (i : Nat) :
    ruleAtM (normalized ps es).rules i=(es[i]?).map (fun e => ⟨1,normalizedBody ps e⟩) := by
  rw [normalized,MixedGrowthCompiler.source_rule]
  simp only [entries,List.getElem?_mapIdx]
  cases hi : es[i]? with
  | none => rfl
  | some e =>
    cases e with
    | growth r => rfl
    | origin P =>
      simp only [Option.map_some,MixedGrowthCompiler.body,normalizedBody,body]
      rw [old_plan_eq ps es P (entry_checked ps es hc (.origin P) (List.mem_of_getElem? hi))]
    | produced D B =>
      simp only [Option.map_some,MixedGrowthCompiler.body,normalizedBody,Plan.exp,
        ReplayControlFusion.sourceLeaf,produced_lookup ps es i D B hi,if_true]

theorem normalized_firstOrder (ps : List Part) (es : List Entry) (hc : check ps es=true) : (normalized ps es).FirstOrder :=
  MixedForwardingCompiler.original_firstOrder _ _ (valid ps es hc)

end Shallot.MacroPeg.CBV.RecursiveProducedCompiler
