import MacroPeg.CBV.FieldPlanCompiler

/-! Move an arbitrary consuming suffix into already bound field entries.
Continuation copies are generated only for positive control paths. Query
leaves stay unchanged, so later failure cannot uncommit an earlier choice. -/
namespace Shallot.MacroPeg.CBV.RetainedContinuationSyntax
open ReplayControlFusion (Plan)
open TypedFieldSyntax (Header)

structure Continuation where
  parameters : List CaptureAlphabetEffects.Alphabet
  result : CaptureAlphabetEffects.Alphabet
  delimiter : Char
  body : MExp

structure Spec where
  plan : Plan
  continuation : Continuation

abbrev Key := Nat × Option Nat

def selected (i : Nat) : Plan → List Key
  | .leaf j => [(i,some j)]
  | .alt a b => selected i a++selected i b
  | .guard _ b => selected i b
  | .notP _ => [(i,none)]
def keys (specs : List Spec) : List Key :=
  specs.zipIdx.flatMap (fun (s,i) => selected i s.plan)
def address (parts : List Header) (specs : List Spec) (key : Key) : Nat :=
  parts.length+(keys specs).idxOf key
def dummy : Header := ⟨[],[],'#',[],.eps⟩
def keyHeader (parts : List Header) (specs : List Spec) (key : Key) : Header :=
  match specs[key.1]? with
  | none => dummy
  | some s => match key.2 with
    | none => ⟨s.continuation.parameters,s.continuation.result,s.continuation.delimiter,[],s.continuation.body⟩
    | some j => match parts[j]? with
      | none => dummy
      | some r => {r with result:=s.continuation.result,body:=.seq r.body s.continuation.body}
def normalizedParts (parts : List Header) (specs : List Spec) : List Header :=
  parts++(keys specs).map (keyHeader parts specs)

def normalizePlan (parts : List Header) (specs : List Spec) (i : Nat) : Plan → Plan
  | .leaf j => .leaf (address parts specs (i,some j))
  | .alt a b => .alt (.guard a (normalizePlan parts specs i a))
      (.guard (.notP a) (normalizePlan parts specs i b))
  | .guard a b => .guard a (normalizePlan parts specs i b)
  | .notP a => .guard (.notP a) (.leaf (address parts specs (i,none)))

def rawSpecs (specs : List Spec) : List FieldPlanSyntax.Spec :=
  specs.map (fun s => ⟨s.continuation.parameters.length,s.plan⟩)
def normalizedSpecs (parts : List Header) (specs : List Spec) : List FieldPlanSyntax.Spec :=
  specs.zipIdx.map (fun (s,i) => ⟨s.continuation.parameters.length,normalizePlan parts specs i s.plan⟩)
def source (parts : List Header) (specs : List Spec) : MGrammar :=
  ⟨specs.map (fun s => ⟨s.continuation.parameters.length,
    .seq (s.plan.exp (FieldPlanSyntax.sourceLeaf parts)) s.continuation.body⟩)⟩
def normalized (parts : List Header) (specs : List Spec) : MGrammar :=
  FieldPlanSyntax.source (normalizedParts parts specs) (normalizedSpecs parts specs)
def check (parts : List Header) (specs : List Spec) : Bool :=
  FieldPlanSyntax.check parts (rawSpecs specs) &&
    specs.all (fun s => MixedGrowthChecks.firstOrderCheck s.continuation.body)

theorem checked (parts : List Header) (specs : List Spec) (hc : check parts specs=true) :
    FieldPlanSyntax.Valid parts (rawSpecs specs) ∧ ∀ s∈specs, s.continuation.body.FirstOrder := by
  obtain ⟨hp,hs⟩ := Bool.and_eq_true_iff.mp hc
  exact ⟨FieldPlanSyntax.checked _ _ hp,(by intro s h; exact MixedGrowthChecks.firstOrder_checked _ (List.all_eq_true.mp hs s h))⟩

theorem selected_global (specs : List Spec) (i : Nat) (s : Spec) (hs : specs[i]?=some s)
    (key : Key) (hk : key∈selected i s.plan) : key∈keys specs := by
  have hm : (s,i)∈specs.zipIdx := List.mem_of_getElem? (show specs.zipIdx[i]?=some (s,i) from by
    simp [List.getElem?_zipIdx,hs])
  exact List.mem_flatMap.mpr ⟨(s,i),hm,hk⟩

theorem original_part (parts : List Header) (specs : List Spec) (j : Nat) (r : Header) (hr : parts[j]?=some r) :
    (normalizedParts parts specs)[j]?=some r := by
  rw [normalizedParts,List.getElem?_append_left (List.getElem?_eq_some_iff.mp hr).1]
  exact hr

theorem added_part (parts : List Header) (specs : List Spec) (key : Key) (hk : key∈keys specs) :
    (normalizedParts parts specs)[address parts specs key]?=some (keyHeader parts specs key) := by
  have hi := DependentProfileCall.index_correct key (keys specs) hk
  simp only [normalizedParts,address,List.getElem?_append_right (by omega : parts.length≤parts.length+(keys specs).idxOf key),
    Nat.add_sub_cancel_left,List.getElem?_map,hi,Option.map_some]

theorem raw_spec (specs : List Spec) (i : Nat) (s : Spec) (hs : specs[i]?=some s) :
    (rawSpecs specs)[i]?=some ⟨s.continuation.parameters.length,s.plan⟩ := by
  simp [rawSpecs,List.getElem?_map,hs]
theorem normalized_spec (parts : List Header) (specs : List Spec) (i : Nat) (s : Spec) (hs : specs[i]?=some s) :
    (normalizedSpecs parts specs)[i]?=some ⟨s.continuation.parameters.length,normalizePlan parts specs i s.plan⟩ := by
  simp [normalizedSpecs,List.getElem?_map,List.getElem?_zipIdx,hs]
theorem source_rule (parts : List Header) (specs : List Spec) (i : Nat) :
    ruleAtM (source parts specs).rules i=(specs[i]?).map (fun s => ⟨s.continuation.parameters.length,
      .seq (s.plan.exp (FieldPlanSyntax.sourceLeaf parts)) s.continuation.body⟩) := by
  simp [source,ruleAtM_eq_getElem?,List.getElem?_map]
theorem normalized_rule (parts : List Header) (specs : List Spec) (i : Nat) :
    ruleAtM (normalized parts specs).rules i=(specs[i]?).map (fun s => ⟨s.continuation.parameters.length,
      (normalizePlan parts specs i s.plan).exp (FieldPlanSyntax.sourceLeaf (normalizedParts parts specs))⟩) := by
  simp [normalized,FieldPlanSyntax.source,normalizedSpecs,ruleAtM_eq_getElem?,List.getElem?_map,List.getElem?_zipIdx]
  rfl

theorem source_firstOrder (parts : List Header) (specs : List Spec) (hc : check parts specs=true) :
    (source parts specs).FirstOrder := by
  obtain ⟨hv,hs⟩ := checked parts specs hc
  intro r hr
  obtain ⟨s,hm,rfl⟩ := List.mem_map.mp hr
  exact ⟨Plan.exp_firstOrder (FieldPlanSyntax.sourceLeaf_firstOrder parts (rawSpecs specs) hv) s.plan,hs s hm⟩

end Shallot.MacroPeg.CBV.RetainedContinuationSyntax
