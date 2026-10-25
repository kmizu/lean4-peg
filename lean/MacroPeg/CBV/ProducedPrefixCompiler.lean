import MacroPeg.CBV.MixedForwardingChecks
import MacroPeg.CBV.ParserPrefixFusion

namespace Shallot.MacroPeg.CBV.ProducedPrefixCompiler
open MultiplyingPrefixCompiler (Spec)
open ReplayControlFusion (Part Plan)
open ParserPrefixFusion (Pure)

inductive Entry where
  | growth : Spec → Entry
  | origin : Plan → Entry
  | produced : MExp → MExp → Entry

def body (parts : List Part) : Entry → MExp
  | .growth r => MultiplyingPrefixCompiler.sourceBody r
  | .origin P => P.exp (ReplayControlFusion.sourceLeaf parts)
  | .produced D B => .seq D B

def source (parts : List Part) (es : List Entry) : MGrammar := ⟨es.map (fun e => ⟨1,body parts e⟩)⟩
def parts (ps : List Part) (es : List Entry) := ps++es.map (fun e => match e with
  | .produced _ B => ({ replay := true,body := B } : Part)
  | _ => ⟨false,MExp.failAlways⟩)
def entries (ps : List Part) (es : List Entry) : List MixedGrowthCompiler.Entry := es.mapIdx (fun i e => match e with
  | .growth r => .growth r
  | .origin P => .origin P
  | .produced _ _ => .origin (.leaf (ps.length+i)))
def normalized (ps : List Part) (es : List Entry) := MixedGrowthCompiler.source (parts ps es) (entries ps es)
def target (ps : List Part) (es : List Entry) := MixedForwardingCompiler.target (parts ps es) (entries ps es)
abbrev render (ps : List Part) (es : List Entry) := MixedForwardingCompiler.render (parts ps es) (entries ps es)

def pureCheck : MExp → Bool
  | .seq a b | .alt a b => pureCheck a && pureCheck b
  | .star a | .notP a => pureCheck a
  | .eps | .any | .chr _ | .range _ _ | .lit _ => true
  | _ => false

theorem pure_checked : ∀ e, pureCheck e=true → Pure e
  | .seq a b,h | .alt a b,h => ⟨pure_checked a (Bool.and_eq_true_iff.mp h).1,pure_checked b (Bool.and_eq_true_iff.mp h).2⟩
  | .star a,h | .notP a,h => pure_checked a h
  | .eps,_ | .any,_ | .chr _,_ | .range _ _,_ | .lit _,_ => trivial
  | .param _,h | .call _ _,h | .dbg _,h | .lam _ _,h | .callParam _ _,h | .invoke _ _ _,h => by cases h

def callCheck (es : List Entry) (i : Nat) (A : MExp) := match es[i]? with
  | some (.produced D _) => MExp.beqE A D
  | _ => true
def conforms (es : List Entry) : MExp → Bool
  | .call i [a] => conforms es a && callCheck es i a
  | .call _ _ => true
  | .seq a b | .alt a b => conforms es a && conforms es b
  | .star a | .notP a => conforms es a
  | _ => true

def entryCheck (ps : List Part) : Entry → Bool
  | .produced D _ => pureCheck D
  | .origin P => MixedGrowthChecks.planCheck ps P
  | .growth _ => true

def check (ps : List Part) (es : List Entry) : Bool :=
  (es.all (entryCheck ps) && es.all (fun e => conforms es (body ps e))) &&
    MixedForwardingChecks.check (parts ps es) (entries ps es)

theorem checked (ps : List Part) (es : List Entry) (hc : check ps es=true) :
    MixedForwardingCompiler.Valid (parts ps es) (entries ps es) ∧
    (∀ e∈es, match e with | .produced D _ => Pure D | .origin P => ReplayControlFusion.ValidPlan ps P | .growth _ => True) ∧
    (∀ e∈es, conforms es (body ps e)=true) := by
  obtain ⟨h,hb⟩ := Bool.and_eq_true_iff.mp hc
  obtain ⟨he,hc⟩ := Bool.and_eq_true_iff.mp h
  refine ⟨MixedForwardingChecks.checked _ _ hb,?_,List.all_eq_true.mp hc⟩
  intro e hi
  have h := (List.all_eq_true.mp he) e hi
  cases e with
  | growth r => trivial
  | origin P => exact MixedGrowthChecks.plan_checked ps P h
  | produced D B => exact pure_checked D h

theorem source_rule (ps : List Part) (es : List Entry) (i : Nat) :
    ruleAtM (source ps es).rules i=(es[i]?).map (fun e => ⟨1,body ps e⟩) := by simp [source,ruleAtM_eq_getElem?]

theorem old_lookup (ps : List Part) (es : List Entry) (i : Nat) (p : Part) (hi : ps[i]?=some p) :
    (parts ps es)[i]?=some p := by
  have hib := (List.getElem?_eq_some_iff.mp hi).1
  simpa only [parts,List.getElem?_append_left hib] using hi

theorem produced_lookup (ps : List Part) (es : List Entry) (i : Nat) (D B : MExp) (hi : es[i]?=some (.produced D B)) :
    (parts ps es)[ps.length+i]?=some ⟨true,B⟩ := by
  rw [parts,List.getElem?_append_right (by omega)]
  simp [hi]

theorem old_plan_eq (ps : List Part) (es : List Entry) : ∀ P, ReplayControlFusion.ValidPlan ps P →
    P.exp (ReplayControlFusion.sourceLeaf (parts ps es))=P.exp (ReplayControlFusion.sourceLeaf ps)
  | .leaf i,h => by
    obtain ⟨p,hp⟩ := h
    simp only [Plan.exp,ReplayControlFusion.sourceLeaf,hp,old_lookup ps es i p hp]
  | .alt a b,h | .guard a b,h => by simp only [Plan.exp,old_plan_eq ps es a h.1,old_plan_eq ps es b h.2]
  | .notP a,h => by simp only [Plan.exp,old_plan_eq ps es a h]

def normalizedBody (ps : List Part) : Entry → MExp
  | .produced _ B => .seq (.param 0) B
  | e => body ps e

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
      rw [old_plan_eq ps es P ((checked ps es hc).2.1 (.origin P) (List.mem_of_getElem? hi))]
    | produced D B =>
      simp only [Option.map_some,MixedGrowthCompiler.body,normalizedBody,Plan.exp,
        ReplayControlFusion.sourceLeaf,produced_lookup ps es i D B hi,if_true]

theorem rule_count (ps : List Part) (es : List Entry) : (target ps es).rules.length=es.length*(es.length+2)+ps.length := by
  simp only [target,MixedForwardingCompiler.rule_count,entries,List.length_mapIdx,parts,List.length_append,List.length_map]
  simp only [Nat.mul_add,Nat.mul_one]
  omega

end Shallot.MacroPeg.CBV.ProducedPrefixCompiler
