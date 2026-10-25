import MacroPeg.CBV.ProducerArgumentRewrite
import MacroPeg.CBV.RecursiveProducedCorrespondence

namespace Shallot.MacroPeg.CBV.CanonicalProducerCompiler
open RecursiveProducedCompiler (Entry)
open ReplayControlFusion (Part Plan)

abbrev source := RecursiveProducedCompiler.source

def core (cores : List MExp) (i : Nat) (d : MExp) := cores[i]?.getD d

/-- Canonical producers are inserted by name as their existing closed AST.
They are required to be already canonical internally, so this finite render
never recursively expands the declaration it is inserting. -/
def render (es : List Entry) : MExp → MExp
  | .call i [a] => match es[i]? with
    | some (.produced d _) => if MExp.beqE a d then .call i [render es a]
        else ProducerArgumentRewrite.guarded i d (render es a)
    | _ => .call i [render es a]
  | .seq a b => .seq (render es a) (render es b)
  | .alt a b => .alt (render es a) (render es b)
  | .notP a => .notP (render es a)
  | .star a => .star (render es a)
  | e => e

def cost (es : List Entry) : MExp → Nat
  | .call i [a] => cost es a + (match es[i]? with
    | some (.produced d _) => if MExp.beqE a d then 0 else 1
    | _ => 0)
  | .seq a b | .alt a b => cost es a+cost es b
  | .notP a | .star a => cost es a
  | _ => 0

def conforms (ps : List Part) (es : List Entry) (cores : List MExp) : MExp → Bool
  | .call i [a] => conforms ps es cores a && (match es[i]? with
    | some (.produced d _) => MExp.beqE a d || EndpointSupport.check (source ps es) a (core cores i d)
    | _ => true)
  | .seq a b | .alt a b => conforms ps es cores a && conforms ps es cores b
  | .notP a | .star a => conforms ps es cores a
  | _ => true

def ready (ps : List Part) (es : List Entry) (cores : List MExp) : Bool :=
  (List.range es.length).all (fun i => match es[i]? with
    | some (.produced d _) => ((ZeroResetOrigin.closedCheck d && RecursiveProducedCompiler.conforms es d) &&
        ZeroResetOrigin.closedCheck (core cores i d)) && EndpointSupport.check (source ps es) d (core cores i d)
    | _ => true)

def outputParts (ps : List Part) (es : List Entry) : List Part := ps.map (fun p => ⟨p.replay,render es p.body⟩)
def outputEntry (es : List Entry) : Entry → Entry
  | .growth r => .growth ⟨r.callee,r.factor,render es r.tail,render es r.fallback⟩
  | .origin p => .origin p
  | .produced d b => .produced d (render es b)
def outputEntries (es : List Entry) := es.map (outputEntry es)
def prepared (ps : List Part) (es : List Entry) := RecursiveProducedCompiler.source (outputParts ps es) (outputEntries es)
def target (ps : List Part) (es : List Entry) := RecursiveProducedCompiler.target (outputParts ps es) (outputEntries es)
def entry (ps : List Part) (es : List Entry) (e : MExp) := RecursiveProducedCompiler.render (outputParts ps es) (outputEntries es) (render es e)

def check (ps : List Part) (es : List Entry) (cores : List MExp) : Bool :=
  ((ready ps es cores && es.all (fun e => MixedGrowthChecks.firstOrderCheck (RecursiveProducedCompiler.body ps e) &&
    conforms ps es cores (RecursiveProducedCompiler.body ps e))) &&
    es.all (fun e => MExp.beqE (render es (RecursiveProducedCompiler.body ps e))
      (RecursiveProducedCompiler.body (outputParts ps es) (outputEntry es e)))) && RecursiveProducedCompiler.check (outputParts ps es) (outputEntries es)

theorem checked_producer (ps : List Part) (es : List Entry) (cores : List MExp) (hc : check ps es cores=true)
    (i : Nat) (d b : MExp) (hi : es[i]?=some (.produced d b)) :
    ReplayFallbackFusion.Closed d ∧ RecursiveProducedCompiler.conforms es d=true ∧
      ReplayFallbackFusion.Closed (core cores i d) ∧ EndpointSupport.check (source ps es) d (core cores i d)=true := by
  have hready := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hc).1).1).1
  have hrange : i∈List.range es.length := List.mem_range.mpr (List.getElem?_eq_some_iff.mp hi).1
  have h := List.all_eq_true.mp hready i hrange
  simp only [hi] at h
  obtain ⟨hab,hD⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨ha,hC⟩ := Bool.and_eq_true_iff.mp hab
  obtain ⟨hd,hcanon⟩ := Bool.and_eq_true_iff.mp ha
  exact ⟨ZeroResetOrigin.closed_checked _ hd,hcanon,ZeroResetOrigin.closed_checked _ hC,hD⟩

theorem checked_body (ps : List Part) (es : List Entry) (cores : List MExp) (hc : check ps es cores=true)
    (e : Entry) (he : e∈es) : (RecursiveProducedCompiler.body ps e).FirstOrder ∧
      conforms ps es cores (RecursiveProducedCompiler.body ps e)=true := by
  have h := List.all_eq_true.mp
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hc).1).1).2 e he
  exact ⟨MixedGrowthChecks.firstOrder_checked _ (Bool.and_eq_true_iff.mp h).1,(Bool.and_eq_true_iff.mp h).2⟩

theorem source_firstOrder (ps : List Part) (es : List Entry) (cores : List MExp) (hc : check ps es cores=true) : (source ps es).FirstOrder := by
  intro r hr
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hr
  exact (checked_body ps es cores hc e he).1

theorem prepared_checked (ps : List Part) (es : List Entry) (cores : List MExp) (hc : check ps es cores=true) :
    RecursiveProducedCompiler.check (outputParts ps es) (outputEntries es)=true := (Bool.and_eq_true_iff.mp hc).2

theorem canonical_identity (es : List Entry) : ∀ e, RecursiveProducedCompiler.conforms es e=true → render es e=e
  | .call i [a],hc => by
    have ih := canonical_identity es a (Bool.and_eq_true_iff.mp hc).1
    cases hi : es[i]? with
    | none => simp [render,hi,ih]
    | some e => cases e with
      | growth r => simp [render,hi,ih]
      | origin P => simp [render,hi,ih]
      | produced d b =>
        have heq : MExp.beqE a d=true := by simpa [RecursiveProducedCompiler.callCheck,ProducedPrefixCompiler.callCheck,hi] using (Bool.and_eq_true_iff.mp hc).2
        simp [render,hi,heq,ih]
  | .seq a b,hc | .alt a b,hc => by
    simp only [render,canonical_identity es a (Bool.and_eq_true_iff.mp hc).1,canonical_identity es b (Bool.and_eq_true_iff.mp hc).2]
  | .notP a,hc | .star a,hc => by simp only [render,canonical_identity es a hc]
  | .eps,_ | .any,_ | .chr _,_ | .range _ _,_ | .lit _,_ | .param _,_ | .dbg _,_ | .lam _ _,_
  | .invoke _ _ _,_ | .callParam _ _,_ | .call _ [],_ | .call _ (_::_::_),_ => rfl

theorem checked_shape (ps : List Part) (es : List Entry) (cores : List MExp) (hc : check ps es cores=true)
    (e : Entry) (he : e∈es) : render es (RecursiveProducedCompiler.body ps e)=
      RecursiveProducedCompiler.body (outputParts ps es) (outputEntry es e) :=
  (MExp.beqE_iff _ _).mp (List.all_eq_true.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hc).1).2 e he)

def rootCheck (ps : List Part) (es : List Entry) (cores : List MExp) (e : MExp) : Bool :=
  (MixedGrowthChecks.firstOrderCheck e && conforms ps es cores e) &&
    RecursiveProducedCompiler.conforms (outputEntries es) (render es e)

theorem root_checked (ps : List Part) (es : List Entry) (cores : List MExp) (e : MExp)
    (hr : rootCheck ps es cores e=true) : e.FirstOrder ∧ conforms ps es cores e=true ∧
      RecursiveProducedCompiler.conforms (outputEntries es) (render es e)=true := by
  obtain ⟨h,ho⟩ := Bool.and_eq_true_iff.mp hr
  obtain ⟨he,hs⟩ := Bool.and_eq_true_iff.mp h
  exact ⟨MixedGrowthChecks.firstOrder_checked e he,hs,ho⟩

end Shallot.MacroPeg.CBV.CanonicalProducerCompiler
