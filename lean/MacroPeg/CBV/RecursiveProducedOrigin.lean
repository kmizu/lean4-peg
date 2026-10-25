import MacroPeg.CBV.RecursiveProducedCorrespondence
import MacroPeg.CBV.CheckedOriginCompiler

namespace Shallot.MacroPeg.CBV.RecursiveProducedOrigin
open RecursiveProducedCompiler (Entry)
open ReplayControlFusion (Part Plan)

/-- One original grammar may contain both a consuming recursive producer
and real zero-return sequences before a retained-value continuation. -/
def body (ps : List Part) : Entry → MExp
  | .origin P => CheckedOriginCompiler.rawPlan ps P
  | e => RecursiveProducedCompiler.body ps e

def source (ps : List Part) (es : List Entry) : MGrammar := ⟨es.map (fun e => ⟨1,body ps e⟩)⟩
abbrev prepared := RecursiveProducedCompiler.source
abbrev target := RecursiveProducedCompiler.target
abbrev render := RecursiveProducedCompiler.render

def check (ps : List Part) (es : List Entry) : Bool :=
  (RecursiveProducedCompiler.check ps es && es.all (fun e => MixedGrowthChecks.firstOrderCheck (body ps e))) &&
    es.all (fun e => match e with
      | .origin P => CheckedOriginCompiler.planCheck (source ps es) ps P
      | _ => true)

theorem prepared_checked (ps : List Part) (es : List Entry) (hc : check ps es=true) :
    RecursiveProducedCompiler.check ps es=true := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hc).1).1

theorem source_firstOrder (ps : List Part) (es : List Entry) (hc : check ps es=true) : (source ps es).FirstOrder := by
  intro r hr
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hr
  exact MixedGrowthChecks.firstOrder_checked _ (List.all_eq_true.mp
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hc).1).2 e he)

theorem source_rule (ps : List Part) (es : List Entry) (i : Nat) :
    ruleAtM (source ps es).rules i=(es[i]?).map (fun e => ⟨1,body ps e⟩) := by simp [source,ruleAtM_eq_getElem?]

theorem parts_valid (ps : List Part) (es : List Entry) (hc : check ps es=true) :
    ∀ r∈ps, ReplayControlFusion.ValidPart r := by
  intro r hr
  exact (RecursiveProducedCompiler.valid ps es (prepared_checked ps es hc)).1 r (List.mem_append_left _ hr)

theorem related (ps : List Part) (es : List Entry) (hc : check ps es=true) :
    FiniteBodyRewrite.Related (source ps es) (prepared ps es) .callByValuePar 0 := by
  intro i
  rw [source_rule,RecursiveProducedCompiler.source_rule]
  cases hi : es[i]? with
  | none => trivial
  | some e =>
    refine ⟨rfl,?_⟩
    intro x k E p hp
    have heq : evV (source ps es) x .callByValuePar (tblV (source ps es) x .callByValuePar k) E (body ps e) p=
        evV (source ps es) x .callByValuePar (tblV (source ps es) x .callByValuePar k) E (RecursiveProducedCompiler.body ps e) p := by
      cases e with
      | growth r => rfl
      | produced D B => rfl
      | origin P =>
        exact CheckedOriginCompiler.plan_eq _ (source_firstOrder ps es hc) ps (parts_valid ps es hc) x k E p hp P
          (List.all_eq_true.mp (Bool.and_eq_true_iff.mp hc).2 (.origin P) (List.mem_of_getElem? hi))
    simp only [Nat.add_zero]
    rw [heq]
    exact ⟨RLe.refl _,RLe.refl _⟩

theorem observations_iff (ps : List Part) (es : List Entry) (hc : check ps es=true)
    (e : MExp) (he : e.FirstOrder) (hs : RecursiveProducedCompiler.conforms es e=true)
    (x : List Char) (rest : Option (List Char)) :
    SObs (source ps es) .callByValuePar e x rest ↔ SObs (target ps es) .callByValueSeq (render ps es e) x rest :=
  (FiniteBodyRewrite.observations (related ps es hc) (source_firstOrder ps es hc)
    (RecursiveProducedCompiler.source_firstOrder ps es (prepared_checked ps es hc)) (by decide) e he x rest).trans
    (RecursiveProducedCorrespondence.observations_iff ps es (prepared_checked ps es hc) e he hs x rest)

theorem undefined_iff (ps : List Part) (es : List Entry) (hc : check ps es=true)
    (x : List Char) (E : List (List Char)) (e : MExp) (he : e.FirstOrder) (hs : RecursiveProducedCompiler.conforms es e=true)
    (p : Nat) (hp : p≤x.length) :
    (∀ k, evV (source ps es) x .callByValuePar (tblV (source ps es) x .callByValuePar k) E e p=none) ↔
      (∀ k, evV (target ps es) x .callByValueSeq (tblV (target ps es) x .callByValueSeq k) E (render ps es e) p=none) :=
  (FiniteBodyRewrite.undefined_iff (related ps es hc) x E e p).trans
    (RecursiveProducedCorrespondence.undefined_iff ps es (prepared_checked ps es hc) x E e he hs p hp)

theorem language_translation (ps : List Part) (es : List Entry) (hc : check ps es=true)
    (e : MExp) (he : e.FirstOrder) (hs : RecursiveProducedCompiler.conforms es e=true) :
    ∃ (g : MGrammar) (entry : MExp), g.FirstOrder ∧ entry.FirstOrder ∧
      ∀ x, SObs (source ps es) .callByValuePar e x (some []) ↔ SObs g .callByValueSeq entry x (some []) :=
  ⟨target ps es,render ps es e,MixedForwardingCompiler.target_firstOrder _ _,MixedForwardingCompiler.render_firstOrder _ _ e,
    fun x => observations_iff ps es hc e he hs x (some [])⟩

end Shallot.MacroPeg.CBV.RecursiveProducedOrigin
