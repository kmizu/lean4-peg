import MacroPeg.CBV.ParReturnEffects
import MacroPeg.CBV.MixedForwardingChecks

namespace Shallot.MacroPeg.CBV.CheckedOriginCompiler
open ReplayControlFusion (Part Plan)
open MixedForwardingCompiler (Entry)

/-- Source control uses actual sequencing at a guard site. The compiler may
insert lookahead only after checking the actual query's return effect. -/
def rawPlan (ps : List Part) : Plan → MExp
  | .leaf i => ReplayControlFusion.sourceLeaf ps i
  | .alt a b => .alt (rawPlan ps a) (rawPlan ps b)
  | .notP a => .notP (rawPlan ps a)
  | .guard a b => .seq (rawPlan ps a) (rawPlan ps b)

def rawBody (ps : List Part) : Entry → MExp
  | .growth r => MultiplyingPrefixCompiler.sourceBody r
  | .origin P => rawPlan ps P

def source (ps : List Part) (es : List Entry) : MGrammar := ⟨es.map (fun e => ⟨1,rawBody ps e⟩)⟩

/-- The query may contain real calls, including recursion. Its zero-width
certificate is computed in the original grammar, with empty-bound clones. -/
def planCheck (g : MGrammar) (ps : List Part) : Plan → Bool
  | .leaf _ => true
  | .alt a b => planCheck g ps a && planCheck g ps b
  | .notP a => planCheck g ps a
  | .guard a b => planCheck g ps a && planCheck g ps b &&
      decide (ParReturnEffects.emptyEffect g (rawPlan ps a) ≠ .any)

def check (ps : List Part) (es : List Entry) : Bool :=
  MixedForwardingChecks.check ps es && es.all (fun e => match e with
    | .growth _ => true | .origin P => planCheck (source ps es) ps P)

abbrev target := MixedForwardingCompiler.target
abbrev render := MixedForwardingCompiler.render

theorem rawPlan_firstOrder (ps : List Part) (hp : ∀ r∈ps, ReplayControlFusion.ValidPart r) :
    ∀ P, (rawPlan ps P).FirstOrder
  | .leaf i => ReplayControlFusion.sourceLeaf_firstOrder hp i
  | .alt a b | .guard a b => ⟨rawPlan_firstOrder ps hp a,rawPlan_firstOrder ps hp b⟩
  | .notP a => rawPlan_firstOrder ps hp a

theorem source_rule (ps : List Part) (es : List Entry) (i : Nat) :
    ruleAtM (source ps es).rules i=(es[i]?).map (fun e => ⟨1,rawBody ps e⟩) := by
  simp [source,ruleAtM_eq_getElem?]

theorem valid (ps : List Part) (es : List Entry) (hc : check ps es=true) : MixedForwardingCompiler.Valid ps es :=
  MixedForwardingChecks.checked ps es (Bool.and_eq_true_iff.mp hc).1

theorem source_firstOrder (ps : List Part) (es : List Entry) (hc : check ps es=true) : (source ps es).FirstOrder := by
  intro r hr
  obtain ⟨e,he,hr⟩ := List.mem_map.mp hr
  subst r
  cases e with
  | growth r =>
    exact MixedForwardingCompiler.original_firstOrder ps es (valid ps es hc)
      ⟨1,MixedForwardingCompiler.body ps (.growth r)⟩ (List.mem_map.mpr ⟨.growth r,he,rfl⟩)
  | origin P => exact rawPlan_firstOrder ps (valid ps es hc).1 P

/-- Certified zero-return queries equal their positive lookahead at the same
physical clock, preserving every finite failure and undefined result. -/
theorem peek_eq (g : MGrammar) (hg : g.FirstOrder) (a : MExp) (ha : a.FirstOrder)
    (hz : ParReturnEffects.emptyEffect g a ≠ .any) (x : List Char) (k : Nat)
    (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV g x .callByValuePar (tblV g x .callByValuePar k) E a p=
      evV g x .callByValuePar (tblV g x .callByValuePar k) E (.andP a) p := by
  rw [CallLookahead.evV_peek]
  cases hs : evV g x .callByValuePar (tblV g x .callByValuePar k) E a p with
  | none => rfl
  | some v => cases v with
    | none => rfl
    | some q =>
      have hq := ParReturnEffects.zero_of_not_any _ hz p q (ParReturnEffects.empty_success g hg a ha x k E p q hp hs)
      subst q
      rfl

theorem plan_eq (g : MGrammar) (hg : g.FirstOrder) (ps : List Part)
    (hf : ∀ r∈ps, ReplayControlFusion.ValidPart r) (x : List Char) (k : Nat) (E : List (List Char))
    (p : Nat) (hp : p≤x.length) : ∀ P, planCheck g ps P=true →
    evV g x .callByValuePar (tblV g x .callByValuePar k) E (rawPlan ps P) p=
      evV g x .callByValuePar (tblV g x .callByValuePar k) E (P.exp (ReplayControlFusion.sourceLeaf ps)) p
  | .leaf _,_ => rfl
  | .alt a b,h => by
    obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp h
    simp only [rawPlan,Plan.exp,evV,plan_eq g hg ps hf x k E p hp a ha,plan_eq g hg ps hf x k E p hp b hb]
  | .notP a,h => by
    simp only [rawPlan,Plan.exp,evV,plan_eq g hg ps hf x k E p hp a h]
  | .guard a b,h => by
    obtain ⟨hab,hz⟩ := Bool.and_eq_true_iff.mp h
    obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp hab
    have hpeek := peek_eq g hg (rawPlan ps a) (rawPlan_firstOrder ps hf a) (of_decide_eq_true hz) x k E p hp
    have hsame := plan_eq g hg ps hf x k E p hp a ha
    have hzero : evV g x .callByValuePar (tblV g x .callByValuePar k) E (rawPlan ps a) p=
        CallLookahead.peek p (evV g x .callByValuePar (tblV g x .callByValuePar k) E (rawPlan ps a) p) := by
      rwa [CallLookahead.evV_peek] at hpeek
    simp only [rawPlan,Plan.exp,evV,CallLookahead.evV_peek,←hsame,←hzero]
    cases hv : evV g x .callByValuePar (tblV g x .callByValuePar k) E (rawPlan ps a) p with
    | none => rfl
    | some v => cases v with
      | none => rfl
      | some q =>
        have hq : q=p := by simpa only [hv,CallLookahead.peek,Option.some.injEq] using hzero
        subst q
        exact plan_eq g hg ps hf x k E p hp b hb

/-- The query normalization has no clock delay, even in a mutually recursive
grammar. The certificate is discharged on source tables, not hypothetical rows. -/
theorem related (ps : List Part) (es : List Entry) (hc : check ps es=true) :
    FiniteBodyRewrite.Related (source ps es) (MixedForwardingCompiler.original ps es) .callByValuePar 0 := by
  intro i
  rw [source_rule,MixedForwardingCompiler.original_rule]
  cases hi : es[i]? with
  | none => trivial
  | some e =>
    refine ⟨rfl,?_⟩
    intro x k E p hp
    have heq : evV (source ps es) x .callByValuePar (tblV (source ps es) x .callByValuePar k) E (rawBody ps e) p=
        evV (source ps es) x .callByValuePar (tblV (source ps es) x .callByValuePar k) E (MixedForwardingCompiler.body ps e) p := by
      cases e with
      | growth r => rfl
      | origin P =>
        exact plan_eq _ (source_firstOrder ps es hc) ps (valid ps es hc).1 x k E p hp P
          (List.all_eq_true.mp (Bool.and_eq_true_iff.mp hc).2 (.origin P) (List.mem_of_getElem? hi))
    simp only [Nat.add_zero]
    rw [heq]
    exact ⟨RLe.refl _,RLe.refl _⟩

theorem evaluator_eq (ps : List Part) (es : List Entry) (hc : check ps es=true)
    (x : List Char) (k : Nat) (E : List (List Char)) (e : MExp) (p : Nat) :
    evV (source ps es) x .callByValuePar (tblV (source ps es) x .callByValuePar k) E e p=
      evV (MixedForwardingCompiler.original ps es) x .callByValuePar
        (tblV (MixedForwardingCompiler.original ps es) x .callByValuePar k) E e p := by
  have hr := related ps es hc
  have ha := FiniteBodyRewrite.arities hr
  have hf := @evV_mono (source ps es) x .callByValuePar _ _ E (FiniteBodyRewrite.forward_tables hr x k) e p
  have hb := @evV_mono (MixedForwardingCompiler.original ps es) x .callByValuePar _ _ E
    (FiniteBodyRewrite.backward_tables hr x k) e p
  simp only [Nat.zero_add,Nat.one_mul] at hb
  rw [SemanticBodyRewrite.evaluator _ _ ha x .callByValuePar
    (tblV (MixedForwardingCompiler.original ps es) x .callByValuePar k) E e p] at hf
  rw [←SemanticBodyRewrite.evaluator _ _ ha x .callByValuePar
    (tblV (source ps es) x .callByValuePar k) E e p] at hb
  exact WordExpansionRefinement.antisymm hf hb

theorem physical_bounds (ps : List Part) (es : List Entry) (hc : check ps es=true)
    (x : List Char) (k : Nat) (E : List (List Char)) (e : MExp) (he : e.FirstOrder)
    (p : Nat) (hp : p≤x.length) :
    RLe (evV (source ps es) x .callByValuePar (tblV (source ps es) x .callByValuePar k) E e p)
      (evV (target ps es) x .callByValueSeq (tblV (target ps es) x .callByValueSeq k) E (render ps es e) p) ∧
    RLe (evV (target ps es) x .callByValueSeq (tblV (target ps es) x .callByValueSeq k) E (render ps es e) p)
      (evV (source ps es) x .callByValuePar (tblV (source ps es) x .callByValuePar ((es.length+2)*k)) E e p) := by
  rw [evaluator_eq ps es hc x k E e p,evaluator_eq ps es hc x ((es.length+2)*k) E e p]
  exact MixedForwardingCorrespondence.physical_bounds ps es (valid ps es hc) x k E e he p hp

theorem observations_iff (ps : List Part) (es : List Entry) (hc : check ps es=true)
    (e : MExp) (he : e.FirstOrder) (x : List Char) (rest : Option (List Char)) :
    SObs (source ps es) .callByValuePar e x rest ↔
      SObs (target ps es) .callByValueSeq (render ps es e) x rest :=
  (FiniteBodyRewrite.observations (related ps es hc) (source_firstOrder ps es hc)
    (MixedForwardingCompiler.original_firstOrder ps es (valid ps es hc)) (by decide) e he x rest).trans
    (MixedForwardingCorrespondence.observations_iff ps es (valid ps es hc) e he x rest)

theorem undefined_iff (ps : List Part) (es : List Entry) (hc : check ps es=true)
    (e : MExp) (he : e.FirstOrder) (x : List Char) :
    (∀ k, evV (source ps es) x .callByValuePar (tblV (source ps es) x .callByValuePar k) [] e x.length=none) ↔
      (∀ k, evV (target ps es) x .callByValueSeq (tblV (target ps es) x .callByValueSeq k) [] (render ps es e) x.length=none) :=
  (FiniteBodyRewrite.undefined_iff (related ps es hc) x [] e x.length).trans
    (MixedForwardingCorrespondence.original_undefined_iff ps es (valid ps es hc) x [] e he x.length (Nat.le_refl _))

theorem language_translation (ps : List Part) (es : List Entry) (hc : check ps es=true)
    (e : MExp) (he : e.FirstOrder) :
    ∃ (g : MGrammar) (entry : MExp), g.FirstOrder ∧ entry.FirstOrder ∧
      ∀ x, SObs (source ps es) .callByValuePar e x (some []) ↔ SObs g .callByValueSeq entry x (some []) :=
  ⟨target ps es,render ps es e,MixedForwardingCompiler.target_firstOrder ps es,
    MixedForwardingCompiler.render_firstOrder ps es e,fun x => observations_iff ps es hc e he x (some [])⟩

end Shallot.MacroPeg.CBV.CheckedOriginCompiler
