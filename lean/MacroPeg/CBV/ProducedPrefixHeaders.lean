import MacroPeg.CBV.ProducedPrefixCorrespondence

namespace Shallot.MacroPeg.CBV.ProducedPrefixHeaders
open ProducedPrefixCompiler
open ReplayControlFusion (Part Plan)

/-- Keep the original, consuming null-capture call in the Par source.
The helper declaration is checked against the actual producer expression. -/
def headerBody (ps : List Part) (es : List Entry) (headers : List Nat) (i : Nat) : Entry → MExp
  | .produced _ B => .seq (.call ((headers[i]?).getD es.length) [.lit []]) B
  | e => body ps e

def original (ps : List Part) (es : List Entry) (headers : List Nat) : MGrammar :=
  ⟨es.mapIdx (fun i e => ⟨1,headerBody ps es headers i e⟩)⟩

def headerCheck (ps : List Part) (es : List Entry) (headers : List Nat) : Bool :=
  (List.range es.length).all (fun i => match es[i]? with
    | some (.produced D _) => match headers[i]? with
      | none => false
      | some h => match ruleAtM (original ps es headers).rules h with
        | none => false
        | some r => decide (r.arity=1) && MExp.beqE r.body D
    | _ => true)

def check (ps : List Part) (es : List Entry) (headers : List Nat) : Bool :=
  ProducedPrefixCompiler.check ps es && headerCheck ps es headers

theorem original_rule (ps : List Part) (es : List Entry) (headers : List Nat) (i : Nat) :
    ruleAtM (original ps es headers).rules i=(es[i]?).map (fun e => ⟨1,headerBody ps es headers i e⟩) := by
  simp [original,ruleAtM_eq_getElem?]

theorem checked_header (ps : List Part) (es : List Entry) (headers : List Nat) (hc : headerCheck ps es headers=true)
    (i : Nat) (D B : MExp) (hi : es[i]?=some (.produced D B)) :
    ∃ h, headers[i]?=some h ∧ ruleAtM (original ps es headers).rules h=some ⟨1,D⟩ := by
  have hh := (List.all_eq_true.mp hc) i (List.mem_range.mpr (List.getElem?_eq_some_iff.mp hi).1)
  simp only [hi] at hh
  cases hs : headers[i]? with
  | none => simp [hs] at hh
  | some h =>
    simp only [hs] at hh
    cases hr : ruleAtM (original ps es headers).rules h with
    | none => simp [hr] at hh
    | some r =>
      simp only [hr,Bool.and_eq_true_iff] at hh
      have har : r.arity=1 := of_decide_eq_true hh.1
      have hb : r.body=D := (MExp.beqE_iff _ _).mp hh.2
      refine ⟨h,rfl,?_⟩
      cases r
      cases har
      cases hb
      exact hr

theorem pure_closed : ∀ D, ParserPrefixFusion.Pure D → ReplayFallbackFusion.Closed D
  | .seq a b,h | .alt a b,h => ⟨pure_closed a h.1,pure_closed b h.2⟩
  | .star a,h | .notP a,h => pure_closed a h
  | .eps,_ | .any,_ | .chr _,_ | .range _ _,_ | .lit _,_ => trivial
  | .param _,h | .call _ _,h | .dbg _,h | .lam _ _,h | .callParam _ _,h | .invoke _ _ _,h => False.elim h

theorem body_bounds (ps : List Part) (es : List Entry) (headers : List Nat) (hc : check ps es headers=true)
    (i : Nat) (D B : MExp) (hi : es[i]?=some (.produced D B))
    (x : List Char) (k : Nat) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    RLe (evV (original ps es headers) x .callByValuePar (tblV (original ps es headers) x .callByValuePar k) E (headerBody ps es headers i (.produced D B)) p)
      (evV (original ps es headers) x .callByValuePar (tblV (original ps es headers) x .callByValuePar k) E (.seq D B) p) ∧
    RLe (evV (original ps es headers) x .callByValuePar (tblV (original ps es headers) x .callByValuePar k) E (.seq D B) p)
      (evV (original ps es headers) x .callByValuePar (tblV (original ps es headers) x .callByValuePar (k+1)) E (headerBody ps es headers i (.produced D B)) p) := by
  obtain ⟨h,hh,hr⟩ := checked_header ps es headers (Bool.and_eq_true_iff.mp hc).2 i D B hi
  have hD := (ProducedPrefixCompiler.checked ps es (Bool.and_eq_true_iff.mp hc).1).2.1 (.produced D B) (List.mem_of_getElem? hi)
  have hdFO := ParserPrefixFusion.pure_firstOrder D hD
  have hb := WordCallUnfolding.context_bounds (original ps es headers) h D hr hdFO (.lit []) True.intro
    (.seq .hole (.atom B)) x k E p hp
  have he : evV (original ps es headers) x .callByValuePar (tblV (original ps es headers) x .callByValuePar k) E
      (WordCallUnfolding.expanded (.lit []) D) p=
      evV (original ps es headers) x .callByValuePar (tblV (original ps es headers) x .callByValuePar k) E D p := by
    have hq : evV (original ps es headers) x .callByValuePar (tblV (original ps es headers) x .callByValuePar k) E (.andP (.lit [])) p=some (some p) := by
      rw [CallLookahead.evV_peek]
      simp [evV,Shallot.stripPrefix?,length_sfx x hp,CallLookahead.peek]
    rw [WordCallUnfolding.expanded,evV_seq_ok hq,ReplayFallbackFusion.subst_closed _ D (pure_closed D hD)]
  have hs := congrArg (fun res => match res with
    | some (some q) => evV (original ps es headers) x .callByValuePar (tblV (original ps es headers) x .callByValuePar k) E B q
    | other => other) he
  simp only [headerBody,hh,Option.getD_some]
  exact ⟨RLe.trans hb.1 (Or.inr hs),RLe.trans (Or.inr hs.symm) hb.2⟩

theorem related (ps : List Part) (es : List Entry) (headers : List Nat) (hc : check ps es headers=true) :
    FiniteBodyRewrite.Related (original ps es headers) (source ps es) .callByValuePar 1 := by
  intro i
  cases hi : es[i]? with
  | none => simp only [original_rule,source_rule,hi,Option.map_none]
  | some e =>
    simp only [original_rule,source_rule,hi,Option.map_some]
    refine ⟨True.intro,?_⟩
    intro x k E p hp
    cases e with
    | produced D B => exact body_bounds ps es headers hc i D B hi x k E p hp
    | growth r => exact ⟨RLe.refl _,evV_mono (tblV_step _ _ _ k) _ _⟩
    | origin P => exact ⟨RLe.refl _,evV_mono (tblV_step _ _ _ k) _ _⟩

theorem observations_iff (ps : List Part) (es : List Entry) (headers : List Nat) (hc : check ps es headers=true)
    (hg : (original ps es headers).FirstOrder) (hi : (source ps es).FirstOrder)
    (e : MExp) (he : e.FirstOrder) (hs : conforms es e=true) (x : List Char) (rest : Option (List Char)) :
    SObs (original ps es headers) .callByValuePar e x rest ↔ SObs (target ps es) .callByValueSeq (render ps es e) x rest :=
  (FiniteBodyRewrite.observations (related ps es headers hc) hg hi (by decide) e he x rest).trans
    (ProducedPrefixCorrespondence.observations_iff ps es hi (Bool.and_eq_true_iff.mp hc).1 e he hs x rest)

theorem physical_bounds (ps : List Part) (es : List Entry) (headers : List Nat) (hc : check ps es headers=true)
    (hi : (source ps es).FirstOrder) (x : List Char) (k : Nat) (E : List (List Char))
    (e : MExp) (he : e.FirstOrder) (hs : conforms es e=true) (p : Nat) (hp : p≤x.length) :
    RLe (evV (original ps es headers) x .callByValuePar (tblV (original ps es headers) x .callByValuePar k) E e p)
      (evV (target ps es) x .callByValueSeq (tblV (target ps es) x .callByValueSeq k) E (render ps es e) p) ∧
    RLe (evV (target ps es) x .callByValueSeq (tblV (target ps es) x .callByValueSeq k) E (render ps es e) p)
      (evV (original ps es headers) x .callByValuePar (tblV (original ps es headers) x .callByValuePar (2*((es.length+2)*k))) E e p) := by
  have hb := ProducedPrefixCorrespondence.physical_bounds ps es hi (Bool.and_eq_true_iff.mp hc).1 x k E e he hs p hp
  have ha := FiniteBodyRewrite.arities (related ps es headers hc)
  rw [←SemanticBodyRewrite.evaluator (original ps es headers) (source ps es) ha x .callByValuePar
    (tblV (source ps es) x .callByValuePar k) E e p] at hb
  rw [←SemanticBodyRewrite.evaluator (original ps es headers) (source ps es) ha x .callByValuePar
    (tblV (source ps es) x .callByValuePar ((es.length+2)*k)) E e p] at hb
  exact ⟨RLe.trans (evV_mono (FiniteBodyRewrite.forward_tables (related ps es headers hc) x k) e p) hb.1,
    RLe.trans hb.2 (evV_mono (FiniteBodyRewrite.backward_tables (related ps es headers hc) x ((es.length+2)*k)) e p)⟩

theorem undefined_iff (ps : List Part) (es : List Entry) (headers : List Nat) (hc : check ps es headers=true)
    (hg : (original ps es headers).FirstOrder) (hi : (source ps es).FirstOrder)
    (e : MExp) (he : e.FirstOrder) (hs : conforms es e=true) (x : List Char) :
    (∀ k, evV (original ps es headers) x .callByValuePar (tblV (original ps es headers) x .callByValuePar k) [] e x.length=none) ↔
      (∀ k, evV (target ps es) x .callByValueSeq (tblV (target ps es) x .callByValueSeq k) [] (render ps es e) x.length=none) :=
  (FiniteBodyRewrite.undefined_iff (related ps es headers hc) x [] e x.length).trans
    (ProducedPrefixCorrespondence.undefined_iff ps es hi (Bool.and_eq_true_iff.mp hc).1 e he hs x)

theorem language_translation (ps : List Part) (es : List Entry) (headers : List Nat) (hc : check ps es headers=true)
    (hg : (original ps es headers).FirstOrder) (hi : (source ps es).FirstOrder) (e : MExp) (he : e.FirstOrder) (hs : conforms es e=true) :
    ∃ (g : MGrammar) (entry : MExp), g.FirstOrder ∧ entry.FirstOrder ∧
      ∀ x, SObs (original ps es headers) .callByValuePar e x (some []) ↔ SObs g .callByValueSeq entry x (some []) :=
  ⟨target ps es,render ps es e,MixedForwardingCompiler.target_firstOrder _ _,MixedForwardingCompiler.render_firstOrder _ _ e,
    fun x => observations_iff ps es headers hc hg hi e he hs x (some [])⟩

end Shallot.MacroPeg.CBV.ProducedPrefixHeaders
