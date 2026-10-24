import MacroPeg.CBV.ArgumentBodyView

/-! Translate ordinary Arg bodies using an automatically generated Body
view. Generated syntactic validity is still an explicit scope restriction. -/
namespace Shallot.MacroPeg.CBV.ArgumentBodyCompiler
open RegularCaptureProduct (Node)
open OriginControlNormalization (Leaf)
open ReplayControlFusion (Plan)
abbrev Arg := RecursiveArgumentCompiler.Expr

abbrev User := Arg

def converted (users : List User) := users.map ArgumentBodyView.view
abbrev ambient (users : List User) := BodySyntaxCompiler.ambient (converted users)
abbrev specs (users : List User) := BodySyntaxCompiler.specs (converted users)
abbrev sourceRender (nodes : List Node) (users : List User) := BodySyntaxCompiler.sourceRender nodes (converted users)
abbrev normalizedGrammar (nodes : List Node) (users : List User) := BodySyntaxCompiler.sourceGrammar nodes (converted users)
abbrev targetGrammar (nodes : List Node) (users : List User) := BodySyntaxCompiler.targetGrammar nodes (converted users)
abbrev targetRender (nodes : List Node) (users : List User) := BodySyntaxCompiler.targetRender nodes (converted users)

def sourceBody (nodes : List Node) (users : List User) (b : Arg) : MExp :=
  sourceRender nodes users b
def sourceRules (nodes : List Node) (users : List User) := users.map (fun u => (⟨1,sourceBody nodes users u⟩ : MRule))
def sourceGrammar (nodes : List Node) (users : List User) : MGrammar :=
  FilteredOverlapCaller.extend nodes (OriginControlNormalization.machine (ambient users) (specs users)) (sourceRules nodes users)
def Valid (nodes : List Node) (users : List User) : Prop :=
  LeadingReplayStar.Valid nodes (BodySyntaxCompiler.converted (converted users))

theorem ready (users : List User) : BodySyntaxCompiler.Readies (converted users) := by
  intro b hb
  obtain ⟨a,_,rfl⟩ := List.mem_map.mp hb
  exact ArgumentBodyView.ready a

theorem body_valid (nodes : List Node) (users : List User) (hv : Valid nodes users) :
    BodySyntaxCompiler.Valid nodes (converted users) := ⟨ready users,hv⟩

theorem body_eq (nodes : List Node) (users : List User) (u : User)
    (g : MGrammar) (x : List Char) (s : Strategy) (hs : s≠.callByName) (T : ClockFreezing.Table)
    (hT : SoundTV g x s T) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV g x s T E (sourceBody nodes users u) p=
    evV g x s T E (BodySyntaxCompiler.sourceBody nodes (converted users) (ArgumentBodyView.view u)) p :=
  ArgumentBodyView.evaluator_eq nodes (ambient users) (specs users) g x s hs T hT E u p hp

theorem headers (nodes : List Node) (users : List User) (i : Nat) :
    (ruleAtM (sourceGrammar nodes users).rules i).map MRule.arity=
    (ruleAtM (normalizedGrammar nodes users).rules i).map MRule.arity := by
  have h : (sourceGrammar nodes users).rules.map MRule.arity=(normalizedGrammar nodes users).rules.map MRule.arity := by
    simp only [sourceGrammar,normalizedGrammar,BodySyntaxCompiler.sourceGrammar,FilteredOverlapCaller.extend,
      sourceRules,BodySyntaxCompiler.sourceRules,List.map_append,List.map_map]
    congr 1
    simp only [Function.comp_def,List.map_const',converted,List.length_map]
  have hi := congrArg (fun l => l[i]?) h
  simpa only [List.getElem?_map,ruleAtM_eq_getElem?] using hi

theorem body_results (nodes : List Node) (users : List User) (g : MGrammar) (x : List Char) (s : Strategy)
    (hs : s≠.callByName) (T : ClockFreezing.Table) (hT : SoundTV g x s T) (E : List (List Char))
    (p : Nat) (hp : p≤x.length) :
    (sourceGrammar nodes users).rules.map (fun r => evV g x s T E r.body p)=
    (normalizedGrammar nodes users).rules.map (fun r => evV g x s T E r.body p) := by
  simp only [sourceGrammar,normalizedGrammar,BodySyntaxCompiler.sourceGrammar,FilteredOverlapCaller.extend,
    sourceRules,BodySyntaxCompiler.sourceRules,List.map_append,List.map_map,converted,Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro u _
  exact body_eq nodes users u g x s hs T hT E p hp

theorem tables_eq (nodes : List Node) (users : List User) (x : List Char) (s : Strategy) (hs : s≠.callByName) :
    ∀ k, tblV (sourceGrammar nodes users) x s k=tblV (normalizedGrammar nodes users) x s k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    funext i E
    have hh := headers nodes users i
    simp only [tblV]
    cases hsrc : ruleAtM (sourceGrammar nodes users).rules i with
    | none =>
      cases hn : ruleAtM (normalizedGrammar nodes users).rules i with
      | none => rfl
      | some r => simp [hsrc,hn] at hh
    | some r =>
      cases hn : ruleAtM (normalizedGrammar nodes users).rules i with
      | none => simp [hsrc,hn] at hh
      | some t =>
        apply List.map_congr_left
        intro p hp
        have hpn : p≤x.length := by have := List.mem_range.mp hp; omega
        rw [ih]
        have hb := congrArg (fun l => l[i]?)
          (body_results nodes users (normalizedGrammar nodes users) x s hs (tblV (normalizedGrammar nodes users) x s k)
            (tblV_sound (BodySyntaxCompiler.source_firstOrder nodes (converted users)) hs k) E p hpn)
        simp only [List.getElem?_map,←ruleAtM_eq_getElem?,hsrc,hn,Option.map_some,Option.some.injEq] at hb
        exact (ContinuationGrammar.eval_headers (sourceGrammar nodes users) (normalizedGrammar nodes users)
          (headers nodes users) x s _ E r.body p).trans hb

theorem evaluator_eq (nodes : List Node) (users : List User) (x : List Char) (s : Strategy) (hs : s≠.callByName)
    (k : Nat) (E : List (List Char)) (e : MExp) (p : Nat) :
    evV (sourceGrammar nodes users) x s (tblV (sourceGrammar nodes users) x s k) E e p=
    evV (normalizedGrammar nodes users) x s (tblV (normalizedGrammar nodes users) x s k) E e p := by
  rw [tables_eq nodes users x s hs k]
  exact ContinuationGrammar.eval_headers (sourceGrammar nodes users) (normalizedGrammar nodes users) (headers nodes users) x s _ E e p

theorem source_firstOrder (nodes : List Node) (users : List User) : (sourceGrammar nodes users).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr|hr
  · exact RegularCaptureProduct.grammar_firstOrder nodes (OriginControlNormalization.machine (ambient users) (specs users)) r hr
  · obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hr
    exact OriginControlNormalization.render_firstOrder nodes (ambient users) (specs users) u

theorem normalized_observations_iff (nodes : List Node) (users : List User) (e : Arg) (x : List Char) (rest : Option (List Char)) :
    SObs (sourceGrammar nodes users) .callByValuePar (sourceRender nodes users e) x rest ↔
    SObs (normalizedGrammar nodes users) .callByValuePar (sourceRender nodes users e) x rest := by
  have hd : decideObsV .callByValuePar (sourceGrammar nodes users) x (sourceRender nodes users e)=
      decideObsV .callByValuePar (normalizedGrammar nodes users) x (sourceRender nodes users e) := by
    unfold decideObsV
    rw [ScannerPairFusion.stable_result_eq (sourceGrammar nodes users) (normalizedGrammar nodes users) x .callByValuePar .callByValuePar
      (sourceRender nodes users e) (sourceRender nodes users e) (fun k => evaluator_eq nodes users x .callByValuePar (by decide) k [] _ x.length)]
  rw [←decideObsV_iff (source_firstOrder nodes users) (by decide) (OriginControlNormalization.render_firstOrder nodes (ambient users) (specs users) e),
    ←decideObsV_iff (BodySyntaxCompiler.source_firstOrder nodes (converted users)) (by decide)
      (OriginControlNormalization.render_firstOrder nodes (ambient users) (specs users) e),hd]

theorem observations_iff (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes) (users : List User)
    (hv : Valid nodes users) (e : Arg) (he : OriginControlNormalization.Valid nodes (specs users) e)
    (x : List Char) (rest : Option (List Char)) :
    SObs (sourceGrammar nodes users) .callByValuePar (sourceRender nodes users e) x rest ↔
    SObs (targetGrammar nodes users) .callByValueSeq (targetRender nodes users e) x rest :=
  (normalized_observations_iff nodes users e x rest).trans
    (BodySyntaxCompiler.observations_iff nodes hNodes (converted users) (body_valid nodes users hv) e he x rest)

theorem language_translation (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes) (users : List User)
    (hv : Valid nodes users) (e : Arg) (he : OriginControlNormalization.Valid nodes (specs users) e) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
    SObs (sourceGrammar nodes users) .callByValuePar (sourceRender nodes users e) x (some []) ↔
    SObs g .callByValueSeq start x (some []) := by
  obtain ⟨g,start,hg,heq,hobs⟩ := BodySyntaxCompiler.language_translation nodes hNodes (converted users) (body_valid nodes users hv) e he
  exact ⟨g,start,hg,heq,fun x => (normalized_observations_iff nodes users e x (some [])).trans (hobs x)⟩

end Shallot.MacroPeg.CBV.ArgumentBodyCompiler
