import MacroPeg.CBV.BodySyntaxNormalization

/-! Compile recursively normalized source bodies into fixed Seq grammars.
Only syntactic readiness and generated-family validity are required. -/
namespace Shallot.MacroPeg.CBV.BodySyntaxCompiler
open RegularCaptureProduct (Node)
open OriginControlNormalization (Leaf)
open ReplayControlFusion (Plan)
abbrev Arg := RecursiveArgumentCompiler.Expr

open BodySyntaxNormalization (Body normalize Ready)
abbrev User := Body

def toLeading (b : Body) : LeadingReplayStar.User :=
  .control ⟨(normalize b).leaves,(normalize b).plan,none⟩
def converted (users : List User) := users.map toLeading
abbrev ambient (users : List User) := LeadingReplayStar.ambient (converted users)
abbrev specs (users : List User) := LeadingReplayStar.specs (converted users)
abbrev sourceRender (nodes : List Node) (users : List User) := LeadingReplayStar.sourceRender nodes (converted users)
abbrev normalizedGrammar (nodes : List Node) (users : List User) := LeadingReplayStar.sourceGrammar nodes (converted users)
abbrev targetGrammar (nodes : List Node) (users : List User) := LeadingReplayStar.targetGrammar nodes (converted users)
abbrev targetRender (nodes : List Node) (users : List User) := LeadingReplayStar.targetRender nodes (converted users)

def sourceBody (nodes : List Node) (users : List User) (b : Body) : MExp :=
  sourceRender nodes users b.expression
def sourceRules (nodes : List Node) (users : List User) := users.map (fun u => (⟨1,sourceBody nodes users u⟩ : MRule))
def sourceGrammar (nodes : List Node) (users : List User) : MGrammar :=
  FilteredOverlapCaller.extend nodes (OriginControlNormalization.machine (ambient users) (specs users)) (sourceRules nodes users)
def Readies (users : List User) : Prop := ∀ b∈users, Ready b
def Valid (nodes : List Node) (users : List User) : Prop :=
  Readies users ∧ LeadingReplayStar.Valid nodes (converted users)

theorem body_eq (nodes : List Node) (users : List User) (u : User) (hr : Ready u)
    (g : MGrammar) (x : List Char) (s : Strategy) (hs : s≠.callByName) (T : ClockFreezing.Table)
    (hT : SoundTV g x s T) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV g x s T E (sourceBody nodes users u) p=
    evV g x s T E (LeadingReplayStar.sourceBody nodes (converted users) (toLeading u)) p := by
  have he := BodySyntaxNormalization.evaluator_eq nodes (ambient users) (specs users) g x s hs T hT E u hr p hp
  unfold BodyNormalForm.Form.syntax StarThenPlan.control at he
  rw [LeadingReplayStar.render_expand] at he
  exact he

theorem headers (nodes : List Node) (users : List User) (i : Nat) :
    (ruleAtM (sourceGrammar nodes users).rules i).map MRule.arity=
    (ruleAtM (normalizedGrammar nodes users).rules i).map MRule.arity := by
  have h : (sourceGrammar nodes users).rules.map MRule.arity=(normalizedGrammar nodes users).rules.map MRule.arity := by
    simp only [sourceGrammar,normalizedGrammar,LeadingReplayStar.sourceGrammar,FilteredOverlapCaller.extend,
      sourceRules,LeadingReplayStar.sourceRules,List.map_append,List.map_map]
    congr 1
    simp only [Function.comp_def,List.map_const',converted,List.length_map]
  have hi := congrArg (fun l => l[i]?) h
  simpa only [List.getElem?_map,ruleAtM_eq_getElem?] using hi

theorem body_results (nodes : List Node) (users : List User) (hReady : Readies users) (g : MGrammar) (x : List Char) (s : Strategy)
    (hs : s≠.callByName) (T : ClockFreezing.Table) (hT : SoundTV g x s T) (E : List (List Char))
    (p : Nat) (hp : p≤x.length) :
    (sourceGrammar nodes users).rules.map (fun r => evV g x s T E r.body p)=
    (normalizedGrammar nodes users).rules.map (fun r => evV g x s T E r.body p) := by
  simp only [sourceGrammar,normalizedGrammar,LeadingReplayStar.sourceGrammar,FilteredOverlapCaller.extend,
    sourceRules,LeadingReplayStar.sourceRules,List.map_append,List.map_map,converted,Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro u hu
  exact body_eq nodes users u (hReady u hu) g x s hs T hT E p hp

theorem tables_eq (nodes : List Node) (users : List User) (hReady : Readies users) (x : List Char) (s : Strategy) (hs : s≠.callByName) :
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
          (body_results nodes users hReady (normalizedGrammar nodes users) x s hs (tblV (normalizedGrammar nodes users) x s k)
            (tblV_sound (LeadingReplayStar.source_firstOrder nodes (converted users)) hs k) E p hpn)
        simp only [List.getElem?_map,←ruleAtM_eq_getElem?,hsrc,hn,Option.map_some,Option.some.injEq] at hb
        exact (ContinuationGrammar.eval_headers (sourceGrammar nodes users) (normalizedGrammar nodes users)
          (headers nodes users) x s _ E r.body p).trans hb

theorem evaluator_eq (nodes : List Node) (users : List User) (hReady : Readies users) (x : List Char) (s : Strategy) (hs : s≠.callByName)
    (k : Nat) (E : List (List Char)) (e : MExp) (p : Nat) :
    evV (sourceGrammar nodes users) x s (tblV (sourceGrammar nodes users) x s k) E e p=
    evV (normalizedGrammar nodes users) x s (tblV (normalizedGrammar nodes users) x s k) E e p := by
  rw [tables_eq nodes users hReady x s hs k]
  exact ContinuationGrammar.eval_headers (sourceGrammar nodes users) (normalizedGrammar nodes users) (headers nodes users) x s _ E e p

theorem source_firstOrder (nodes : List Node) (users : List User) : (sourceGrammar nodes users).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr|hr
  · exact RegularCaptureProduct.grammar_firstOrder nodes (OriginControlNormalization.machine (ambient users) (specs users)) r hr
  · obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hr
    exact OriginControlNormalization.render_firstOrder nodes (ambient users) (specs users) u.expression

theorem normalized_observations_iff (nodes : List Node) (users : List User) (hReady : Readies users) (e : Arg) (x : List Char) (rest : Option (List Char)) :
    SObs (sourceGrammar nodes users) .callByValuePar (sourceRender nodes users e) x rest ↔
    SObs (normalizedGrammar nodes users) .callByValuePar (sourceRender nodes users e) x rest := by
  have hd : decideObsV .callByValuePar (sourceGrammar nodes users) x (sourceRender nodes users e)=
      decideObsV .callByValuePar (normalizedGrammar nodes users) x (sourceRender nodes users e) := by
    unfold decideObsV
    rw [ScannerPairFusion.stable_result_eq (sourceGrammar nodes users) (normalizedGrammar nodes users) x .callByValuePar .callByValuePar
      (sourceRender nodes users e) (sourceRender nodes users e) (fun k => evaluator_eq nodes users hReady x .callByValuePar (by decide) k [] _ x.length)]
  rw [←decideObsV_iff (source_firstOrder nodes users) (by decide) (OriginControlNormalization.render_firstOrder nodes (ambient users) (specs users) e),
    ←decideObsV_iff (LeadingReplayStar.source_firstOrder nodes (converted users)) (by decide)
      (OriginControlNormalization.render_firstOrder nodes (ambient users) (specs users) e),hd]

theorem observations_iff (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes) (users : List User)
    (hv : Valid nodes users) (e : Arg) (he : OriginControlNormalization.Valid nodes (specs users) e)
    (x : List Char) (rest : Option (List Char)) :
    SObs (sourceGrammar nodes users) .callByValuePar (sourceRender nodes users e) x rest ↔
    SObs (targetGrammar nodes users) .callByValueSeq (targetRender nodes users e) x rest :=
  (normalized_observations_iff nodes users hv.1 e x rest).trans
    (LeadingReplayStar.observations_iff nodes hNodes (converted users) hv.2 e he x rest)

theorem language_translation (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes) (users : List User)
    (hv : Valid nodes users) (e : Arg) (he : OriginControlNormalization.Valid nodes (specs users) e) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
    SObs (sourceGrammar nodes users) .callByValuePar (sourceRender nodes users e) x (some []) ↔
    SObs g .callByValueSeq start x (some []) := by
  obtain ⟨g,start,hg,heq,hobs⟩ := LeadingReplayStar.language_translation nodes hNodes (converted users) hv.2 e he
  exact ⟨g,start,hg,heq,fun x => (normalized_observations_iff nodes users hv.1 e x (some [])).trans (hobs x)⟩

end Shallot.MacroPeg.CBV.BodySyntaxCompiler
