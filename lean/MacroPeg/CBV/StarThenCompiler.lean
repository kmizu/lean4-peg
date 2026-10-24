import MacroPeg.CBV.StarThenPlan

/-! Compile leading `(A B)* C` bodies without a mandatory final replay.
Syntactic plan bounds/Consumer certificates are part of the source description;
no semantic row or replacement-source certificate is supplied. -/
namespace Shallot.MacroPeg.CBV.StarThenCompiler
open RegularCaptureProduct (Node)
open OriginControlNormalization (Leaf)
open ReplayControlFusion (Plan)
abbrev Arg := RecursiveArgumentCompiler.Expr

inductive User where
  | control : LeadingReplayStar.User → User
  | starThen (ls : List Leaf) (P Q : Plan) (B : Arg)
      (consumer : LeafContinuation.Consumer P)
      (bounded : P.All (fun i => i<ls.length)) (finalBounded : Q.All (fun i => i<ls.length)) : User

def User.toLeading : User → LeadingReplayStar.User
  | .control u => u
  | .starThen ls P Q B _ _ _ => .control (StarThenPlan.user ls P Q B)
def converted (users : List User) := users.map User.toLeading
abbrev ambient (users : List User) := LeadingReplayStar.ambient (converted users)
abbrev specs (users : List User) := LeadingReplayStar.specs (converted users)
abbrev sourceRender (nodes : List Node) (users : List User) := LeadingReplayStar.sourceRender nodes (converted users)
abbrev normalizedGrammar (nodes : List Node) (users : List User) := LeadingReplayStar.sourceGrammar nodes (converted users)
abbrev targetGrammar (nodes : List Node) (users : List User) := LeadingReplayStar.targetGrammar nodes (converted users)
abbrev targetRender (nodes : List Node) (users : List User) := LeadingReplayStar.targetRender nodes (converted users)

def sourceBody (nodes : List Node) (users : List User) : User → MExp
  | .control u => LeadingReplayStar.sourceBody nodes (converted users) u
  | .starThen ls P Q B _ _ _ =>
    .seq (.star (.seq (sourceRender nodes users (StarThenPlan.control ls P)) (sourceRender nodes users B)))
      (sourceRender nodes users (StarThenPlan.control ls Q))
def sourceRules (nodes : List Node) (users : List User) := users.map (fun u => (⟨1,sourceBody nodes users u⟩ : MRule))
def sourceGrammar (nodes : List Node) (users : List User) : MGrammar :=
  FilteredOverlapCaller.extend nodes (OriginControlNormalization.machine (ambient users) (specs users)) (sourceRules nodes users)
def Valid (nodes : List Node) (users : List User) : Prop := LeadingReplayStar.Valid nodes (converted users)

theorem body_eq (nodes : List Node) (users : List User) (u : User) (g : MGrammar) (x : List Char)
    (s : Strategy) (hs : s≠.callByName) (T : ClockFreezing.Table) (hT : SoundTV g x s T)
    (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV g x s T E (sourceBody nodes users u) p=
    evV g x s T E (LeadingReplayStar.sourceBody nodes (converted users) u.toLeading) p := by
  cases u with
  | control u => rfl
  | starThen ls P Q B hc hP hQ =>
    exact StarThenPlan.body_eq nodes (ambient users) (specs users) ls P Q B hc hP hQ g x s hs T hT E p hp

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

theorem body_results (nodes : List Node) (users : List User) (g : MGrammar) (x : List Char) (s : Strategy)
    (hs : s≠.callByName) (T : ClockFreezing.Table) (hT : SoundTV g x s T) (E : List (List Char))
    (p : Nat) (hp : p≤x.length) :
    (sourceGrammar nodes users).rules.map (fun r => evV g x s T E r.body p)=
    (normalizedGrammar nodes users).rules.map (fun r => evV g x s T E r.body p) := by
  simp only [sourceGrammar,normalizedGrammar,LeadingReplayStar.sourceGrammar,FilteredOverlapCaller.extend,
    sourceRules,LeadingReplayStar.sourceRules,List.map_append,List.map_map,converted,Function.comp_def]
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
            (tblV_sound (LeadingReplayStar.source_firstOrder nodes (converted users)) hs k) E p hpn)
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
    cases u with
    | control u =>
      apply LeadingReplayStar.source_firstOrder nodes (converted users)
      apply List.mem_append.mpr
      right
      apply List.mem_map.mpr
      refine ⟨u,?_,rfl⟩
      exact List.mem_map.mpr ⟨.control u,hu,rfl⟩
    | starThen ls P Q B _ _ _ =>
      exact ⟨⟨OriginControlNormalization.render_firstOrder nodes (ambient users) (specs users) (StarThenPlan.control ls P),
        OriginControlNormalization.render_firstOrder nodes (ambient users) (specs users) B⟩,
        OriginControlNormalization.render_firstOrder nodes (ambient users) (specs users) (StarThenPlan.control ls Q)⟩

theorem normalized_observations_iff (nodes : List Node) (users : List User) (e : Arg) (x : List Char) (rest : Option (List Char)) :
    SObs (sourceGrammar nodes users) .callByValuePar (sourceRender nodes users e) x rest ↔
    SObs (normalizedGrammar nodes users) .callByValuePar (sourceRender nodes users e) x rest := by
  have hd : decideObsV .callByValuePar (sourceGrammar nodes users) x (sourceRender nodes users e)=
      decideObsV .callByValuePar (normalizedGrammar nodes users) x (sourceRender nodes users e) := by
    unfold decideObsV
    rw [ScannerPairFusion.stable_result_eq (sourceGrammar nodes users) (normalizedGrammar nodes users) x .callByValuePar .callByValuePar
      (sourceRender nodes users e) (sourceRender nodes users e) (fun k => evaluator_eq nodes users x .callByValuePar (by decide) k [] _ x.length)]
  rw [←decideObsV_iff (source_firstOrder nodes users) (by decide) (OriginControlNormalization.render_firstOrder nodes (ambient users) (specs users) e),
    ←decideObsV_iff (LeadingReplayStar.source_firstOrder nodes (converted users)) (by decide)
      (OriginControlNormalization.render_firstOrder nodes (ambient users) (specs users) e),hd]

theorem observations_iff (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes) (users : List User)
    (hv : Valid nodes users) (e : Arg) (he : OriginControlNormalization.Valid nodes (specs users) e)
    (x : List Char) (rest : Option (List Char)) :
    SObs (sourceGrammar nodes users) .callByValuePar (sourceRender nodes users e) x rest ↔
    SObs (targetGrammar nodes users) .callByValueSeq (targetRender nodes users e) x rest :=
  (normalized_observations_iff nodes users e x rest).trans
    (LeadingReplayStar.observations_iff nodes hNodes (converted users) hv e he x rest)

theorem language_translation (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes) (users : List User)
    (hv : Valid nodes users) (e : Arg) (he : OriginControlNormalization.Valid nodes (specs users) e) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
    SObs (sourceGrammar nodes users) .callByValuePar (sourceRender nodes users e) x (some []) ↔
    SObs g .callByValueSeq start x (some []) := by
  obtain ⟨g,start,hg,heq,hobs⟩ := LeadingReplayStar.language_translation nodes hNodes (converted users) hv e he
  exact ⟨g,start,hg,heq,fun x => (normalized_observations_iff nodes users e x (some [])).trans (hobs x)⟩

end Shallot.MacroPeg.CBV.StarThenCompiler
