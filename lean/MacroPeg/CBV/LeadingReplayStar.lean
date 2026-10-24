import MacroPeg.CBV.GreedyRotation
import MacroPeg.CBV.ContinuationFamily

/-! A leading greedy repetition can precede the first retained replay. Rotate
`(replay B)* replay` into `replay (B replay)* !B`, then use the existing fixed
Seq compiler. B and the tail may themselves capture and recurse. -/
namespace Shallot.MacroPeg.CBV.LeadingReplayStar
open RegularCaptureProduct (Node)
open OriginControlNormalization (Leaf)
open ReplayControlFusion (Plan)
abbrev Arg := RecursiveArgumentCompiler.Expr

def replay (shift : List Char) : Arg := .seq (.lit shift) (.param 0)

inductive User where
  | control : ContinuationFamily.User → User
  | repeated : List Char → Arg → Arg → User
  | selected : List Leaf → Plan → Arg → Arg → User

def selectedBody (leaves : List Leaf) (P : Plan) : Arg :=
  OriginControlNormalization.expand (LeafContinuation.lookup leaves) P

def rotatedTail (A B tail : Arg) : Arg := .seq (.seq (.star (.seq B A)) (.notP B)) tail

def User.toControl : User → ContinuationFamily.User
  | .control u => u
  | .repeated u B tail => ⟨[⟨some u,.seq (.seq (.star (.seq B (replay u))) (.notP B)) tail⟩],.leaf 0,none⟩
  | .selected leaves P B tail => ⟨leaves,P,some (rotatedTail (selectedBody leaves P) B tail)⟩
def converted (users : List User) := users.map User.toControl
abbrev ambient (users : List User) := ContinuationFamily.leaves (converted users)
abbrev specs (users : List User) := ContinuationFamily.specs (converted users)
abbrev sourceRender (nodes : List Node) (users : List User) := ContinuationFamily.sourceRender nodes (converted users)
abbrev normalizedGrammar (nodes : List Node) (users : List User) := ContinuationFamily.sourceGrammar nodes (converted users)
abbrev targetGrammar (nodes : List Node) (users : List User) := ContinuationFamily.targetGrammar nodes (converted users)
abbrev targetRender (nodes : List Node) (users : List User) := ContinuationFamily.targetRender nodes (converted users)

def sourceBody (nodes : List Node) (users : List User) : User → MExp
  | .control u => ContinuationFamily.body nodes (ambient users) (specs users) u
  | .repeated u B tail => .seq
      (.seq (.star (.seq (sourceRender nodes users (replay u)) (sourceRender nodes users B))) (sourceRender nodes users (replay u)))
      (sourceRender nodes users tail)
  | .selected leaves P B tail => .seq
      (.seq (.star (.seq (sourceRender nodes users (selectedBody leaves P)) (sourceRender nodes users B)))
        (sourceRender nodes users (selectedBody leaves P))) (sourceRender nodes users tail)
def sourceRules (nodes : List Node) (users : List User) := users.map (fun u => (⟨1,sourceBody nodes users u⟩ : MRule))
def sourceGrammar (nodes : List Node) (users : List User) : MGrammar :=
  FilteredOverlapCaller.extend nodes (OriginControlNormalization.machine (ambient users) (specs users)) (sourceRules nodes users)

def Valid (nodes : List Node) (users : List User) : Prop := ContinuationFamily.Valid nodes (converted users)

theorem sequence_assoc (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table)
    (E : List (List Char)) (A B C : MExp) (p : Nat) :
    evV g x s T E (.seq (.seq A B) C) p=evV g x s T E (.seq A (.seq B C)) p := by
  change (match (match evV g x s T E A p with | some (some j) => evV g x s T E B j | other => other) with
    | some (some j) => evV g x s T E C j | other => other)=
    (match evV g x s T E A p with | some (some j) => evV g x s T E (.seq B C) j | other => other)
  cases evV g x s T E A p with
  | none => rfl
  | some result => cases result <;> rfl


theorem render_expand (nodes : List Node) (leaves : List Leaf) (ps : List Plan) (L : Nat → Arg) :
    ∀ P, OriginControlNormalization.render nodes leaves ps (OriginControlNormalization.expand L P)=
      P.exp (fun i => OriginControlNormalization.render nodes leaves ps (L i))
  | .leaf _ => rfl
  | .alt a b | .guard a b => by
    simp only [OriginControlNormalization.expand,OriginControlNormalization.render,Plan.exp,
      render_expand nodes leaves ps L a,render_expand nodes leaves ps L b,MExp.andP]
  | .notP a => by
    simp only [OriginControlNormalization.expand,OriginControlNormalization.render,Plan.exp,render_expand nodes leaves ps L a]

theorem rotate_tail (g : MGrammar) (x : List Char) (s : Strategy) (hs : s≠.callByName)
    (T : ClockFreezing.Table) (hT : SoundTV g x s T) (E : List (List Char)) (A B C : MExp)
    (ha : A.FirstOrder) (hb : B.FirstOrder) (p : Nat) (hp : p≤x.length) :
    evV g x s T E (.seq (.seq (.star (.seq A B)) A) C) p=
      evV g x s T E (.seq A (.seq (.seq (.star (.seq B A)) (.notP B)) C)) p := by
  have hr := GreedyRotation.expression_eq g x s hs T hT E A B ha hb p hp
  rw [←sequence_assoc g x s T E A (.seq (.star (.seq B A)) (.notP B)) C p]
  change (match evV g x s T E (.seq (.star (.seq A B)) A) p with
    | some (some j) => evV g x s T E C j | other => other)=_
  rw [hr]
  rfl

theorem body_eq (nodes : List Node) (users : List User) (u : User)
    (g : MGrammar) (x : List Char) (s : Strategy) (hs : s≠.callByName)
    (T : ClockFreezing.Table) (hT : SoundTV g x s T) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV g x s T E (sourceBody nodes users u) p=
    evV g x s T E (ContinuationFamily.body nodes (ambient users) (specs users) u.toControl) p := by
  cases u with
  | control u => rfl
  | repeated u B tail =>
    let A := sourceRender nodes users (replay u)
    let b := sourceRender nodes users B
    let c := sourceRender nodes users tail
    change evV g x s T E (.seq (.seq (.star (.seq A b)) A) c) p=
      evV g x s T E (.seq A (.seq (.seq (.star (.seq b A)) (.notP b)) c)) p
    exact rotate_tail g x s hs T hT E A b c
      (OriginControlNormalization.render_firstOrder nodes (ambient users) (specs users) (replay u))
      (OriginControlNormalization.render_firstOrder nodes (ambient users) (specs users) B) p hp
  | selected ls P B tail =>
    let a := selectedBody ls P
    let A := sourceRender nodes users a
    let b := sourceRender nodes users B
    let c := sourceRender nodes users tail
    change evV g x s T E (.seq (.seq (.star (.seq A b)) A) c) p=
      evV g x s T E (.seq (P.exp (fun i => sourceRender nodes users (LeafContinuation.lookup ls i)))
        (.seq (.seq (.star (.seq b A)) (.notP b)) c)) p
    rw [←render_expand nodes (ambient users) (specs users) (LeafContinuation.lookup ls) P]
    exact rotate_tail g x s hs T hT E A b c
      (OriginControlNormalization.render_firstOrder nodes (ambient users) (specs users) a)
      (OriginControlNormalization.render_firstOrder nodes (ambient users) (specs users) B) p hp

theorem headers (nodes : List Node) (users : List User) (i : Nat) :
    (ruleAtM (sourceGrammar nodes users).rules i).map MRule.arity=
    (ruleAtM (normalizedGrammar nodes users).rules i).map MRule.arity := by
  have h : (sourceGrammar nodes users).rules.map MRule.arity=(normalizedGrammar nodes users).rules.map MRule.arity := by
    simp only [sourceGrammar,normalizedGrammar,ContinuationFamily.sourceGrammar,FilteredOverlapCaller.extend,
      sourceRules,ContinuationFamily.sourceRules,List.map_append,List.map_map]
    congr 1
    simp only [Function.comp_def,List.map_const',converted,List.length_map]
  have hi := congrArg (fun l => l[i]?) h
  simpa only [List.getElem?_map,ruleAtM_eq_getElem?] using hi

theorem body_results (nodes : List Node) (users : List User) (g : MGrammar) (x : List Char) (s : Strategy)
    (hs : s≠.callByName) (T : ClockFreezing.Table) (hT : SoundTV g x s T) (E : List (List Char))
    (p : Nat) (hp : p≤x.length) :
    (sourceGrammar nodes users).rules.map (fun r => evV g x s T E r.body p)=
    (normalizedGrammar nodes users).rules.map (fun r => evV g x s T E r.body p) := by
  simp only [sourceGrammar,normalizedGrammar,ContinuationFamily.sourceGrammar,FilteredOverlapCaller.extend,
    sourceRules,ContinuationFamily.sourceRules,List.map_append,List.map_map,converted,Function.comp_def]
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
            (tblV_sound (ContinuationFamily.source_firstOrder nodes (converted users)) hs k) E p hpn)
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
  · obtain ⟨u,_,rfl⟩ := List.mem_map.mp hr
    change (sourceBody nodes users u).FirstOrder
    cases u with
    | control u =>
      change (ContinuationFamily.body nodes (ambient users) (specs users) u).FirstOrder
      unfold ContinuationFamily.body
      cases u.tail with
      | none => exact Plan.exp_firstOrder (fun i => OriginControlNormalization.render_firstOrder nodes (ambient users) (specs users) _) u.control
      | some tail => exact ⟨Plan.exp_firstOrder (fun i => OriginControlNormalization.render_firstOrder nodes (ambient users) (specs users) _) u.control,
          OriginControlNormalization.render_firstOrder nodes (ambient users) (specs users) tail⟩
    | repeated u B tail =>
      have ha := OriginControlNormalization.render_firstOrder nodes (ambient users) (specs users) (replay u)
      have hb := OriginControlNormalization.render_firstOrder nodes (ambient users) (specs users) B
      have ht := OriginControlNormalization.render_firstOrder nodes (ambient users) (specs users) tail
      exact ⟨⟨⟨ha,hb⟩,ha⟩,ht⟩
    | selected ls P B tail =>
      have ha := OriginControlNormalization.render_firstOrder nodes (ambient users) (specs users) (selectedBody ls P)
      have hb := OriginControlNormalization.render_firstOrder nodes (ambient users) (specs users) B
      have ht := OriginControlNormalization.render_firstOrder nodes (ambient users) (specs users) tail
      exact ⟨⟨⟨ha,hb⟩,ha⟩,ht⟩

theorem normalized_observations_iff (nodes : List Node) (users : List User) (e : Arg) (x : List Char) (rest : Option (List Char)) :
    SObs (sourceGrammar nodes users) .callByValuePar (sourceRender nodes users e) x rest ↔
    SObs (normalizedGrammar nodes users) .callByValuePar (sourceRender nodes users e) x rest := by
  have hd : decideObsV .callByValuePar (sourceGrammar nodes users) x (sourceRender nodes users e)=
      decideObsV .callByValuePar (normalizedGrammar nodes users) x (sourceRender nodes users e) := by
    unfold decideObsV
    rw [ScannerPairFusion.stable_result_eq (sourceGrammar nodes users) (normalizedGrammar nodes users) x .callByValuePar .callByValuePar
      (sourceRender nodes users e) (sourceRender nodes users e) (fun k => evaluator_eq nodes users x .callByValuePar (by decide) k [] _ x.length)]
  rw [←decideObsV_iff (source_firstOrder nodes users) (by decide) (OriginControlNormalization.render_firstOrder nodes (ambient users) (specs users) e),
    ←decideObsV_iff (ContinuationFamily.source_firstOrder nodes (converted users)) (by decide)
      (OriginControlNormalization.render_firstOrder nodes (ambient users) (specs users) e),hd]

theorem observations_iff (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes) (users : List User)
    (hv : Valid nodes users) (e : Arg) (he : OriginControlNormalization.Valid nodes (specs users) e)
    (x : List Char) (rest : Option (List Char)) :
    SObs (sourceGrammar nodes users) .callByValuePar (sourceRender nodes users e) x rest ↔
    SObs (targetGrammar nodes users) .callByValueSeq (targetRender nodes users e) x rest :=
  (normalized_observations_iff nodes users e x rest).trans
    (ContinuationFamily.observations_iff nodes hNodes (converted users) hv e he x rest)

theorem language_translation (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes) (users : List User)
    (hv : Valid nodes users) (e : Arg) (he : OriginControlNormalization.Valid nodes (specs users) e) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
    SObs (sourceGrammar nodes users) .callByValuePar (sourceRender nodes users e) x (some []) ↔
    SObs g .callByValueSeq start x (some []) := by
  obtain ⟨g,start,hg,heq,hobs⟩ := ContinuationFamily.language_translation nodes hNodes (converted users) hv e he
  exact ⟨g,start,hg,heq,fun x => (normalized_observations_iff nodes users e x (some [])).trans (hobs x)⟩

end Shallot.MacroPeg.CBV.LeadingReplayStar
