import MacroPeg.CBV.WordPrefixInlining

namespace Shallot.MacroPeg.CBV.ChangedWordPrefix
open ExpressionContext (Context plug)
open ReplayCallInlining (body)
open WordPrefixInlining (argument expanded)

/-- The prefix call captures a new word formed from the old capture
and a word-valued suffix. Callee and parent values remain distinct. -/
def source (h : MGrammar) (caller callee : Nat) (V : MExp) (C : Context) : MGrammar :=
  ⟨h.rules.mapIdx (fun i r => if i=caller then ⟨r.arity,plug (.call callee [argument V]) C⟩ else r)⟩

def check (h : MGrammar) (caller callee : Nat) (V B : MExp) (C : Context) : Bool :=
  decide (caller≠callee) && match ruleAtM h.rules caller,ruleAtM h.rules callee with
  | some a,some b => WordCallUnfolding.wordCheck V &&
      (decide (b.arity=1 ∧ b.body=body B) && decide (a.body=plug (expanded V B) C))
  | _,_ => false

theorem checked (h : MGrammar) (caller callee : Nat) (V B : MExp) (C : Context)
    (hc : check h caller callee V B C=true) :
    caller≠callee ∧ WordCallUnfolding.wordCheck V=true ∧
      ruleAtM h.rules callee=some ⟨1,body B⟩ ∧
      ∃ a, ruleAtM h.rules caller=some a ∧ a.body=plug (expanded V B) C := by
  have hne : caller≠callee := of_decide_eq_true (Bool.and_eq_true_iff.mp hc).1
  have hc := (Bool.and_eq_true_iff.mp hc).2
  cases ha : ruleAtM h.rules caller with
  | none => simp [ha] at hc
  | some a =>
    cases hb : ruleAtM h.rules callee with
    | none => simp [ha,hb] at hc
    | some b =>
      simp only [ha,hb] at hc
      have hbF : b.arity=1 ∧ b.body=body B := of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hc).2).1
      have hb' : b=⟨1,body B⟩ := by cases b; cases hbF.1; cases hbF.2; rfl
      exact ⟨hne,(Bool.and_eq_true_iff.mp hc).1,congrArg some hb',a,rfl,
        of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hc).2).2⟩

theorem rule (h : MGrammar) (caller callee : Nat) (V : MExp) (C : Context) (i : Nat) :
    ruleAtM (source h caller callee V C).rules i=
      (ruleAtM h.rules i).map (fun r => if i=caller then ⟨r.arity,plug (.call callee [argument V]) C⟩ else r) := by
  simp [source,ruleAtM_eq_getElem?,List.getElem?_mapIdx]

theorem related (h : MGrammar) (hh : h.FirstOrder) (caller callee : Nat) (V B : MExp) (C : Context)
    (hc : check h caller callee V B C=true) :
    BoundedBodyRewrite.Related (source h caller callee V C) h .callByValuePar := by
  obtain ⟨hne,hWord,hB,a,ha,haB⟩ := checked h caller callee V B C hc
  have hsB : ruleAtM (source h caller callee V C).rules callee=some ⟨1,body B⟩ := by
    rw [rule,hB]; simp [Ne.symm hne]
  have hBF : B.FirstOrder := (hh _ (ruleAtM_mem hB)).2
  intro i
  rw [rule]
  cases hi : ruleAtM h.rules i with
  | none => trivial
  | some r =>
    by_cases hic : i=caller
    · subst i
      have he : r=a := Option.some.inj (hi.symm.trans ha)
      subst r
      simp only [Option.map_some]
      refine ⟨rfl,?_⟩
      intro x k E p hp
      rw [haB]
      exact WordPrefixInlining.context_bounds (source h caller callee V C) callee B hsB hBF V (WordCallUnfolding.word_checked V hWord) C x k E p hp
    · simp only [Option.map_some,if_neg hic]
      exact ⟨True.intro,fun x k E p _ => ⟨RLe.refl _,evV_mono (tblV_step (source h caller callee V C) x .callByValuePar k) r.body p⟩⟩

theorem source_firstOrder (h : MGrammar) (hh : h.FirstOrder) (caller callee : Nat) (V B : MExp) (C : Context)
    (hc : check h caller callee V B C=true) : (source h caller callee V C).FirstOrder := by
  obtain ⟨_,hWord,_,a,ha,haB⟩ := checked h caller callee V B C hc
  intro r hr
  obtain ⟨i,hi,hr⟩ := List.mem_iff_getElem.mp hr
  have hri : ruleAtM (source h caller callee V C).rules i=some r := by
    rw [ruleAtM_eq_getElem?,List.getElem?_eq_getElem hi,hr]
  clear hr
  rw [rule] at hri
  cases ht : ruleAtM h.rules i with
  | none => simp [ht] at hri
  | some t =>
    by_cases hic : i=caller
    · subst i
      have he : t=a := Option.some.inj (ht.symm.trans ha)
      subst t
      simp only [ht,Option.map_some,Option.some.injEq] at hri
      subst r
      apply ExpressionContext.firstOrder (expanded V B) (.call callee [argument V])
        (by exact ⟨WordArguments.word_firstOrder _ ⟨True.intro,WordCallUnfolding.word_checked V hWord⟩,True.intro⟩) C
      rw [←haB]
      exact hh a (ruleAtM_mem ha)
    · simp only [ht,Option.map_some,if_neg hic,Option.some.injEq] at hri
      subst r
      exact hh t (ruleAtM_mem ht)

theorem observations (h : MGrammar) (hh : h.FirstOrder) (caller callee : Nat) (V B : MExp) (C : Context)
    (hc : check h caller callee V B C=true) (e : MExp) (he : e.FirstOrder) (x : List Char) (rest : Option (List Char)) :
    SObs (source h caller callee V C) .callByValuePar e x rest ↔ SObs h .callByValuePar e x rest :=
  BoundedBodyRewrite.observations (related h hh caller callee V B C hc)
    (source_firstOrder h hh caller callee V B C hc) hh (by decide) e he x rest

/-- Changed prefix arguments are connected to the actual recursive Seq
compiler by finite word/arity/body checks on the constructed source. -/
theorem language_translation (nodes : List RegularCaptureProduct.Node) (hn : RegularCaptureProduct.Valid nodes)
    (users : List LeadingReplayStar.User) (hu : LeadingReplayStar.Valid nodes users)
    (caller callee : Nat) (V B : MExp) (C : Context)
    (hc : check (LeadingReplayStar.sourceGrammar nodes users) caller callee V B C=true)
    (e : LeadingReplayStar.Arg) (he : OriginControlNormalization.Valid nodes (LeadingReplayStar.specs users) e) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
      SObs (source (LeadingReplayStar.sourceGrammar nodes users) caller callee V C) .callByValuePar
        (LeadingReplayStar.sourceRender nodes users e) x (some []) ↔ SObs g .callByValueSeq start x (some []) := by
  obtain ⟨g,start,hg,hstart,hobs⟩ := LeadingReplayStar.language_translation nodes hn users hu e he
  refine ⟨g,start,hg,hstart,?_⟩
  intro x
  exact (observations _ (LeadingReplayStar.source_firstOrder nodes users) caller callee V B C hc _
    (OriginControlNormalization.render_firstOrder nodes (LeadingReplayStar.ambient users) (LeadingReplayStar.specs users) e)
    x (some [])).trans (hobs x)

theorem translated_observations (nodes : List RegularCaptureProduct.Node) (hn : RegularCaptureProduct.Valid nodes)
    (users : List LeadingReplayStar.User) (hu : LeadingReplayStar.Valid nodes users)
    (caller callee : Nat) (V B : MExp) (C : Context)
    (hc : check (LeadingReplayStar.sourceGrammar nodes users) caller callee V B C=true)
    (e : LeadingReplayStar.Arg) (he : OriginControlNormalization.Valid nodes (LeadingReplayStar.specs users) e)
    (x : List Char) (rest : Option (List Char)) :
    SObs (source (LeadingReplayStar.sourceGrammar nodes users) caller callee V C) .callByValuePar
      (LeadingReplayStar.sourceRender nodes users e) x rest ↔
    SObs (LeadingReplayStar.targetGrammar nodes users) .callByValueSeq (LeadingReplayStar.targetRender nodes users e) x rest :=
  (observations _ (LeadingReplayStar.source_firstOrder nodes users) caller callee V B C hc _
    (OriginControlNormalization.render_firstOrder nodes (LeadingReplayStar.ambient users) (LeadingReplayStar.specs users) e) x rest).trans
    (LeadingReplayStar.observations_iff nodes hn users hu e he x rest)

theorem undefined_iff (nodes : List RegularCaptureProduct.Node) (hn : RegularCaptureProduct.Valid nodes)
    (users : List LeadingReplayStar.User) (hu : LeadingReplayStar.Valid nodes users)
    (caller callee : Nat) (V B : MExp) (C : Context)
    (hc : check (LeadingReplayStar.sourceGrammar nodes users) caller callee V B C=true)
    (e : LeadingReplayStar.Arg) (he : OriginControlNormalization.Valid nodes (LeadingReplayStar.specs users) e) (x : List Char) :
    (∀ k, evV (source (LeadingReplayStar.sourceGrammar nodes users) caller callee V C) x .callByValuePar
      (tblV (source (LeadingReplayStar.sourceGrammar nodes users) caller callee V C) x .callByValuePar k)
      [] (LeadingReplayStar.sourceRender nodes users e) x.length=none) ↔
    ∀ k, evV (LeadingReplayStar.targetGrammar nodes users) x .callByValueSeq
      (tblV (LeadingReplayStar.targetGrammar nodes users) x .callByValueSeq k) []
      (LeadingReplayStar.targetRender nodes users e) x.length=none :=
  BoundedBodyRewrite.undefined_of_observations _ _
    (source_firstOrder _ (LeadingReplayStar.source_firstOrder nodes users) caller callee V B C hc)
    (RecursiveArgumentCompiler.seq_firstOrder nodes
      (OriginControlNormalization.coreUsers (LeadingReplayStar.ambient users) (LeadingReplayStar.specs users)))
    .callByValuePar .callByValueSeq (by decide) (by decide) _ _
    (OriginControlNormalization.render_firstOrder nodes (LeadingReplayStar.ambient users) (LeadingReplayStar.specs users) e)
    (RecursiveArgumentCompiler.plain_firstOrder nodes
      (OriginControlNormalization.coreUsers (LeadingReplayStar.ambient users) (LeadingReplayStar.specs users)) []
      (OriginControlNormalization.normalize (LeadingReplayStar.ambient users) (LeadingReplayStar.specs users) e)) x
    (translated_observations nodes hn users hu caller callee V B C hc e he x)

end Shallot.MacroPeg.CBV.ChangedWordPrefix
