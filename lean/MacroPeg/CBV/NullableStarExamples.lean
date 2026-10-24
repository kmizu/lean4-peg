import MacroPeg.CBV.BodySyntaxCompiler

namespace Shallot.MacroPeg.CBV.NullableStarExamples
open BodySyntaxCompiler
open BodySyntaxNormalization (Body normalize Ready)
open ReplayControlFusion (Plan)
abbrev Arg := RecursiveArgumentCompiler.Expr

def replay : Body := .leaf ⟨some [],.lit ['!']⟩
def hash : Body := .leaf ⟨none,.lit ['#']⟩
def operand : Body := .alt replay (.notP hash)
def finish : Body := .leaf ⟨some ['#'],.lit []⟩
def normal : Body := .seq (.star operand) finish
def nested : Body := .seq (.star (.star replay)) finish
def users : List User := [normal,nested]
def entry : Arg := .user 0 (.lit ['a','b'])
def nestedEntry : Arg := .user 1 (.lit ['a','b'])

/-- The new star accepts a predicate-output operand, without pretending that
that operand is Consumer. -/
theorem predicate_output : ¬LeafContinuation.Consumer (normalize operand).plan := by
  simp [operand,replay,hash,normalize,BodyNormalForm.choice,BodyNormalForm.join,BodyNormalForm.neg,
    BodyNormalForm.atom,ContinuationFamily.shift,LeafContinuation.Consumer]

set_option maxRecDepth 4000 in
theorem valid : Valid [] users := by
  simp [Valid,Readies,Ready,normalize,BodyNormalForm.atom,BodyNormalForm.neg,BodyNormalForm.choice,
    BodyNormalForm.compose,BodyNormalForm.repeatThen,BodyNormalForm.join,
    NullableStarControl.iterate,NullableStarControl.strict,NullableStarControl.done,NullableStarControl.freeze,
    NullableStarControl.identity,NullableStarControl.diverge,NullableStarControl.dummy,
    LeadingReplayStar.Valid,ContinuationFamily.Valid,ContinuationFamily.Shapes,ContinuationFamily.User.Shape,
    users,normal,nested,operand,replay,hash,finish,converted,toLeading,LeadingReplayStar.converted,LeadingReplayStar.User.toControl,
    StarThenPlan.layout,StarThenPlan.copies,ConsumingPlanOutputs.outputs,StarThenPlan.plan,StarThenPlan.tail,StarThenPlan.control,
    LeafContinuation.appendBody,LeafContinuation.chain,ContinuationPlan.bind,ContinuationFamily.shift,
    OriginControlNormalization.LeavesValid,OriginControlNormalization.Valid,OriginControlNormalization.Closed,
    Plan.All,LeafContinuation.Consumer,OriginControlNormalization.expand,LeafContinuation.lookup,LeafContinuation.raw]

theorem entry_valid : OriginControlNormalization.Valid [] (specs users) entry := by
  have hlen : (specs users).length=2 := (ContinuationFamily.emit_length 0 (LeadingReplayStar.converted (converted users))).trans rfl
  simp [entry,OriginControlNormalization.Valid,hlen]

theorem observations (x : List Char) (rest : Option (List Char)) :
    SObs (sourceGrammar [] users) .callByValuePar (sourceRender [] users entry) x rest ↔
    SObs (targetGrammar [] users) .callByValueSeq (targetRender [] users entry) x rest :=
  observations_iff [] (by simp [RegularCaptureProduct.Valid]) users valid entry entry_valid x rest

/-- The retained capture is replayed in iterations and after stopping. A
predicate success at ? is undefined, whereas a failed final copy rejects. -/
theorem source_execution :
    evV (sourceGrammar [] users) "ab!ab!#ab".toList .callByValuePar
      (tblV (sourceGrammar [] users) "ab!ab!#ab".toList .callByValuePar 2) []
      (sourceRender [] users entry) 9=some (some 0) ∧
    evV (sourceGrammar [] users) "ab!#a".toList .callByValuePar
      (tblV (sourceGrammar [] users) "ab!#a".toList .callByValuePar 2) []
      (sourceRender [] users entry) 5=some none ∧
    evV (sourceGrammar [] users) "ab!?".toList .callByValuePar
      (tblV (sourceGrammar [] users) "ab!?".toList .callByValuePar 2) []
      (sourceRender [] users entry) 4=none ∧
    evV (sourceGrammar [] users) "ab!#ab".toList .callByValuePar
      (tblV (sourceGrammar [] users) "ab!#ab".toList .callByValuePar 2) []
      (sourceRender [] users nestedEntry) 6=none := by decide +kernel

theorem translated_accept :
    SObs (targetGrammar [] users) .callByValueSeq (targetRender [] users entry) "ab!ab!#ab".toList (some []) := by
  apply (observations _ (some [])).mp
  obtain ⟨o,hd,ho⟩ := evV_derives (source_firstOrder [] users) (by decide)
    (OriginControlNormalization.render_firstOrder [] (ambient users) (specs users) entry)
    2 (by decide) source_execution.1
  change MDerives _ _ _ "ab!ab!#ab".toList o at hd
  obtain ⟨t,rest,rfl,hlen⟩ := obsR_ok ho
  have hr : rest=[] := List.length_eq_zero_iff.mp hlen
  subst rest
  exact ⟨_,hd,rfl⟩

/-- The actual source nested-star body is undefined at every position and
under every table, hence also at every physical approximation round. -/
theorem nested_body_undefined (g : MGrammar) (x : List Char) (s : Strategy)
    (T : ClockFreezing.Table) (E : List (List Char)) (p : Nat) :
    evV g x s T E (sourceBody [] users nested) p=none := by
  change (match evStar (evStar (fun q => evV g x s T E
    (sourceRender [] users replay.expression) q)) p with
    | some (some j) => evV g x s T E (sourceRender [] users finish.expression) j | other => other)=none
  rw [NullableStarControl.nested_star_none]

end Shallot.MacroPeg.CBV.NullableStarExamples
