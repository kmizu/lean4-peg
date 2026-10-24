import MacroPeg.CBV.ArgumentBodyCompiler
import MacroPeg.CBV.LeadingReplayStarExamples

namespace Shallot.MacroPeg.CBV.ArgumentBodyExamples
open ArgumentBodyCompiler
open OriginControlNormalization (Leaf)
open ReplayControlFusion (Plan)
open LeadingReplayStarExamples (rootArgument rootBody loopBody chunkBody w child entry)
abbrev Arg := RecursiveArgumentCompiler.Expr

def left : Arg := .seq (.lit ['a']) (.seq (.param 0) (.lit ['L']))
def probe : Arg := .seq (.lit ['Z']) (.param 0)
def iteration : Arg :=
  .alt (.seq (.lit ['a']) (.seq (.param 0) (.seq (.lit ['L']) loopBody)))
    (.seq (.lit ['a','a']) (.seq (.param 0) (.seq (.lit ['R']) loopBody)))
def finalBody : Arg := .alt (.seq (.param 0) (.seq (.lit ['$']) (.param 0)))
  (.alt left (.alt (.lit ['a','c']) (.notP probe)))
def repeated : Arg := .seq (.star iteration) finalBody

/-- These are ordinary recursive Arg bodies, not supplied Body trees or
normalized leaf arrays. -/
def users : List User := [
  .seq (.param 0) rootBody,
  repeated,
  .seq (.lit ['a']) (.seq (.param 0) chunkBody),
  .seq (.param 0) (.seq (.lit ['!']) (.param 0))]

def leftWord : List Char := ['a']++w++['L']
def rightWord : List Char := ['a','a']++w++['R']
def childWord : List Char := ['#']++child++['!']++child

def zero : List Char := "aa@".toList++w++['$']++w++"?aa".toList
def zeroPredicate : List Char := "aa@?aa".toList
def mixed : List Char := "aa@".toList++leftWord++childWord++rightWord++childWord++w++['$']++w++"?aa".toList
def failedLast : List Char := "aa@".toList++leftWord++childWord++rightWord++childWord++leftWord++"?aa".toList
def shortCopy : List Char := "aa@".toList++leftWord++childWord++w++['$']++List.replicate 5 'a'++"?aa".toList

set_option maxRecDepth 4000 in
theorem valid : Valid [] users := by
  have hlen : ∀ us : List ContinuationFamily.User, (ContinuationFamily.specs us).length=us.length :=
    fun us => ContinuationFamily.emit_length 0 us
  simp [Valid,converted,BodySyntaxCompiler.converted,BodySyntaxCompiler.toLeading,
    ArgumentBodyView.view,ArgumentBodyView.replayHead,
    BodySyntaxNormalization.normalize,BodyNormalForm.atom,BodyNormalForm.neg,BodyNormalForm.choice,
    BodyNormalForm.compose,BodyNormalForm.repeatThen,BodyNormalForm.join,
    NullableStarControl.iterate,NullableStarControl.strict,NullableStarControl.done,NullableStarControl.freeze,
    NullableStarControl.identity,NullableStarControl.diverge,NullableStarControl.dummy,
    LeadingReplayStar.Valid,ContinuationFamily.Valid,ContinuationFamily.Shapes,ContinuationFamily.User.Shape,
    users,repeated,iteration,finalBody,left,probe,LeadingReplayStar.converted,LeadingReplayStar.User.toControl,
    StarThenPlan.layout,StarThenPlan.copies,ConsumingPlanOutputs.outputs,StarThenPlan.plan,StarThenPlan.tail,StarThenPlan.control,
    LeafContinuation.appendBody,LeafContinuation.chain,ContinuationPlan.bind,ContinuationFamily.shift,
    OriginControlNormalization.LeavesValid,OriginControlNormalization.Valid,OriginControlNormalization.Closed,
    Plan.All,LeafContinuation.Consumer,OriginControlNormalization.expand,LeafContinuation.lookup,LeafContinuation.raw,
    rootArgument,rootBody,loopBody,chunkBody,hlen]

theorem entry_valid : OriginControlNormalization.Valid [] (specs users) entry := by
  have hlen : (specs users).length=4 := (ContinuationFamily.emit_length 0 (LeadingReplayStar.converted (BodySyntaxCompiler.converted (converted users)))).trans rfl
  simp [LeadingReplayStarExamples.entry,OriginControlNormalization.Valid,hlen]

/-- The post-star Q need not be A. Both a zero-iteration capture-dependent
Q and a mixed L/R run followed by a different replay Q succeed. -/
theorem source_execution :
    evV (sourceGrammar [] users) zero .callByValuePar (tblV (sourceGrammar [] users) zero .callByValuePar 20) []
      (sourceRender [] users entry) zero.length=some (some 0) ∧
    evV (sourceGrammar [] users) mixed .callByValuePar (tblV (sourceGrammar [] users) mixed .callByValuePar 20) []
      (sourceRender [] users entry) mixed.length=some (some 0) ∧
    evV (sourceGrammar [] users) failedLast .callByValuePar (tblV (sourceGrammar [] users) failedLast .callByValuePar 20) []
      (sourceRender [] users entry) failedLast.length=some (some 0) ∧
    evV (sourceGrammar [] users) zeroPredicate .callByValuePar (tblV (sourceGrammar [] users) zeroPredicate .callByValuePar 20) []
      (sourceRender [] users entry) zeroPredicate.length=some (some 0) ∧
    evV (sourceGrammar [] users) shortCopy .callByValuePar (tblV (sourceGrammar [] users) shortCopy .callByValuePar 20) []
      (sourceRender [] users entry) shortCopy.length=some none := by decide +kernel

theorem translated_observations (x : List Char) (rest : Option (List Char)) :
    SObs (sourceGrammar [] users) .callByValuePar (sourceRender [] users entry) x rest ↔
    SObs (targetGrammar [] users) .callByValueSeq (targetRender [] users entry) x rest :=
  observations_iff [] (by simp [RegularCaptureProduct.Valid]) users valid entry entry_valid x rest

/-- Q may be a negative test returning before the argument endpoint. -/
theorem returns_origin :
    evV (sourceGrammar [] users) "aaaaZ".toList .callByValuePar
      (tblV (sourceGrammar [] users) "aaaaZ".toList .callByValuePar 1) []
      (sourceRender [] users (.user 1 (.lit ['a']))) 5=some (some 5) := by decide +kernel

theorem translated_execution :
    SObs (targetGrammar [] users) .callByValueSeq (targetRender [] users entry) zero (some []) ∧
    SObs (targetGrammar [] users) .callByValueSeq (targetRender [] users entry) mixed (some []) ∧
    SObs (targetGrammar [] users) .callByValueSeq (targetRender [] users entry) failedLast (some []) ∧
    SObs (targetGrammar [] users) .callByValueSeq (targetRender [] users entry) zeroPredicate (some []) ∧
    SObs (targetGrammar [] users) .callByValueSeq (targetRender [] users entry) shortCopy none := by
  have accept (x : List Char)
      (hv : evV (sourceGrammar [] users) x .callByValuePar (tblV (sourceGrammar [] users) x .callByValuePar 20) []
        (sourceRender [] users entry) x.length=some (some 0)) :
      SObs (targetGrammar [] users) .callByValueSeq (targetRender [] users entry) x (some []) := by
    apply (translated_observations x (some [])).mp
    obtain ⟨o,hd,ho⟩ := evV_derives (source_firstOrder [] users) (by decide)
      (OriginControlNormalization.render_firstOrder [] (ambient users) (specs users) entry) 20 (Nat.le_refl x.length) hv
    rw [sfx_self] at hd
    obtain ⟨t,rest,rfl,hlen⟩ := obsR_ok ho
    have hr : rest=[] := List.length_eq_zero_iff.mp hlen
    subst rest
    exact ⟨_,hd,rfl⟩
  have reject (x : List Char)
      (hv : evV (sourceGrammar [] users) x .callByValuePar (tblV (sourceGrammar [] users) x .callByValuePar 20) []
        (sourceRender [] users entry) x.length=some none) :
      SObs (targetGrammar [] users) .callByValueSeq (targetRender [] users entry) x none := by
    apply (translated_observations x none).mp
    obtain ⟨o,hd,ho⟩ := evV_derives (source_firstOrder [] users) (by decide)
      (OriginControlNormalization.render_firstOrder [] (ambient users) (specs users) entry) 20 (Nat.le_refl x.length) hv
    rw [sfx_self] at hd
    rw [obsR_fail ho] at hd
    exact ⟨_,hd,rfl⟩
  exact ⟨accept zero source_execution.1,accept mixed source_execution.2.1,
    accept failedLast source_execution.2.2.1,accept zeroPredicate source_execution.2.2.2.1,
    reject shortCopy source_execution.2.2.2.2⟩

theorem closed_final :
    evV (sourceGrammar [] users) "ac".toList .callByValuePar
      (tblV (sourceGrammar [] users) "ac".toList .callByValuePar 2) []
      (sourceRender [] users (.user 1 (.lit ['a']))) 2=some (some 0) := by decide +kernel


/-- An actual accepted original body outside this normalization criterion:
a consuming closed star precedes the first retained-value replay. -/
def consumingPrefix : Arg := .seq (.star (.lit ['a'])) (.seq (.lit ['#']) (.param 0))

theorem consuming_prefix_source :
    evV (sourceGrammar [] [consumingPrefix]) "aaa#a".toList .callByValuePar
      (tblV (sourceGrammar [] [consumingPrefix]) "aaa#a".toList .callByValuePar 2) []
      (sourceRender [] [consumingPrefix] (.user 0 (.lit ['a']))) 5=some (some 0) := by decide +kernel

set_option maxRecDepth 4000 in
/-- This is an exclusion by generated syntax validity, not a language-class
separation: the automatic bridge does not cover all ordinary source bodies. -/
theorem consuming_prefix_not_valid : ¬Valid [] [consumingPrefix] := by
  simp [Valid,converted,BodySyntaxCompiler.converted,BodySyntaxCompiler.toLeading,
    ArgumentBodyView.view,ArgumentBodyView.replayHead,
    BodySyntaxNormalization.normalize,BodyNormalForm.atom,BodyNormalForm.neg,
    BodyNormalForm.compose,BodyNormalForm.repeatThen,BodyNormalForm.join,
    NullableStarControl.iterate,NullableStarControl.strict,NullableStarControl.done,NullableStarControl.freeze,
    NullableStarControl.identity,NullableStarControl.diverge,NullableStarControl.dummy,
    LeadingReplayStar.Valid,ContinuationFamily.Valid,ContinuationFamily.Shapes,ContinuationFamily.User.Shape,
    consumingPrefix,LeadingReplayStar.converted,LeadingReplayStar.User.toControl,
    StarThenPlan.layout,StarThenPlan.copies,ConsumingPlanOutputs.outputs,StarThenPlan.plan,StarThenPlan.tail,StarThenPlan.control,
    LeafContinuation.appendBody,LeafContinuation.chain,ContinuationPlan.bind,ContinuationFamily.shift,
    OriginControlNormalization.LeavesValid,OriginControlNormalization.Valid,OriginControlNormalization.Closed,
    Plan.All,LeafContinuation.Consumer,OriginControlNormalization.expand,LeafContinuation.lookup,LeafContinuation.raw]

end Shallot.MacroPeg.CBV.ArgumentBodyExamples
