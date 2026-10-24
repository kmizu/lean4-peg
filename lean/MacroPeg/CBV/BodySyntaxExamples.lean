import MacroPeg.CBV.BodySyntaxCompiler
import MacroPeg.CBV.LeadingReplayStarExamples

namespace Shallot.MacroPeg.CBV.BodySyntaxExamples
open BodySyntaxCompiler
open BodySyntaxNormalization (Body normalize Ready)
open OriginControlNormalization (Leaf)
open ReplayControlFusion (Plan)
open LeadingReplayStarExamples (rootArgument rootBody loopBody chunkBody w child entry)
abbrev Arg := RecursiveArgumentCompiler.Expr

def probe : Body := .leaf ⟨some ['Z'],.lit []⟩
def left : Body := .leaf ⟨some ['a'],.lit ['L']⟩
def right : Body := .leaf ⟨some ['a','a'],.lit ['R']⟩
def inner : Body := .starThen left (.lit ['b']) right
def A : Body := .alt inner (.alt (.seq (.notP probe) left) right)
def C : Body := .alt (.leaf ⟨some [],.seq (.lit ['$']) (.param 0)⟩)
  (.alt left (.alt (.leaf ⟨none,.lit ['a','c']⟩) (.notP probe)))
def repeated : Body := .seq (.notP probe)
  (.seq (.starThen A loopBody C) (.leaf ⟨none,.lit []⟩))
def users : List User := [
  .leaf ⟨some [],rootBody⟩,
  repeated,
  .leaf ⟨some ['a'],chunkBody⟩,
  .leaf ⟨some [],.seq (.lit ['!']) (.param 0)⟩]

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
  simp [Valid,Readies,Ready,normalize,BodyNormalForm.atom,BodyNormalForm.neg,BodyNormalForm.choice,
    BodyNormalForm.compose,BodyNormalForm.repeatThen,BodyNormalForm.join,
    LeadingReplayStar.Valid,ContinuationFamily.Valid,ContinuationFamily.Shapes,ContinuationFamily.User.Shape,
    users,repeated,A,inner,C,probe,left,right,converted,toLeading,LeadingReplayStar.converted,LeadingReplayStar.User.toControl,
    StarThenPlan.layout,StarThenPlan.copies,ConsumingPlanOutputs.outputs,StarThenPlan.plan,StarThenPlan.tail,StarThenPlan.control,
    LeafContinuation.appendBody,LeafContinuation.chain,ContinuationPlan.bind,ContinuationFamily.shift,
    OriginControlNormalization.LeavesValid,OriginControlNormalization.Valid,OriginControlNormalization.Closed,
    Plan.All,LeafContinuation.Consumer,OriginControlNormalization.expand,LeafContinuation.lookup,LeafContinuation.raw,
    rootArgument,rootBody,loopBody,chunkBody,hlen]

theorem entry_valid : OriginControlNormalization.Valid [] (specs users) entry := by
  have hlen : (specs users).length=4 := (ContinuationFamily.emit_length 0 (LeadingReplayStar.converted (converted users))).trans rfl
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

def nested : List Char := "aa@".toList++leftWord++['b']++leftWord++['b']++rightWord++childWord++w++['$']++w++"?aa".toList

/-- Two inner iterations occur inside one outer iteration. No normalized
leaf layout or intermediate source-equivalence certificate is supplied. -/
theorem nested_execution :
    evV (sourceGrammar [] users) nested .callByValuePar
      (tblV (sourceGrammar [] users) nested .callByValuePar 20) []
      (sourceRender [] users entry) nested.length=some (some 0) := by decide +kernel

theorem translated_nested :
    SObs (targetGrammar [] users) .callByValueSeq (targetRender [] users entry) nested (some []) := by
  apply (translated_observations nested (some [])).mp
  obtain ⟨o,hd,ho⟩ := evV_derives (source_firstOrder [] users) (by decide)
    (OriginControlNormalization.render_firstOrder [] (ambient users) (specs users) entry)
    20 (Nat.le_refl nested.length) nested_execution
  rw [sfx_self] at hd
  obtain ⟨t,rest,rfl,hlen⟩ := obsR_ok ho
  have hr : rest=[] := List.length_eq_zero_iff.mp hlen
  subst rest
  exact ⟨_,hd,rfl⟩

end Shallot.MacroPeg.CBV.BodySyntaxExamples
