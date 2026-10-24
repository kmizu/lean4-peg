import MacroPeg.CBV.StarThenCompiler
import MacroPeg.CBV.LeadingReplayStarExamples

namespace Shallot.MacroPeg.CBV.StarThenExamples
open StarThenCompiler
open OriginControlNormalization (Leaf)
open ReplayControlFusion (Plan)
open LeadingReplayStarExamples (rootArgument rootBody loopBody chunkBody w child entry)
abbrev Arg := RecursiveArgumentCompiler.Expr

def parts : List Leaf := [⟨some ['a'],.lit ['L']⟩,⟨some ['a','a'],.lit ['R']⟩,⟨some ['Z'],.lit []⟩,
  ⟨some [],.seq (.lit ['$']) (.param 0)⟩,⟨none,.lit ['a','c']⟩]
def P : Plan := .alt (.guard (.notP (.leaf 2)) (.leaf 0)) (.leaf 1)
def Q : Plan := .alt (.leaf 3) (.alt (.leaf 0) (.alt (.leaf 4) (.notP (.leaf 2))))
theorem consumer : LeafContinuation.Consumer P := by simp [P,LeafContinuation.Consumer]
theorem bounded : P.All (fun i => i<parts.length) := by simp [P,Plan.All,parts]
theorem final_bounded : Q.All (fun i => i<parts.length) := by simp [Q,Plan.All,parts]

def users : List User := [
  .control (.control ⟨[⟨some [],rootBody⟩],.leaf 0,none⟩),
  .starThen parts P Q loopBody consumer bounded final_bounded,
  .control (.control ⟨[⟨some ['a'],chunkBody⟩],.leaf 0,none⟩),
  .control (.control ⟨[⟨some [],.seq (.lit ['!']) (.param 0)⟩],.leaf 0,none⟩)]

def leftWord : List Char := ['a']++w++['L']
def rightWord : List Char := ['a','a']++w++['R']
def childWord : List Char := ['#']++child++['!']++child

def zero : List Char := "aa@".toList++w++['$']++w++"?aa".toList
def zeroPredicate : List Char := "aa@?aa".toList
def mixed : List Char := "aa@".toList++leftWord++childWord++rightWord++childWord++w++['$']++w++"?aa".toList
def failedLast : List Char := "aa@".toList++leftWord++childWord++rightWord++childWord++leftWord++"?aa".toList
def shortCopy : List Char := "aa@".toList++leftWord++childWord++w++['$']++List.replicate 5 'a'++"?aa".toList

theorem valid : Valid [] users := by
  have hlen : ∀ us : List ContinuationFamily.User, (ContinuationFamily.specs us).length=us.length :=
    fun us => ContinuationFamily.emit_length 0 us
  simp [Valid,LeadingReplayStar.Valid,ContinuationFamily.Valid,ContinuationFamily.Shapes,ContinuationFamily.User.Shape,
    users,converted,User.toLeading,LeadingReplayStar.converted,LeadingReplayStar.User.toControl,
    StarThenPlan.user,StarThenPlan.layout,StarThenPlan.copies,ConsumingPlanOutputs.outputs,StarThenPlan.plan,StarThenPlan.tail,StarThenPlan.control,
    LeafContinuation.appendBody,LeafContinuation.chain,ContinuationPlan.bind,
    OriginControlNormalization.LeavesValid,OriginControlNormalization.Valid,OriginControlNormalization.Closed,
    Plan.All,LeafContinuation.Consumer,parts,P,Q,OriginControlNormalization.expand,LeafContinuation.lookup,LeafContinuation.raw,
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

/-- Advancing the final A before checking its B loses a valid C=ac suffix. -/
def naive (A B C : MExp) : MExp :=
  .alt (.seq (.andP (.seq A B)) (.seq A (.seq (.star (.seq B A)) (.seq B C))))
    (.seq (.notP (.seq A B)) C)
theorem next_iteration_guard_required :
    evV ⟨[]⟩ "abac".toList .callByValuePar (fun _ _ => []) []
      (.seq (.star (.seq (.lit ['a']) (.lit ['b']))) (.lit ['a','c'])) 4=some (some 0) ∧
    evV ⟨[]⟩ "abac".toList .callByValuePar (fun _ _ => []) []
      (naive (.lit ['a']) (.lit ['b']) (.lit ['a','c'])) 4=some none ∧
    evV ⟨[]⟩ "abac".toList .callByValuePar (fun _ _ => []) []
      (GuardedStarFactor.expression (.lit ['a']) (.lit ['b']) (.lit ['a','c'])) 4=some (some 0) := by decide +kernel

theorem empty_loop :
    evV ⟨[]⟩ ['#'] .callByValuePar (fun _ _ => []) [[]]
      (.seq (.star (.seq (.param 0) (.lit []))) (.lit ['#'])) 1=none ∧
    evV ⟨[]⟩ ['#'] .callByValuePar (fun _ _ => []) [[]]
      (GuardedStarFactor.expression (.param 0) (.lit []) (.lit ['#'])) 1=none := by decide +kernel


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

/-- A final closed leaf remains closed in unused copies even though the
iteration continuation itself depends on the retained capture. -/
theorem closed_final :
    evV (sourceGrammar [] users) "ac".toList .callByValuePar
      (tblV (sourceGrammar [] users) "ac".toList .callByValuePar 2) []
      (sourceRender [] users (.user 1 (.lit ['a']))) 2=some (some 0) ∧
    (StarThenPlan.layout parts P Q loopBody)[4]?=some ⟨none,.lit ['a','c']⟩ ∧
    (StarThenPlan.layout parts P Q loopBody)[9]?=some ⟨none,.lit ['a','c']⟩ ∧
    (StarThenPlan.layout parts P Q loopBody)[14]?=some ⟨none,.lit ['a','c']⟩ := by
  constructor
  · decide +kernel
  · simp [StarThenPlan.layout,StarThenPlan.copies,parts,P,ConsumingPlanOutputs.outputs]

/-- Failure of C after a successful iteration cannot retry C at the origin. -/
theorem final_failure_commits :
    evV ⟨[]⟩ "ab".toList .callByValuePar (fun _ _ => []) []
      (.seq (.star (.seq (.lit ['a']) (.lit ['b']))) (.lit ['a','b'])) 2=some none ∧
    evV ⟨[]⟩ "ab".toList .callByValuePar (fun _ _ => []) []
      (GuardedStarFactor.expression (.lit ['a']) (.lit ['b']) (.lit ['a','b'])) 2=some none ∧
    evV ⟨[]⟩ "ab".toList .callByValuePar (fun _ _ => []) []
      (.alt (.seq (.lit ['a']) (.seq (.lit ['b']) (.lit ['a','b']))) (.lit ['a','b'])) 2=some (some 0) := by decide +kernel

end Shallot.MacroPeg.CBV.StarThenExamples
