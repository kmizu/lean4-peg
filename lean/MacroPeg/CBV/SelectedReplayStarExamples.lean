import MacroPeg.CBV.LeadingReplayStarExamples

/-! A different replay alternative can be selected on each leading-star
iteration. Capture scope and branch commitment survive the fixed Seq compiler. -/
namespace Shallot.MacroPeg.CBV.SelectedReplayStarExamples
open LeadingReplayStar
open OriginControlNormalization (Leaf)
open ReplayControlFusion (Plan)
open LeadingReplayStarExamples (rootArgument rootBody loopBody loopTail chunkBody w child entry)
abbrev Arg := RecursiveArgumentCompiler.Expr

def parts : List Leaf := [⟨some ['a'],.lit ['L']⟩,⟨some ['a','a'],.lit ['R']⟩,⟨some ['Z'],.lit []⟩]
def plan : Plan := .alt (.guard (.notP (.leaf 2)) (.leaf 0)) (.leaf 1)
def A : Arg := selectedBody parts plan

def users : List User := [
  .control ⟨[⟨some [],rootBody⟩],.leaf 0,none⟩,
  .selected parts plan loopBody loopTail,
  .control ⟨[⟨some ['a'],chunkBody⟩],.leaf 0,none⟩,
  .control ⟨[⟨some [],.seq (.lit ['!']) (.param 0)⟩],.leaf 0,none⟩]

def leftWord : List Char := ['a']++w++['L']
def rightWord : List Char := ['a','a']++w++['R']
def childWord : List Char := ['#']++child++['!']++child

def leftInput : List Char := "aa@".toList++leftWord++childWord++leftWord++['$']++w++"?aa".toList
def mixedInput : List Char := "aa@".toList++leftWord++childWord++rightWord++childWord++leftWord++['$']++w++"?aa".toList
def shortChild : List Char := "aa@".toList++rightWord++['#']++child++['!']++List.replicate 11 'a'++['$']++w++"?aa".toList
def shortParent : List Char := "aa@".toList++leftWord++childWord++leftWord++['$']++List.replicate 5 'a'++"?aa".toList

theorem valid : Valid [] users := by
  have hlen : ∀ us : List ContinuationFamily.User, (ContinuationFamily.specs us).length=us.length :=
    fun us => ContinuationFamily.emit_length 0 us
  simp [Valid,ContinuationFamily.Valid,ContinuationFamily.Shapes,ContinuationFamily.User.Shape,
    users,converted,User.toControl,OriginControlNormalization.LeavesValid,OriginControlNormalization.Valid,
    OriginControlNormalization.Closed,Plan.All,LeafContinuation.Consumer,parts,plan,rotatedTail,selectedBody,
    OriginControlNormalization.expand,LeafContinuation.lookup,LeafContinuation.raw,
    rootArgument,rootBody,loopBody,loopTail,chunkBody,hlen]

theorem entry_valid : OriginControlNormalization.Valid [] (specs users) entry := by
  have hlen : (specs users).length=4 := (ContinuationFamily.emit_length 0 (converted users)).trans rfl
  simp [LeadingReplayStarExamples.entry,OriginControlNormalization.Valid,hlen]

/-- The two selected leaves consume different spans under the same capture. -/
theorem branch_executions :
    evV (sourceGrammar [] users) leftWord .callByValuePar (fun _ _ => []) [w]
      (sourceRender [] users A) leftWord.length=some (some 0) ∧
    evV (sourceGrammar [] users) rightWord .callByValuePar (fun _ _ => []) [w]
      (sourceRender [] users A) rightWord.length=some (some 0) := by decide +kernel

/-- The second run uses L then R then L within one leading repetition, with
six retained characters and a fresh twelve-character child capture each time. -/
theorem source_execution :
    evV (sourceGrammar [] users) leftInput .callByValuePar (tblV (sourceGrammar [] users) leftInput .callByValuePar 20) []
      (sourceRender [] users entry) leftInput.length=some (some 0) ∧
    evV (sourceGrammar [] users) mixedInput .callByValuePar (tblV (sourceGrammar [] users) mixedInput .callByValuePar 20) []
      (sourceRender [] users entry) mixedInput.length=some (some 0) ∧
    evV (sourceGrammar [] users) shortChild .callByValuePar (tblV (sourceGrammar [] users) shortChild .callByValuePar 20) []
      (sourceRender [] users entry) shortChild.length=some none ∧
    evV (sourceGrammar [] users) shortParent .callByValuePar (tblV (sourceGrammar [] users) shortParent .callByValuePar 20) []
      (sourceRender [] users entry) shortParent.length=some none := by decide +kernel

theorem translated_observations (x : List Char) (rest : Option (List Char)) :
    SObs (sourceGrammar [] users) .callByValuePar (sourceRender [] users entry) x rest ↔
    SObs (targetGrammar [] users) .callByValueSeq (targetRender [] users entry) x rest :=
  observations_iff [] (by simp [RegularCaptureProduct.Valid]) users valid entry entry_valid x rest

/-- A successful short A is not reopened just because the post-star tail
fails. Plain distribution over the two leaf continuations would accept. -/
def short : MExp := .param 0
def long : MExp := .seq (.lit ['a']) (.param 0)
def choiceA : MExp := .alt short long
def b : MExp := .lit ['Z']
def tail : MExp := .lit ['b']
def continuation : MExp := .seq (.seq (.star (.seq b choiceA)) (.notP b)) tail

theorem commitment_required :
    evV ⟨[]⟩ "aab".toList .callByValuePar (fun _ _ => []) [['a']]
      (.seq (.seq (.star (.seq choiceA b)) choiceA) tail) 3=some none ∧
    evV ⟨[]⟩ "aab".toList .callByValuePar (fun _ _ => []) [['a']]
      (.alt (.seq short continuation) (.seq long continuation)) 3=some (some 0) := by decide +kernel


theorem translated_execution :
    SObs (targetGrammar [] users) .callByValueSeq (targetRender [] users entry) leftInput (some []) ∧
    SObs (targetGrammar [] users) .callByValueSeq (targetRender [] users entry) mixedInput (some []) ∧
    SObs (targetGrammar [] users) .callByValueSeq (targetRender [] users entry) shortChild none ∧
    SObs (targetGrammar [] users) .callByValueSeq (targetRender [] users entry) shortParent none := by
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
  exact ⟨accept leftInput source_execution.1,accept mixedInput source_execution.2.1,
    reject shortChild source_execution.2.2.1,reject shortParent source_execution.2.2.2⟩

end Shallot.MacroPeg.CBV.SelectedReplayStarExamples
