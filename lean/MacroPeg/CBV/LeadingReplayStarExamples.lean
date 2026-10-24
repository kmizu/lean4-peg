import MacroPeg.CBV.LeadingReplayStar

namespace Shallot.MacroPeg.CBV.LeadingReplayStarExamples
open LeadingReplayStar
open OriginControlNormalization (Leaf)
open ReplayControlFusion (Plan)
abbrev Arg := RecursiveArgumentCompiler.Expr

def rootArgument : Arg := .star (.user 2 (.lit ['a','a']))
def rootBody : Arg := .seq (.lit ['@']) (.seq (.user 1 rootArgument) (.seq (.lit ['?']) (.param 0)))
def loopBody : Arg := .seq (.lit ['#']) (.user 3 (.seq (.param 0) (.param 0)))
def loopTail : Arg := .seq (.lit ['$']) (.param 0)
def chunkBody : Arg := .alt (.user 2 (.param 0)) (.lit [])
def users : List User := [
  .control ⟨[⟨some [],rootBody⟩],.leaf 0,none⟩,
  .repeated ['a'] loopBody loopTail,
  .control ⟨[⟨some ['a'],chunkBody⟩],.leaf 0,none⟩,
  .control ⟨[⟨some [],.seq (.lit ['!']) (.param 0)⟩],.leaf 0,none⟩]
def entry : Arg := .user 0 (.lit ['a','a'])
def w : List Char := List.replicate 6 'a'
def child : List Char := List.replicate 12 'a'
def replayWord : List Char := ['a']++w
def blockWord : List Char := replayWord++['#']++child++['!']++child
def good : List Char := "aa@".toList++blockWord++replayWord++['$']++w++"?aa".toList
def deep : List Char := "aa@".toList++blockWord++blockWord++replayWord++['$']++w++"?aa".toList
def shortChild : List Char := "aa@".toList++replayWord++['#']++child++['!']++List.replicate 11 'a'++['$']++w++"?aa".toList
def shortParent : List Char := "aa@".toList++blockWord++replayWord++['$']++List.replicate 5 'a'++"?aa".toList

theorem valid : Valid [] users := by
  have hlen : ∀ us : List ContinuationFamily.User, (ContinuationFamily.specs us).length=us.length :=
    fun us => ContinuationFamily.emit_length 0 us
  simp [Valid,ContinuationFamily.Valid,ContinuationFamily.Shapes,ContinuationFamily.User.Shape,
    users,converted,User.toControl,
    OriginControlNormalization.LeavesValid,OriginControlNormalization.Valid,OriginControlNormalization.Closed,
    Plan.All,rootArgument,rootBody,loopBody,loopTail,chunkBody,replay,hlen]


theorem entry_valid : OriginControlNormalization.Valid [] (specs users) entry := by
  have hlen : (specs users).length=4 := (ContinuationFamily.emit_length 0 (converted users)).trans rfl
  simp [entry,OriginControlNormalization.Valid,hlen]

/-- A six-character capture is replayed inside the leading star. Each loop
recaptures twelve characters in a different user; parent values survive return. -/
theorem source_execution :
    evV (sourceGrammar [] users) good .callByValuePar (tblV (sourceGrammar [] users) good .callByValuePar 20) []
      (sourceRender [] users entry) good.length=some (some 0) ∧
    evV (sourceGrammar [] users) deep .callByValuePar (tblV (sourceGrammar [] users) deep .callByValuePar 20) []
      (sourceRender [] users entry) deep.length=some (some 0) ∧
    evV (sourceGrammar [] users) shortChild .callByValuePar (tblV (sourceGrammar [] users) shortChild .callByValuePar 20) []
      (sourceRender [] users entry) shortChild.length=some none ∧
    evV (sourceGrammar [] users) shortParent .callByValuePar (tblV (sourceGrammar [] users) shortParent .callByValuePar 20) []
      (sourceRender [] users entry) shortParent.length=some none := by decide +kernel

theorem translated_observations (x : List Char) (rest : Option (List Char)) :
    SObs (sourceGrammar [] users) .callByValuePar (sourceRender [] users entry) x rest ↔
    SObs (targetGrammar [] users) .callByValueSeq (targetRender [] users entry) x rest :=
  observations_iff [] (by simp [RegularCaptureProduct.Valid]) users valid entry entry_valid x rest

/-- Omitting the final negative test accepts after one a, although the
original greedy star consumes ab and then fails its final a. -/
theorem stop_required :
    evV ⟨[]⟩ "ab#".toList .callByValuePar (fun _ _ => []) [['a']]
      (.seq (.star (.seq (.param 0) (.lit ['b']))) (.param 0)) 3=some none ∧
    evV ⟨[]⟩ "ab#".toList .callByValuePar (fun _ _ => []) [['a']]
      (.seq (.param 0) (.star (.seq (.lit ['b']) (.param 0)))) 3=some (some 2) ∧
    evV ⟨[]⟩ "ab#".toList .callByValuePar (fun _ _ => []) [['a']]
      (.seq (.param 0) (.seq (.star (.seq (.lit ['b']) (.param 0))) (.notP (.lit ['b'])))) 3=some none := by decide +kernel

/-- Empty replay and empty loop bodies remain undefined on both sides. -/
theorem empty_loop :
    evV ⟨[]⟩ ['#'] .callByValuePar (fun _ _ => []) [[]]
      (.seq (.star (.seq (.param 0) (.lit []))) (.param 0)) 1=none ∧
    evV ⟨[]⟩ ['#'] .callByValuePar (fun _ _ => []) [[]]
      (.seq (.param 0) (.seq (.star (.seq (.lit []) (.param 0))) (.notP (.lit [])))) 1=none := by decide +kernel


/-- Empty capture is allowed when B supplies the progress in each iteration. -/
theorem empty_capture_progress :
    evV ⟨[]⟩ "aaa#".toList .callByValuePar (fun _ _ => []) [[]]
      (.seq (.star (.seq (.param 0) (.lit ['a']))) (.param 0)) 4=some (some 1) ∧
    evV ⟨[]⟩ "aaa#".toList .callByValuePar (fun _ _ => []) [[]]
      (.seq (.param 0) (.seq (.star (.seq (.lit ['a']) (.param 0))) (.notP (.lit ['a'])))) 4=some (some 1) := by decide +kernel


theorem translated_execution :
    SObs (targetGrammar [] users) .callByValueSeq (targetRender [] users entry) good (some []) ∧
    SObs (targetGrammar [] users) .callByValueSeq (targetRender [] users entry) deep (some []) ∧
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
  exact ⟨accept good source_execution.1,accept deep source_execution.2.1,
    reject shortChild source_execution.2.2.1,reject shortParent source_execution.2.2.2⟩

end Shallot.MacroPeg.CBV.LeadingReplayStarExamples
