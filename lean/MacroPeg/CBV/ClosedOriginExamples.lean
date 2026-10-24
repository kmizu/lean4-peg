import MacroPeg.CBV.OriginControlNormalization

/-! Capture-independent consuming branches in the same recursive family as
retained-dependent replay branches and recursive captured arguments. -/
namespace Shallot.MacroPeg.CBV.ClosedOriginExamples
open OriginControlNormalization
open ReplayControlFusion (Plan)
abbrev Arg := RecursiveArgumentCompiler.Expr

def body0 : Arg := .alt (.user 0 (.param 0)) (.lit [])
def rootArgument : Arg := .star (.user 0 (.lit ['a','a']))
def body1 : Arg := .seq (.lit ['#']) (.seq (.param 0) (.seq (.lit ['?']) (.param 0)))
def closedBody : Arg := .seq (.lit ['a']) (.seq (.user 0 (.lit ['a','a']))
  (.seq (.star (.lit ['a'])) (.seq (.lit ['!']) (.user 1 (.lit ['a'])))))
def body3 : Arg := .seq (.lit ['#']) (.seq (.param 0) (.seq (.lit ['!'])
  (.seq (.user 1 rootArgument) (.seq (.lit ['?']) (.param 0)))))
def leaves : List Leaf := [⟨some ['a'],body0⟩,⟨some [],body1⟩,⟨none,closedBody⟩,⟨some ['a'],body3⟩]
def specs : List Plan := [.leaf 0,.alt (.leaf 1) (.leaf 2),.leaf 3]
def entry : Arg := .user 2 (.lit ['a'])
def fallbackInput : List Char := "aa#a!".toList++List.replicate 8 'a'++"!a#a?a?a".toList
def replayInput : List Char := "aa#a!".toList++List.replicate 6 'a'++['#']++List.replicate 6 'a'++['?']++
  List.replicate 6 'a'++"?a".toList
def bad : List Char := "aa#a!".toList++List.replicate 8 'a'++"!a#a?b?a".toList

theorem plans_valid : PlansValid leaves specs := by simp [PlansValid,leaves,specs,Plan.All]
theorem leaves_valid : LeavesValid [] leaves specs := by
  simp [LeavesValid,leaves,OriginControlNormalization.Closed,closedBody,body0,body1,body3,rootArgument,Valid,specs]
theorem entry_valid : Valid [] specs entry := by simp [Valid,specs,entry]

/-- The closed fallback begins at the original origin, consumes a literal,
calls a recursive capture parser, repeats literals, then recaptures into the
replay user. The outer parent value is used again after return. -/
theorem source_execution :
    evV (sourceGrammar [] leaves specs) fallbackInput .callByValuePar (tblV (sourceGrammar [] leaves specs) fallbackInput .callByValuePar 28) []
      (render [] leaves specs entry) fallbackInput.length=some (some 0) ∧
    evV (sourceGrammar [] leaves specs) replayInput .callByValuePar (tblV (sourceGrammar [] leaves specs) replayInput .callByValuePar 28) []
      (render [] leaves specs entry) replayInput.length=some (some 0) ∧
    evV (sourceGrammar [] leaves specs) bad .callByValuePar (tblV (sourceGrammar [] leaves specs) bad .callByValuePar 28) []
      (render [] leaves specs entry) bad.length=some none := by
  decide +kernel

theorem translated_observations :
    SObs (targetGrammar [] leaves specs) .callByValueSeq (targetRender [] leaves specs entry) fallbackInput (some []) ∧
    SObs (targetGrammar [] leaves specs) .callByValueSeq (targetRender [] leaves specs entry) replayInput (some []) ∧
    SObs (targetGrammar [] leaves specs) .callByValueSeq (targetRender [] leaves specs entry) bad none := by
  have hn : RegularCaptureProduct.Valid [] := by simp [RegularCaptureProduct.Valid]
  have finish (x : List Char)
      (hv : evV (sourceGrammar [] leaves specs) x .callByValuePar (tblV (sourceGrammar [] leaves specs) x .callByValuePar 28) []
        (render [] leaves specs entry) x.length=some (some 0)) :
      SObs (targetGrammar [] leaves specs) .callByValueSeq (targetRender [] leaves specs entry) x (some []) := by
    apply (observations_iff [] hn leaves specs plans_valid leaves_valid entry entry_valid x (some [])).mp
    obtain ⟨o,hd,ho⟩ := evV_derives (source_firstOrder [] leaves specs) (by decide)
      (render_firstOrder [] leaves specs entry) 28 (Nat.le_refl x.length) hv
    rw [sfx_self] at hd
    obtain ⟨t,rest,rfl,hlen⟩ := obsR_ok ho
    have hr : rest=[] := List.length_eq_zero_iff.mp hlen
    subst rest
    exact ⟨_,hd,rfl⟩
  refine ⟨finish fallbackInput source_execution.1,finish replayInput source_execution.2.1,?_⟩
  apply (observations_iff [] hn leaves specs plans_valid leaves_valid entry entry_valid bad none).mp
  obtain ⟨o,hd,ho⟩ := evV_derives (source_firstOrder [] leaves specs) (by decide)
    (render_firstOrder [] leaves specs entry) 28 (Nat.le_refl bad.length) source_execution.2.2
  rw [sfx_self] at hd
  rw [obsR_fail ho] at hd
  exact ⟨_,hd,rfl⟩

/-- Reusing the original six-character argument for the closed leaf advances
the core entry too far. Its correct empty argument preserves the origin. -/
theorem empty_handoff_required :
    let x := List.replicate 8 'a'++"!a#a?a".toList
    let g := coreGrammar [] leaves specs
    let T := tblV g x .callByValuePar 28
    evV g x .callByValuePar T []
      (RecursiveArgumentCompiler.parRender [] (coreUsers leaves specs) (.user 2 (.lit []))) x.length=some (some 0) ∧
    evV g x .callByValuePar T []
      (RecursiveArgumentCompiler.parRender [] (coreUsers leaves specs) (.user 2 (normalize leaves specs rootArgument))) x.length=some none := by
  decide +kernel

end Shallot.MacroPeg.CBV.ClosedOriginExamples
