import MacroPeg.CBV.ContinuationFamily

namespace Shallot.MacroPeg.CBV.ContinuationFamilyExamples
open ContinuationFamily
open ReplayControlFusion (Plan)
open OriginControlNormalization (Leaf)
abbrev Arg := RecursiveArgumentCompiler.Expr

def parentLeaves : List Leaf := [⟨some [],.lit []⟩,⟨some [],.lit ['b']⟩,⟨some ['Z'],.lit []⟩]
def parentPlan : Plan := .alt (.guard (.notP (.leaf 2)) (.leaf 0)) (.leaf 1)
def parentTail : Arg := .seq (.lit ['#']) (.seq (.user 1 (.seq (.param 0) (.param 0)))
  (.seq (.lit ['?']) (.param 0)))
def childLeaves : List Leaf := [⟨some ['a'],.alt (.user 1 (.param 0)) (.lit [])⟩]
def rootLeaves : List Leaf := [⟨none,.seq (.lit ['a']) (.seq (.user 3 (.lit ['a'])) (.user 0 (.lit ['a','a'])))⟩]
def users : List User := [⟨parentLeaves,parentPlan,some parentTail⟩,⟨childLeaves,.leaf 0,some (.lit [])⟩,
  ⟨rootLeaves,.leaf 0,some (.lit ['!'])⟩,⟨[⟨some ['Z'],.lit []⟩],.notP (.leaf 0),none⟩]
def entry : Arg := .user 2 (.lit [])
def good : List Char := "aaa#aaaaa?aa!".toList
def deep : List Char := "aaa#aaaaaaaaaa?aa!".toList
def badChoice : List Char := "aaab#aaaaa?aa!".toList
def shortChild : List Char := "aaa#aaaa?aa!".toList
def shortParent : List Char := "aaa#aaaaa?a!".toList

theorem shapes : Shapes users := by
  simp [Shapes,User.Shape,users,parentPlan,LeafContinuation.Consumer,Plan.All,parentLeaves,childLeaves,rootLeaves]

theorem valid : Valid [] users := by
  refine ⟨shapes,?_⟩
  have hlen : ∀ us : List User, (specs us).length=us.length := fun us => emit_length 0 us
  simp [users,parentLeaves,childLeaves,rootLeaves,OriginControlNormalization.LeavesValid,
    OriginControlNormalization.Valid,parentTail,OriginControlNormalization.Closed,hlen]

theorem entry_valid : OriginControlNormalization.Valid [] (specs users) entry := by
  have hlen : (specs users).length=4 := by rw [specs,emit_length]; rfl
  simp [entry,OriginControlNormalization.Valid,hlen]

/-- Distinct tails for parent, child, and closed root; the child consumes a
nonempty shift and a fresh four-character capture, then the parent replays aa. -/
theorem source_execution :
    evV (sourceGrammar [] users) good .callByValuePar (tblV (sourceGrammar [] users) good .callByValuePar 10) []
      (sourceRender [] users entry) good.length=some (some 0) ∧
    evV (sourceGrammar [] users) deep .callByValuePar (tblV (sourceGrammar [] users) deep .callByValuePar 10) []
      (sourceRender [] users entry) deep.length=some (some 0) ∧
    evV (sourceGrammar [] users) badChoice .callByValuePar (tblV (sourceGrammar [] users) badChoice .callByValuePar 10) []
      (sourceRender [] users entry) badChoice.length=some none ∧
    evV (sourceGrammar [] users) shortChild .callByValuePar (tblV (sourceGrammar [] users) shortChild .callByValuePar 10) []
      (sourceRender [] users entry) shortChild.length=some none ∧
    evV (sourceGrammar [] users) shortParent .callByValuePar (tblV (sourceGrammar [] users) shortParent .callByValuePar 10) []
      (sourceRender [] users entry) shortParent.length=some none := by
  decide +kernel

/-- This is a grammar-changing Par-to-Seq theorem on every original input;
the concrete source runs above are not used as a language equivalence oracle. -/
theorem translated_observations (x : List Char) (rest : Option (List Char)) :
    SObs (sourceGrammar [] users) .callByValuePar (sourceRender [] users entry) x rest ↔
    SObs (targetGrammar [] users) .callByValueSeq (targetRender [] users entry) x rest :=
  observations_iff [] (by simp [RegularCaptureProduct.Valid]) users valid entry entry_valid x rest


/-- A control-only user shares the family with consuming users. It captures
one character but returns at the original position after its negative test. -/
theorem test_returns_origin :
    evV (sourceGrammar [] users) ['a','a'] .callByValuePar (tblV (sourceGrammar [] users) ['a','a'] .callByValuePar 1) []
      (sourceRender [] users (.user 3 (.lit ['a']))) 2=some (some 2) := by decide +kernel

theorem translated_execution :
    SObs (targetGrammar [] users) .callByValueSeq (targetRender [] users entry) good (some []) ∧
    SObs (targetGrammar [] users) .callByValueSeq (targetRender [] users entry) deep (some []) ∧
    SObs (targetGrammar [] users) .callByValueSeq (targetRender [] users entry) badChoice none ∧
    SObs (targetGrammar [] users) .callByValueSeq (targetRender [] users entry) shortChild none ∧
    SObs (targetGrammar [] users) .callByValueSeq (targetRender [] users entry) shortParent none := by
  have accept (x : List Char)
      (hv : evV (sourceGrammar [] users) x .callByValuePar (tblV (sourceGrammar [] users) x .callByValuePar 10) []
        (sourceRender [] users entry) x.length=some (some 0)) :
      SObs (targetGrammar [] users) .callByValueSeq (targetRender [] users entry) x (some []) := by
    apply (translated_observations x (some [])).mp
    obtain ⟨o,hd,ho⟩ := evV_derives (source_firstOrder [] users) (by decide)
      (OriginControlNormalization.render_firstOrder [] (leaves users) (specs users) entry) 10 (Nat.le_refl x.length) hv
    rw [sfx_self] at hd
    obtain ⟨t,rest,rfl,hlen⟩ := obsR_ok ho
    have hr : rest=[] := List.length_eq_zero_iff.mp hlen
    subst rest
    exact ⟨_,hd,rfl⟩
  have reject (x : List Char)
      (hv : evV (sourceGrammar [] users) x .callByValuePar (tblV (sourceGrammar [] users) x .callByValuePar 10) []
        (sourceRender [] users entry) x.length=some none) :
      SObs (targetGrammar [] users) .callByValueSeq (targetRender [] users entry) x none := by
    apply (translated_observations x none).mp
    obtain ⟨o,hd,ho⟩ := evV_derives (source_firstOrder [] users) (by decide)
      (OriginControlNormalization.render_firstOrder [] (leaves users) (specs users) entry) 10 (Nat.le_refl x.length) hv
    rw [sfx_self] at hd
    rw [obsR_fail ho] at hd
    exact ⟨_,hd,rfl⟩
  exact ⟨accept good source_execution.1,accept deep source_execution.2.1,
    reject badChoice source_execution.2.2.1,reject shortChild source_execution.2.2.2.1,
    reject shortParent source_execution.2.2.2.2⟩

end Shallot.MacroPeg.CBV.ContinuationFamilyExamples
