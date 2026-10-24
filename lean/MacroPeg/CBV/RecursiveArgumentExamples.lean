import MacroPeg.CBV.RecursiveArgumentCorrespondence

/-! Recursive users inside retained-dependent arguments, including repetition,
child captures, and reuse of the unchanged ancestor value after return. -/
namespace Shallot.MacroPeg.CBV.RecursiveArgumentExamples
open RecursiveArgumentCompiler
open RecursiveArgumentCorrespondence (observations_iff evaluator_eq)
abbrev Arg := RecursiveArgumentCompiler.Expr

def body0 : Arg := .alt (.user 0 (.param 0)) (.lit [])
def argument : Arg := .star (.user 0 (.param 0))
def body1 : Arg := .seq (.lit ['#']) (.seq (.param 0)
  (.alt (.notP (.lit ['!']))
    (.seq (.lit ['!']) (.seq (.user 1 argument) (.seq (.lit ['?']) (.param 0))))))
def users : List User := [⟨['a'],body0⟩,⟨['a','a'],body1⟩]
def entry : Arg := .user 1 (.star (.user 0 (.lit ['a','a'])))
def input : List Char := List.replicate 8 'a'++['#']++List.replicate 6 'a'++['!']++
  List.replicate 16 'a'++['#']++List.replicate 14 'a'++['?']++List.replicate 6 'a'
def badChild : List Char := List.replicate 8 'a'++['#']++List.replicate 6 'a'++['!']++
  List.replicate 16 'a'++['#']++List.replicate 6 'a'++['?']++List.replicate 6 'a'
def badParent : List Char := List.replicate 8 'a'++['#']++List.replicate 6 'a'++['!']++
  List.replicate 16 'a'++['#']++List.replicate 14 'a'++['?']++List.replicate 2 'a'

theorem users_valid : UsersValid [] users := by
  simp [UsersValid,users,body0,body1,argument,RecursiveArgumentCompiler.Valid]
theorem entry_valid : RecursiveArgumentCompiler.Valid [] users entry := by
  simp [RecursiveArgumentCompiler.Valid,users,entry]

/-- The recursive argument first captures six a's, then a child captures
fourteen a's by calling the retained-dependent recursive user under star. -/
theorem source_execution :
    evV (parGrammar [] users) input .callByValuePar (tblV (parGrammar [] users) input .callByValuePar 24) []
      (parRender [] users entry) input.length=some (some 0) ∧
    evV (parGrammar [] users) badChild .callByValuePar (tblV (parGrammar [] users) badChild .callByValuePar 24) []
      (parRender [] users entry) badChild.length=some none ∧
    evV (parGrammar [] users) badParent .callByValuePar (tblV (parGrammar [] users) badParent .callByValuePar 24) []
      (parRender [] users entry) badParent.length=some none := by
  decide +kernel

/-- Generated Seq observations follow from the full compiler theorem; no
bounded execution of the large profile/product grammar is substituted. -/
theorem translated_observations :
    SObs (seqGrammar [] users) .callByValueSeq (plain [] users [] entry) input (some []) ∧
    SObs (seqGrammar [] users) .callByValueSeq (plain [] users [] entry) badChild none ∧
    SObs (seqGrammar [] users) .callByValueSeq (plain [] users [] entry) badParent none := by
  have hnodes : RegularCaptureProduct.Valid [] := by simp [RegularCaptureProduct.Valid]
  constructor
  · apply (observations_iff [] hnodes users users_valid entry entry_valid input (some [])).mp
    obtain ⟨o,hd,ho⟩ := evV_derives (par_firstOrder [] users) (by decide)
      (parRender_firstOrder [] users entry) 24 (Nat.le_refl input.length) source_execution.1
    rw [sfx_self] at hd
    obtain ⟨t,rest,rfl,hlen⟩ := obsR_ok ho
    have hr : rest=[] := List.length_eq_zero_iff.mp hlen
    subst rest
    exact ⟨_,hd,rfl⟩
  · constructor
    · apply (observations_iff [] hnodes users users_valid entry entry_valid badChild none).mp
      obtain ⟨o,hd,ho⟩ := evV_derives (par_firstOrder [] users) (by decide)
        (parRender_firstOrder [] users entry) 24 (Nat.le_refl badChild.length) source_execution.2.1
      rw [sfx_self] at hd
      rw [obsR_fail ho] at hd
      exact ⟨_,hd,rfl⟩
    · apply (observations_iff [] hnodes users users_valid entry entry_valid badParent none).mp
      obtain ⟨o,hd,ho⟩ := evV_derives (par_firstOrder [] users) (by decide)
        (parRender_firstOrder [] users entry) 24 (Nat.le_refl badParent.length) source_execution.2.2
      rw [sfx_self] at hd
      rw [obsR_fail ho] at hd
      exact ⟨_,hd,rfl⟩

theorem empty_iteration_undefined (k : Nat) :
    evV (seqGrammar [] users) ['#'] .callByValueSeq (seqTable [] users ['#'] k) []
      (plain [] users [] (.user 1 (.star (.lit [])))) 1=none := by
  rw [evaluator_eq [] (by simp [RegularCaptureProduct.Valid]) users users_valid ['#'] k
    (.user 1 (.star (.lit []))) (by simp [RecursiveArgumentCompiler.Valid,users]) [] []
    (DependentCaptureFilter.environment_accurate (machine users) []) 1 (by decide)]
  have hrule : ruleAtM (parGrammar [] users).rules 1=
      some ⟨1,.seq (.seq (.lit ['a','a']) (.param 0)) (parRender [] users body1)⟩ :=
    source_rule [] users 1 ⟨['a','a'],body1⟩ rfl
  rw [show parRender [] users (.user 1 (.star (.lit [])))=
    .call 1 [.star (.lit [])] from rfl,evV_call_par hrule rfl (by decide)]
  have hstar : evV (parGrammar [] users) ['#'] .callByValuePar (parTable [] users ['#'] k) [] (.star (.lit [])) 1=none :=
    evStar_stuck (j := 1) rfl (by omega)
  simp only [evParArgs,hstar]

end Shallot.MacroPeg.CBV.RecursiveArgumentExamples
