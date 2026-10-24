import MacroPeg.CBV.OriginControlNormalization

/-! Recursive arguments with capture-dependent origin control and rollback. -/
namespace Shallot.MacroPeg.CBV.OriginControlExamples
open OriginControlNormalization
open ReplayControlFusion (Plan)
abbrev Arg := RecursiveArgumentCompiler.Expr

def body0 : Arg := .alt (.user 0 (.param 0)) (.lit [])
def argument : Arg := .star (.user 0 (.param 0))
def body1 : Arg := .seq (.lit ['#']) (.seq (.param 0)
  (.alt (.notP (.lit ['!']))
    (.seq (.lit ['!']) (.seq (.user 1 argument) (.seq (.lit ['?']) (.param 0))))))
def leaves : List Leaf := [⟨['a'],body0⟩,⟨['a','a'],body1⟩,⟨['a'],.lit []⟩,⟨['a'],.lit ['?']⟩]
def specs : List Plan := [.leaf 0,.alt (.guard (.leaf 2) (.leaf 1)) (.notP (.leaf 3))]
def rootArgument : Arg := .star (.user 0 (.lit ['a','a']))
def entry : Arg := .seq (.user 1 rootArgument) (.lit ['$'])
def originEntry : Arg := .seq (.user 1 rootArgument) (.lit ['a'])
def input : List Char := List.replicate 8 'a'++['#']++List.replicate 6 'a'++['!']++
  List.replicate 16 'a'++['#']++List.replicate 14 'a'++['?']++List.replicate 6 'a'++['$']
def badChild : List Char := List.replicate 8 'a'++['#']++List.replicate 6 'a'++['!']++
  List.replicate 16 'a'++['#']++List.replicate 6 'a'++['?']++List.replicate 6 'a'++['$']
def badParent : List Char := List.replicate 8 'a'++['#']++List.replicate 6 'a'++['!']++
  List.replicate 16 'a'++['#']++List.replicate 14 'a'++['?']++List.replicate 2 'a'++['$']

theorem plans_valid : PlansValid leaves specs := by simp [PlansValid,leaves,specs,Plan.All]
theorem leaves_valid : LeavesValid [] leaves specs := by
  simp [LeavesValid,leaves,body0,body1,argument,Valid,specs]
theorem entry_valid : Valid [] specs entry := by simp [Valid,specs,entry,rootArgument]
theorem originEntry_valid : Valid [] specs originEntry := by simp [Valid,specs,originEntry,rootArgument]

/-- The successful branch keeps parent six / child fourteen / parent six.
The same original control user can roll back to its origin after failure. -/
theorem source_execution :
    evV (sourceGrammar [] leaves specs) input .callByValuePar (tblV (sourceGrammar [] leaves specs) input .callByValuePar 28) []
      (render [] leaves specs entry) input.length=some (some 0) ∧
    evV (sourceGrammar [] leaves specs) badChild .callByValuePar (tblV (sourceGrammar [] leaves specs) badChild .callByValuePar 28) []
      (render [] leaves specs entry) badChild.length=some none ∧
    evV (sourceGrammar [] leaves specs) badParent .callByValuePar (tblV (sourceGrammar [] leaves specs) badParent .callByValuePar 28) []
      (render [] leaves specs entry) badParent.length=some none := by
  decide +kernel

/-- The argument captures six characters, but the whole caller returns after
one character: its capture-dependent fallback restores the original position. -/
theorem before_capture_endpoint :
    evV (sourceGrammar [] leaves specs) badChild .callByValuePar (tblV (sourceGrammar [] leaves specs) badChild .callByValuePar 28) []
      (render [] leaves specs rootArgument) badChild.length=some (some (badChild.length-6)) ∧
    evV (sourceGrammar [] leaves specs) badChild .callByValuePar (tblV (sourceGrammar [] leaves specs) badChild .callByValuePar 28) []
      (render [] leaves specs originEntry) badChild.length=some (some (badChild.length-1)) := by
  decide +kernel

theorem translated_observations :
    SObs (targetGrammar [] leaves specs) .callByValueSeq (targetRender [] leaves specs entry) input (some []) ∧
    SObs (targetGrammar [] leaves specs) .callByValueSeq (targetRender [] leaves specs entry) badChild none ∧
    SObs (targetGrammar [] leaves specs) .callByValueSeq (targetRender [] leaves specs entry) badParent none := by
  have hn : RegularCaptureProduct.Valid [] := by simp [RegularCaptureProduct.Valid]
  constructor
  · apply (observations_iff [] hn leaves specs plans_valid leaves_valid entry entry_valid input (some [])).mp
    obtain ⟨o,hd,ho⟩ := evV_derives (source_firstOrder [] leaves specs) (by decide)
      (render_firstOrder [] leaves specs entry) 28 (Nat.le_refl input.length) source_execution.1
    rw [sfx_self] at hd
    obtain ⟨t,rest,rfl,hlen⟩ := obsR_ok ho
    have hr : rest=[] := List.length_eq_zero_iff.mp hlen
    subst rest
    exact ⟨_,hd,rfl⟩
  · constructor
    · apply (observations_iff [] hn leaves specs plans_valid leaves_valid entry entry_valid badChild none).mp
      obtain ⟨o,hd,ho⟩ := evV_derives (source_firstOrder [] leaves specs) (by decide)
        (render_firstOrder [] leaves specs entry) 28 (Nat.le_refl badChild.length) source_execution.2.1
      rw [sfx_self] at hd
      rw [obsR_fail ho] at hd
      exact ⟨_,hd,rfl⟩
    · apply (observations_iff [] hn leaves specs plans_valid leaves_valid entry entry_valid badParent none).mp
      obtain ⟨o,hd,ho⟩ := evV_derives (source_firstOrder [] leaves specs) (by decide)
        (render_firstOrder [] leaves specs entry) 28 (Nat.le_refl badParent.length) source_execution.2.2
      rw [sfx_self] at hd
      rw [obsR_fail ho] at hd
      exact ⟨_,hd,rfl⟩

theorem translated_before_capture :
    SObs (targetGrammar [] leaves specs) .callByValueSeq (targetRender [] leaves specs originEntry)
      badChild (some (sfx badChild (badChild.length-1))) := by
  apply (observations_iff [] (by simp [RegularCaptureProduct.Valid]) leaves specs plans_valid leaves_valid
    originEntry originEntry_valid badChild _).mp
  obtain ⟨o,hd,ho⟩ := evV_derives (source_firstOrder [] leaves specs) (by decide)
    (render_firstOrder [] leaves specs originEntry) 28 (Nat.le_refl badChild.length) before_capture_endpoint.2
  obtain ⟨t,rest,rfl,hlen⟩ := obsR_ok ho
  have hsuf := rest_eq_sfx' hd
  rw [hlen] at hsuf
  rw [sfx_self] at hd
  exact ⟨_,hd,by rw [hsuf]; rfl⟩

/-- Omitting the argument guard would let a failed argument become success
through a negative branch of the expanded source control tree. -/
theorem unguarded_false_positive :
    evV (sourceGrammar [] leaves specs) ['a'] .callByValuePar (tblV (sourceGrammar [] leaves specs) ['a'] .callByValuePar 0) []
      (render [] leaves specs (.user 1 (.lit ['Z']))) 1=some none ∧
    evV (coreGrammar [] leaves specs) ['a'] .callByValuePar (tblV (coreGrammar [] leaves specs) ['a'] .callByValuePar 0) []
      (RecursiveArgumentCompiler.parRender [] (coreUsers leaves specs)
        (expand (fun j => .user j (.lit ['Z'])) (.alt (.guard (.leaf 2) (.leaf 1)) (.notP (.leaf 3))))) 1=some (some 1) ∧
    evV (coreGrammar [] leaves specs) ['a'] .callByValuePar (tblV (coreGrammar [] leaves specs) ['a'] .callByValuePar 0) []
      (coreRender [] leaves specs (.user 1 (.lit ['Z']))) 1=some none := by
  decide +kernel

theorem source_undefined (k : Nat) :
    evV (sourceGrammar [] leaves specs) ['a'] .callByValuePar (tblV (sourceGrammar [] leaves specs) ['a'] .callByValuePar k) []
      (render [] leaves specs (.user 1 (.star (.lit [])))) 1=none := by
  have hrule : ruleAtM (sourceGrammar [] leaves specs).rules 1=some ⟨1,
      (Plan.alt (.guard (.leaf 2) (.leaf 1)) (.notP (.leaf 3))).exp (sourceLeaf [] leaves specs)⟩ :=
    source_rule [] leaves specs 1 _ rfl
  rw [show render [] leaves specs (.user 1 (.star (.lit [])))=.call 1 [.star (.lit [])] from rfl,
    evV_call_par hrule rfl (by decide)]
  have hstar : evV (sourceGrammar [] leaves specs) ['a'] .callByValuePar (tblV (sourceGrammar [] leaves specs) ['a'] .callByValuePar k) []
      (.star (.lit [])) 1=none := evStar_stuck (j := 1) rfl (by omega)
  simp only [evParArgs,hstar]

theorem target_undefined (rest : Option (List Char)) :
    ¬SObs (targetGrammar [] leaves specs) .callByValueSeq
      (targetRender [] leaves specs (.user 1 (.star (.lit [])))) ['a'] rest := by
  rw [←observations_iff [] (by simp [RegularCaptureProduct.Valid]) leaves specs plans_valid leaves_valid
    (.user 1 (.star (.lit []))) (by simp [Valid,specs]) ['a'] rest]
  intro h
  have he := (decideObsV_iff (source_firstOrder [] leaves specs) (by decide)
    (render_firstOrder [] leaves specs (.user 1 (.star (.lit [])))) ['a'] rest).mpr h
  unfold decideObsV at he
  simp only [List.length_cons,List.length_nil] at he
  rw [source_undefined] at he
  cases he

end Shallot.MacroPeg.CBV.OriginControlExamples
