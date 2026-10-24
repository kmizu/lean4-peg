import MacroPeg.CBV.HeterogeneousProfiledRecursion

/-! Distinct replay prefixes in one mutually recursive generated grammar. -/
namespace Shallot.MacroPeg.CBV.HeterogeneousReplayExamples
open HeterogeneousProfiledRecursion
open RegularCaptureProduct (Node)

def nodes : List Node := [.lit "aa".toList,.lit ['a']]
def body0 : MExp := .seq (.lit ['#']) (.seq (.param 0)
  (.alt (.seq (.lit ['!']) (.seq (.call 1 []) (.seq (.lit ['?']) (.param 0)))) .eps))
def body1 : MExp := .seq (.lit ['@']) (.seq (.param 0)
  (.alt (.seq (.lit ['%']) (.seq (.call 0 []) (.seq (.lit ['$']) (.param 0)))) .eps))
def users : List User := [⟨.helper 0,['a'],body0⟩,⟨.seq (.param 0) (.helper 1),"aa".toList,body1⟩]
def entry : MExp := .seq (.call 0 []) (.notP .any)
def input : List Char := "aaa#aa!aaaaa@aaa%aaa#aa$aaa?aa".toList
def bad : List Char := "aaa#aa!aaaaa@aaa%aaa#aa$aa?aa".toList

theorem nodes_valid : RegularCaptureProduct.Valid nodes := by simp [RegularCaptureProduct.Valid,nodes]
theorem users_valid : Valid nodes users := by simp [Valid,users,nodes,DependentCaptureFilter.Valid]

theorem joint_phase_execution :
    let shifts := ["ab".toList,"aab".toList]
    let P := CaptureTransitionProfile.profile (CaptureMachineFamily.machine shifts) "aaba".toList
    P[CaptureMachineFamily.start shifts 0]?.getD 0-CaptureMachineFamily.start shifts 0=2 ∧
      P[CaptureMachineFamily.start shifts 1]?.getD 0-CaptureMachineFamily.start shifts 1=1 := by
  decide +kernel

/-- The second rule uses shift aa, while the first uses shift a. It retains
its longer aaa capture after recapturing aa through the first rule. -/
theorem source_execution :
    evV (parGrammar nodes users) input .callByValuePar (tblV (parGrammar nodes users) input .callByValuePar 18) []
        (parRender nodes users entry) input.length=some (some 0) ∧
    evV (parGrammar nodes users) bad .callByValuePar (tblV (parGrammar nodes users) bad .callByValuePar 18) []
        (parRender nodes users entry) bad.length=some none := by
  decide +kernel

/-- The generated Seq grammar's observations follow from the unbounded
compiler theorem, not from a second finite-table experiment. -/
theorem translated_observations :
    SObs (seqGrammar nodes users) .callByValueSeq (seqRender nodes users [] entry) input (some []) ∧
      SObs (seqGrammar nodes users) .callByValueSeq (seqRender nodes users [] entry) bad none := by
  constructor
  · apply (observations_iff nodes nodes_valid users users_valid entry input (some [])).mp
    obtain ⟨o,hd,ho⟩ := evV_derives (par_firstOrder nodes users) (by decide)
      (parRender_firstOrder nodes users entry) 18 (Nat.le_refl input.length) source_execution.1
    rw [sfx_self] at hd
    obtain ⟨t,rest,rfl,hlen⟩ := obsR_ok ho
    have hr : rest=[] := List.length_eq_zero_iff.mp hlen
    subst rest
    exact ⟨_,hd,rfl⟩
  · apply (observations_iff nodes nodes_valid users users_valid entry bad none).mp
    obtain ⟨o,hd,ho⟩ := evV_derives (par_firstOrder nodes users) (by decide)
      (parRender_firstOrder nodes users entry) 18 (Nat.le_refl bad.length) source_execution.2
    rw [sfx_self] at hd
    rw [obsR_fail ho] at hd
    exact ⟨_,hd,rfl⟩

end Shallot.MacroPeg.CBV.HeterogeneousReplayExamples
