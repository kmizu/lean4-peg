import MacroPeg.CBV.HeterogeneousProfiledRecursion

/-! Greedy retained-word repetition inside newly captured arguments. -/
namespace Shallot.MacroPeg.CBV.WordStarExamples
open HeterogeneousProfiledRecursion
open RegularCaptureProduct (Node)

theorem greedy_filter_execution :
    let D := PeriodicCaptureMachine.machine "ab".toList
    let E := ["aba".toList]
    let S := E.map (CaptureTransitionProfile.profile D)
    let g : MGrammar := ⟨[]⟩
    let T : ClockFreezing.Table := fun _ _ => []
    let x := "abaaba#".toList
    evV g x .callByValueSeq T E (.star (.param 0)) x.length=some (some 1) ∧
    evV g x .callByValueSeq T E (WordStarFilter.filter D S (.param 0) 0 1) x.length=some none ∧
    evV g x .callByValueSeq T E (WordStarFilter.filter D S (.param 0) 0 2) x.length=some (some 1) ∧
    evV g ['#'] .callByValueSeq T [[]] (WordStarFilter.filter D [CaptureTransitionProfile.profile D []] (.param 0) 0 0) 1=none ∧
    evV g ['#'] .callByValueSeq T [] (WordStarFilter.filter D [] (.param 0) 0 0) 1=some (some 1) := by
  decide +kernel

def nodes : List Node := [.lit "abab".toList]
def body0 : MExp := .seq (.lit ['#']) (.seq (.param 0)
  (.alt (.seq (.lit ['!']) (.seq (.call 1 []) (.seq (.lit ['?']) (.param 0)))) .eps))
def body1 : MExp := .seq (.lit ['@']) (.param 0)
def users : List User := [⟨.helper 0,"ab".toList,body0⟩,⟨.star (.param 0),"ab".toList,body1⟩]
def entry : MExp := .seq (.call 0 []) (.notP .any)
def input : List Char := "ababab#abab!ababababab@abababab?abab".toList
def bad : List Char := "ababab#abab!ababababab@abab?abab".toList

theorem nodes_valid : RegularCaptureProduct.Valid nodes := by simp [RegularCaptureProduct.Valid,nodes]
theorem users_valid : Valid nodes users := by
  simp [Valid,users,nodes,DependentCaptureFilter.Valid]

/-- The parent retains abab; its child's argument greedily captures two
copies, abababab, and the parent still uses abab after return. -/
theorem source_execution :
    evV (parGrammar nodes users) input .callByValuePar (tblV (parGrammar nodes users) input .callByValuePar 18) []
        (parRender nodes users entry) input.length=some (some 0) ∧
    evV (parGrammar nodes users) bad .callByValuePar (tblV (parGrammar nodes users) bad .callByValuePar 18) []
        (parRender nodes users entry) bad.length=some none := by
  decide +kernel

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

end Shallot.MacroPeg.CBV.WordStarExamples
