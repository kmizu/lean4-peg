import MacroPeg.CBV.HeterogeneousProfiledRecursion

/-! Nonuniform fresh captures and nested retained-dependent repetitions. -/
namespace Shallot.MacroPeg.CBV.GeneralStarExamples
open HeterogeneousProfiledRecursion
open RegularCaptureProduct (Node)
abbrev Arg := DependentCaptureFilter.Expr

def parity : RegularCaptureProduct.Machine := ⟨2,fun q c => if c='b' then 1-q else q⟩
def helperNodes : List Node := [.seq 1 2,.lit ['a'],.star 3,.lit ['b']]
def ac : Arg := .seq (.param 0) (.lit ['c'])
def varying : Arg := .star (.alt (.seq ac (.star ac)) (.helper 0))

/-- The actual iterations are a, ab, abb, and acac. Their lengths and state
transitions differ; acac itself uses a retained-dependent nested star. -/
theorem varying_capture_execution :
    let g := RegularCaptureProduct.grammar helperNodes parity
    let x := "aababbacac#".toList
    let E := [['a']]
    let S := E.map (CaptureTransitionProfile.profile parity)
    let T := tblV g x .callByValueSeq 18
    evV g x .callByValueSeq T E (DependentCaptureFilter.render varying) x.length=some (some 1) ∧
    evV g x .callByValueSeq T E (DependentCaptureFilter.filter helperNodes parity S varying 0 1) x.length=some (some 1) ∧
    evV g x .callByValueSeq T E (DependentCaptureFilter.filter helperNodes parity S varying 0 0) x.length=some none ∧
    evV g ['#'] .callByValueSeq T E (DependentCaptureFilter.filter helperNodes parity S (.star (.star (.param 0))) 0 0) 1=none := by
  decide +kernel

def nodes : List Node := [.lit "abab".toList,.lit "ababab".toList]
def look : Arg := .notP (.notP (.lit "ab".toList))
def argument : Arg := .star (.alt (.seq (.helper 1) look) (.seq (.param 0) look))
def body0 : MExp := .seq (.lit ['#']) (.seq (.param 0)
  (.alt (.seq (.lit ['!']) (.seq (.call 1 []) (.seq (.lit ['?']) (.param 0)))) .eps))
def body1 : MExp := .seq (.lit ['@']) (.param 0)
def users : List User := [⟨.helper 0,"ab".toList,body0⟩,⟨argument,"ab".toList,body1⟩]
def entry : MExp := .seq (.call 0 []) (.notP .any)
def input : List Char := "ababab#abab!abababababab@ababababab?abab".toList
def bad : List Char := "ababab#abab!abababababab@abab?abab".toList

theorem nodes_valid : RegularCaptureProduct.Valid nodes := by simp [RegularCaptureProduct.Valid,nodes]
theorem users_valid : Valid nodes users := by
  simp [Valid,users,nodes,argument,look,DependentCaptureFilter.Valid]

/-- A fresh six-character helper capture and the retained four-character
value are different iterations in the child's ten-character new capture. -/
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

end Shallot.MacroPeg.CBV.GeneralStarExamples
