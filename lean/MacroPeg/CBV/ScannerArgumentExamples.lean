import MacroPeg.CBV.ScannerArgumentFusion

namespace Shallot.MacroPeg.CBV.ScannerArgumentExamples
open ScannerArgumentFusion
open ScannerCapturedArguments (Safe)
open NestedScannerArguments (accepts scan)

def alphabet : List Char := ['a','b']
def argument : MExp := .seq (.notP (.call 0 [.lit ['b']]))
  (.seq (.param 0) (.seq (.param 0) (.star (.lit ['b']))))
def tail : MExp := .seq (.lit ['#']) (.seq (.param 0)
  (.alt (.seq (.lit ['@']) (.seq (.call 0 [argument]) (.seq (.lit ['?']) (.param 0)))) (.lit ['!'])))
def tails : List MExp := [tail]
def entry : MExp := .call 0 [.lit ['a']]
def good : List Char := "abba#a@aabbbab#aabbb!?a".toList
def zeroFresh : List Char := "abba#a@aaaab#aa!?a".toList
def shortChild : List Char := "abba#a@aabbbab#aabb!?a".toList

theorem valid : Valid alphabet tails := by
  simp [Valid,tails,tail,argument,Supported,Safe,alphabet,accepts,Shallot.beqChar]
theorem entry_valid : Supported alphabet entry := by
  simp [entry,Supported,Safe,alphabet,accepts,Shallot.beqChar]

theorem source_execution :
    evV (grammar alphabet tails) good .callByValuePar
      (tblV (grammar alphabet tails) good .callByValuePar 8) [] entry good.length=some (some 0) ∧
    evV (grammar alphabet tails) zeroFresh .callByValuePar
      (tblV (grammar alphabet tails) zeroFresh .callByValuePar 8) [] entry zeroFresh.length=some (some 0) ∧
    evV (grammar alphabet tails) shortChild .callByValuePar
      (tblV (grammar alphabet tails) shortChild .callByValuePar 8) [] entry shortChild.length=some none := by decide +kernel

/-- At the child call, retained a is used twice and fresh b* adds bbb.
The child's scanner then consumes the remaining ab before replaying aabbb. -/
theorem fresh_capture :
    evV (grammar alphabet tails) "aabbbab#".toList .callByValuePar
      (tblV (grammar alphabet tails) "aabbbab#".toList .callByValuePar 4) [['a']]
      argument 8=some (some 3) ∧ pre "aabbbab#".toList 8 3="aabbb".toList := by decide +kernel

theorem all_inputs (x : List Char) (rest : Option (List Char)) :
    SObs (grammar alphabet tails) .callByValuePar entry x rest ↔
    SObs (grammar alphabet tails) .callByValueSeq entry x rest :=
  observations_iff alphabet tails valid entry entry_valid x rest

theorem translated_execution :
    SObs (grammar alphabet tails) .callByValueSeq entry good (some []) ∧
    SObs (grammar alphabet tails) .callByValueSeq entry zeroFresh (some []) ∧
    SObs (grammar alphabet tails) .callByValueSeq entry shortChild none := by
  have accept (x : List Char)
      (h : evV (grammar alphabet tails) x .callByValuePar
        (tblV (grammar alphabet tails) x .callByValuePar 8) [] entry x.length=some (some 0)) :
      SObs (grammar alphabet tails) .callByValueSeq entry x (some []) := by
    apply (all_inputs x (some [])).mp
    obtain ⟨o,hd,ho⟩ := evV_derives (firstOrder alphabet tails valid) (by decide)
      (supported_firstOrder alphabet entry entry_valid) 8 (Nat.le_refl _) h
    rw [sfx_self] at hd
    obtain ⟨t,rest,rfl,hlen⟩ := obsR_ok ho
    have hr : rest=[] := List.length_eq_zero_iff.mp hlen
    subst rest
    exact ⟨_,hd,rfl⟩
  have reject : SObs (grammar alphabet tails) .callByValueSeq entry shortChild none := by
    apply (all_inputs shortChild none).mp
    obtain ⟨o,hd,ho⟩ := evV_derives (firstOrder alphabet tails valid) (by decide)
      (supported_firstOrder alphabet entry entry_valid) 8 (Nat.le_refl _) source_execution.2.2
    rw [sfx_self,obsR_fail ho] at hd
    exact ⟨_,hd,rfl⟩
  exact ⟨accept good source_execution.1,accept zeroFresh source_execution.2.1,reject⟩

/-- The former a*;#;param gap has a fixed Seq recognizer once arguments are
restricted syntactically to the scanner alphabet; no initial replay is used. -/
theorem consuming_prefix :
    SObs (grammar ['a'] [.seq (.lit ['#']) (.param 0)]) .callByValuePar (.call 0 [.lit ['a']]) "aaa#a".toList (some []) ↔
    SObs (grammar ['a'] [.seq (.lit ['#']) (.param 0)]) .callByValueSeq (.call 0 [.lit ['a']]) "aaa#a".toList (some []) := by
  apply observations_iff
  · simp [Valid,Supported]
  · simp [Supported,Safe,accepts,Shallot.beqChar]

/-- Crossing the delimiter violates alphabet safety. The two evaluations
then differ; this is a boundary of this theorem, not a class separator. -/
theorem crossing_boundary :
    evV (grammar ['a'] [.seq (.lit ['#']) (.param 0)]) "a#a#a#".toList .callByValuePar
      (tblV (grammar ['a'] [.seq (.lit ['#']) (.param 0)]) "a#a#a#".toList .callByValuePar 2) []
      (.call 0 [.lit "a#a#".toList]) 6=some (some 0) ∧
    evV (grammar ['a'] [.seq (.lit ['#']) (.param 0)]) "a#a#a#".toList .callByValueSeq
      (tblV (grammar ['a'] [.seq (.lit ['#']) (.param 0)]) "a#a#a#".toList .callByValueSeq 2) []
      (.call 0 [.lit "a#a#".toList]) 6=some none ∧
    ¬Safe ['a'] (.lit "a#a#".toList) := by
  constructor
  · decide +kernel
  constructor
  · decide +kernel
  · change ¬("a#a#".toList.all (accepts ['a']))=true
    decide +kernel

end Shallot.MacroPeg.CBV.ScannerArgumentExamples
