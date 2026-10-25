import MacroPeg.CBV.DoublingPrefixCorrespondence

namespace Shallot.MacroPeg.CBV.DoublingPrefixExamples
open DoublingPrefixCompiler
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def specs : List Spec := [⟨0,.eps,.eps⟩]
def entry : MExp := .call 0 [.lit ['a','b']]
def input (n : Nat) := (List.replicate n ['a','b']).flatten
def sourceRun (rs : List Spec) (e : MExp) (x : List Char) (k : Nat) :=
  evV (source rs) x .callByValuePar (sourceTable rs x k) [] e x.length
def targetRun (rs : List Spec) (e : MExp) (x : List Char) (k : Nat) :=
  evV (target rs) x .callByValueSeq (targetTable rs x k) [] (render rs e) x.length

theorem valid : Valid specs := by simp [Valid,specs,MExp.FirstOrder]
theorem grammar_size : (source specs).rules.length=1 ∧ (target specs).rules.length=2 := by decide +kernel
theorem source_powers : ∀ n∈[1,2,4,8,16], sourceRun specs entry (input n) 8=some (some 0) := by decide +kernel
theorem target_powers : ∀ n∈[1,2,4,8,16], targetRun specs entry (input n) 8=some (some 0) := by decide +kernel
theorem source_nonpowers : sourceRun specs entry (input 3) 8=some (some 2) ∧
    sourceRun specs entry (input 5) 8=some (some 2) := by decide +kernel
theorem target_nonpowers : targetRun specs entry (input 3) 8=some (some 2) ∧
    targetRun specs entry (input 5) 8=some (some 2) := by decide +kernel
theorem original_language (x : List Char) : SObs (source specs) .callByValuePar entry x (some []) ↔
    SObs (target specs) .callByValueSeq (render specs entry) x (some []) :=
  DoublingPrefixCorrespondence.observations_iff specs valid entry (by trivial) x (some [])

/-- The source's unknown rule 1 aliases a real half-view helper in the
target; rendering must reject it instead of exposing that helper. -/
theorem private_helper : sourceRun specs (.call 1 [.lit ['a']]) ['a'] 8=some none ∧
    targetRun specs (.call 1 [.lit ['a']]) ['a'] 8=some none ∧
    evV (target specs) ['a'] .callByValueSeq (targetTable specs ['a'] 8) []
      (.call 1 [.lit ['a']]) 1=some (some 0) := by decide +kernel

def mutualSpecs : List Spec := [⟨1,.param 0,.eps⟩,⟨0,.param 0,.eps⟩]
theorem mutual_valid : Valid mutualSpecs := by simp [Valid,mutualSpecs,MExp.FirstOrder]
theorem mutual_source : ∀ n∈[1,3,7,15], sourceRun mutualSpecs entry (input n) 8=some (some 0) := by decide +kernel
theorem mutual_target : ∀ n∈[1,3,7,15], targetRun mutualSpecs entry (input n) 8=some (some 0) := by decide +kernel

def freshSpecs : List Spec := [
  ⟨1,.seq (.lit ['!']) (.seq (.call 1 [.star (.chr 'c')]) (.param 0)),.eps⟩,
  ⟨1,.eps,.eps⟩]
theorem fresh_valid : Valid freshSpecs := by simp [Valid,freshSpecs,MExp.FirstOrder,MExp.FirstOrderArgs]
theorem fresh_source : ∀ n∈[1,3,8], sourceRun freshSpecs entry
    (input 2++['!']++List.replicate n 'c'++['a','b']) 8=some (some 0) := by decide +kernel
theorem fresh_target : ∀ n∈[1,3,8], targetRun freshSpecs entry
    (input 2++['!']++List.replicate n 'c'++['a','b']) 8=some (some 0) := by decide +kernel

theorem fresh_empty : sourceRun freshSpecs entry (input 2++['!','a','b']) 8=none ∧
    targetRun freshSpecs entry (input 2++['!','a','b']) 8=none := by decide +kernel

theorem parent_mismatch : sourceRun freshSpecs (.seq entry (.notP .any))
    (input 2++['!','c','c','a','c']) 8=some none ∧
    targetRun freshSpecs (.seq entry (.notP .any))
      (input 2++['!','c','c','a','c']) 8=some none := by decide +kernel

theorem translation_required : sourceRun specs entry ['a','b'] 8=some (some 0) ∧
    evV (source specs) ['a','b'] .callByValueSeq (tblV (source specs) ['a','b'] .callByValueSeq 8)
      [] entry 2=some none := by decide +kernel

theorem missing_prefix_callee : sourceRun [⟨1,.eps,.eps⟩] entry ['a','b'] 8=some (some 0) ∧
    targetRun [⟨1,.eps,.eps⟩] entry ['a','b'] 8=some (some 0) := by decide +kernel

theorem arity_preflight : sourceRun specs (.call 0 [.star (.lit []),.eps]) ['a'] 8=some none ∧
    targetRun specs (.call 0 [.star (.lit []),.eps]) ['a'] 8=some none := by decide +kernel

end Shallot.MacroPeg.CBV.DoublingPrefixExamples
