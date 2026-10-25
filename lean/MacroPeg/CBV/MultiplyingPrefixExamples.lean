import MacroPeg.CBV.MultiplyingPrefixCorrespondence

namespace Shallot.MacroPeg.CBV.MultiplyingPrefixExamples
open MultiplyingPrefixCompiler
open RepeatedWordArguments (copies expression)
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def entry : MExp := .call 0 [.lit ['a','b']]
def sourceRun (rs : List Spec) (e : MExp) (x : List Char) (k : Nat) :=
  evV (source rs) x .callByValuePar (sourceTable rs x k) [] e x.length
def targetRun (rs : List Spec) (e : MExp) (x : List Char) (k : Nat) :=
  evV (target rs) x .callByValueSeq (targetTable rs x k) [] (render rs.length e) x.length
def triple : List Spec := [⟨0,3,.eps,.eps⟩]
theorem triple_valid : Valid triple := by simp [Valid,triple,MExp.FirstOrder]
theorem triple_source : ∀ n∈[1,3,9,27], sourceRun triple entry (copies ['a','b'] n) 8=some (some 0) := by decide +kernel
theorem triple_target : ∀ n∈[1,3,9,27], targetRun triple entry (copies ['a','b'] n) 8=some (some 0) := by decide +kernel
theorem triple_nonpowers : sourceRun triple entry (copies ['a','b'] 5) 8=some (some 4) ∧
    targetRun triple entry (copies ['a','b'] 5) 8=some (some 4) := by decide +kernel

/-- Incoming 2x and 3x representations coexist and change repeatedly in
the same mutually recursive grammar. -/
def mixed : List Spec := [⟨1,3,.eps,.eps⟩,⟨0,2,.eps,.eps⟩]
theorem mixed_valid : Valid mixed := by simp [Valid,mixed,MExp.FirstOrder]
theorem mixed_source : ∀ n∈[1,3,6,18,36], sourceRun mixed entry (copies ['a','b'] n) 8=some (some 0) := by decide +kernel
theorem mixed_target : ∀ n∈[1,3,6,18,36], targetRun mixed entry (copies ['a','b'] n) 8=some (some 0) := by decide +kernel
theorem mixed_language (x : List Char) : SObs (source mixed) .callByValuePar entry x (some []) ↔
    SObs (target mixed) .callByValueSeq (render mixed.length entry) x (some []) :=
  MultiplyingPrefixCorrespondence.observations_iff mixed mixed_valid entry (by trivial) x (some [])
theorem mixed_layout : (target mixed).rules.length=6 ∧
    ruleAtM (target mixed).rules 3=some ⟨2,targetBody mixed 1 3 ⟨0,2,.eps,.eps⟩⟩ ∧
    ruleAtM (target mixed).rules 4=some ⟨1,targetBody mixed 0 2 ⟨1,3,.eps,.eps⟩⟩ := ⟨rfl,rfl,rfl⟩

def restoring : List Spec := [⟨1,3,.param 0,.eps⟩,⟨0,2,.param 0,.eps⟩]
theorem restoring_valid : Valid restoring := by simp [Valid,restoring,MExp.FirstOrder]
theorem restoring_source : ∀ n∈[1,4,10,28], sourceRun restoring entry (copies ['a','b'] n) 8=some (some 0) := by decide +kernel
theorem restoring_target : ∀ n∈[1,4,10,28], targetRun restoring entry (copies ['a','b'] n) 8=some (some 0) := by decide +kernel

def fresh : List Spec := [
  ⟨1,3,.seq (.lit ['!']) (.seq (.call 1 [.star (.chr 'c')]) (.param 0)),.eps⟩,
  ⟨0,2,.eps,.eps⟩]
theorem fresh_valid : Valid fresh := by simp [Valid,fresh,MExp.FirstOrder,MExp.FirstOrderArgs]
theorem fresh_source : ∀ n∈[1,4], sourceRun fresh entry
    (copies ['a','b'] 3++['!']++List.replicate n 'c'++['a','b']) 8=some (some 0) := by decide +kernel
theorem fresh_target : ∀ n∈[1,4], targetRun fresh entry
    (copies ['a','b'] 3++['!']++List.replicate n 'c'++['a','b']) 8=some (some 0) := by decide +kernel
theorem fresh_empty : sourceRun fresh entry (copies ['a','b'] 3++['!','a','b']) 8=none ∧
    targetRun fresh entry (copies ['a','b'] 3++['!','a','b']) 8=none := by decide +kernel
theorem parent_mismatch : sourceRun fresh (.seq entry (.notP .any))
    (copies ['a','b'] 3++['!','c','c','a','c']) 8=some none ∧
    targetRun fresh (.seq entry (.notP .any))
      (copies ['a','b'] 3++['!','c','c','a','c']) 8=some none := by decide +kernel

theorem distinct_captures : evSeqArgs (target mixed) (copies ['a','b'] 6) .callByValueSeq
    (targetTable mixed (copies ['a','b'] 6) 8) [['a','b'],['a','b']]
    (List.replicate 2 (view 3)) 12=some (some ([copies ['a','b'] 3,copies ['a','b'] 3],0)) := by decide +kernel

theorem private_helper : sourceRun mixed (.call 2 [.lit ['a','b'],.lit ['a','b']]) ['a','b','a','b'] 8=some none ∧
    targetRun mixed (.call 2 [.lit ['a','b'],.lit ['a','b']]) ['a','b','a','b'] 8=some none ∧
    evV (target mixed) ['a','b','a','b'] .callByValueSeq (targetTable mixed ['a','b','a','b'] 8) []
      (.call 2 [.lit ['a','b'],.lit ['a','b']]) 4=some (some 0) := by decide +kernel

theorem missing_prefix : sourceRun [⟨1,3,.eps,.eps⟩] entry ['a','b'] 8=some (some 0) ∧
    targetRun [⟨1,3,.eps,.eps⟩] entry ['a','b'] 8=some (some 0) := by decide +kernel

end Shallot.MacroPeg.CBV.MultiplyingPrefixExamples
