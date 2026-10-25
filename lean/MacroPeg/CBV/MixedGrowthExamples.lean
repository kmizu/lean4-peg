import MacroPeg.CBV.MixedGrowthChecks

namespace Shallot.MacroPeg.CBV.MixedGrowthExamples
open MixedGrowthCompiler
open MixedGrowthChecks (check)
open ReplayControlFusion (Part Plan)
open RepeatedWordArguments (copies)
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def parts : List Part := [⟨false,.lit ['X']⟩,
  ⟨true,.seq (.call 0 [.lit ['x']]) (.param 0)⟩]
def specs : List Entry := [
  .growth ⟨0,3,.seq (.chr '!') (.seq (.call 1 [.star (.chr 'c')]) (.param 0)),.chr 'g'⟩,
  .origin (.alt (.leaf 0) (.leaf 1))]
def entry : MExp := .call 0 [.lit ['a','b']]
theorem checked : check parts specs=true := by decide +kernel

def sourceRun (e : MExp) (x : List Char) (k : Nat) :=
  evV (source parts specs) x .callByValuePar (sourceTable parts specs x k) [] e x.length
def targetRun (e : MExp) (x : List Char) (k : Nat) :=
  evV (target parts specs) x .callByValueSeq (targetTable parts specs x k) [] (render parts specs e) x.length
def suffix (w : List Char) (n : Nat) := ['!']++List.replicate n 'c'++['x','g']++List.replicate n 'c'++w

theorem mutual_source : ∀ n∈[0,1,4], sourceRun entry
    (copies ['a','b'] 3++['g']++suffix ['a','b'] n) 12=some (some 0) := by decide +kernel
theorem mutual_target : ∀ n∈[0,1,4], targetRun entry
    (copies ['a','b'] 3++['g']++suffix ['a','b'] n) 12=some (some 0) := by decide +kernel
theorem nested_source : ∀ n∈[0,1,4], sourceRun entry
    (copies ['a','b'] 9++['g']++suffix (copies ['a','b'] 3) n++suffix ['a','b'] n) 12=some (some 0) := by decide +kernel
theorem nested_target : ∀ n∈[0,1,4], targetRun entry
    (copies ['a','b'] 9++['g']++suffix (copies ['a','b'] 3) n++suffix ['a','b'] n) 12=some (some 0) := by decide +kernel
theorem short_origin : sourceRun (.call 1 [.lit ['X','?']]) ['X','?'] 12=some (some 1) ∧
    targetRun (.call 1 [.lit ['X','?']]) ['X','?'] 12=some (some 1) := by decide +kernel
theorem origin_preflight : targetRun (.call 1 [.lit ['Z']]) ['X'] 12=some none := by decide +kernel
theorem nullable_origin : targetRun (.call 1 [.star (.lit [])]) ['X'] 12=none := by decide +kernel
theorem private_helpers : targetRun (.call 6 []) ['X'] 12=some none := by decide +kernel
theorem short_copies : ∀ n∈[0,1,4], targetRun entry
    (copies ['a','b'] 9++['g']++suffix ['a','b'] n++suffix ['a','b'] n) 12=some none := by decide +kernel

theorem all_observations (e : MExp) (he : e.FirstOrder) (x : List Char) (rest : Option (List Char)) :
    SObs (source parts specs) .callByValuePar e x rest ↔
      SObs (target parts specs) .callByValueSeq (render parts specs e) x rest :=
  MixedGrowthChecks.observations_iff parts specs checked e he x rest

theorem growth_to_origin_rejected : check parts [.growth ⟨1,3,.eps,.eps⟩,.origin (.leaf 0)]=false := by decide +kernel
theorem missing_leaf_rejected : check parts [.origin (.leaf 2)]=false := by decide +kernel
theorem dependent_closed_rejected : check [⟨false,.param 0⟩] [.origin (.leaf 0)]=false := by decide +kernel
theorem unit_growth_rejected : check [] [.growth ⟨0,1,.eps,.eps⟩]=false := by decide +kernel

end Shallot.MacroPeg.CBV.MixedGrowthExamples
