import MacroPeg.CBV.MixedForwardingReset
import MacroPeg.CBV.MixedResetExamples

namespace Shallot.MacroPeg.CBV.MixedForwardingExamples
open MultiplyingPrefixCompiler (Spec source sourceBody)
open RepeatedWordArguments (copies)
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def argument : MExp := .seq (.star (.chr 'c')) (.lit ['!','x','g','x','a','b'])
def specs : List Spec := [
  ⟨1,1,.param 0,.chr 'f'⟩,
  ⟨1,3,.seq (.chr '!') (.seq (.call 2 [argument]) (.param 0)),.chr 'g'⟩,
  ⟨3,0,.seq (.chr '!') (.call 0 [.lit ['x']]),.chr '?'⟩,
  ⟨9,2,.eps,.star (.chr 'c')⟩,
  ⟨5,1,.eps,.eps⟩,⟨4,1,.eps,.eps⟩]
def entry : MExp := .call 0 [.lit ['a','b']]
theorem checked : MixedForwardingReset.check specs=true := by decide +kernel
theorem firstOrder : (source specs).FirstOrder := by
  simp [source,sourceBody,specs,argument,MGrammar.FirstOrder,MExp.FirstOrder,MExp.FirstOrderArgs,
    RepeatedWordArguments.expression]
def sourceRun (e : MExp) (x : List Char) (k : Nat) :=
  evV (source specs) x .callByValuePar (tblV (source specs) x .callByValuePar k) [] e x.length
def targetRun (e : MExp) (x : List Char) (k : Nat) :=
  evV (MixedForwardingReset.target specs) x .callByValueSeq (tblV (MixedForwardingReset.target specs) x .callByValueSeq k)
    [] (MixedForwardingReset.render specs e) x.length

def suffix (w : List Char) (n : Nat) := ['!']++List.replicate n 'c'++['!','x','g','x']++w

theorem mixed_source : ∀ n∈[0,1,4], sourceRun entry
    (copies ['a','b'] 3++['g']++suffix ['a','b'] n++['a','b']) 16=some (some 0) := by decide +kernel
theorem mixed_target : ∀ n∈[0,1,4], targetRun entry
    (copies ['a','b'] 3++['g']++suffix ['a','b'] n++['a','b']) 16=some (some 0) := by decide +kernel
theorem nested_source : ∀ n∈[0,1,4], sourceRun entry
    (copies ['a','b'] 9++['g']++suffix (copies ['a','b'] 3) n++suffix ['a','b'] n++['a','b']) 16=some (some 0) := by decide +kernel
theorem nested_target : ∀ n∈[0,1,4], targetRun entry
    (copies ['a','b'] 9++['g']++suffix (copies ['a','b'] 3) n++suffix ['a','b'] n++['a','b']) 16=some (some 0) := by decide +kernel
theorem early_reset : sourceRun (.call 2 [argument]) ['c','c','!','x','g','x','a','b'] 16=some (some 2) ∧
    targetRun (.call 2 [argument]) ['c','c','!','x','g','x','a','b'] 16=some (some 2) := by decide +kernel
theorem clock_difference : sourceRun entry ['a','b','g','a','b'] 1=none ∧
    targetRun entry ['a','b','g','a','b'] 1=some (some 0) := by decide +kernel
theorem short_parent_rejected : ∀ n∈[0,1,4], targetRun entry
    (copies ['a','b'] 9++['g']++suffix ['a','b'] n++suffix ['a','b'] n++['a','b']) 16=some none := by decide +kernel
theorem scope_restored : targetRun (.call 0 [.lit ['x']]) ['x','g','x'] 16=some (some 0) ∧
    targetRun (.call 0 [.lit ['x']]) ['x','g','a','b'] 16=some none := by decide +kernel
theorem reset_fallback : targetRun (.call 2 [.lit ['d']]) ['d','?'] 16=some (some 0) := by decide +kernel
theorem reset_preflight : targetRun (.call 2 [argument]) ['c','!','x','g','x'] 16=some none ∧
    targetRun (.call 2 [.star (.lit [])]) ['!','x','g','x'] 16=none := by decide +kernel
theorem cycle_preflight : sourceRun (.call 4 [.lit ['a','b']]) ['x'] 16=some none ∧
    targetRun (.call 4 [.lit ['a','b']]) ['x'] 16=some none := by decide +kernel
theorem private_helper : targetRun (.call 42 []) ['x'] 16=some none := by decide +kernel

theorem all_observations (e : MExp) (he : e.FirstOrder) (x : List Char) (rest : Option (List Char)) :
    SObs (source specs) .callByValuePar e x rest ↔
      SObs (MixedForwardingReset.target specs) .callByValueSeq (MixedForwardingReset.render specs e) x rest :=
  MixedForwardingReset.observations_iff specs firstOrder checked e he x rest

theorem cycle_checked : ForwardingPrefixCycles.check specs [4,5]=true := by decide +kernel

theorem cycle_source (x : List Char) (k : Nat) : sourceRun (.call 4 [.lit []]) x k=none := by
  have hr : ruleAtM (source specs).rules 4=some ⟨1,sourceBody ⟨5,1,.eps,.eps⟩⟩ := rfl
  have hh := ForwardingPrefixCycles.rows_none specs [4,5]
    ((ForwardingPrefixCycles.checked_iff specs [4,5]).mp cycle_checked) x k 4 (by simp) [] x.length x.length
    ⟨Nat.le_refl _,Nat.le_refl _,rfl⟩
  unfold sourceRun
  rw [evV_call_par hr rfl (by decide)]
  simpa only [evParArgs,evV,Shallot.stripPrefix?,length_sfx x (Nat.le_refl _),
    pre,Nat.sub_self,List.take_zero] using hh

theorem cycle_target (x : List Char) (k : Nat) : targetRun (.call 4 [.lit []]) x k=none :=
  (MixedForwardingReset.undefined_iff specs firstOrder checked (.call 4 [.lit []]) (by trivial) x).mp
    (cycle_source x) k

/-- Explicit origin Plan entries still coexist with unit forwarding. -/
def originParts : List ReplayControlFusion.Part := [⟨false,.lit ['X']⟩,
  ⟨true,.seq (.call 0 [.lit ['x']]) (.param 0)⟩]
def originSpecs : List MixedGrowthCompiler.Entry := [
  .growth ⟨1,1,.param 0,.chr 'f'⟩,
  .growth ⟨1,3,.seq (.chr '!') (.seq (.call 2 [.star (.chr 'c')]) (.param 0)),.chr 'g'⟩,
  .origin (.alt (.leaf 0) (.leaf 1))]
theorem origin_checked : MixedForwardingChecks.check originParts originSpecs=true := by decide +kernel

def originSourceRun (e : MExp) (x : List Char) (k : Nat) :=
  evV (MixedForwardingCompiler.original originParts originSpecs) x .callByValuePar
    (tblV (MixedForwardingCompiler.original originParts originSpecs) x .callByValuePar k) [] e x.length

def originTargetRun (e : MExp) (x : List Char) (k : Nat) :=
  evV (MixedForwardingCompiler.target originParts originSpecs) x .callByValueSeq
    (MixedForwardingCompiler.targetTable originParts originSpecs x k) [] (MixedForwardingCompiler.render originParts originSpecs e) x.length

theorem origin_source : ∀ n∈[0,1,4], originSourceRun entry
    (copies ['a','b'] 3++['g','!']++List.replicate n 'c'++['x','g','x']++List.replicate n 'c'++copies ['a','b'] 2) 16=some (some 0) := by decide +kernel
theorem origin_target : ∀ n∈[0,1,4], originTargetRun entry
    (copies ['a','b'] 3++['g','!']++List.replicate n 'c'++['x','g','x']++List.replicate n 'c'++copies ['a','b'] 2) 16=some (some 0) := by decide +kernel
theorem short_origin : originSourceRun (.call 2 [.lit ['X','?']]) ['X','?'] 16=some (some 1) ∧
    originTargetRun (.call 2 [.lit ['X','?']]) ['X','?'] 16=some (some 1) := by decide +kernel

theorem origin_observations (e : MExp) (he : e.FirstOrder) (x : List Char) (rest : Option (List Char)) :
    SObs (MixedForwardingCompiler.original originParts originSpecs) .callByValuePar e x rest ↔
      SObs (MixedForwardingCompiler.target originParts originSpecs) .callByValueSeq (MixedForwardingCompiler.render originParts originSpecs e) x rest :=
  MixedForwardingChecks.observations_iff originParts originSpecs origin_checked e he x rest

theorem committed_checked : MixedForwardingReset.check ForwardingHeadExamples.committed=true := by decide +kernel

theorem committed_choice : evV (MixedForwardingReset.target ForwardingHeadExamples.committed) ['a','a','a','b','c'] .callByValueSeq
    (tblV (MixedForwardingReset.target ForwardingHeadExamples.committed) ['a','a','a','b','c'] .callByValueSeq 16) []
    (MixedForwardingReset.render ForwardingHeadExamples.committed (.call 0 [.lit ['a']])) 5=some none := by decide +kernel

theorem dependent_reset_rejected : MixedForwardingReset.check [⟨0,0,.param 0,.eps⟩]=false := by decide +kernel
theorem unit_head_to_origin_rejected : MixedForwardingChecks.check originParts
    [.growth ⟨1,1,.eps,.eps⟩,.origin (.leaf 0)]=false := by decide +kernel

end Shallot.MacroPeg.CBV.MixedForwardingExamples
