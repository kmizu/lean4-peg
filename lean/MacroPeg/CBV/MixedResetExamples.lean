import MacroPeg.CBV.MixedResetCompiler
import MacroPeg.CBV.ZeroResetExamples

namespace Shallot.MacroPeg.CBV.MixedResetExamples
open MixedResetCompiler
open MultiplyingPrefixCompiler (Spec source sourceBody)
open RepeatedWordArguments (copies)
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def argument : MExp := .seq (.star (.chr 'c')) (.lit ['!','x','g','a','b'])
def specs : List Spec := [
  ⟨0,3,.seq (.chr '!') (.seq (.call 1 [argument]) (.param 0)),.chr 'g'⟩,
  ⟨2,0,.seq (.chr '!') (.call 0 [.lit ['x']]),.chr '?'⟩,
  ⟨9,2,.eps,.star (.chr 'c')⟩]
def entry : MExp := .call 0 [.lit ['a','b']]
theorem checked : check specs=true := by decide +kernel
theorem firstOrder : (source specs).FirstOrder := by
  simp [source,sourceBody,specs,argument,MGrammar.FirstOrder,MExp.FirstOrder,MExp.FirstOrderArgs,
    RepeatedWordArguments.expression]
def sourceRun (e : MExp) (x : List Char) (k : Nat) :=
  evV (source specs) x .callByValuePar (tblV (source specs) x .callByValuePar k) [] e x.length
def targetRun (e : MExp) (x : List Char) (k : Nat) :=
  evV (target specs) x .callByValueSeq (tblV (target specs) x .callByValueSeq k) [] (render specs e) x.length

def suffix (w : List Char) (n : Nat) := ['!']++List.replicate n 'c'++['!','x','g']++w

theorem mixed_source : ∀ n∈[0,1,4], sourceRun entry
    (copies ['a','b'] 3++['g']++suffix ['a','b'] n) 12=some (some 0) := by decide +kernel
theorem mixed_target : ∀ n∈[0,1,4], targetRun entry
    (copies ['a','b'] 3++['g']++suffix ['a','b'] n) 12=some (some 0) := by decide +kernel
theorem nested_source : ∀ n∈[0,1,4], sourceRun entry
    (copies ['a','b'] 9++['g']++suffix (copies ['a','b'] 3) n++suffix ['a','b'] n) 12=some (some 0) := by decide +kernel
theorem nested_target : ∀ n∈[0,1,4], targetRun entry
    (copies ['a','b'] 9++['g']++suffix (copies ['a','b'] 3) n++suffix ['a','b'] n) 12=some (some 0) := by decide +kernel
theorem reset_returns_early : sourceRun (.call 1 [argument]) ['c','c','!','x','g','a','b'] 12=some (some 2) ∧
    targetRun (.call 1 [argument]) ['c','c','!','x','g','a','b'] 12=some (some 2) := by decide +kernel
theorem reset_fallback : sourceRun (.call 1 [.lit ['d']]) ['d','?'] 12=some (some 0) ∧
    targetRun (.call 1 [.lit ['d']]) ['d','?'] 12=some (some 0) := by decide +kernel
theorem wrong_restored_word : ∀ n∈[0,1,4], targetRun entry
    (copies ['a','b'] 9++['g']++suffix ['a','b'] n++suffix ['a','b'] n) 12=some none := by decide +kernel
theorem missing_argument_suffix : targetRun (.call 1 [argument]) ['c','!','x','g'] 12=some none := by decide +kernel
theorem nullable_preflight : targetRun (.call 1 [.star (.lit [])]) ['!','x','g'] 12=none := by decide +kernel

theorem all_observations (e : MExp) (he : e.FirstOrder) (x : List Char) (rest : Option (List Char)) :
    SObs (source specs) .callByValuePar e x rest ↔
      SObs (target specs) .callByValueSeq (render specs e) x rest :=
  MixedResetCompiler.observations_iff specs firstOrder checked e he x rest

theorem old_reset_checked : check ZeroResetExamples.reset=true := by decide +kernel
theorem old_reset : evV (target ZeroResetExamples.reset) ['a','!'] .callByValueSeq
    (tblV (target ZeroResetExamples.reset) ['a','!'] .callByValueSeq 12) []
    (render ZeroResetExamples.reset (.call 0 [.lit ['a']])) 2=some (some 0) := by decide +kernel
theorem dependent_reset_rejected : check [⟨0,0,.param 0,.eps⟩]=false := by decide +kernel
theorem growth_head_to_reset_rejected : check [⟨1,3,.eps,.eps⟩,⟨9,0,.eps,.eps⟩]=false := by decide +kernel

theorem cycle_checked : check ZeroResetExamples.cycle=true := by decide +kernel

theorem cycle_target (x : List Char) (k : Nat) :
    evV (target ZeroResetExamples.cycle) x .callByValueSeq (tblV (target ZeroResetExamples.cycle) x .callByValueSeq k)
      [] (render ZeroResetExamples.cycle (.call 0 [.lit []])) x.length=none :=
  (MixedResetCompiler.undefined_iff ZeroResetExamples.cycle ZeroResetExamples.cycle_firstOrder cycle_checked
    (.call 0 [.lit []]) (by trivial) x).mp (MultiplyingPrefixExamples.empty_source 0 x) k

end Shallot.MacroPeg.CBV.MixedResetExamples
