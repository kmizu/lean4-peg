import MacroPeg.CBV.EmptyArgumentCorrespondence
import MacroPeg.CBV.ForwardingSeqExamples

namespace Shallot.MacroPeg.CBV.EmptyArgumentExamples
open EmptyArgumentSpecialization
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def grammar : MGrammar := ⟨[
  ⟨1,.seq (.param 0) (.chr '!')⟩,
  ⟨1,.seq (.param 0) (.notP (.param 1))⟩,
  ⟨2,.seq (.param 0) (.param 1)⟩,
  ⟨1,.call 3 [.lit []]⟩]⟩
theorem firstOrder : grammar.FirstOrder := by
  simp [grammar,MGrammar.FirstOrder,MExp.FirstOrder,MExp.FirstOrderArgs]
def originalRun (g : MGrammar) (s : Strategy) (e : MExp) (x : List Char) (k : Nat) :=
  evV g x s (sourceTable g x s k) [] e x.length
def compiledRun (g : MGrammar) (s : Strategy) (e : MExp) (x : List Char) (k : Nat) :=
  evV (target g) x s (targetTable g x s k) [] (render g e) x.length

theorem layout : (target grammar).rules.length=8 ∧
    ruleAtM (target grammar).rules 4=some ⟨0,render grammar (MExp.subst [.lit []] (.seq (.param 0) (.chr '!')))⟩ := ⟨rfl,rfl⟩
theorem zero_queries : zeroCheck (.andP (.call 0 [.star (.chr 'c')]))=true ∧
    zeroCheck (.star (.notP .any))=true ∧ zeroCheck (.star (.chr 'c'))=false := by decide +kernel

theorem query_success : ∀ s∈[Strategy.callByValuePar,.callByValueSeq],
    originalRun grammar s (.call 0 [.andP (.chr '!')]) ['!'] 8=some (some 0) ∧
    compiledRun grammar s (.call 0 [.andP (.chr '!')]) ['!'] 8=some (some 0) := by decide +kernel
theorem query_guard_required : compiledRun grammar .callByValuePar (.call 0 [.andP (.chr 'a')]) ['!'] 8=some none ∧
    evV (target grammar) ['!'] .callByValuePar (targetTable grammar ['!'] .callByValuePar 8) []
      (.call 4 []) 1=some (some 0) := by decide +kernel
theorem nullable_argument : ∀ s∈[Strategy.callByValuePar,.callByValueSeq],
    compiledRun grammar s (.call 1 [.star (.notP .any)]) ['a'] 8=some (some 1) ∧
    compiledRun grammar s (.call 1 [.star (.notP .any)]) [] 8=none := by decide +kernel
theorem arity_preflight : ∀ s∈[Strategy.callByValuePar,.callByValueSeq],
    originalRun grammar s (.call 2 [.star (.lit [])]) ['a'] 8=some none ∧
    compiledRun grammar s (.call 2 [.star (.lit [])]) ['a'] 8=some none := by decide +kernel
theorem private_helper : originalRun grammar .callByValuePar (.call 4 []) ['!'] 8=some none ∧
    compiledRun grammar .callByValuePar (.call 4 []) ['!'] 8=some none := by decide +kernel

/-- Other arguments remain input-dependent and unbounded; they are not
restricted to a finite set of words by the empty-capture specialization. -/
theorem dynamic_arguments : ∀ n∈[0,1,4],
    originalRun grammar .callByValuePar (.call 0 [.star (.chr 'c')]) (List.replicate n 'c'++['!']) 8=some (some 0) ∧
    compiledRun grammar .callByValuePar (.call 0 [.star (.chr 'c')]) (List.replicate n 'c'++['!']) 8=some (some 0) := by decide +kernel
theorem other_arities : originalRun grammar .callByValuePar (.call 2 [.lit ['a'],.lit ['a']]) ['a','a'] 8=some (some 0) ∧
    compiledRun grammar .callByValuePar (.call 2 [.lit ['a'],.lit ['a']]) ['a','a'] 8=some (some 0) := by decide +kernel
theorem clone_scope : evV (target grammar) ['a'] .callByValuePar (targetTable grammar ['a'] .callByValuePar 8)
    [['z'],['a']] (render grammar (MExp.subst [.lit []] (.seq (.param 0) (.notP (.param 1))))) 1=some (some 1) := by decide +kernel

def resetSource := MultiplyingPrefixCompiler.source ForwardingSeqExamples.zeroFactor
theorem reset_firstOrder : resetSource.FirstOrder := by
  simp [resetSource,MultiplyingPrefixCompiler.source,ForwardingSeqExamples.zeroFactor,MGrammar.FirstOrder,
    MultiplyingPrefixCompiler.sourceBody,MExp.FirstOrder,MExp.FirstOrderArgs,RepeatedWordArguments.expression]
theorem actual_reset : originalRun resetSource .callByValuePar (.call 0 [.lit ['a']]) ['a','!'] 8=some (some 0) ∧
    compiledRun resetSource .callByValuePar (.call 0 [.lit ['a']]) ['a','!'] 8=some (some 0) ∧
    originalRun resetSource .callByValueSeq (.call 0 [.lit ['a']]) ['a','!'] 8=some none ∧
    compiledRun resetSource .callByValueSeq (.call 0 [.lit ['a']]) ['a','!'] 8=some none := by decide +kernel

theorem reset_observations (s : Strategy) (hs : s≠.callByName) (x : List Char) (rest : Option (List Char)) :
    SObs resetSource s (.call 0 [.lit ['a']]) x rest ↔
      SObs (target resetSource) s (render resetSource (.call 0 [.lit ['a']])) x rest :=
  EmptyArgumentCorrespondence.observations_iff resetSource reset_firstOrder s hs _ (by trivial) x rest

theorem empty_cycle_source (x : List Char) (s : Strategy) (k : Nat) :
    originalRun grammar s (.call 3 [.lit []]) x k=none := by
  have hr : ruleAtM grammar.rules 3=some ⟨1,.call 3 [.lit []]⟩ := rfl
  have hrow : valAt (sourceTable grammar x s k 3 [[]]) x.length=none := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [valAt_tblV_succ hr [[]] (Nat.le_refl _)]
      cases s <;> simp [evV,hr,evParArgs,evSeqArgs,Shallot.stripPrefix?,length_sfx x (Nat.le_refl _),
        pre,Nat.sub_self,List.take_zero,ih]
  unfold originalRun
  cases s <;> simp [evV,hr,evParArgs,evSeqArgs,Shallot.stripPrefix?,length_sfx x (Nat.le_refl _),
    pre,Nat.sub_self,List.take_zero,hrow]
theorem empty_cycle_target (x : List Char) (s : Strategy) (k : Nat) :
    compiledRun grammar s (.call 3 [.lit []]) x k=none := by
  unfold compiledRun
  rw [←EmptyArgumentCorrespondence.evaluator_eq grammar firstOrder x s k [] (.call 3 [.lit []])
    (by trivial) x.length (Nat.le_refl _)]
  exact empty_cycle_source x s k

end Shallot.MacroPeg.CBV.EmptyArgumentExamples
