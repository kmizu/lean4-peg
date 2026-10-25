import MacroPeg.CBV.ZeroResetCorrespondence
import MacroPeg.CBV.EmptyArgumentExamples
import MacroPeg.CBV.MultiplyingPrefixUndefined

namespace Shallot.MacroPeg.CBV.ZeroResetExamples
open ZeroResetOrigin
open MultiplyingPrefixCompiler (Spec source sourceBody)
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def sourceRun (rs : List Spec) (e : MExp) (x : List Char) (k : Nat) :=
  evV (source rs) x .callByValuePar (tblV (source rs) x .callByValuePar k) [] e x.length
def targetRun (rs : List Spec) (e : MExp) (x : List Char) (k : Nat) :=
  evV (target rs) x .callByValueSeq (tblV (target rs) x .callByValueSeq k) [] (render rs e) x.length
abbrev reset := ForwardingSeqExamples.zeroFactor
abbrev entry : MExp := .call 0 [.lit ['a']]

theorem reset_checked : check reset=true := by decide +kernel
theorem reset_firstOrder : (source reset).FirstOrder := EmptyArgumentExamples.reset_firstOrder
theorem actual_reset : sourceRun reset entry ['a','!'] 8=some (some 0) ∧
    targetRun reset entry ['a','!'] 8=some (some 0) := by decide +kernel
theorem earlier_than_capture : sourceRun reset (.call 0 [.lit ['a','!','q']]) ['a','!','q'] 8=some (some 1) ∧
    targetRun reset (.call 0 [.lit ['a','!','q']]) ['a','!','q'] 8=some (some 1) := by decide +kernel
theorem preflight_required : sourceRun reset (.call 0 [.lit ['b']]) ['a','!'] 8=some none ∧
    targetRun reset (.call 0 [.lit ['b']]) ['a','!'] 8=some none ∧
    evV (target reset) ['a','!'] .callByValueSeq (tblV (target reset) ['a','!'] .callByValueSeq 8)
      [] (.call 0 []) 2=some (some 0) := by decide +kernel
theorem nullable_preflight : sourceRun reset (.call 0 [.star (.lit [])]) ['a','!'] 8=none ∧
    targetRun reset (.call 0 [.star (.lit [])]) ['a','!'] 8=none := by decide +kernel
theorem arity_preflight : targetRun reset (.call 0 [.star (.lit []),.eps]) ['a','!'] 8=some none := by decide +kernel
theorem private_helpers : targetRun reset (.call 2 []) ['a','!'] 8=some none := by decide +kernel
theorem reset_observations (e : MExp) (he : e.FirstOrder) (x : List Char) (rest : Option (List Char)) :
    SObs (source reset) .callByValuePar e x rest ↔
      SObs (target reset) .callByValueSeq (render reset e) x rest :=
  ZeroResetCorrespondence.observations_iff reset reset_firstOrder reset_checked e he x rest

/-- The closed origin branch consumes a!, then calls a replay client with c*.
The client calls the reset rule again with a new x; its fallback must replay
x rather than the outer parent's a. No bound on the c* capture is assumed. -/
def fresh : List Spec := [
  ⟨1,0,.seq (.chr '!') (.call 2 [.star (.chr 'c')]),.chr 'z'⟩,
  ⟨9,2,.eps,.chr 'a'⟩,
  ⟨9,2,.eps,.seq (.chr '?') (.call 0 [.lit ['x']])⟩]
theorem fresh_checked : check fresh=true := by decide +kernel
theorem fresh_firstOrder : (source fresh).FirstOrder := by
  simp [fresh,source,sourceBody,MGrammar.FirstOrder,MExp.FirstOrder,MExp.FirstOrderArgs,
    RepeatedWordArguments.expression]
theorem fresh_source : ∀ n∈[0,1,4], sourceRun fresh entry
    (['a','!']++List.replicate n 'c'++['?','x','z']) 12=some (some 0) := by decide +kernel
theorem fresh_target : ∀ n∈[0,1,4], targetRun fresh entry
    (['a','!']++List.replicate n 'c'++['?','x','z']) 12=some (some 0) := by decide +kernel
theorem fresh_wrong_parent : ∀ n∈[0,1,4], targetRun fresh entry
    (['a','!']++List.replicate n 'c'++['?','a','z']) 12=some none := by decide +kernel
theorem fresh_observations (e : MExp) (he : e.FirstOrder) (x : List Char) (rest : Option (List Char)) :
    SObs (source fresh) .callByValuePar e x rest ↔
      SObs (target fresh) .callByValueSeq (render fresh e) x rest :=
  ZeroResetCorrespondence.observations_iff fresh fresh_firstOrder fresh_checked e he x rest

theorem positive_known_rejected : check [⟨0,1,.eps,.eps⟩]=false := by decide +kernel
theorem dependent_tail_rejected : check [⟨0,0,.param 0,.eps⟩]=false := by decide +kernel

abbrev cycle := MultiplyingPrefixExamples.nullable 0
theorem cycle_checked : check cycle=true := by decide +kernel
theorem cycle_firstOrder : (source cycle).FirstOrder := by
  simp [cycle,MultiplyingPrefixExamples.nullable,source,sourceBody,MGrammar.FirstOrder,MExp.FirstOrder,
    MExp.FirstOrderArgs,RepeatedWordArguments.expression]
theorem cycle_target (x : List Char) (k : Nat) : targetRun cycle (.call 0 [.lit []]) x k=none :=
  (ZeroResetCorrespondence.undefined_iff cycle cycle_firstOrder cycle_checked (.call 0 [.lit []]) (by trivial) x).mp
    (MultiplyingPrefixExamples.empty_source 0 x) k

end Shallot.MacroPeg.CBV.ZeroResetExamples
