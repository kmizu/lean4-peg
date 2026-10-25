import MacroPeg.CBV.OriginHeadRawCompiler

namespace Shallot.MacroPeg.CBV.OriginHeadExamples
open OriginHeadRawCompiler
open MultiplyingPrefixCompiler (Spec source sourceBody)
open RepeatedWordArguments (copies)
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def parent : Spec := ⟨1,3,.seq (.star (.chr 'a')) (.chr '!'),.chr 'Z'⟩
def childPlan : ReplayControlFusion.Plan := .alt (.leaf 2) (.leaf 3)
def continuation : MExp := .seq (.chr 'Y') (.seq (.param 0)
  (.seq (.alt (.call 0 [.lit ['x']]) .eps) (.param 0)))
def specs : List Spec := [parent,⟨2,0,.eps,continuation⟩,⟨9,2,.eps,.chr 'a'⟩]
def entry : MExp := .call 0 [.lit ['a']]
def dynamicEntry : MExp := .call 0 [.seq (.star (.chr 'c')) (.chr 'd')]
theorem parent_lookup : (entries specs)[0]?=some (.growth parent) := rfl
theorem child_lookup : (entries specs)[parent.callee]?=some (.origin childPlan) := rfl
theorem checked : check specs 0=true := by decide +kernel
theorem old_backend_rejected : MixedForwardingReset.check specs=false := by decide +kernel
theorem firstOrder : (source specs).FirstOrder := by
  simp [source,sourceBody,specs,parent,continuation,MGrammar.FirstOrder,MExp.FirstOrder,MExp.FirstOrderArgs,
    RepeatedWordArguments.expression]

def sourceRun (e : MExp) (x : List Char) (k : Nat) :=
  evV (source specs) x .callByValuePar (tblV (source specs) x .callByValuePar k) [] e x.length
def targetRun (e : MExp) (x : List Char) (k : Nat) :=
  evV (target specs 0 parent childPlan) x .callByValueSeq (tblV (target specs 0 parent childPlan) x .callByValueSeq k)
    [] (render specs 0 parent childPlan e) x.length

theorem closed_origin : sourceRun entry ['a','a','a','!'] 16=some (some 0) ∧
    targetRun entry ['a','a','a','!'] 16=some (some 0) := by decide +kernel
theorem replay_origin : sourceRun (.call 0 [.lit ['b']]) ['b','b','b','Y','b','b','b','x','Z','b','b','b','!'] 16=some (some 0) ∧
    targetRun (.call 0 [.lit ['b']]) ['b','b','b','Y','b','b','b','x','Z','b','b','b','!'] 16=some (some 0) := by decide +kernel

def input (n : Nat) := let w := List.replicate n 'c'++['d'];
  copies w 3++['Y']++copies w 3++['x','Z']++copies w 3++['!']
theorem dynamic_source : ∀ n∈[0,1,4], sourceRun dynamicEntry (input n) 16=some (some 0) := by decide +kernel
theorem dynamic_target : ∀ n∈[0,1,4], targetRun dynamicEntry (input n) 16=some (some 0) := by decide +kernel

theorem preflight_required : sourceRun entry ['a','!'] 16=some none ∧ targetRun entry ['a','!'] 16=some none ∧
    evV (target specs 0 parent childPlan) ['a','!'] .callByValueSeq
      (tblV (target specs 0 parent childPlan) ['a','!'] .callByValueSeq 16) [] (.call 26 []) 2=some (some 0) := by decide +kernel

theorem committed_child : sourceRun entry ['a','a','a','Y','a','a','a','x','Z','a','a','a','!'] 16=some none ∧
    targetRun entry ['a','a','a','Y','a','a','a','x','Z','a','a','a','!'] 16=some none := by decide +kernel

theorem parent_fallback : sourceRun entry ['a','Z'] 16=some (some 0) ∧
    targetRun entry ['a','Z'] 16=some (some 0) := by decide +kernel
theorem nullable_argument : targetRun (.call 0 [.star (.lit [])]) ['a','a','a','!'] 16=none := by decide +kernel
theorem short_new_word : targetRun (.call 0 [.lit ['b']]) ['b','b','b','Y','b','x','Z','b','!'] 16=some none := by decide +kernel
theorem helper_privacy : targetRun (.call 26 []) ['a','!'] 16=some none := by decide +kernel
theorem fixed_target : (target specs 0 parent childPlan).rules.length=33 := rfl

theorem observations (e : MExp) (he : e.FirstOrder) (x : List Char) (rest : Option (List Char)) :
    SObs (source specs) .callByValuePar e x rest ↔
      SObs (target specs 0 parent childPlan) .callByValueSeq (render specs 0 parent childPlan e) x rest :=
  OriginHeadRawCompiler.observations_iff specs 0 parent childPlan parent_lookup child_lookup firstOrder checked e he x rest

/-- Directly distributing a suffix into alternatives retries a committed child. -/
theorem naive_suffix_counterexample :
    evV (source specs) ['a','b'] .callByValuePar (tblV (source specs) ['a','b'] .callByValuePar 0) []
      (.seq (.alt (.lit ['a']) (.lit ['a','b'])) (.notP .any)) 2=some none ∧
    evV (source specs) ['a','b'] .callByValuePar (tblV (source specs) ['a','b'] .callByValuePar 0) []
      (.alt (.seq (.lit ['a']) (.notP .any)) (.seq (.lit ['a','b']) (.notP .any))) 2=some (some 0) := by decide +kernel

end Shallot.MacroPeg.CBV.OriginHeadExamples
