import MacroPeg.CBV.ProducedPrefixHeaders

namespace Shallot.MacroPeg.CBV.ProducedPrefixExamples
open ProducedPrefixCompiler
open ReplayControlFusion (Part Plan)
open RepeatedWordArguments (copies)
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def producer : MExp := .seq (.star (.chr 'a')) (.chr 'b')
def continuation : MExp := .seq (.chr '!') (.seq (.call 1 [.param 0]) (.seq (.call 2 [.star (.chr 'c')]) (.param 0)))
def growth : MultiplyingPrefixCompiler.Spec := ⟨1,3,.seq (.chr '@') (.seq (.call 0 [producer]) (.param 0)),.chr 'g'⟩
def ps : List Part := [⟨false,.chr 'X'⟩,⟨true,.eps⟩,⟨false,producer⟩]
def specs : List Entry := [.produced producer continuation,.growth growth,
  .origin (.alt (.leaf 0) (.leaf 1)),.origin (.leaf 2)]
def headers := [3,0,0,0]
abbrev inlineSource := source ps specs
abbrev original := ProducedPrefixHeaders.original ps specs headers
abbrev compiled := target ps specs
abbrev compiledEntry := render ps specs

def entry : MExp := .call 0 [producer]
theorem checked : ProducedPrefixHeaders.check ps specs headers=true := by decide +kernel
theorem root_checked : conforms specs entry=true := by decide +kernel

theorem inline_firstOrder : inlineSource.FirstOrder := by
  simp [inlineSource,source,body,ps,specs,producer,continuation,growth,MultiplyingPrefixCompiler.sourceBody,
    Plan.exp,ReplayControlFusion.sourceLeaf,MGrammar.FirstOrder,MExp.FirstOrder,MExp.FirstOrderArgs,RepeatedWordArguments.expression]
theorem firstOrder : original.FirstOrder := by
  simp [original,ProducedPrefixHeaders.original,ProducedPrefixHeaders.headerBody,headers,
    body,ps,specs,producer,continuation,growth,MultiplyingPrefixCompiler.sourceBody,
    Plan.exp,ReplayControlFusion.sourceLeaf,MGrammar.FirstOrder,MExp.FirstOrder,MExp.FirstOrderArgs,RepeatedWordArguments.expression]

def sourceRun (e : MExp) (x : List Char) (k : Nat) := evV original x .callByValuePar (tblV original x .callByValuePar k) [] e x.length
def targetRun (e : MExp) (x : List Char) (k : Nat) := evV compiled x .callByValueSeq (tblV compiled x .callByValueSeq k) [] (compiledEntry e) x.length

def word (n : Nat) := List.replicate n 'a'++['b']
def simple (w : List Char) (n : Nat) := w++['!']++w++['g']++List.replicate n 'c'++w
def nested (w v : List Char) (n : Nat) := w++['!']++copies w 3++['g','@']++simple v n++w++List.replicate n 'c'++w

theorem simple_source : ∀ n∈[0,1,4], sourceRun entry (simple (word n) n) 16=some (some 0) := by decide +kernel
theorem simple_target : ∀ n∈[0,1,4], targetRun entry (simple (word n) n) 16=some (some 0) := by decide +kernel
theorem nested_source : ∀ pair∈[(0,4),(1,0),(4,2)], sourceRun entry (nested (word pair.1) (word pair.2) 2) 16=some (some 0) := by decide +kernel
theorem nested_target : ∀ pair∈[(0,4),(1,0),(4,2)], targetRun entry (nested (word pair.1) (word pair.2) 2) 16=some (some 0) := by decide +kernel

theorem origin_short_result : sourceRun (.call 2 [.lit ['X','?']]) ['X','?'] 16=some (some 1) ∧
    targetRun (.call 2 [.lit ['X','?']]) ['X','?'] 16=some (some 1) := by decide +kernel

theorem wrong_capture_rejected : conforms specs (.call 0 [.lit ['a']])=false ∧
    sourceRun (.call 0 [.lit ['a']]) ['a','b','!','a','g','a'] 16=some (some 0) ∧
    targetRun (.call 0 [.lit ['a']]) ['a','b','!','a','g','a'] 16=some none := by decide +kernel

theorem wrong_header_rejected : ProducedPrefixHeaders.check ps specs [2,0,0,0]=false := by decide +kernel
theorem missing_header_rejected : ProducedPrefixHeaders.check ps specs []=false := by decide +kernel
theorem nested_bad_argument_rejected : ProducedPrefixCompiler.check ps
    [.produced producer continuation,.growth ⟨1,3,.call 0 [.lit ['a']],.chr 'g'⟩,
      .origin (.alt (.leaf 0) (.leaf 1)),.origin (.leaf 2)]=false := by decide +kernel
theorem private_helpers : targetRun (.call 23 []) ['X'] 16=some none := by decide +kernel
theorem arity_before_argument : sourceRun (.call 0 [.star (.lit []),.eps]) ['!'] 16=some none ∧
    targetRun (.call 0 [.star (.lit []),.eps]) ['!'] 16=some none := by decide +kernel
theorem fixed_target : compiled.rules.length=27 := rfl

theorem observations (e : MExp) (he : e.FirstOrder) (hs : conforms specs e=true) (x : List Char) (rest : Option (List Char)) :
    SObs original .callByValuePar e x rest ↔ SObs compiled .callByValueSeq (compiledEntry e) x rest :=
  ProducedPrefixHeaders.observations_iff ps specs headers checked firstOrder inline_firstOrder e he hs x rest

def tinyPs : List Part := [⟨false,producer⟩]
def tinySpecs : List Entry := [.produced producer (.param 0),.origin (.leaf 0)]
def tinyHeaders := [1,0]
abbrev tinySource := ProducedPrefixHeaders.original tinyPs tinySpecs tinyHeaders
abbrev tinyTarget := target tinyPs tinySpecs

theorem tiny_checked : ProducedPrefixHeaders.check tinyPs tinySpecs tinyHeaders=true := by decide +kernel
theorem clock_gap : evV tinySource ['b','b'] .callByValuePar (tblV tinySource ['b','b'] .callByValuePar 1) [] entry 2=none ∧
    evV tinySource ['b','b'] .callByValuePar (tblV tinySource ['b','b'] .callByValuePar 2) [] entry 2=some (some 0) ∧
    evV tinyTarget ['b','b'] .callByValueSeq (tblV tinyTarget ['b','b'] .callByValueSeq 1) [] (render tinyPs tinySpecs entry) 2=some (some 0) := by decide +kernel

def nullable : List Entry := [.produced (.star (.lit [])) (.chr '!')]
theorem nullable_checked : ProducedPrefixCompiler.check [] nullable=true := by decide +kernel
theorem nullable_firstOrder : (source [] nullable).FirstOrder := by simp [source,body,nullable,MGrammar.FirstOrder,MExp.FirstOrder]
theorem nullable_root_checked : conforms nullable (.call 0 [.star (.lit [])])=true := by decide +kernel

theorem nullable_source (x : List Char) (k : Nat) :
    evV (source [] nullable) x .callByValuePar (tblV (source [] nullable) x .callByValuePar k) [] (.call 0 [.star (.lit [])]) x.length=none := by
  have hr : ruleAtM (source [] nullable).rules 0=some ⟨1,.seq (.star (.lit [])) (.chr '!')⟩ := rfl
  have hz : evV (source [] nullable) x .callByValuePar (tblV (source [] nullable) x .callByValuePar k) [] (.star (.lit [])) x.length=none := by
    rw [evV_star]
    exact evStar_stuck (j := x.length) (by simp [evV,Shallot.stripPrefix?,length_sfx x (Nat.le_refl _)]) (by omega)
  rw [evV_call_par hr rfl (by decide),evPar_cons_none hz]

theorem nullable_target (x : List Char) (k : Nat) :
    evV (target [] nullable) x .callByValueSeq (tblV (target [] nullable) x .callByValueSeq k) []
      (render [] nullable (.call 0 [.star (.lit [])])) x.length=none :=
  (ProducedPrefixCorrespondence.undefined_iff [] nullable nullable_firstOrder nullable_checked (.call 0 [.star (.lit [])]) (by trivial)
    nullable_root_checked x).mp (nullable_source x) k

end Shallot.MacroPeg.CBV.ProducedPrefixExamples
