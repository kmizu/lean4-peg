import MacroPeg.CBV.FrontierPairCaptureCompiler
import MacroPeg.CBV.ProducedPrefixFamilyExamples

namespace Shallot.MacroPeg.CBV.IndependentFrontierExamples
open FrontierArgumentNormalization (Argument argument arguments)
open NestedScannerArguments (choice scan)
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def lexer : MExp := .alt (.seq (.lit ['a']) (.call 0 [])) .eps
def balanced (i : Nat) (c : Char) : MExp :=
  .alt (.seq (.lit ['a']) (.seq (.call i []) (.lit [c]))) .eps

def helpers : List MExp := [.seq .eps lexer,.seq .eps (balanced 1 'b'),.seq .eps (balanced 2 'c')]
def parser (i : Nat) (A : List Char) : MExp :=
  .alt (.seq (.call i []) (.notP (choice A))) (.call 0 [])
def left : Argument := ⟨['a','b'],helpers,parser 1 ['a','b']⟩
def right : Argument := ⟨['a','c'],helpers,parser 2 ['a','c']⟩
def ds : List Argument := [left,right]

def tail : MExp := .seq (.lit ['!']) (.seq (.param 0) (.seq (.lit [':']) (.param 1)))
def original : MGrammar := ⟨helpers.map (fun b => ⟨0,b⟩) ++ [⟨2,
  RootObservation.branch (ScannerFrontier.guard left.alphabet right.alphabet)
    (.seq (.param 1) tail) (.seq (.param 0) tail)⟩]⟩
def selection : FrontierArgumentCompiler.Selection := [none,none,none,some ds]
def root : MExp := .call 3 (arguments ds)

theorem left_mask : MaskedScannerAbsorption.mask helpers left.alphabet=[true,true,false] := by decide +kernel

theorem right_mask : MaskedScannerAbsorption.mask helpers right.alphabet=[true,false,true] := by decide +kernel

theorem left_checked : FrontierArgumentNormalization.check original left=true := by decide +kernel

theorem right_checked : FrontierArgumentNormalization.check original right=true := by decide +kernel

theorem checked : FrontierArgumentCompiler.check original selection=true := by decide +kernel

/-- Checking every helper against both alphabets would incorrectly reject
these separately consuming recursive components. -/
theorem old_uniform_check_rejects :
    helpers.all (FrontierArgumentNormalization.safeCheck helpers.length left.alphabet)=false ∧
    helpers.all (FrontierArgumentNormalization.safeCheck helpers.length right.alphabet)=false := by decide +kernel

theorem non_nested : ¬NestedScannerArguments.Included left.alphabet right.alphabet ∧
    ¬NestedScannerArguments.Included right.alphabet left.alphabet := by
  constructor
  · intro h; have hh := h 'b' (by decide); cases hh
  · intro h; have hh := h 'c' (by decide); cases hh

def commonWord (n : Nat) := List.replicate n 'a'
def longWord (n : Nat) (c : Char) := commonWord n++List.replicate n c
def sample (n : Nat) (c : Char) := longWord n c++['!']++
  (if c='b' then longWord n c++[':']++commonWord n else commonWord n++[':']++longWord n c)

def sourceRun (x : List Char) (k : Nat) := evV original x .callByValuePar
  (tblV original x .callByValuePar k) [] root x.length

def preparedRun (x : List Char) (k : Nat) := evV (FrontierArgumentCompiler.target original selection) x .callByValuePar
  (tblV (FrontierArgumentCompiler.target original selection) x .callByValuePar k) []
  (FrontierArgumentCompiler.render selection root) x.length

theorem actual_captures_both_orders : ∀ n∈[1,2,4], ∀ c∈['b','c'],
    evParArgs original (sample n c) .callByValuePar (tblV original (sample n c) .callByValuePar 14) [] (arguments ds) (sample n c).length=
      some (some (if c='b' then [longWord n c,commonWord n] else [commonWord n,longWord n c])) := by decide +kernel

theorem source_executes_both_orders : ∀ n∈[1,2,4], ∀ c∈['b','c'],
    sourceRun (sample n c) 16=some (some 0) := by decide +kernel

theorem prepared_executes_both_orders : ∀ n∈[1,2,4], ∀ c∈['b','c'],
    preparedRun (sample n c) 16=some (some 0) := by decide +kernel

theorem observations (x : List Char) (rest : Option (List Char)) :
    SObs original .callByValuePar root x rest ↔ SObs (FrontierArgumentCompiler.target original selection)
      .callByValuePar (FrontierArgumentCompiler.render selection root) x rest :=
  FrontierArgumentCompiler.observations_iff original selection checked root (by trivial) x rest

theorem direct_unsafe_call_rejected : FrontierArgumentNormalization.check original
    ⟨left.alphabet,helpers,.call 2 []⟩=false := by decide +kernel

def badHelpers : List MExp := [.call 1 [],.seq (.lit ['c']) (.call 0 [])]

theorem unsafe_cycle_propagates : MaskedScannerAbsorption.mask badHelpers ['a','b']=[false,false] := by decide +kernel

theorem unsafe_cycle_rejected : MaskedScannerAbsorption.check badHelpers ['a','b'] (.call 0 [])=false := by decide +kernel

def mutualHelpers : List MExp :=
  [.alt (.seq (.lit ['a']) (.call 1 [])) .eps,.alt (.seq (.lit ['b']) (.call 0 [])) .eps]

theorem safe_mutual_component_kept : MaskedScannerAbsorption.mask mutualHelpers ['a','b']=[true,true] ∧
    MaskedScannerAbsorption.check mutualHelpers ['a','b'] (.call 0 [])=true := by decide +kernel

/-- Final closure validation supplies the actual-row invariant without
assuming convergence of candidate generation. -/
theorem candidate_validation (x : List Char) (s : Strategy) (k : Nat) (E : List (List Char)) (p q : Nat)
    (hp : p≤x.length) (h : evV original x s (tblV original x s k) E left.parser p=some (some q)) :
    evV original x s (tblV original x s k) E (scan left.alphabet) p=
      evV original x s (tblV original x s k) E (scan left.alphabet) q := by
  have hc := FrontierArgumentNormalization.checked original left left_checked
  exact MaskedScannerAbsorption.scan_after_success hc.1 _ _ hc.2.1 x s k E _ hc.2.2 p q hp h

def entries : List MixedScannerPairFusion.Entry :=
  helpers.map (fun b => ⟨none,b⟩) ++ [⟨some (left.alphabet,right.alphabet),tail⟩]
def templateRoot (args : List Argument) := MExp.seq (FrontierArgumentNormalization.preflight args) (.call 3 [])

theorem pair_checked : FrontierPairCaptureCompiler.check original selection entries=true := by decide +kernel

theorem pair_root_checked : FrontierPairCaptureCompiler.rootCheck selection entries root (templateRoot ds)=true := by decide +kernel

theorem seq_layout : (MixedScannerPairFusion.seqGrammar entries).rules.map MRule.arity=[0,0,0,0,0,0,2,2] := by decide +kernel

def targetRun (x : List Char) (k : Nat) := evV (MixedScannerPairFusion.seqGrammar entries) x .callByValueSeq
  (tblV (MixedScannerPairFusion.seqGrammar entries) x .callByValueSeq k) []
  (MixedScannerPairFusion.render entries false (templateRoot ds)) x.length

theorem seq_executes_both_orders : ∀ n∈[1,2,4], ∀ c∈['b','c'],
    targetRun (sample n c) 16=some (some 0) := by decide +kernel

theorem seq_observations (x : List Char) (rest : Option (List Char)) :
    SObs original .callByValuePar root x rest ↔
      SObs (MixedScannerPairFusion.seqGrammar entries) .callByValueSeq
        (MixedScannerPairFusion.render entries false (templateRoot ds)) x rest :=
  FrontierPairCaptureCompiler.observations_iff original selection entries pair_checked root (templateRoot ds) pair_root_checked x rest

def unbalanced := ['a','b','b','!','a','b','b',':','a']

theorem unbalanced_rejected : sourceRun unbalanced 12=some none ∧ targetRun unbalanced 12=some none := by decide +kernel

theorem missing_preflight_accepts_unbalanced : evV (MixedScannerPairFusion.seqGrammar entries) unbalanced .callByValueSeq
    (tblV (MixedScannerPairFusion.seqGrammar entries) unbalanced .callByValueSeq 12) []
    (MixedScannerPairFusion.render entries false (.call 3 [])) unbalanced.length=some (some 0) := by decide +kernel

def stuck : Argument := ⟨left.alphabet,helpers,.star .eps⟩
def nullableArgs : List Argument := [stuck,right]
def nullableSelection : FrontierArgumentCompiler.Selection := [none,none,none,some nullableArgs]
def nullableRoot : MExp := .call 3 (arguments nullableArgs)

theorem nullable_checked : FrontierPairCaptureCompiler.check original nullableSelection entries=true := by decide +kernel

theorem nullable_root_checked : FrontierPairCaptureCompiler.rootCheck nullableSelection entries nullableRoot (templateRoot nullableArgs)=true := by decide +kernel

theorem nullable_source (x : List Char) (k : Nat) :
    evV original x .callByValuePar (tblV original x .callByValuePar k) [] nullableRoot x.length=none := by
  have hs : evV original x .callByValuePar (tblV original x .callByValuePar k) [] (.star .eps) x.length=none := by
    rw [evV_star]; exact evStar_stuck (j := x.length) rfl (by omega)
  have harg : evV original x .callByValuePar (tblV original x .callByValuePar k) [] (argument stuck) x.length=none :=
    evV_seq_none hs
  have hr : ruleAtM original.rules 3=some ⟨2,RootObservation.branch (ScannerFrontier.guard left.alphabet right.alphabet)
    (.seq (.param 1) tail) (.seq (.param 0) tail)⟩ := rfl
  change evV _ _ _ _ [] (.call 3 [argument stuck,argument right]) _=none
  rw [evV_call_par hr rfl (by decide),evPar_cons_none harg]

theorem nullable_seq (x : List Char) (k : Nat) :
    evV (MixedScannerPairFusion.seqGrammar entries) x .callByValueSeq
      (tblV (MixedScannerPairFusion.seqGrammar entries) x .callByValueSeq k) []
      (MixedScannerPairFusion.render entries false (templateRoot nullableArgs)) x.length=none :=
  (FrontierPairCaptureCompiler.undefined_iff original nullableSelection entries nullable_checked nullableRoot
    (templateRoot nullableArgs) nullable_root_checked x).mp (nullable_source x) k

def recursiveTail (child : MExp) : MExp := .seq (.lit ['!']) (.seq (.param 0) (.seq (.lit [':'])
  (.seq (.param 1) (.seq (.lit ['?']) (.seq (.alt (.seq (.lit ['@']) child) .eps)
    (.seq (.lit ['/']) (.seq (.param 1) (.seq (.lit [':']) (.param 0)))))))))
def recursiveOriginal : MGrammar := ⟨helpers.map (fun b => ⟨0,b⟩) ++ [⟨2,
  RootObservation.branch (ScannerFrontier.guard left.alphabet right.alphabet)
    (.seq (.param 1) (recursiveTail root)) (.seq (.param 0) (recursiveTail root))⟩]⟩
def recursiveEntries : List MixedScannerPairFusion.Entry := helpers.map (fun b => ⟨none,b⟩) ++
  [⟨some (left.alphabet,right.alphabet),recursiveTail (templateRoot ds)⟩]

theorem recursive_checked : FrontierPairCaptureCompiler.check recursiveOriginal selection recursiveEntries=true := by decide +kernel

theorem recursive_root_checked : FrontierPairCaptureCompiler.rootCheck selection recursiveEntries root (templateRoot ds)=true := by decide +kernel

def leftValue (n : Nat) (c : Char) := if c='b' then longWord n c else commonWord n
def rightValue (n : Nat) (c : Char) := if c='b' then commonWord n else longWord n c
def recursiveSimple (n : Nat) (c : Char) := sample n c++['?','/']++rightValue n c++[':']++leftValue n c
def recursiveNested (n : Nat) (c : Char) (m : Nat) (d : Char) := sample n c++['?','@']++recursiveSimple m d++
  ['/']++rightValue n c++[':']++leftValue n c

theorem recursive_source : ∀ pair∈[((1,'b'),(2,'c')),((2,'c'),(1,'b')),((2,'b'),(0,'c'))],
    let x := recursiveNested pair.1.1 pair.1.2 pair.2.1 pair.2.2
    evV recursiveOriginal x .callByValuePar (tblV recursiveOriginal x .callByValuePar 20) [] root x.length=some (some 0) := by decide +kernel

theorem recursive_seq : ∀ pair∈[((1,'b'),(2,'c')),((2,'c'),(1,'b')),((2,'b'),(0,'c'))],
    let x := recursiveNested pair.1.1 pair.1.2 pair.2.1 pair.2.2
    evV (MixedScannerPairFusion.seqGrammar recursiveEntries) x .callByValueSeq
      (tblV (MixedScannerPairFusion.seqGrammar recursiveEntries) x .callByValueSeq 20) []
      (MixedScannerPairFusion.render recursiveEntries false (templateRoot ds)) x.length=some (some 0) := by decide +kernel

theorem recursive_observations (x : List Char) (rest : Option (List Char)) :
    SObs recursiveOriginal .callByValuePar root x rest ↔
      SObs (MixedScannerPairFusion.seqGrammar recursiveEntries) .callByValueSeq
        (MixedScannerPairFusion.render recursiveEntries false (templateRoot ds)) x rest :=
  FrontierPairCaptureCompiler.observations_iff recursiveOriginal selection recursiveEntries recursive_checked root
    (templateRoot ds) recursive_root_checked x rest

end Shallot.MacroPeg.CBV.IndependentFrontierExamples
