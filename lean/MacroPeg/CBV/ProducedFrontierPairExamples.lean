import MacroPeg.CBV.ProducedFrontierPairCompiler
import MacroPeg.CBV.IndependentFrontierExamples

namespace Shallot.MacroPeg.CBV.ProducedFrontierPairExamples
open IndependentFrontierExamples (helpers left right ds root selection entries templateRoot sample
  tail recursiveTail recursiveEntries recursiveNested unbalanced nullableArgs nullableSelection nullableRoot)
open ScannedPairFusion (maxScanner)
open NestedScannerArguments (scan)
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def original : MGrammar := ⟨helpers.map (fun b => ⟨0,b⟩) ++
  [⟨2,.seq (maxScanner left.alphabet right.alphabet) tail⟩]⟩
def recursiveOriginal : MGrammar := ⟨helpers.map (fun b => ⟨0,b⟩) ++
  [⟨2,.seq (maxScanner left.alphabet right.alphabet) (recursiveTail root)⟩]⟩

theorem checked : ProducedFrontierPairCompiler.check original selection entries=true := by decide +kernel

theorem root_checked : ProducedFrontierPairCompiler.rootCheck selection entries root (templateRoot ds)=true := by decide +kernel

theorem actual_source_rule : ruleAtM original.rules 3=some
    ⟨2,.seq (maxScanner left.alphabet right.alphabet) tail⟩ := by rfl

theorem actual_head_closed : ZeroResetOrigin.closedCheck (maxScanner left.alphabet right.alphabet)=true := by decide +kernel

def sourceRun (x : List Char) (k : Nat) := evV original x .callByValuePar (tblV original x .callByValuePar k) [] root x.length

theorem source_both_orders : ∀ n∈[1,2,4], ∀ c∈['b','c'], sourceRun (sample n c) 16=some (some 0) := by decide +kernel

theorem seq_both_orders : ∀ n∈[1,2,4], ∀ c∈['b','c'],
    IndependentFrontierExamples.targetRun (sample n c) 16=some (some 0) :=
  IndependentFrontierExamples.seq_executes_both_orders

theorem observations (x : List Char) (rest : Option (List Char)) :
    SObs original .callByValuePar root x rest ↔ SObs (MixedScannerPairFusion.seqGrammar entries) .callByValueSeq
      (MixedScannerPairFusion.render entries false (templateRoot ds)) x rest :=
  ProducedFrontierPairCompiler.observations_iff original selection entries checked root (templateRoot ds) root_checked x rest

/-- The two source-body shapes agree only after deriving their actual
argument/frontier alignment; whole emitted grammars share one fixed target. -/
theorem original_replay_correspondence (x : List Char) (rest : Option (List Char)) :
    SObs original .callByValuePar root x rest ↔
      SObs IndependentFrontierExamples.original .callByValuePar root x rest :=
  (observations x rest).trans (IndependentFrontierExamples.seq_observations x rest).symm

theorem recursive_checked : ProducedFrontierPairCompiler.check recursiveOriginal selection recursiveEntries=true := by decide +kernel

theorem recursive_root_checked : ProducedFrontierPairCompiler.rootCheck selection recursiveEntries root (templateRoot ds)=true := by decide +kernel

theorem recursive_source : ∀ pair∈[((1,'b'),(2,'c')),((2,'c'),(1,'b')),((2,'b'),(0,'c'))],
    let x := recursiveNested pair.1.1 pair.1.2 pair.2.1 pair.2.2
    evV recursiveOriginal x .callByValuePar (tblV recursiveOriginal x .callByValuePar 20) [] root x.length=some (some 0) := by decide +kernel

theorem recursive_seq : ∀ pair∈[((1,'b'),(2,'c')),((2,'c'),(1,'b')),((2,'b'),(0,'c'))],
    let x := recursiveNested pair.1.1 pair.1.2 pair.2.1 pair.2.2
    evV (MixedScannerPairFusion.seqGrammar recursiveEntries) x .callByValueSeq
      (tblV (MixedScannerPairFusion.seqGrammar recursiveEntries) x .callByValueSeq 20) []
      (MixedScannerPairFusion.render recursiveEntries false (templateRoot ds)) x.length=some (some 0) :=
  IndependentFrontierExamples.recursive_seq

theorem recursive_observations (x : List Char) (rest : Option (List Char)) :
    SObs recursiveOriginal .callByValuePar root x rest ↔
      SObs (MixedScannerPairFusion.seqGrammar recursiveEntries) .callByValueSeq
        (MixedScannerPairFusion.render recursiveEntries false (templateRoot ds)) x rest :=
  ProducedFrontierPairCompiler.observations_iff recursiveOriginal selection recursiveEntries recursive_checked root
    (templateRoot ds) recursive_root_checked x rest

theorem unbalanced_rejected : sourceRun unbalanced 12=some none := by decide +kernel

theorem source_seq_unchanged_leaves_input : evV original (sample 2 'b') .callByValueSeq
    (tblV original (sample 2 'b') .callByValueSeq 16) [] root (sample 2 'b').length=some (some 2) := by decide +kernel

def crossing := ['a','b','c','!','a','b',':','a']
def unionOriginal : MGrammar := ⟨helpers.map (fun b => ⟨0,b⟩) ++
  [⟨2,.seq (scan ['a','b','c']) tail⟩]⟩

theorem union_is_not_maximum : sourceRun crossing 12=some none ∧
    evV unionOriginal crossing .callByValuePar (tblV unionOriginal crossing .callByValuePar 12) [] root crossing.length=some (some 0) := by decide +kernel

theorem union_head_rejected : ProducedFrontierPairCompiler.check unionOriginal selection entries=false := by decide +kernel

theorem nullable_checked : ProducedFrontierPairCompiler.check original nullableSelection entries=true := by decide +kernel

theorem nullable_root_checked : ProducedFrontierPairCompiler.rootCheck nullableSelection entries nullableRoot (templateRoot nullableArgs)=true := by decide +kernel

theorem nullable_source (x : List Char) (k : Nat) :
    evV original x .callByValuePar (tblV original x .callByValuePar k) [] nullableRoot x.length=none := by
  have hs : evV original x .callByValuePar (tblV original x .callByValuePar k) [] (.star .eps) x.length=none := by
    rw [evV_star]; exact evStar_stuck (j := x.length) rfl (by omega)
  have harg : evV original x .callByValuePar (tblV original x .callByValuePar k) []
      (FrontierArgumentNormalization.argument IndependentFrontierExamples.stuck) x.length=none := evV_seq_none hs
  rw [show nullableRoot=.call 3 [FrontierArgumentNormalization.argument IndependentFrontierExamples.stuck,
      FrontierArgumentNormalization.argument right] by rfl]
  rw [evV_call_par actual_source_rule rfl (by decide),evPar_cons_none harg]

theorem nullable_seq (x : List Char) (k : Nat) :
    evV (MixedScannerPairFusion.seqGrammar entries) x .callByValueSeq
      (tblV (MixedScannerPairFusion.seqGrammar entries) x .callByValueSeq k) []
      (MixedScannerPairFusion.render entries false (templateRoot nullableArgs)) x.length=none :=
  (ProducedFrontierPairCompiler.undefined_iff original nullableSelection entries nullable_checked nullableRoot
    (templateRoot nullableArgs) nullable_root_checked x).mp (nullable_source x) k

end Shallot.MacroPeg.CBV.ProducedFrontierPairExamples
