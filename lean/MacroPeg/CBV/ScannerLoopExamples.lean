import MacroPeg.CBV.ScannerLoopCompiler
import MacroPeg.CBV.StatefulScannerBridge

namespace Shallot.MacroPeg.CBV.ScannerLoopExamples
open ScannerLoopCompiler
open RecursiveScannerProductCompiler (Arg sourceExpr)
open StatefulScanner (advance run next)
set_option maxHeartbeats 0
set_option maxRecDepth 100000

abbrev M := StatefulScannerBridge.changedState
def block (k : Nat) : List Char := 'a'::List.replicate k 'b'

/-- The child captures a fresh scanner result; after the recursive child
finishes, the parent replays its own whole retained value. -/
def tail : Arg := .alt
  (.seq (.lit ['c']) (.seq (.user 0 (.user 1 (.lit []))) (.param 0)))
  (.lit ['d'])

theorem checked : check M 0 tail=true := by decide +kernel

theorem inferred_alphabet : alphabet M=['a','b'] := by decide +kernel

theorem advance_bs (k : Nat) : advance M 1 (List.replicate k 'b')=some 1 := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [List.replicate_succ,advance,StatefulScannerBridge.changedState,next,Shallot.beqChar] using ih

theorem advance_block (k : Nat) : advance M 0 (block k)=some 1 := by
  simpa [block,advance,StatefulScannerBridge.changedState,next,Shallot.beqChar] using advance_bs k

/-- There is no bound on the actual captured scanner word. Its state
profile and readability are inferred for every a b^k. -/
theorem readable_blocks (k : Nat) :
    CaptureTransitionProfile.profile (DynamicScannerCapture.observer M) (block k)∈H M 0 := by
  apply List.mem_filter.mpr
  refine ⟨AlphabetCaptureProfiles.word_mem _ (DynamicScannerCapture.observer_valid M) (alphabet M) (block k) ?_,?_⟩
  · intro c hc
    simp only [block,List.mem_cons,List.mem_replicate] at hc
    rcases hc with rfl | ⟨_,rfl⟩ <;> decide
  · exact (ScannerFrontierCertificate.check_actual M (block k) 0).mpr (by rw [advance_block]; decide)

theorem scanned_blocks (k : Nat) : run M 0 (block k++['c'])=(1,['c']) := by
  rw [StatefulScanner.run_after_prefix M (block k) ['c'] 0 1 (advance_block k)]
  rfl

/-- This is the actual installed getter row, with the scanner helper
stabilized from its own rules. It supplies the new retained argument. -/
theorem getter_row (x : List Char) (k p : Nat) (E : List (List Char)) (hp : p≤x.length) :
    valAt (RecursiveScannerProductCompiler.sourceTable M (entries 0) (bodies tail) x (k+1)
      (RecursiveScannerProductCompiler.offset M+1) E) p=
      some (some (run M 0 (sfx x p)).2.length) := by
  rw [RecursiveScannerProductCorrespondence.source_step M (entries 0) (bodies tail) x k 1 (.lit []) (by rfl) E p hp]
  have hs := RecursiveScannerProductHeader.source_scan M (entries 0) (bodies tail) 0 x k p E hp
  change evV _ _ _ _ E (.seq (.call 0 []) (.lit [])) p=_
  refine (evV_seq_ok (b := .lit []) hs).trans ?_
  simp only [evV,Shallot.stripPrefix?,length_sfx x
    (RecursiveScannerProductHeader.source_scan_prefix M (entries 0) (bodies tail) 0 x k p E hp).1]

def sourceRun (x : List Char) (k : Nat) :=
  evV (source M 0 tail) x .callByValuePar (tblV (source M 0 tail) x .callByValuePar k)
    [] (sourceExpr M root) x.length

def targetRun (x : List Char) (k : Nat) :=
  evV (target M 0 tail) x .callByValueSeq (tblV (target M 0 tail) x .callByValueSeq k)
    [] (targetExpr M tail) x.length

def simpleInput : List Char := block 1++block 3++block 1++['d']
def recursiveInput : List Char := block 1++block 3++block 1++['c']++block 0++['d']++block 1

theorem source_simple : sourceRun simpleInput 12=some (some 0) := by decide +kernel

theorem source_recursive : sourceRun recursiveInput 12=some (some 0) := by decide +kernel

theorem target_simple : ∃ k, targetRun simpleInput k=some (some 0) :=
  (defined_iff M 0 tail checked simpleInput (some 0)).mp ⟨12,source_simple⟩

theorem target_recursive : ∃ k, targetRun recursiveInput k=some (some 0) :=
  (defined_iff M 0 tail checked recursiveInput (some 0)).mp ⟨12,source_recursive⟩

theorem direct_target : targetRun simpleInput 12=some (some 0) := by decide +kernel

theorem direct_recursive_target : targetRun recursiveInput 12=some (some 0) := by decide +kernel

theorem failed_tail : sourceRun (block 1++['X']) 6=some none ∧
    targetRun (block 1++['X']) 8=some none := by decide +kernel

theorem nullable_samples : ∀ k∈[0,1,2,4,8], sourceRun ['X'] k=none ∧ targetRun ['X'] k=none := by decide +kernel

/-- A nonreadable b cannot be used as a loop capture; the source scanner
would stop immediately and its successful query would be nullable. -/
theorem bad_capture_rejected :
    ProfileCheckedScannerCorrespondence.check M (entries 0) (bodies tail) (C M 0) (A M 0) [] (.user 0 (.lit ['b']))=false := by decide +kernel

theorem bad_scope_rejected : check M 0 (.user 2 (.lit []))=false := by decide +kernel

theorem bad_priority_rejected :
    ReadableScannerProfiles.arcsCheck (⟨fun _ : Fin 2 => [('a',0),('a',1)]⟩ : StatefulScanner.Machine 2)=false := by decide +kernel

theorem language : ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
    SObs (source M 0 tail) .callByValuePar (sourceExpr M root) x (some []) ↔
      SObs g .callByValueSeq start x (some []) :=
  language_translation M 0 tail checked

end Shallot.MacroPeg.CBV.ScannerLoopExamples
