import MacroPeg.CBV.ScannerLoopExamples

namespace Shallot.MacroPeg.CBV.ScannerLoopExamples
open ScannerLoopCompiler
open RecursiveScannerProductCompiler (sourceExpr sourceTable offset)
open RecursiveScannerProductCorrespondence (source_zero source_step)

theorem frozen_empty_row (k : Nat) :
    valAt (sourceTable M (entries 0) (bodies tail) ['X'] k (offset M) [[]]) 1=none := by
  cases k with
  | zero => simpa using source_zero M (entries 0) (bodies tail) ['X'] 0 [[]] 1
  | succ k =>
    rw [show offset M=offset M+0 by omega,
      source_step M (entries 0) (bodies tail) ['X'] k 0 tail (by rfl) [[]] 1 (by decide)]
    have hscan : evV (source M 0 tail) ['X'] .callByValuePar
        (sourceTable M (entries 0) (bodies tail) ['X'] k) [[]] (.call 0 []) 1=some (some 1) :=
      RecursiveScannerProductHeader.source_scan M (entries 0) (bodies tail) 0 ['X'] k 1 [[]] (by decide)
    have hstep : evV (source M 0 tail) ['X'] .callByValuePar
        (sourceTable M (entries 0) (bodies tail) ['X'] k) [[]] (GuardedScannerIteration.step (0 : Fin 2)) 1=some (some 1) := by
      unfold GuardedScannerIteration.step
      refine (evV_seq_ok (b := .andP (.param 0)) hscan).trans ?_
      rfl
    have hstar : evV (source M 0 tail) ['X'] .callByValuePar
        (sourceTable M (entries 0) (bodies tail) ['X'] k) [[]]
        (.star (GuardedScannerIteration.step (0 : Fin 2))) 1=none := by
      rw [evV_star,evStar_stuck hstep (by omega)]
    exact evV_seq_none (evV_seq_none hstar)

theorem frozen_root_none (k : Nat) :
    evV (source M 0 tail) ['X'] .callByValuePar (sourceTable M (entries 0) (bodies tail) ['X'] k)
      [] (sourceExpr M root) 1=none := by
  have hf := RecursiveScannerProductCompiler.source_rule M (entries 0) (bodies tail) 0 tail (by rfl)
  have hg := RecursiveScannerProductCompiler.source_rule M (entries 0) (bodies tail) 1 (.lit []) (by rfl)
  have harg : evV (source M 0 tail) ['X'] .callByValuePar
      (sourceTable M (entries 0) (bodies tail) ['X'] k) [] (sourceExpr M (.user 1 (.lit []))) 1=
      valAt (sourceTable M (entries 0) (bodies tail) ['X'] k (offset M+1) [[]]) 1 := by
    rw [sourceExpr,evV_call_par hg rfl (by decide)]
    rfl
  change evV _ _ _ _ [] (.call (offset M+0) [sourceExpr M (.user 1 (.lit []))]) 1=none
  rw [evV_call_par hf rfl (by decide)]
  simp only [evParArgs,harg]
  cases k with
  | zero => rw [source_zero]
  | succ k => rw [getter_row ['X'] k 1 [[]] (by decide)]; exact frozen_empty_row (k+1)

/-- Empty capture makes the actual scanner/query step nullable. Every
ordinary physical source clock is undefined, and so is the generated Seq
grammar at every ordinary clock. -/
theorem source_allclock_none (k : Nat) : sourceRun ['X'] k=none := by
  have hs := RecursiveParserStability.helpers_stable (RecursiveScannerProductHelpers.lexical M)
    (RecursiveScannerProductHelpers.installed M (RecursiveScannerProductCompiler.sourceRules M (entries 0) (bodies tail))) ['X'] .callByValuePar
  cases hv : sourceRun ['X'] k with
  | none => rfl
  | some v =>
    obtain ⟨j,hj⟩ := (ClockFreezing.defined_iff (source M 0 tail) ['X'] .callByValuePar _ _ hs []
      (sourceExpr M root) 1 v).mpr ⟨k,hv⟩
    change evV _ _ _ (sourceTable M (entries 0) (bodies tail) ['X'] j) [] (sourceExpr M root) 1=some v at hj
    rw [frozen_root_none] at hj
    cases hj

theorem target_allclock_none : ∀ k, targetRun ['X'] k=none :=
  (undefined_iff M 0 tail checked ['X']).mp source_allclock_none

/-- Bypassing the frontier check would turn source nullable divergence
into finite target failure. The rejected capture really is unsound. -/
theorem unreadable_capture_mismatch :
    evV (source M 0 tail) ['b'] .callByValuePar (tblV (source M 0 tail) ['b'] .callByValuePar 6)
      [] (sourceExpr M (.user 0 (.lit ['b']))) 1=none ∧
    evV (target M 0 tail) ['b'] .callByValueSeq (tblV (target M 0 tail) ['b'] .callByValueSeq 8)
      [] (RecursiveScannerProductCompiler.plain M (bodies tail) [] (.user 0 (.lit ['b']))) 1=some none := by decide +kernel

end Shallot.MacroPeg.CBV.ScannerLoopExamples
