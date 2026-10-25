import MacroPeg.CBV.ScannerLoopExamples

namespace Shallot.MacroPeg.CBV.ScannerLoopExamples
open ScannerLoopCompiler
open RecursiveScannerProductCompiler (sourceExpr sourceTable)

/-- Every a b^k is captured by an actual source user call at an ordinary
physical clock. No finite list of permitted captured strings is supplied. -/
theorem physical_unbounded_capture (k : Nat) :
    ∃ clock, evV (source M 0 tail) (block k++['c']) .callByValuePar
      (tblV (source M 0 tail) (block k++['c']) .callByValuePar clock) []
      (sourceExpr M (.user 1 (.lit []))) (block k++['c']).length=some (some 1) ∧
      pre (block k++['c']) (block k++['c']).length 1=block k := by
  have hrow := RecursiveScannerProductCompiler.source_rule M (entries 0) (bodies tail) 1 (.lit []) (by rfl)
  have hfrozen : evV (source M 0 tail) (block k++['c']) .callByValuePar
      (sourceTable M (entries 0) (bodies tail) (block k++['c']) 1) []
      (sourceExpr M (.user 1 (.lit []))) (block k++['c']).length=some (some 1) := by
    rw [sourceExpr,evV_call_par hrow rfl (by decide)]
    simp only [sourceExpr,evParArgs,evV,Shallot.stripPrefix?,sfx_self,pre,Nat.sub_self,List.take_zero]
    rw [getter_row (block k++['c']) 0 _ [[]] (Nat.le_refl _)]
    simp only [sfx_self,scanned_blocks]
    rfl
  have hs := RecursiveParserStability.helpers_stable (RecursiveScannerProductHelpers.lexical M)
    (RecursiveScannerProductHelpers.installed M (RecursiveScannerProductCompiler.sourceRules M (entries 0) (bodies tail)))
    (block k++['c']) .callByValuePar
  obtain ⟨clock,hclock⟩ := (ClockFreezing.defined_iff (source M 0 tail) (block k++['c']) .callByValuePar _ _ hs []
    (sourceExpr M (.user 1 (.lit []))) (block k++['c']).length (some 1)).mp ⟨1,hfrozen⟩
  refine ⟨clock,hclock,?_⟩
  exact pre_eq (p := block k) (rest := ['c']) ⟨[],rfl⟩ rfl

theorem capture_lengths_unbounded (bound : Nat) :
    ∃ w, bound<w.length ∧ CaptureTransitionProfile.profile (DynamicScannerCapture.observer M) w∈H M 0 ∧
      ∃ clock, evV (source M 0 tail) (w++['c']) .callByValuePar
        (tblV (source M 0 tail) (w++['c']) .callByValuePar clock) []
        (sourceExpr M (.user 1 (.lit []))) (w++['c']).length=some (some 1) ∧
        pre (w++['c']) (w++['c']).length 1=w := by
  refine ⟨block bound,?_,readable_blocks bound,physical_unbounded_capture bound⟩
  simp [block]

end Shallot.MacroPeg.CBV.ScannerLoopExamples
