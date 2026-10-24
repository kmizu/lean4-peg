import MacroPeg.CBV.RecursiveScannerCorrespondence
import MacroPeg.CBV.RecursiveCaptureExamples
import MacroPeg.CBV.StatefulActionExamples
import MacroPeg.CBV.RelocatedScannerFastTable

namespace Shallot.MacroPeg.CBV.RecursiveScannerFusionExamples
open RecursiveScannerCompiler
open RecursiveScannerCorrespondence
open DynamicScannerCapture (observer)
abbrev machine := StatefulActionExamples.machine
abbrev nodes := RecursiveCaptureExamples.nodes
abbrev Form := RecursiveScannerCompiler.Expr

def initial : Arg := .helper 0
def child : Arg := .seq (.param 0) (.helper 0)
def finish : Form := .seq (.lit ['!']) (.param 0)
def bodies : List Form := [
  .alt finish (.seq (.lit ['Z']) (.seq (.user 1 child) (.seq (.lit ['?']) (.param 0)))),
  .alt finish (.seq (.lit ['X']) (.seq (.user 0 child) (.seq (.lit ['?']) (.param 0))))]
def eof : Form := .notP .any
def root : Form := .seq (.user 0 initial) eof
def input := ("acbZ"++"acacX"++"acacacb!acacac"++"?acac?ac").toList

set_option maxRecDepth 4000
set_option maxHeartbeats 0

theorem syntax_checked : nodesCheck nodes=true ∧
    (nodes.map RegularCaptureProduct.body).all (RecursiveCaptureSafety.check machine nodes.length)=true ∧
    bodies.all (check machine nodes bodies)=true ∧ check machine nodes bodies root=true := by
  decide +kernel

/-- Recursive helper arguments now belong to the whole generated mutually
recursive grammar, on all original inputs and all finite observations. -/
theorem language (x : List Char) (rest : Option (List Char)) :
    SObs (source machine nodes 0 bodies) .callByValuePar (sourceExpr machine nodes bodies root) x rest ↔
      SObs (target machine nodes 0 bodies) .callByValueSeq (targetExpr machine nodes bodies [] root) x rest :=
  checked_observations_iff machine nodes syntax_checked.1 syntax_checked.2.1 0 bodies
    syntax_checked.2.2.1 root syntax_checked.2.2.2 x rest

theorem source_scanner (q : Fin 2) :
    ruleAtM (source machine nodes 0 bodies).rules (RecursiveScannerHelpers.base machine nodes+q.val)=
      some ⟨0,StatefulScanner.branches (RecursiveScannerHelpers.base machine nodes)
        (StatefulScanner.terminal true) (machine.arcs q)⟩ :=
  RecursiveScannerHelpers.scanner_rule machine nodes _ q

/-- Actual source evaluation captures ac → acac → acacac through H,
executes user 0 → 1 → 0, scans extra b characters, then restores both parents. -/
theorem mutual_returns :
    evV (source machine nodes 0 bodies) input .callByValuePar
      (tblV (source machine nodes 0 bodies) input .callByValuePar (input.length+1+8)) []
      (sourceExpr machine nodes bodies root) input.length=some (some 0) := by
  apply RelocatedScannerFastTable.physical machine (RecursiveScannerHelpers.base machine nodes) _ _ _ source_scanner 8
  decide +kernel

theorem target_scanner (q : Fin 2) :
    ruleAtM (target machine nodes 0 bodies).rules (RecursiveScannerHelpers.base machine nodes+q.val)=
      some ⟨0,StatefulScanner.branches (RecursiveScannerHelpers.base machine nodes)
        (StatefulScanner.terminal true) (machine.arcs q)⟩ :=
  RecursiveScannerHelpers.scanner_rule machine nodes _ q

theorem generated_returns :
    evV (target machine nodes 0 bodies) input .callByValueSeq
      (tblV (target machine nodes 0 bodies) input .callByValueSeq (input.length+1+12)) []
      (targetExpr machine nodes bodies [] root) input.length=some (some 0) := by
  apply RelocatedScannerFastTable.physical machine (RecursiveScannerHelpers.base machine nodes) _ _ _ target_scanner 12
  decide +kernel

/-- The exact generated Seq grammar has an ordinary finite physical
accepting computation, as a consequence of the all-input correspondence. -/
theorem generated_physical : ∃ clock,
    evV (target machine nodes 0 bodies) input .callByValueSeq
      (tblV (target machine nodes 0 bodies) input .callByValueSeq clock) []
      (targetExpr machine nodes bodies [] root) input.length=some (some 0) :=
  (defined_iff machine nodes (nodesCheck_sound nodes syntax_checked.1) syntax_checked.2.1 0 bodies
    (bodies_check_sound machine nodes bodies syntax_checked.2.2.1) root
    (check_sound machine nodes bodies root syntax_checked.2.2.2) input (some 0)).mp ⟨_,mutual_returns⟩

theorem actual_actions :
    StatefulScanner.advance machine 0 "ac".toList=some 1 ∧
    StatefulScanner.advance machine 0 "acac".toList=some 0 ∧
    StatefulScanner.advance machine 0 "acacac".toList=some 1 := by decide +kernel

theorem short_copies : ∀ x∈[
    "acbZacacXacacacb!acac?acac?ac".toList,
    "acbZacacXacacacb!acacac?ac?ac".toList,
    "acbZacacXacacacb!acacac?acac?a".toList],
    evV (source machine nodes 0 bodies) x .callByValuePar
      (tblV (source machine nodes 0 bodies) x .callByValuePar (x.length+1+8)) []
      (sourceExpr machine nodes bodies root) x.length=some none ∧
    ∃ clock, evV (target machine nodes 0 bodies) x .callByValueSeq
      (tblV (target machine nodes 0 bodies) x .callByValueSeq clock) []
      (targetExpr machine nodes bodies [] root) x.length=some none := by
  intro x hx
  have hs : evV (source machine nodes 0 bodies) x .callByValuePar
      (tblV (source machine nodes 0 bodies) x .callByValuePar (x.length+1+8)) []
      (sourceExpr machine nodes bodies root) x.length=some none := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl
    all_goals
      apply RelocatedScannerFastTable.physical machine (RecursiveScannerHelpers.base machine nodes) _ _ _ source_scanner 8
      decide +kernel
  exact ⟨hs,(defined_iff machine nodes (nodesCheck_sound nodes syntax_checked.1) syntax_checked.2.1 0 bodies
    (bodies_check_sound machine nodes bodies syntax_checked.2.2.1) root
    (check_sound machine nodes bodies root syntax_checked.2.2.2) x none).mp ⟨_,hs⟩⟩

def variableInput := ("acbZ"++"acaaccbX"++"acaaccac!acaaccac"++"?acaacc?ac").toList

/-- Fresh recursive captures have different sizes: ac, then aacc, then ac.
Both generated grammars retain each whole new value and restore both parents. -/
theorem variable_helper_returns :
    evV (source machine nodes 0 bodies) variableInput .callByValuePar
      (tblV (source machine nodes 0 bodies) variableInput .callByValuePar (variableInput.length+1+12)) []
      (sourceExpr machine nodes bodies root) variableInput.length=some (some 0) ∧
    evV (target machine nodes 0 bodies) variableInput .callByValueSeq
      (tblV (target machine nodes 0 bodies) variableInput .callByValueSeq (variableInput.length+1+16)) []
      (targetExpr machine nodes bodies [] root) variableInput.length=some (some 0) := by
  constructor
  · apply RelocatedScannerFastTable.physical machine (RecursiveScannerHelpers.base machine nodes) _ _ _ source_scanner 12
    decide +kernel
  · apply RelocatedScannerFastTable.physical machine (RecursiveScannerHelpers.base machine nodes) _ _ _ target_scanner 16
    decide +kernel

def chosen : Form := .seq (.user 0 (.alt (.lit []) (.helper 0))) eof
def explicitHelper : Form := .seq (.user 0 (.helper 0)) eof

/-- A successful empty argument stays selected even when its continuation
later rejects; explicitly selecting H accepts on the same original string. -/
theorem committed_helper_choice :
    evV (source machine nodes 0 bodies) "ac!ac".toList .callByValuePar
      (tblV (source machine nodes 0 bodies) "ac!ac".toList .callByValuePar 14) []
      (sourceExpr machine nodes bodies chosen) 5=some none ∧
    evV (target machine nodes 0 bodies) "ac!ac".toList .callByValueSeq
      (tblV (target machine nodes 0 bodies) "ac!ac".toList .callByValueSeq 14) []
      (targetExpr machine nodes bodies [] chosen) 5=some none ∧
    evV (source machine nodes 0 bodies) "ac!ac".toList .callByValuePar
      (tblV (source machine nodes 0 bodies) "ac!ac".toList .callByValuePar 14) []
      (sourceExpr machine nodes bodies explicitHelper) 5=some (some 0) ∧
    evV (target machine nodes 0 bodies) "ac!ac".toList .callByValueSeq
      (tblV (target machine nodes 0 bodies) "ac!ac".toList .callByValueSeq 14) []
      (targetExpr machine nodes bodies [] explicitHelper) 5=some (some 0) := by
  refine ⟨?_,?_,?_,?_⟩
  · apply RelocatedScannerFastTable.physical machine (RecursiveScannerHelpers.base machine nodes) _ _ _ source_scanner 8
    decide +kernel
  · apply RelocatedScannerFastTable.physical machine (RecursiveScannerHelpers.base machine nodes) _ _ _ target_scanner 8
    decide +kernel
  · apply RelocatedScannerFastTable.physical machine (RecursiveScannerHelpers.base machine nodes) _ _ _ source_scanner 8
    decide +kernel
  · apply RelocatedScannerFastTable.physical machine (RecursiveScannerHelpers.base machine nodes) _ _ _ target_scanner 8
    decide +kernel

theorem empty_recursive_capture :
    evV (source machine nodes 0 bodies) ['!'] .callByValuePar
      (tblV (source machine nodes 0 bodies) ['!'] .callByValuePar 10) []
      (sourceExpr machine nodes bodies root) 1=some (some 0) ∧
    evV (target machine nodes 0 bodies) ['!'] .callByValueSeq
      (tblV (target machine nodes 0 bodies) ['!'] .callByValueSeq 10) []
      (targetExpr machine nodes bodies [] root) 1=some (some 0) := by
  constructor
  · apply RelocatedScannerFastTable.physical machine (RecursiveScannerHelpers.base machine nodes) _ _ _ source_scanner 8
    decide +kernel
  · apply RelocatedScannerFastTable.physical machine (RecursiveScannerHelpers.base machine nodes) _ _ _ target_scanner 8
    decide +kernel

theorem argument_failure_clock_zero :
    evV (source machine nodes 0 bodies) ['!'] .callByValuePar
      (tblV (source machine nodes 0 bodies) ['!'] .callByValuePar 0) []
      (sourceExpr machine nodes bodies (.user 0 (.lit ['a']))) 1=some none ∧
    evV (target machine nodes 0 bodies) ['!'] .callByValueSeq
      (tblV (target machine nodes 0 bodies) ['!'] .callByValueSeq 0) []
      (targetExpr machine nodes bodies [] (.user 0 (.lit ['a']))) 1=some none := by
  decide +kernel

def loopRoot : Form := .user 0 (.star (.helper 0))

/-- H's final empty alternative prevents finite failure at any physical
clock. Incomplete recursive computations remain undefined. -/
theorem helper_no_failure (x : List Char) (k p : Nat) (hp : p≤x.length) :
    evV (source machine nodes 0 bodies) x .callByValuePar
      (tblV (source machine nodes 0 bodies) x .callByValuePar k) [] (.call 0 []) p≠some none := by
  have hr : ruleAtM (source machine nodes 0 bodies).rules 0=some ⟨0,RegularCaptureProduct.body (RegularCaptureProduct.Node.alt 1 2)⟩ := by
    exact RecursiveScannerHelpers.originals_installed machine nodes _ 0 _ rfl
  have hempty : ruleAtM (source machine nodes 0 bodies).rules 2=some ⟨0,.lit []⟩ := by
    exact RecursiveScannerHelpers.originals_installed machine nodes _ 2 _ rfl
  cases k with
  | zero => simp [evV,hr,evParArgs,tblV,valAt_nil]
  | succ k =>
    simp only [evV,hr,evParArgs,List.length_nil,ite_true]
    rw [valAt_tblV_succ hr [] hp]
    change evV _ _ _ _ _ (.alt (.call 1 []) (.call 2 [])) p≠some none
    cases hleft : evV (source machine nodes 0 bodies) x .callByValuePar
        (tblV (source machine nodes 0 bodies) x .callByValuePar k) [] (.call 1 []) p with
    | none => simp [evV_alt_none hleft]
    | some v => cases v with
      | some j => simp [evV_alt_ok hleft]
      | none =>
        rw [evV_alt_fail hleft]
        cases k with
        | zero => simp [evV,hempty,evParArgs,tblV,valAt_nil]
        | succ k =>
          simp only [evV,hempty,evParArgs,List.length_nil,ite_true]
          rw [valAt_tblV_succ hempty [] hp]
          simp [evV,Shallot.stripPrefix?,length_sfx x hp]

/-- Repeating this actual recursive helper eventually encounters a
nullable success; undefinedness is preserved on every input at every clock. -/
theorem recursive_nullable_undefined (x : List Char) :
    (∀ k, evV (source machine nodes 0 bodies) x .callByValuePar
      (tblV (source machine nodes 0 bodies) x .callByValuePar k) []
      (sourceExpr machine nodes bodies loopRoot) x.length=none) ∧
    (∀ k, evV (target machine nodes 0 bodies) x .callByValueSeq
      (tblV (target machine nodes 0 bodies) x .callByValueSeq k) []
      (targetExpr machine nodes bodies [] loopRoot) x.length=none) := by
  have hs : ∀ k, evV (source machine nodes 0 bodies) x .callByValuePar
      (tblV (source machine nodes 0 bodies) x .callByValuePar k) []
      (sourceExpr machine nodes bodies loopRoot) x.length=none := by
    intro k
    have hstar : ∀ p, p≤x.length → evStar (fun q => evV (source machine nodes 0 bodies) x .callByValuePar
        (tblV (source machine nodes 0 bodies) x .callByValuePar k) [] (.call 0 []) q) p=none := by
      intro p
      induction p using Nat.strongRecOn with
      | ind p ih =>
        intro hp
        cases ha : evV (source machine nodes 0 bodies) x .callByValuePar
            (tblV (source machine nodes 0 bodies) x .callByValuePar k) [] (.call 0 []) p with
        | none => exact evStar_none ha
        | some v => cases v with
          | none => exact False.elim (helper_no_failure x k p hp ha)
          | some j =>
            by_cases hj : j<p
            · rw [evStar_ok ha hj]; exact ih j hj (by omega)
            · exact evStar_stuck ha hj
    unfold sourceExpr loopRoot
    rw [evV_call_par (source_rule machine nodes 0 bodies 0 _ rfl) rfl (by decide)]
    have hh : evV (source machine nodes 0 bodies) x .callByValuePar
        (tblV (source machine nodes 0 bodies) x .callByValuePar k) [] (DependentCaptureFilter.render (.star (.helper 0))) x.length=none :=
      hstar x.length (Nat.le_refl _)
    simp only [evParArgs,hh]
  exact ⟨hs,(undefined_iff machine nodes (nodesCheck_sound nodes syntax_checked.1) syntax_checked.2.1 0 bodies
    (bodies_check_sound machine nodes bodies syntax_checked.2.2.1) loopRoot
    (check_sound machine nodes bodies loopRoot (by decide +kernel)) x).mp hs⟩

end Shallot.MacroPeg.CBV.RecursiveScannerFusionExamples
