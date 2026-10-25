import MacroPeg.CBV.ScannerOriginControl
import MacroPeg.CBV.ScannerReplayResidualExamples

namespace Shallot.MacroPeg.CBV.ScannerOriginControlExamples
open RecursiveScannerProductCompiler (Arg sourceExpr offset)
open ScannerOriginControl
open ScannerReplayResidualExamples (machine residuals D argument scanners)
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def parts : List (Part 3) := [
  ⟨.shift 0 residuals,ScannerReplayResidualExamples.shifted⟩,
  ⟨.scan 2,.lit ['Z']⟩,
  ⟨.scan 2,ScannerReplayResidualExamples.scanned⟩,
  ⟨.replay,.lit []⟩]
def plans : List ReplayControlFusion.Plan := [.alt (.leaf 0) (.notP (.leaf 1)),.leaf 2,.leaf 3]
def root : Arg := .user 0 (.user 2 argument)
def input : List Char := ScannerReplayResidualExamples.input

def summary : RecursiveCaptureProfiles.Summary := fun i P =>
  if i=3 then [P] else if i=1 then [CaptureTransitionProfile.profile D ['Z']]
  else [CaptureTransitionProfile.compose (CaptureTransitionProfile.profile D ['!']) P]
def inputs : ProfileCheckedScannerCorrespondence.Inputs := fun i =>
  if i<2 then [CaptureTransitionProfile.profile D [],CaptureTransitionProfile.profile D ['a']]
  else if i=2 then [CaptureTransitionProfile.profile D ['b']] else CaptureTransitionProfile.profiles D

theorem checked :
    readyCheck parts plans=true ∧ scopeCheck plans root=true ∧
    RecursiveCaptureProfiles.scannerCheck machine scanners=true ∧
    RecursiveCaptureProfiles.grammarCheck machine (coreEntries parts) (coreBodies parts plans) scanners summary=true ∧
    ProfileCheckedScannerCorrespondence.bodiesCheck machine (coreEntries parts) (coreBodies parts plans) summary inputs=true ∧
    ProfileCheckedScannerCorrespondence.check machine (coreEntries parts) (coreBodies parts plans) summary inputs [] (normalize plans root)=true := by
  decide +kernel

theorem positive_source :
    evV (original machine parts plans) input .callByValuePar
      (tblV (original machine parts plans) input .callByValuePar 14) []
      (sourceExpr machine root) input.length=some (some 0) := by decide +kernel

theorem positive_target : ∃ k,
    evV (target machine parts plans) input .callByValueSeq
      (tblV (target machine parts plans) input .callByValueSeq k) []
      (targetExpr machine parts plans root) input.length=some (some 0) :=
  (defined_iff machine parts plans checked.1 root checked.2.1 scanners summary inputs
    checked.2.2.1 checked.2.2.2.1 checked.2.2.2.2.1 checked.2.2.2.2.2 input (some 0)).mp ⟨14,positive_source⟩

def rollbackInput : List Char := "ababaX".toList
def rollbackRoot : Arg := .seq root (.lit rollbackInput)

/-- A successful three-character argument is retained, but the source
callee succeeds back at its original position through a negative leaf. -/
theorem rollback_source :
    evV (original machine parts plans) rollbackInput .callByValuePar
      (tblV (original machine parts plans) rollbackInput .callByValuePar 14) []
      (sourceExpr machine root) rollbackInput.length=some (some rollbackInput.length) ∧
    evV (original machine parts plans) rollbackInput .callByValuePar
      (tblV (original machine parts plans) rollbackInput .callByValuePar 14) []
      (sourceExpr machine rollbackRoot) rollbackInput.length=some (some 0) := by decide +kernel

theorem rollback_target : ∃ k,
    evV (target machine parts plans) rollbackInput .callByValueSeq
      (tblV (target machine parts plans) rollbackInput .callByValueSeq k) []
      (targetExpr machine parts plans rollbackRoot) rollbackInput.length=some (some 0) :=
  (defined_iff machine parts plans checked.1 rollbackRoot (by decide +kernel) scanners summary inputs
    checked.2.2.1 checked.2.2.2.1 checked.2.2.2.2.1 (by decide +kernel) rollbackInput (some 0)).mp ⟨14,rollback_source.2⟩

/-- Omitting argument preflight lets a failed argument turn into a
successful negative leaf. The original unary call rejects first. -/
def failedArg : Arg := .seq (.notP (.lit ['a'])) (.lit ['a'])
def failedRoot : Arg := .user 0 failedArg

theorem preflight_required :
    evV (original machine parts plans) rollbackInput .callByValuePar
      (tblV (original machine parts plans) rollbackInput .callByValuePar 14) []
      (sourceExpr machine failedRoot) rollbackInput.length=some none ∧
    evV (core machine parts plans) rollbackInput .callByValuePar
      (tblV (core machine parts plans) rollbackInput .callByValuePar 14) []
      (sourceExpr machine (expand failedArg (plans[0]))) rollbackInput.length=some (some rollbackInput.length) := by decide +kernel

theorem failed_target : ∃ k,
    evV (target machine parts plans) rollbackInput .callByValueSeq
      (tblV (target machine parts plans) rollbackInput .callByValueSeq k) []
      (targetExpr machine parts plans failedRoot) rollbackInput.length=some none :=
  (defined_iff machine parts plans checked.1 failedRoot (by decide +kernel) scanners summary inputs
    checked.2.2.1 checked.2.2.2.1 checked.2.2.2.2.1 (by decide +kernel) rollbackInput none).mp ⟨14,preflight_required.1⟩

theorem language : ∃ (g : MGrammar) (e : MExp), g.FirstOrder ∧ e.FirstOrder ∧ ∀ x,
    SObs (original machine parts plans) .callByValuePar (sourceExpr machine rollbackRoot) x (some []) ↔
      SObs g .callByValueSeq e x (some []) :=
  language_translation machine parts plans checked.1 rollbackRoot (by decide +kernel) scanners summary inputs
    checked.2.2.1 checked.2.2.2.1 checked.2.2.2.2.1 (by decide +kernel)

theorem captured_argument :
    evV (original machine parts plans) rollbackInput .callByValuePar
      (tblV (original machine parts plans) rollbackInput .callByValuePar 14) []
      (sourceExpr machine (.user 2 argument)) rollbackInput.length=some (some 3) ∧
    pre rollbackInput rollbackInput.length 3="aba".toList := by decide +kernel

theorem target_returns_origin : ∃ k,
    evV (target machine parts plans) rollbackInput .callByValueSeq
      (tblV (target machine parts plans) rollbackInput .callByValueSeq k) []
      (targetExpr machine parts plans root) rollbackInput.length=some (some rollbackInput.length) :=
  (defined_iff machine parts plans checked.1 root checked.2.1 scanners summary inputs
    checked.2.2.1 checked.2.2.2.1 checked.2.2.2.2.1 checked.2.2.2.2.2 rollbackInput (some rollbackInput.length)).mp ⟨14,rollback_source.1⟩

def nullable : Arg := .user 0 (.star (.lit []))

theorem nullable_source (x : List Char) (clock : Nat) :
    evV (original machine parts plans) x .callByValuePar
      (tblV (original machine parts plans) x .callByValuePar clock) []
      (sourceExpr machine nullable) x.length=none := by
  have he : evV (original machine parts plans) x .callByValuePar
      (tblV (original machine parts plans) x .callByValuePar clock) []
      (.star (.lit [])) x.length=none := by
    exact evStar_stuck (show evV (original machine parts plans) x .callByValuePar
      (tblV (original machine parts plans) x .callByValuePar clock) []
      (.lit []) x.length=some (some x.length) from by
        simp [evV,Shallot.stripPrefix?,length_sfx x (Nat.le_refl _)])
      (Nat.not_lt.mpr (Nat.le_refl _))
  rw [show sourceExpr machine nullable=.call (offset machine+0) [.star (.lit [])] from rfl,
    evV_call_par (original_rule machine parts plans 0 (plans[0]) (by rfl)) rfl]
  · simp only [evParArgs,he]
  · decide

theorem nullable_target (x : List Char) (clock : Nat) :
    evV (target machine parts plans) x .callByValueSeq
      (tblV (target machine parts plans) x .callByValueSeq clock) []
      (targetExpr machine parts plans nullable) x.length=none :=
  (undefined_iff machine parts plans checked.1 nullable (by decide +kernel) scanners summary inputs
    checked.2.2.1 checked.2.2.2.1 checked.2.2.2.2.1 (by decide +kernel) x).mp (nullable_source x) clock

end Shallot.MacroPeg.CBV.ScannerOriginControlExamples
