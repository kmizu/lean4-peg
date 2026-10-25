import MacroPeg.CBV.ProfileCheckedScannerCorrespondence

namespace Shallot.MacroPeg.CBV.ScannerReplayResidualExamples
open RecursiveScannerProductCompiler
open ProfileCheckedScannerCorrespondence
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The ab cycle and an unrelated a/b scanner share one partial machine. -/
def machine : StatefulScanner.Machine 3 := ⟨fun q =>
  if q.val=0 then [('a',1)] else if q.val=1 then [('b',0)] else [('a',2),('b',2)]⟩
def residuals : ScannerReplayResidual.Labels 3 := fun q =>
  if q.val=0 then some "ab".toList else if q.val=1 then some "ba".toList else none
def D := DynamicScannerCapture.observer machine

def entries : Entries 3 := fun i => if i=0 then .shift 0 residuals else if i=1 then .scan 2 else .replay
def shifted : Arg := .seq (.lit ['!']) (.seq (.param 0)
  (.seq (.alt (.seq (.lit [':']) (.user 1 (.lit ['b']))) (.lit []))
    (.seq (.lit ['?']) (.param 0))))
def scanned : Arg := .seq (.lit ['!']) (.seq (.param 0)
  (.seq (.alt (.seq (.lit [':']) (.user 0 (.user 2 (.lit "ababa".toList)))) (.lit []))
    (.seq (.lit ['?']) (.param 0))))
def bodies : List Arg := [shifted,scanned,.lit []]
/-- Leave the final aba for the shifted header, without bounding the
number of captured ab blocks. The query commits each real iteration. -/
def argument : Arg := .seq (.star (.seq (.lit "ab".toList)
  (.notP (.notP (.lit "aba".toList))))) (.lit ['a'])
def root : Arg := .user 0 (.user 2 argument)
def committedRoot : Arg := .user 0 (.user 2 (.alt (.lit "aba".toList) (.lit ['a'])))
def scanProfiles : List (List Nat) :=
  [[],['a'],['b'],['a','a'],['a','b'],['b','a']].map (CaptureTransitionProfile.profile D)
def scanners : RecursiveCaptureProfiles.ScannerSummary 3 := fun _ => scanProfiles
def summary : RecursiveCaptureProfiles.Summary := fun i P => if i<2 then [CaptureTransitionProfile.compose (CaptureTransitionProfile.profile D ['!']) P] else [P]
def inputs : Inputs := fun i => if i=0 then [CaptureTransitionProfile.profile D [],CaptureTransitionProfile.profile D ['a']]
  else if i=1 then [CaptureTransitionProfile.profile D ['b']] else CaptureTransitionProfile.profiles D

theorem checked :
    RecursiveCaptureProfiles.scannerCheck machine scanners=true ∧
    RecursiveCaptureProfiles.grammarCheck machine entries bodies scanners summary=true ∧
    ProfileCheckedScannerCorrespondence.bodiesCheck machine entries bodies summary inputs=true ∧
    ProfileCheckedScannerCorrespondence.check machine entries bodies summary inputs [] root=true := by
  decide +kernel

theorem layout_and_entry_checks :
    ScannerReplayResidual.entryCheck machine residuals 0=true ∧
    ScannerReplayResidual.check machine (fun _ => some "ab".toList)=false ∧
    TotalCaptureSafety.wordCheck machine "aba".toList=false ∧
    ScannerFrontierCertificate.check (CaptureTransitionProfile.profile D ['b']) (0 : Fin 3)=false ∧
    RecursiveScannerProductHeader.entryCheck machine (entries 0) (CaptureTransitionProfile.profile D ['b'])=true := by
  decide +kernel

theorem noncommuting : "ab".toList++"aba".toList≠"aba".toList++"ab".toList := by decide

theorem residual_actual :
    StatefulScanner.advance machine 0 "aba".toList=some 1 ∧
    (residuals 1).getD []="ba".toList ∧
    "ab".toList++"aba".toList="aba".toList++"ba".toList := by decide

def input : List Char := "ababa!aba:b!b:abababa!ababa?ababa?b?aba".toList

theorem source_accepts :
    evV (source machine entries bodies) input .callByValuePar
      (tblV (source machine entries bodies) input .callByValuePar 12) []
      (sourceExpr machine root) input.length=some (some 0) := by decide +kernel

theorem target_accepts : ∃ k,
    evV (target machine entries bodies) input .callByValueSeq
      (tblV (target machine entries bodies) input .callByValueSeq k) []
      (plain machine bodies [] root) input.length=some (some 0) :=
  (ProfileCheckedScannerCorrespondence.defined_iff machine entries bodies scanners summary inputs
    checked.1 checked.2.1 checked.2.2.1 root checked.2.2.2 input (some 0)).mp ⟨12,source_accepts⟩

theorem language : ∃ (g : MGrammar) (e : MExp), g.FirstOrder ∧ e.FirstOrder ∧ ∀ x,
    SObs (source machine entries bodies) .callByValuePar (sourceExpr machine root) x (some []) ↔
      SObs g .callByValueSeq e x (some []) :=
  ProfileCheckedScannerCorrespondence.language_translation machine entries bodies scanners summary inputs
    checked.1 checked.2.1 checked.2.2.1 root checked.2.2.2

def shortCopies : List (List Char) := [
  "ababa!ab:b!b:abababa!ababa?ababa?b?aba".toList,
  "ababa!aba:b!b:abababa!abab?ababa?b?aba".toList,
  "ababa!aba:b!b:abababa!ababa?ababa?b?ab".toList]

theorem short_source : shortCopies.all (fun x =>
    evV (source machine entries bodies) x .callByValuePar
      (tblV (source machine entries bodies) x .callByValuePar 12) []
      (sourceExpr machine root) x.length == some none)=true := by decide +kernel

theorem short_target (x : List Char) (hx : x∈shortCopies) : ∃ k,
    evV (target machine entries bodies) x .callByValueSeq
      (tblV (target machine entries bodies) x .callByValueSeq k) []
      (plain machine bodies [] root) x.length=some none := by
  have hv : evV (source machine entries bodies) x .callByValuePar
      (tblV (source machine entries bodies) x .callByValuePar 12) []
      (sourceExpr machine root) x.length=some none := by
    simpa using (List.all_eq_true.mp short_source) x hx
  exact (ProfileCheckedScannerCorrespondence.defined_iff machine entries bodies scanners summary inputs
    checked.1 checked.2.1 checked.2.2.1 root checked.2.2.2 x none).mp ⟨12,hv⟩

def commitInput : List Char := "aba!a?a".toList
def explicitShort : Arg := .user 0 (.lit ['a'])

theorem committed_argument :
    evV (source machine entries bodies) commitInput .callByValuePar
      (tblV (source machine entries bodies) commitInput .callByValuePar 10) []
      (sourceExpr machine committedRoot) commitInput.length=some none ∧
    evV (source machine entries bodies) commitInput .callByValuePar
      (tblV (source machine entries bodies) commitInput .callByValuePar 10) []
      (sourceExpr machine explicitShort) commitInput.length=some (some 0) := by decide +kernel

def nullable : Arg := .user 0 (.star (.lit []))

theorem nullable_source (x : List Char) (clock : Nat) :
    evV (source machine entries bodies) x .callByValuePar
      (tblV (source machine entries bodies) x .callByValuePar clock) []
      (sourceExpr machine nullable) x.length=none := by
  have he : evV (source machine entries bodies) x .callByValuePar
      (tblV (source machine entries bodies) x .callByValuePar clock) []
      (.star (.lit [])) x.length=none := by
    exact evStar_stuck (show evV (source machine entries bodies) x .callByValuePar
      (tblV (source machine entries bodies) x .callByValuePar clock) []
      (.lit []) x.length=some (some x.length) from by
        simp [evV,Shallot.stripPrefix?,length_sfx x (Nat.le_refl _)])
      (Nat.not_lt.mpr (Nat.le_refl _))
  rw [show sourceExpr machine nullable=.call (offset machine+0) [.star (.lit [])] from rfl,
    evV_call_par (source_rule machine entries bodies 0 shifted (by rfl)) rfl]
  · simp only [evParArgs,he]
  · decide

theorem nullable_target (x : List Char) (clock : Nat) :
    evV (target machine entries bodies) x .callByValueSeq
      (tblV (target machine entries bodies) x .callByValueSeq clock) []
      (plain machine bodies [] nullable) x.length=none :=
  (ProfileCheckedScannerCorrespondence.undefined_iff machine entries bodies scanners summary inputs
    checked.1 checked.2.1 checked.2.2.1 nullable (by decide +kernel) x).mp (nullable_source x) clock

end Shallot.MacroPeg.CBV.ScannerReplayResidualExamples
