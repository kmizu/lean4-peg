import MacroPeg.CBV.ScannerReplayResidualExamples

namespace Shallot.MacroPeg.CBV.EntryControlScannerExamples
open RecursiveScannerProductCompiler
open ProfileCheckedScannerCorrespondence
open ScannerReplayResidualExamples (machine residuals D bodies root input scanners summary inputs)
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- The same user chooses a scanner after a positive shifted-replay test,
or direct replay after the corresponding negative test. -/
def controlled : Entry 3 := .alt (.guard true (.shift 0 residuals) (.scan 2))
  (.guard false (.shift 0 residuals) .replay)
def entries : Entries 3 := fun i => if i=0 then controlled else if i=1 then .scan 2 else .replay

theorem checked :
    RecursiveCaptureProfiles.scannerCheck machine scanners=true ∧
    RecursiveCaptureProfiles.grammarCheck machine entries bodies scanners summary=true ∧
    ProfileCheckedScannerCorrespondence.bodiesCheck machine entries bodies summary inputs=true ∧
    ProfileCheckedScannerCorrespondence.check machine entries bodies summary inputs [] root=true := by
  decide +kernel

theorem positive_source :
    evV (source machine entries bodies) input .callByValuePar
      (tblV (source machine entries bodies) input .callByValuePar 14) []
      (sourceExpr machine root) input.length=some (some 0) := by decide +kernel

def negativeInput : List Char := "a!a?a".toList

theorem negative_source :
    evV (source machine entries bodies) negativeInput .callByValuePar
      (tblV (source machine entries bodies) negativeInput .callByValuePar 8) []
      (sourceExpr machine root) negativeInput.length=some (some 0) := by decide +kernel

theorem positive_target : ∃ k,
    evV (target machine entries bodies) input .callByValueSeq
      (tblV (target machine entries bodies) input .callByValueSeq k) []
      (plain machine bodies [] root) input.length=some (some 0) :=
  (ProfileCheckedScannerCorrespondence.defined_iff machine entries bodies scanners summary inputs
    checked.1 checked.2.1 checked.2.2.1 root checked.2.2.2 input (some 0)).mp ⟨14,positive_source⟩

theorem negative_target : ∃ k,
    evV (target machine entries bodies) negativeInput .callByValueSeq
      (tblV (target machine entries bodies) negativeInput .callByValueSeq k) []
      (plain machine bodies [] root) negativeInput.length=some (some 0) :=
  (ProfileCheckedScannerCorrespondence.defined_iff machine entries bodies scanners summary inputs
    checked.1 checked.2.1 checked.2.2.1 root checked.2.2.2 negativeInput (some 0)).mp ⟨8,negative_source⟩

theorem language : ∃ (g : MGrammar) (e : MExp), g.FirstOrder ∧ e.FirstOrder ∧ ∀ x,
    SObs (source machine entries bodies) .callByValuePar (sourceExpr machine root) x (some []) ↔
      SObs g .callByValueSeq e x (some []) :=
  ProfileCheckedScannerCorrespondence.language_translation machine entries bodies scanners summary inputs
    checked.1 checked.2.1 checked.2.2.1 root checked.2.2.2

/-- A successful replay entry commits even if its following body fails.
Distributing the body into both alternatives accepts this input incorrectly. -/
def commitEntries : Entries 3 := fun _ => .alt .replay (.scan 2)
def commitBodies : List Arg := [.lit ['!']]
def commitRoot : Arg := .user 0 (.lit ['a'])
def commitInput : List Char := "ab!".toList

theorem committed_source :
    evV (source machine commitEntries commitBodies) commitInput .callByValuePar
      (tblV (source machine commitEntries commitBodies) commitInput .callByValuePar 8) []
      (sourceExpr machine commitRoot) commitInput.length=some none ∧
    evV (source machine commitEntries commitBodies) commitInput .callByValuePar
      (tblV (source machine commitEntries commitBodies) commitInput .callByValuePar 8) [['a']]
      (.alt (.seq (.param 0) (.lit ['!'])) (.seq (.call 2 []) (.lit ['!']))) commitInput.length=some (some 0) := by
  decide +kernel

def commitSummary : RecursiveCaptureProfiles.Summary := fun _ _ => [CaptureTransitionProfile.profile D ['!']]
def commitInputs : Inputs := fun _ => [CaptureTransitionProfile.profile D ['a']]

theorem commit_checked :
    RecursiveCaptureProfiles.grammarCheck machine commitEntries commitBodies scanners commitSummary=true ∧
    ProfileCheckedScannerCorrespondence.bodiesCheck machine commitEntries commitBodies commitSummary commitInputs=true ∧
    ProfileCheckedScannerCorrespondence.check machine commitEntries commitBodies commitSummary commitInputs [] commitRoot=true := by decide +kernel

theorem committed_target : ∃ k,
    evV (target machine commitEntries commitBodies) commitInput .callByValueSeq
      (tblV (target machine commitEntries commitBodies) commitInput .callByValueSeq k) []
      (plain machine commitBodies [] commitRoot) commitInput.length=some none :=
  (ProfileCheckedScannerCorrespondence.defined_iff machine commitEntries commitBodies scanners commitSummary commitInputs
    checked.1 commit_checked.1 commit_checked.2.1 commitRoot commit_checked.2.2 commitInput none).mp ⟨8,committed_source.1⟩

def shortCopies : List (List Char) := [
  "ababa!ab:b!b:abababa!ababa?ababa?b?aba".toList,
  "ababa!aba:b!b:abababa!abab?ababa?b?aba".toList,
  "ababa!aba:b!b:abababa!ababa?ababa?b?ab".toList]

theorem short_source : shortCopies.all (fun x =>
    evV (source machine entries bodies) x .callByValuePar
      (tblV (source machine entries bodies) x .callByValuePar 14) []
      (sourceExpr machine root) x.length == some none)=true := by decide +kernel

theorem short_target (x : List Char) (hx : x∈shortCopies) : ∃ k,
    evV (target machine entries bodies) x .callByValueSeq
      (tblV (target machine entries bodies) x .callByValueSeq k) []
      (plain machine bodies [] root) x.length=some none := by
  have hv : evV (source machine entries bodies) x .callByValuePar
      (tblV (source machine entries bodies) x .callByValuePar 14) []
      (sourceExpr machine root) x.length=some none := by
    simpa using (List.all_eq_true.mp short_source) x hx
  exact (ProfileCheckedScannerCorrespondence.defined_iff machine entries bodies scanners summary inputs
    checked.1 checked.2.1 checked.2.2.1 root checked.2.2.2 x none).mp ⟨14,hv⟩

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
    evV_call_par (source_rule machine entries bodies 0 ScannerReplayResidualExamples.shifted (by rfl)) rfl]
  · simp only [evParArgs,he]
  · decide

theorem nullable_target (x : List Char) (clock : Nat) :
    evV (target machine entries bodies) x .callByValueSeq
      (tblV (target machine entries bodies) x .callByValueSeq clock) []
      (plain machine bodies [] nullable) x.length=none :=
  (ProfileCheckedScannerCorrespondence.undefined_iff machine entries bodies scanners summary inputs
    checked.1 checked.2.1 checked.2.2.1 nullable (by decide +kernel) x).mp (nullable_source x) clock

end Shallot.MacroPeg.CBV.EntryControlScannerExamples
