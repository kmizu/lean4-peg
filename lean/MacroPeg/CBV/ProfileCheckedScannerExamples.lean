import MacroPeg.CBV.ProfileCheckedScannerCorrespondence

namespace Shallot.MacroPeg.CBV.ProfileCheckedScannerExamples
open RecursiveScannerProductCompiler
open ProfileCheckedScannerCorrespondence

/-- b is readable only in state 1. a is readable from both states. -/
def machine : StatefulScanner.Machine 2 := ⟨fun q =>
  if q.val=0 then [('a',0)] else [('a',1),('b',1)]⟩
def D := DynamicScannerCapture.observer machine

def safeProfiles : List (List Nat) := RecursiveCaptureProfiles.closure D [CaptureTransitionProfile.profile D ['b']]
def scanners : RecursiveCaptureProfiles.ScannerSummary 2 := fun q =>
  if q.val=0 then [CaptureTransitionProfile.profile D []] else safeProfiles

def entries : Entries 2 := fun _ => .scan 1
def nextArg : Arg := .user 1 (.seq (.param 0) (.lit ['b']))
def body : Arg := .seq (.lit ['!']) (.seq (.param 0)
  (.seq (.alt (.seq (.lit [':']) (.user 0 nextArg)) (.lit []))
    (.seq (.lit ['?']) (.param 0))))
def bodies : List Arg := [body,.lit []]
def root : Arg := .user 0 (.user 1 (.star (.alt (.lit ['a']) (.lit ['b']))))
def summary : RecursiveCaptureProfiles.Summary := fun i _ => if i=0 then CaptureTransitionProfile.profiles D else safeProfiles
def inputs : Inputs := fun _ => safeProfiles

theorem checked :
    RecursiveCaptureProfiles.scannerCheck machine scanners=true ∧
    RecursiveCaptureProfiles.grammarCheck machine entries bodies scanners summary=true ∧
    ProfileCheckedScannerCorrespondence.bodiesCheck machine entries bodies summary inputs=true ∧
    ProfileCheckedScannerCorrespondence.check machine entries bodies summary inputs [] root=true := by
  decide +kernel

theorem genuinely_partial :
    ScannerLanguageSafety.safe machine 1=false ∧
    TotalCaptureSafety.wordCheck machine ['a','b']=false ∧
    TotalCaptureSafety.wordCheck machine ['b']=false ∧
    RecursiveScannerProductCompiler.check machine entries bodies 0 true root=false := by decide +kernel

def input : List Char := "ab!ab:abb!abb?abb?ab".toList

theorem source_accepts :
    evV (source machine entries bodies) input .callByValuePar
      (tblV (source machine entries bodies) input .callByValuePar 18) []
      (sourceExpr machine root) input.length=some (some 0) := by decide +kernel

theorem target_accepts : ∃ k,
    evV (target machine entries bodies) input .callByValueSeq
      (tblV (target machine entries bodies) input .callByValueSeq k) []
      (plain machine bodies [] root) input.length=some (some 0) :=
  (ProfileCheckedScannerCorrespondence.defined_iff machine entries bodies scanners summary inputs
    checked.1 checked.2.1 checked.2.2.1 root checked.2.2.2 input (some 0)).mp ⟨18,source_accepts⟩

theorem language : ∃ (g : MGrammar) (e : MExp), g.FirstOrder ∧ e.FirstOrder ∧ ∀ x,
    SObs (source machine entries bodies) .callByValuePar (sourceExpr machine root) x (some []) ↔
      SObs g .callByValueSeq e x (some []) :=
  ProfileCheckedScannerCorrespondence.language_translation machine entries bodies scanners summary inputs
    checked.1 checked.2.1 checked.2.2.1 root checked.2.2.2

def shortCopies : List (List Char) := [
  "ab!ab:ab!abb?abb?ab".toList,
  "ab!ab:abb!ab?abb?ab".toList,
  "ab!ab:abb!abb?ab?ab".toList,
  "ab!ab:abb!abb?abb?a".toList]

theorem short_source : shortCopies.all (fun x =>
    evV (source machine entries bodies) x .callByValuePar
      (tblV (source machine entries bodies) x .callByValuePar 18) []
      (sourceExpr machine root) x.length == some none)=true := by decide +kernel

theorem short_target (x : List Char) (hx : x∈shortCopies) : ∃ k,
    evV (target machine entries bodies) x .callByValueSeq
      (tblV (target machine entries bodies) x .callByValueSeq k) []
      (plain machine bodies [] root) x.length=some none := by
  have h := (List.all_eq_true.mp short_source) x hx
  have hv : evV (source machine entries bodies) x .callByValuePar
      (tblV (source machine entries bodies) x .callByValuePar 18) []
      (sourceExpr machine root) x.length=some none := by simpa using h
  exact (ProfileCheckedScannerCorrespondence.defined_iff machine entries bodies scanners summary inputs
    checked.1 checked.2.1 checked.2.2.1 root checked.2.2.2 x none).mp ⟨18,hv⟩

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
    evV_call_par (source_rule machine entries bodies 0 body (by rfl)) rfl]
  · simp only [evParArgs,he]
  · decide

theorem nullable_target (x : List Char) (clock : Nat) :
    evV (target machine entries bodies) x .callByValueSeq
      (tblV (target machine entries bodies) x .callByValueSeq clock) []
      (plain machine bodies [] nullable) x.length=none :=
  (ProfileCheckedScannerCorrespondence.undefined_iff machine entries bodies scanners summary inputs
    checked.1 checked.2.1 checked.2.2.1 nullable (by decide +kernel) x).mp (nullable_source x) clock

end Shallot.MacroPeg.CBV.ProfileCheckedScannerExamples
