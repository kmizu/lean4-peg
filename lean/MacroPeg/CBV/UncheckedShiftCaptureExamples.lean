import MacroPeg.CBV.CaptureIndependentOriginExamples

namespace Shallot.MacroPeg.CBV.UncheckedShiftCaptureExamples
open RecursiveScannerProductCompiler (Arg sourceExpr)
open ScannerOriginControl
open ScannerReplayResidualExamples (machine D residuals scanners argument)
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- The first branch produces arbitrarily long captures ending in c,
unreadable by the ab residual cycle. The other branch retains the previous
unbounded recursive capture example. Both are real source computations. -/
def actualArgument : Arg := .alt
  (.seq (.star (.lit ['a','b'])) (.lit ['c'])) argument

def parts := CaptureIndependentOriginExamples.parts
def plans : List ReplayControlFusion.Plan := CaptureIndependentOriginExamples.plans ++
  [.leaf 0,.guard (.notP (.leaf 0)) (.leaf 4)]
def root : Arg := .user 5 (.user 2 actualArgument)
def guarded : Arg := .user 6 (.user 2 actualArgument)
def summary := CaptureIndependentOriginExamples.summary
def inputs : ProfileCheckedScannerCorrespondence.Inputs := fun i =>
  if i=0 then CaptureTransitionProfile.profiles D else CaptureIndependentOriginExamples.inputs i

theorem checked :
    readyCheck parts plans=true ∧ scopeCheck plans root=true ∧
    RecursiveCaptureProfiles.scannerCheck machine scanners=true ∧
    RecursiveCaptureProfiles.grammarCheck machine (coreEntries parts) (coreBodies parts plans) scanners summary=true ∧
    ProfileCheckedScannerCorrespondence.bodiesCheck machine (coreEntries parts) (coreBodies parts plans) summary inputs=true ∧
    ProfileCheckedScannerCorrespondence.check machine (coreEntries parts) (coreBodies parts plans) summary inputs [] (normalize parts plans root)=true := by
  decide +kernel

/-- Completeness admits every captured profile, including unreadable ones. -/
theorem all_shift_profiles (P : List Nat) :
    RecursiveScannerProductHeader.entryCheck machine (.shift 0 residuals) P=true := by
  have hc : ScannerReplayResidual.completeCheck machine residuals=true := by decide +kernel
  exact Bool.or_eq_true_iff.mpr (Or.inl hc)

def unreadableInput : List Char := "abababc".toList

theorem actual_unreadable_capture :
    evV (original machine parts plans) unreadableInput .callByValuePar
      (tblV (original machine parts plans) unreadableInput .callByValuePar 4) []
      (sourceExpr machine (.user 2 actualArgument)) unreadableInput.length=some (some 0) ∧
    pre unreadableInput unreadableInput.length 0=unreadableInput ∧
    StatefulScanner.advance machine 0 unreadableInput=none ∧
    ScannerFrontierCertificate.check (CaptureTransitionProfile.profile D unreadableInput) (0 : Fin 3)=false ∧
    RecursiveScannerProductHeader.entryCheck machine (.shift 0 residuals)
      (CaptureTransitionProfile.profile D unreadableInput)=true := by decide +kernel

/-- A real capture succeeds, but the shift header fails. Under negative
control this lets an independent consuming leaf read a at the old origin. -/
theorem unreadable_source :
    evV (original machine parts plans) unreadableInput .callByValuePar
      (tblV (original machine parts plans) unreadableInput .callByValuePar 4) []
      (sourceExpr machine root) unreadableInput.length=some none ∧
    evV (original machine parts plans) unreadableInput .callByValuePar
      (tblV (original machine parts plans) unreadableInput .callByValuePar 4) []
      (sourceExpr machine guarded) unreadableInput.length=some (some 6) := by decide +kernel

theorem unreadable_target :
    (∃ k, evV (target machine parts plans) unreadableInput .callByValueSeq
      (tblV (target machine parts plans) unreadableInput .callByValueSeq k) []
      (targetExpr machine parts plans root) unreadableInput.length=some none) ∧
    (∃ k, evV (target machine parts plans) unreadableInput .callByValueSeq
      (tblV (target machine parts plans) unreadableInput .callByValueSeq k) []
      (targetExpr machine parts plans guarded) unreadableInput.length=some (some 6)) :=
  ⟨(defined_iff machine parts plans checked.1 root checked.2.1 scanners summary inputs
      checked.2.2.1 checked.2.2.2.1 checked.2.2.2.2.1 checked.2.2.2.2.2 unreadableInput none).mp
        ⟨4,unreadable_source.1⟩,
   (defined_iff machine parts plans checked.1 guarded (by decide +kernel) scanners summary inputs
      checked.2.2.1 checked.2.2.2.1 checked.2.2.2.2.1 (by decide +kernel) unreadableInput (some 6)).mp
        ⟨4,unreadable_source.2⟩⟩

theorem readable_recursive_source :
    evV (original machine parts plans) ScannerOriginControlExamples.input .callByValuePar
      (tblV (original machine parts plans) ScannerOriginControlExamples.input .callByValuePar 14) []
      (sourceExpr machine root) ScannerOriginControlExamples.input.length=some (some 0) := by decide +kernel

theorem readable_recursive_target : ∃ k,
    evV (target machine parts plans) ScannerOriginControlExamples.input .callByValueSeq
      (tblV (target machine parts plans) ScannerOriginControlExamples.input .callByValueSeq k) []
      (targetExpr machine parts plans root) ScannerOriginControlExamples.input.length=some (some 0) :=
  (defined_iff machine parts plans checked.1 root checked.2.1 scanners summary inputs
    checked.2.2.1 checked.2.2.2.1 checked.2.2.2.2.1 checked.2.2.2.2.2 ScannerOriginControlExamples.input (some 0)).mp
      ⟨14,readable_recursive_source⟩

theorem language : ∃ (g : MGrammar) (e : MExp), g.FirstOrder ∧ e.FirstOrder ∧ ∀ x,
    SObs (original machine parts plans) .callByValuePar (sourceExpr machine root) x (some []) ↔
      SObs g .callByValueSeq e x (some []) :=
  language_translation machine parts plans checked.1 root checked.2.1 scanners summary inputs
    checked.2.2.1 checked.2.2.2.1 checked.2.2.2.2.1 checked.2.2.2.2.2

theorem guarded_language : ∃ (g : MGrammar) (e : MExp), g.FirstOrder ∧ e.FirstOrder ∧ ∀ x,
    SObs (original machine parts plans) .callByValuePar
      (sourceExpr machine (.seq guarded (.lit "bababc".toList))) x (some []) ↔
      SObs g .callByValueSeq e x (some []) :=
  language_translation machine parts plans checked.1 (.seq guarded (.lit "bababc".toList))
    (by decide +kernel) scanners summary inputs
    checked.2.2.1 checked.2.2.2.1 checked.2.2.2.2.1 (by decide +kernel)

def nullable : Arg := .user 5 (.star (.lit []))

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
  rw [show sourceExpr machine nullable=.call (RecursiveScannerProductCompiler.offset machine+5) [.star (.lit [])] from rfl,
    evV_call_par (original_rule machine parts plans 5 (plans[5]) (by rfl)) rfl]
  · simp only [evParArgs,he]
  · decide

theorem nullable_target (x : List Char) (clock : Nat) :
    evV (target machine parts plans) x .callByValueSeq
      (tblV (target machine parts plans) x .callByValueSeq clock) []
      (targetExpr machine parts plans nullable) x.length=none :=
  (undefined_iff machine parts plans checked.1 nullable (by decide +kernel) scanners summary inputs
    checked.2.2.1 checked.2.2.2.1 checked.2.2.2.2.1 (by decide +kernel) x).mp (nullable_source x) clock

/-- A missing required head arc is not a failure certificate: the old
sound-label check permits this machine, while the complete check rejects it. -/
def missing : StatefulScanner.Machine 1 := ⟨fun _ => []⟩
def missingLabels : ScannerReplayResidual.Labels 1 := fun _ => some ['a']

theorem missing_arc_rejected :
    ScannerReplayResidual.entryCheck missing missingLabels 0=true ∧
    ScannerReplayResidual.completeCheck missing missingLabels=false ∧
    StatefulScanner.advance missing 0 ['a']=none ∧
    evV (⟨[]⟩ : MGrammar) ['a','a'] .callByValuePar (fun _ _ => []) [['a']]
      (.seq (.lit ['a']) (.param 0)) 2=some (some 0) ∧
    RecursiveScannerProductHeader.entryCheck missing (.shift 0 missingLabels)
      (CaptureTransitionProfile.profile (DynamicScannerCapture.observer missing) ['a'])=false := by decide +kernel

end Shallot.MacroPeg.CBV.UncheckedShiftCaptureExamples
