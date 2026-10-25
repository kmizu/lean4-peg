import MacroPeg.CBV.ScannerOriginControlExamples

namespace Shallot.MacroPeg.CBV.CaptureIndependentOriginExamples
open RecursiveScannerProductCompiler (Arg sourceExpr)
open ScannerOriginControl
open ScannerReplayResidualExamples (machine D argument scanners)
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- A closed leaf may recursively call the same original user and mix with
users that inspect fresh, unbounded captures. -/
def recursiveBody : Arg := .alt
  (.seq (.lit ['c']) (.user 4 (.lit [])))
  (.user 0 (.user 2 argument))

def parts : List (Part 3) := ScannerOriginControlExamples.parts ++
  [⟨.replay,.lit ['a'],true⟩,⟨.replay,recursiveBody,true⟩]
def plans : List ReplayControlFusion.Plan := ScannerOriginControlExamples.plans ++ [.alt (.leaf 4) (.leaf 3),.leaf 5]
def root : Arg := .user 3 (.lit "abc".toList)
def recursiveRoot : Arg := .user 4 (.lit [])
def summary : RecursiveCaptureProfiles.Summary := fun i P =>
  if i=4 then [CaptureTransitionProfile.compose P (CaptureTransitionProfile.profile D ['a'])]
  else if i=5 then [P,CaptureTransitionProfile.profile D ['c']]
  else ScannerOriginControlExamples.summary i P

def inputs : ProfileCheckedScannerCorrespondence.Inputs := fun i =>
  if i<4 then ScannerOriginControlExamples.inputs i else [CaptureTransitionProfile.profile D []]

theorem checked :
    readyCheck parts plans=true ∧ scopeCheck plans root=true ∧
    RecursiveCaptureProfiles.scannerCheck machine scanners=true ∧
    RecursiveCaptureProfiles.grammarCheck machine (coreEntries parts) (coreBodies parts plans) scanners summary=true ∧
    ProfileCheckedScannerCorrespondence.bodiesCheck machine (coreEntries parts) (coreBodies parts plans) summary inputs=true ∧
    ProfileCheckedScannerCorrespondence.check machine (coreEntries parts) (coreBodies parts plans) summary inputs [] (normalize parts plans root)=true := by
  decide +kernel

/-- The argument really captures abc, but the body consumes only a,
before the capture endpoint. -/
theorem before_capture_source :
    evV (original machine parts plans) "abc".toList .callByValuePar
      (tblV (original machine parts plans) "abc".toList .callByValuePar 2) []
      (sourceExpr machine root) 3=some (some 2) := by decide +kernel

theorem before_capture_target : ∃ k,
    evV (target machine parts plans) "abc".toList .callByValueSeq
      (tblV (target machine parts plans) "abc".toList .callByValueSeq k) []
      (targetExpr machine parts plans root) 3=some (some 2) :=
  (defined_iff machine parts plans checked.1 root checked.2.1 scanners summary inputs
    checked.2.2.1 checked.2.2.2.1 checked.2.2.2.2.1 checked.2.2.2.2.2 "abc".toList (some 2)).mp
      ⟨2,before_capture_source⟩

theorem short_language : ∃ (g : MGrammar) (e : MExp), g.FirstOrder ∧ e.FirstOrder ∧ ∀ x,
    SObs (original machine parts plans) .callByValuePar
      (sourceExpr machine (.seq root (.lit ['b','c']))) x (some []) ↔
      SObs g .callByValueSeq e x (some []) :=
  language_translation machine parts plans checked.1 (.seq root (.lit ['b','c']))
    (by decide +kernel) scanners summary inputs
    checked.2.2.1 checked.2.2.2.1 checked.2.2.2.2.1 (by decide +kernel)

def fallbackRoot : Arg := .user 3 (.lit "bbc".toList)

/-- The same source user's Plan mixes an independent consuming leaf with
an ordinary leaf that replays its full actual captured value. -/
theorem dependent_fallback_source :
    evV (original machine parts plans) "bbc".toList .callByValuePar
      (tblV (original machine parts plans) "bbc".toList .callByValuePar 2) []
      (sourceExpr machine fallbackRoot) 3=some (some 0) := by decide +kernel

theorem dependent_fallback_target : ∃ k,
    evV (target machine parts plans) "bbc".toList .callByValueSeq
      (tblV (target machine parts plans) "bbc".toList .callByValueSeq k) []
      (targetExpr machine parts plans fallbackRoot) 3=some (some 0) :=
  (defined_iff machine parts plans checked.1 fallbackRoot (by decide +kernel) scanners summary inputs
    checked.2.2.1 checked.2.2.2.1 checked.2.2.2.2.1 (by decide +kernel) "bbc".toList (some 0)).mp
      ⟨2,dependent_fallback_source⟩

def input : List Char := ['c','c','c'] ++ ScannerOriginControlExamples.input

theorem recursive_source :
    evV (original machine parts plans) input .callByValuePar
      (tblV (original machine parts plans) input .callByValuePar 20) []
      (sourceExpr machine recursiveRoot) input.length=some (some 0) := by decide +kernel

theorem recursive_target : ∃ k,
    evV (target machine parts plans) input .callByValueSeq
      (tblV (target machine parts plans) input .callByValueSeq k) []
      (targetExpr machine parts plans recursiveRoot) input.length=some (some 0) :=
  (defined_iff machine parts plans checked.1 recursiveRoot (by decide +kernel) scanners summary inputs
    checked.2.2.1 checked.2.2.2.1 checked.2.2.2.2.1 (by decide +kernel) input (some 0)).mp
      ⟨20,recursive_source⟩

/-- A fixed first-order Seq grammar preserves this recursive original
language on every unchanged input, rather than only the sample. -/
theorem language : ∃ (g : MGrammar) (e : MExp), g.FirstOrder ∧ e.FirstOrder ∧ ∀ x,
    SObs (original machine parts plans) .callByValuePar (sourceExpr machine recursiveRoot) x (some []) ↔
      SObs g .callByValueSeq e x (some []) :=
  language_translation machine parts plans checked.1 recursiveRoot (by decide +kernel) scanners summary inputs
    checked.2.2.1 checked.2.2.2.1 checked.2.2.2.2.1 (by decide +kernel)

/-- Discarding the captured value must not discard evaluation of the
actual source argument. Here the body could read a, but abc fails first. -/
theorem argument_failure_source :
    evV (original machine parts plans) "ab".toList .callByValuePar
      (tblV (original machine parts plans) "ab".toList .callByValuePar 2) []
      (sourceExpr machine root) 2=some none := by decide +kernel

theorem argument_failure_target : ∃ k,
    evV (target machine parts plans) "ab".toList .callByValueSeq
      (tblV (target machine parts plans) "ab".toList .callByValueSeq k) []
      (targetExpr machine parts plans root) 2=some none :=
  (defined_iff machine parts plans checked.1 root checked.2.1 scanners summary inputs
    checked.2.2.1 checked.2.2.2.1 checked.2.2.2.2.1 checked.2.2.2.2.2 "ab".toList none).mp
      ⟨2,argument_failure_source⟩

def nullable : Arg := .user 3 (.star (.lit []))

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
  rw [show sourceExpr machine nullable=.call (RecursiveScannerProductCompiler.offset machine+3) [.star (.lit [])] from rfl,
    evV_call_par (original_rule machine parts plans 3 (plans[3]) (by rfl)) rfl]
  · simp only [evParArgs,he]
  · decide

theorem nullable_target (x : List Char) (clock : Nat) :
    evV (target machine parts plans) x .callByValueSeq
      (tblV (target machine parts plans) x .callByValueSeq clock) []
      (targetExpr machine parts plans nullable) x.length=none :=
  (undefined_iff machine parts plans checked.1 nullable (by decide +kernel) scanners summary inputs
    checked.2.2.1 checked.2.2.2.1 checked.2.2.2.2.1 (by decide +kernel) x).mp (nullable_source x) clock

/-- Queries and user arguments cannot hide a dependence on the old value. -/
theorem rejects_hidden_parameters :
    independent (.notP (.param 0))=false ∧ independent (.user 0 (.param 0))=false ∧
    readyCheck [(⟨.replay,.notP (.param 0),true⟩ : Part 3)] [.leaf 0]=false := by decide +kernel

end Shallot.MacroPeg.CBV.CaptureIndependentOriginExamples
