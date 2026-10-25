import MacroPeg.CBV.PrefixCaptureQuery
import MacroPeg.CBV.UncheckedShiftCaptureExamples

namespace Shallot.MacroPeg.CBV.PrefixCaptureQueryExamples
open RecursiveScannerProductCompiler (Arg sourceExpr)
open ScannerOriginControl (Part coreEntries coreBodies normalize target targetExpr readyCheck scopeCheck)
open PrefixCaptureQuery
open ScannerReplayResidualExamples (machine D residuals scanners)
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def link : Link := ⟨6,7⟩
def parts : List (Part 3) := UncheckedShiftCaptureExamples.parts ++ [
  ⟨.replay,.lit ['a','b'],true⟩,
  ⟨.shift 0 residuals,.lit [],false⟩,
  ⟨.replay,.seq (.lit ['c']) (.user 8 (.seq (.star (.lit ['c'])) (.lit "ababa".toList))),true⟩]
/-- These are actual raw user bodies, not hand-expanded origin Plans. The
positive query user recursively re-enters itself with a fresh capture. -/
def bodies : List Body := UncheckedShiftCaptureExamples.plans.map liftPlan ++
  [.after false link,.alt (.leaf 8) (.after true link)]
def root : Arg := .user 7 (.user 2 UncheckedShiftCaptureExamples.actualArgument)
def positive : Arg := .user 8 (.user 2 (.lit "ababa".toList))
def recursive : Arg := .seq (.user 8 (.lit [])) (.lit "ababa".toList)

def summary : RecursiveCaptureProfiles.Summary := fun i P =>
  if i=6 then [CaptureTransitionProfile.compose P (CaptureTransitionProfile.profile D ['a','b'])]
  else if i=7 then [CaptureTransitionProfile.compose (CaptureTransitionProfile.profile D ['a','b']) P]
  else if i=8 then [CaptureTransitionProfile.profile D ['c']]
  else UncheckedShiftCaptureExamples.summary i P

def inputs : ProfileCheckedScannerCorrespondence.Inputs := fun i =>
  if i=7 then CaptureTransitionProfile.profiles D
  else if i=6 || i=8 then [CaptureTransitionProfile.profile D []]
  else UncheckedShiftCaptureExamples.inputs i

theorem checked :
    syntaxCheck parts bodies=true ∧ readyCheck parts (plans bodies)=true ∧ scopeCheck (plans bodies) root=true ∧
    RecursiveCaptureProfiles.scannerCheck machine scanners=true ∧
    RecursiveCaptureProfiles.grammarCheck machine (coreEntries parts) (coreBodies parts (plans bodies)) scanners summary=true ∧
    ProfileCheckedScannerCorrespondence.bodiesCheck machine (coreEntries parts) (coreBodies parts (plans bodies)) summary inputs=true ∧
    ProfileCheckedScannerCorrespondence.check machine (coreEntries parts) (coreBodies parts (plans bodies)) summary inputs [] (normalize parts (plans bodies) root)=true := by
  decide +kernel

/-- The source rule itself contains ab; !param0. It is not already a
caller-side test followed by an independent leaf. -/
theorem actual_negative_rule :
    ruleAtM (source machine parts bodies).rules (RecursiveScannerProductCompiler.offset machine+7)=
      some ⟨1,.seq (.lit ['a','b']) (.notP (.param 0))⟩ := by rfl

def negativeInput : List Char := "abababc".toList

theorem negative_source :
    evV (source machine parts bodies) negativeInput .callByValuePar
      (tblV (source machine parts bodies) negativeInput .callByValuePar 4) []
      (sourceExpr machine (.user 2 UncheckedShiftCaptureExamples.actualArgument)) negativeInput.length=some (some 0) ∧
    evV (source machine parts bodies) negativeInput .callByValuePar
      (tblV (source machine parts bodies) negativeInput .callByValuePar 4) []
      (sourceExpr machine root) negativeInput.length=some (some 5) := by decide +kernel

theorem negative_target : ∃ k,
    evV (target machine parts (plans bodies)) negativeInput .callByValueSeq
      (tblV (target machine parts (plans bodies)) negativeInput .callByValueSeq k) []
      (targetExpr machine parts (plans bodies) root) negativeInput.length=some (some 5) :=
  (defined_iff machine parts bodies checked.1 checked.2.1 root checked.2.2.1 scanners summary inputs
    checked.2.2.2.1 checked.2.2.2.2.1 checked.2.2.2.2.2.1 checked.2.2.2.2.2.2 negativeInput (some 5)).mp
      ⟨4,negative_source.2⟩

/-- With the same actual five-character capture, a complete shifted copy
lets the positive test consume only ab; a three-character copy rejects. -/
theorem positive_source :
    evV (source machine parts bodies) "abababa".toList .callByValuePar
      (tblV (source machine parts bodies) "abababa".toList .callByValuePar 4) []
      (sourceExpr machine positive) 7=some (some 5) ∧
    evV (source machine parts bodies) "ababa".toList .callByValuePar
      (tblV (source machine parts bodies) "ababa".toList .callByValuePar 4) []
      (sourceExpr machine positive) 5=some none := by decide +kernel

theorem positive_target :
    (∃ k, evV (target machine parts (plans bodies)) "abababa".toList .callByValueSeq
      (tblV (target machine parts (plans bodies)) "abababa".toList .callByValueSeq k) []
      (targetExpr machine parts (plans bodies) positive) 7=some (some 5)) ∧
    (∃ k, evV (target machine parts (plans bodies)) "ababa".toList .callByValueSeq
      (tblV (target machine parts (plans bodies)) "ababa".toList .callByValueSeq k) []
      (targetExpr machine parts (plans bodies) positive) 5=some none) :=
  ⟨(defined_iff machine parts bodies checked.1 checked.2.1 positive (by decide +kernel) scanners summary inputs
      checked.2.2.2.1 checked.2.2.2.2.1 checked.2.2.2.2.2.1 (by decide +kernel) "abababa".toList (some 5)).mp
        ⟨4,positive_source.1⟩,
   (defined_iff machine parts bodies checked.1 checked.2.1 positive (by decide +kernel) scanners summary inputs
      checked.2.2.2.1 checked.2.2.2.2.1 checked.2.2.2.2.2.1 (by decide +kernel) "ababa".toList none).mp
        ⟨4,positive_source.2⟩⟩

theorem recursive_source :
    evV (source machine parts bodies) "cccabababa".toList .callByValuePar
      (tblV (source machine parts bodies) "cccabababa".toList .callByValuePar 5) []
      (sourceExpr machine recursive) 10=some (some 0) := by decide +kernel

theorem recursive_target : ∃ k,
    evV (target machine parts (plans bodies)) "cccabababa".toList .callByValueSeq
      (tblV (target machine parts (plans bodies)) "cccabababa".toList .callByValueSeq k) []
      (targetExpr machine parts (plans bodies) recursive) 10=some (some 0) :=
  (defined_iff machine parts bodies checked.1 checked.2.1 recursive (by decide +kernel) scanners summary inputs
    checked.2.2.2.1 checked.2.2.2.2.1 checked.2.2.2.2.2.1 (by decide +kernel) "cccabababa".toList (some 0)).mp
      ⟨5,recursive_source⟩

theorem negative_language : ∃ (g : MGrammar) (e : MExp), g.FirstOrder ∧ e.FirstOrder ∧ ∀ x,
    SObs (source machine parts bodies) .callByValuePar
      (sourceExpr machine (.seq root (.lit "ababc".toList))) x (some []) ↔
      SObs g .callByValueSeq e x (some []) :=
  language_translation machine parts bodies checked.1 checked.2.1 (.seq root (.lit "ababc".toList))
    (by decide +kernel) scanners summary inputs
    checked.2.2.2.1 checked.2.2.2.2.1 checked.2.2.2.2.2.1 (by decide +kernel)

theorem recursive_language : ∃ (g : MGrammar) (e : MExp), g.FirstOrder ∧ e.FirstOrder ∧ ∀ x,
    SObs (source machine parts bodies) .callByValuePar (sourceExpr machine recursive) x (some []) ↔
      SObs g .callByValueSeq e x (some []) :=
  language_translation machine parts bodies checked.1 checked.2.1 recursive
    (by decide +kernel) scanners summary inputs
    checked.2.2.2.1 checked.2.2.2.2.1 checked.2.2.2.2.2.1 (by decide +kernel)

/-- A mismatched literal and a nonempty copy continuation cannot be used
to certify a raw prefix query. -/
theorem invalid_links_rejected :
    linkCheck parts ⟨4,7⟩=false ∧ linkCheck parts ⟨6,0⟩=false := by decide +kernel

def nullable : Arg := .user 7 (.star (.lit []))

theorem nullable_source (x : List Char) (clock : Nat) :
    evV (source machine parts bodies) x .callByValuePar
      (tblV (source machine parts bodies) x .callByValuePar clock) []
      (sourceExpr machine nullable) x.length=none := by
  have he : evV (source machine parts bodies) x .callByValuePar
      (tblV (source machine parts bodies) x .callByValuePar clock) [] (.star (.lit [])) x.length=none :=
    evStar_stuck (show evV (source machine parts bodies) x .callByValuePar
      (tblV (source machine parts bodies) x .callByValuePar clock) [] (.lit []) x.length=some (some x.length) from by
        simp [evV,Shallot.stripPrefix?,length_sfx x (Nat.le_refl _)]) (Nat.not_lt.mpr (Nat.le_refl _))
  have hr : ruleAtM (source machine parts bodies).rules (RecursiveScannerProductCompiler.offset machine+7)=
      some ⟨1,.seq (.lit ['a','b']) (.notP (.param 0))⟩ := actual_negative_rule
  rw [show sourceExpr machine nullable=.call (RecursiveScannerProductCompiler.offset machine+7) [.star (.lit [])] from rfl,
    evV_call_par hr rfl (by decide)]
  simp only [evParArgs,he]

theorem nullable_target (x : List Char) (clock : Nat) :
    evV (target machine parts (plans bodies)) x .callByValueSeq
      (tblV (target machine parts (plans bodies)) x .callByValueSeq clock) []
      (targetExpr machine parts (plans bodies) nullable) x.length=none :=
  (undefined_iff machine parts bodies checked.1 checked.2.1 nullable (by decide +kernel) scanners summary inputs
    checked.2.2.2.1 checked.2.2.2.2.1 checked.2.2.2.2.2.1 (by decide +kernel) x).mp (nullable_source x) clock

end Shallot.MacroPeg.CBV.PrefixCaptureQueryExamples
