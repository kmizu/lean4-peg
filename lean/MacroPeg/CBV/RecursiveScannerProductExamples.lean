import MacroPeg.CBV.RecursiveScannerProductCorrespondence

namespace Shallot.MacroPeg.CBV.RecursiveScannerProductExamples
open RecursiveScannerProductCompiler
open RecursiveScannerProductCorrespondence

def M : StatefulScanner.Machine 2 := ⟨fun q => [('a',⟨1-q.val,by omega⟩),('b',q)]⟩

/-- User 0 is a certified positive parameterized parser. At its scanner
frontier it tests its retained value, then queries the ordinary user 1.
User 1 consumes ! and ?, outside the certified consuming component. -/
def parser : Arg := .seq (.notP (.param 0)) (.notP (.user 1 (.lit [])))
def capture : Arg := .user 0 (.lit ['a'])
def body : Arg := .seq (.lit ['!']) (.seq (.param 0)
  (.seq (.alt (.seq (.lit [':']) (.user 1 capture)) (.lit [])) (.seq (.lit ['?']) (.param 0))))
def bodies : List Arg := [parser,body]
def root : Arg := .user 1 capture

def input : List Char := "ab!ab:aab!aab?aab?ab".toList

set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem checked : sourceSafe M (0 : Fin 2) bodies 1=true ∧
    bodies.all (check M bodies 1)=true ∧ check M bodies 1 root=true := by decide +kernel

/-- The non-certified !/? consumer remains in the same actual grammar,
and can occur under a query in the certified parser's body. -/
theorem selective_component :
    ParameterizedCaptureSafety.grammarCheck M (source M (0 : Fin 2) bodies)=false ∧
    ParameterizedCaptureSafety.componentCheck M (source M (0 : Fin 2) bodies) (offset M+1)=true := by decide +kernel

theorem correspondence (x : List Char) (r : Option (List Char)) :
    SObs (source M (0 : Fin 2) bodies) .callByValuePar (sourceExpr M root) x r ↔
      SObs (target M (0 : Fin 2) bodies) .callByValueSeq (plain M bodies [] root) x r :=
  observations_iff M 0 bodies 1 checked.1 checked.2.1 root checked.2.2 x r

/-- Actual source tables capture ab through user 0, capture aab in its
recursive child, and restore/reuse both complete values after the child. -/
theorem parent_return :
    evV (source M (0 : Fin 2) bodies) input .callByValuePar
      (tblV (source M (0 : Fin 2) bodies) input .callByValuePar 14) []
      (sourceExpr M root) input.length=some (some 0) := by decide +kernel

/-- The fixed generated grammar has an ordinary physical accepting run;
its clock may differ from the actual source clock. -/
theorem target_physical : ∃ k,
    evV (target M (0 : Fin 2) bodies) input .callByValueSeq
      (tblV (target M (0 : Fin 2) bodies) input .callByValueSeq k) []
      (plain M bodies [] root) input.length=some (some 0) :=
  (defined_iff M 0 bodies 1 checked.1 checked.2.1 root checked.2.2 input (some 0)).mp ⟨14,parent_return⟩

/-- Whole captured values change the residual scanner states. -/
theorem actual_states :
    StatefulScanner.advance M 0 "ab".toList=some 1 ∧
    StatefulScanner.advance M 0 "aab".toList=some 0 := by decide +kernel

/-- Each complete retained value is required, including after return. -/
def shortCopies : List (List Char) := [
  "ab!ab:aab!aa?aab?ab".toList,
  "ab!ab:aab!aab?aa?ab".toList,
  "ab!ab:aab!aab?aab?a".toList]

theorem short_source : shortCopies.all (fun x =>
    evV (source M (0 : Fin 2) bodies) x .callByValuePar
      (tblV (source M (0 : Fin 2) bodies) x .callByValuePar 14) []
      (sourceExpr M root) x.length == some none)=true := by decide +kernel

theorem short_target (x : List Char) (hx : x∈shortCopies) : ∃ k,
    evV (target M (0 : Fin 2) bodies) x .callByValueSeq
      (tblV (target M (0 : Fin 2) bodies) x .callByValueSeq k) []
      (plain M bodies [] root) x.length=some none := by
  have h := (List.all_eq_true.mp short_source) x hx
  have hv : evV (source M (0 : Fin 2) bodies) x .callByValuePar
      (tblV (source M (0 : Fin 2) bodies) x .callByValuePar 14) []
      (sourceExpr M root) x.length=some none := by simpa using h
  exact (defined_iff M 0 bodies 1 checked.1 checked.2.1 root checked.2.2 x none).mp ⟨14,hv⟩

/-- Empty succeeds first in the inner argument choice. The subsequent
parameter query fails; the longer argument is never retried. -/
def chosenRoot : Arg := .user 1 (.user 0 (.alt (.lit []) (.lit ['a'])))

theorem committed_empty :
    check M bodies 1 chosenRoot=true ∧
    evV (source M (0 : Fin 2) bodies) input .callByValuePar
      (tblV (source M (0 : Fin 2) bodies) input .callByValuePar 14) []
      (sourceExpr M chosenRoot) input.length=some none := by decide +kernel

theorem committed_target : ∃ k,
    evV (target M (0 : Fin 2) bodies) input .callByValueSeq
      (tblV (target M (0 : Fin 2) bodies) input .callByValueSeq k) []
      (plain M bodies [] chosenRoot) input.length=some none :=
  (defined_iff M 0 bodies 1 checked.1 checked.2.1 chosenRoot committed_empty.1 input none).mp
    ⟨14,committed_empty.2⟩

/-- Actual argument failure precedes the unavailable user rows at clock 0. -/
theorem clock_zero_argument_failure :
    evV (source M (0 : Fin 2) bodies) ['!'] .callByValuePar
      (tblV (source M (0 : Fin 2) bodies) ['!'] .callByValuePar 0) []
      (sourceExpr M root) 1=some none ∧
    evV (target M (0 : Fin 2) bodies) ['!'] .callByValueSeq
      (tblV (target M (0 : Fin 2) bodies) ['!'] .callByValueSeq 0) []
      (plain M bodies [] root) 1=some none := by decide +kernel

def nullable : Arg := .user 1 (.star (.lit []))

theorem nullable_source (x : List Char) (clock : Nat) :
    evV (source M (0 : Fin 2) bodies) x .callByValuePar
      (tblV (source M (0 : Fin 2) bodies) x .callByValuePar clock) []
      (sourceExpr M nullable) x.length=none := by
  have he : evV (source M (0 : Fin 2) bodies) x .callByValuePar
      (tblV (source M (0 : Fin 2) bodies) x .callByValuePar clock) []
      (.star (.lit [])) x.length=none := by
    exact evStar_stuck (show evV (source M (0 : Fin 2) bodies) x .callByValuePar
      (tblV (source M (0 : Fin 2) bodies) x .callByValuePar clock) []
      (.lit []) x.length=some (some x.length) from by simp [evV,Shallot.stripPrefix?,length_sfx x (Nat.le_refl _)])
      (Nat.not_lt.mpr (Nat.le_refl _))
  rw [show sourceExpr M nullable=.call (offset M+1) [.star (.lit [])] from rfl,
    evV_call_par (source_rule M 0 bodies 1 body (by rfl)) rfl]
  · simp only [evParArgs,he]
  · decide

theorem nullable_target (x : List Char) (clock : Nat) :
    evV (target M (0 : Fin 2) bodies) x .callByValueSeq
      (tblV (target M (0 : Fin 2) bodies) x .callByValueSeq clock) []
      (plain M bodies [] nullable) x.length=none :=
  (undefined_iff M 0 bodies 1 checked.1 checked.2.1 nullable (by decide +kernel) x).mp
    (nullable_source x) clock

/-- The positive parameterized parser can itself receive a fresh argument
assembled from its caller's retained value and a new literal. -/
def retainedCapture : Arg := .user 0 (.seq (.param 0) (.lit ['b']))
def retainedBody : Arg := .seq (.lit ['!']) (.seq (.param 0)
  (.seq (.alt (.seq (.lit [':']) (.user 1 retainedCapture)) (.lit []))
    (.seq (.lit ['?']) (.param 0))))
def retainedBodies : List Arg := [parser,retainedBody]
def retainedInput : List Char := "ab!ab:abb!abb?abb?ab".toList

theorem retained_checked : sourceSafe M (0 : Fin 2) retainedBodies 1=true ∧
    retainedBodies.all (check M retainedBodies 1)=true ∧
    check M retainedBodies 1 root=true := by decide +kernel

theorem retained_source :
    evV (source M (0 : Fin 2) retainedBodies) retainedInput .callByValuePar
      (tblV (source M (0 : Fin 2) retainedBodies) retainedInput .callByValuePar 14) []
      (sourceExpr M root) retainedInput.length=some (some 0) := by decide +kernel

theorem retained_target : ∃ k,
    evV (target M (0 : Fin 2) retainedBodies) retainedInput .callByValueSeq
      (tblV (target M (0 : Fin 2) retainedBodies) retainedInput .callByValueSeq k) []
      (plain M retainedBodies [] root) retainedInput.length=some (some 0) :=
  (defined_iff M 0 retainedBodies 1 retained_checked.1 retained_checked.2.1 root
    retained_checked.2.2 retainedInput (some 0)).mp ⟨14,retained_source⟩

end Shallot.MacroPeg.CBV.RecursiveScannerProductExamples
