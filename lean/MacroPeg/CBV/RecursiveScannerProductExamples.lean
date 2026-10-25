import MacroPeg.CBV.RecursiveScannerProductCorrespondence

namespace Shallot.MacroPeg.CBV.RecursiveScannerProductExamples
open RecursiveScannerProductCompiler
open RecursiveScannerProductCorrespondence

def M : StatefulScanner.Machine 2 := ⟨fun q => [('a',⟨1-q.val,by omega⟩),('b',q)]⟩

def entries : Entries 2 := fun _ => some 0

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

theorem checked : sourceSafe M entries bodies 1=true ∧
    bodies.all (check M bodies 1)=true ∧ check M bodies 1 root=true := by decide +kernel

/-- The non-certified !/? consumer remains in the same actual grammar,
and can occur under a query in the certified parser's body. -/
theorem selective_component :
    ParameterizedCaptureSafety.grammarCheck M (source M entries bodies)=false ∧
    ParameterizedCaptureSafety.componentCheck M (source M entries bodies) (offset M+1)=true := by decide +kernel

theorem correspondence (x : List Char) (r : Option (List Char)) :
    SObs (source M entries bodies) .callByValuePar (sourceExpr M root) x r ↔
      SObs (target M entries bodies) .callByValueSeq (plain M bodies [] root) x r :=
  observations_iff M entries bodies 1 checked.1 checked.2.1 root checked.2.2 x r

/-- Actual source tables capture ab through user 0, capture aab in its
recursive child, and restore/reuse both complete values after the child. -/
theorem parent_return :
    evV (source M entries bodies) input .callByValuePar
      (tblV (source M entries bodies) input .callByValuePar 14) []
      (sourceExpr M root) input.length=some (some 0) := by decide +kernel

/-- The fixed generated grammar has an ordinary physical accepting run;
its clock may differ from the actual source clock. -/
theorem target_physical : ∃ k,
    evV (target M entries bodies) input .callByValueSeq
      (tblV (target M entries bodies) input .callByValueSeq k) []
      (plain M bodies [] root) input.length=some (some 0) :=
  (defined_iff M entries bodies 1 checked.1 checked.2.1 root checked.2.2 input (some 0)).mp ⟨14,parent_return⟩

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
    evV (source M entries bodies) x .callByValuePar
      (tblV (source M entries bodies) x .callByValuePar 14) []
      (sourceExpr M root) x.length == some none)=true := by decide +kernel

theorem short_target (x : List Char) (hx : x∈shortCopies) : ∃ k,
    evV (target M entries bodies) x .callByValueSeq
      (tblV (target M entries bodies) x .callByValueSeq k) []
      (plain M bodies [] root) x.length=some none := by
  have h := (List.all_eq_true.mp short_source) x hx
  have hv : evV (source M entries bodies) x .callByValuePar
      (tblV (source M entries bodies) x .callByValuePar 14) []
      (sourceExpr M root) x.length=some none := by simpa using h
  exact (defined_iff M entries bodies 1 checked.1 checked.2.1 root checked.2.2 x none).mp ⟨14,hv⟩

/-- Empty succeeds first in the inner argument choice. The subsequent
parameter query fails; the longer argument is never retried. -/
def chosenRoot : Arg := .user 1 (.user 0 (.alt (.lit []) (.lit ['a'])))

theorem committed_empty :
    check M bodies 1 chosenRoot=true ∧
    evV (source M entries bodies) input .callByValuePar
      (tblV (source M entries bodies) input .callByValuePar 14) []
      (sourceExpr M chosenRoot) input.length=some none := by decide +kernel

theorem committed_target : ∃ k,
    evV (target M entries bodies) input .callByValueSeq
      (tblV (target M entries bodies) input .callByValueSeq k) []
      (plain M bodies [] chosenRoot) input.length=some none :=
  (defined_iff M entries bodies 1 checked.1 checked.2.1 chosenRoot committed_empty.1 input none).mp
    ⟨14,committed_empty.2⟩

/-- Actual argument failure precedes the unavailable user rows at clock 0. -/
theorem clock_zero_argument_failure :
    evV (source M entries bodies) ['!'] .callByValuePar
      (tblV (source M entries bodies) ['!'] .callByValuePar 0) []
      (sourceExpr M root) 1=some none ∧
    evV (target M entries bodies) ['!'] .callByValueSeq
      (tblV (target M entries bodies) ['!'] .callByValueSeq 0) []
      (plain M bodies [] root) 1=some none := by decide +kernel

def nullable : Arg := .user 1 (.star (.lit []))

theorem nullable_source (x : List Char) (clock : Nat) :
    evV (source M entries bodies) x .callByValuePar
      (tblV (source M entries bodies) x .callByValuePar clock) []
      (sourceExpr M nullable) x.length=none := by
  have he : evV (source M entries bodies) x .callByValuePar
      (tblV (source M entries bodies) x .callByValuePar clock) []
      (.star (.lit [])) x.length=none := by
    exact evStar_stuck (show evV (source M entries bodies) x .callByValuePar
      (tblV (source M entries bodies) x .callByValuePar clock) []
      (.lit []) x.length=some (some x.length) from by simp [evV,Shallot.stripPrefix?,length_sfx x (Nat.le_refl _)])
      (Nat.not_lt.mpr (Nat.le_refl _))
  rw [show sourceExpr M nullable=.call (offset M+1) [.star (.lit [])] from rfl,
    evV_call_par (source_rule M entries bodies 1 body (by rfl)) rfl]
  · simp only [evParArgs,he]
  · decide

theorem nullable_target (x : List Char) (clock : Nat) :
    evV (target M entries bodies) x .callByValueSeq
      (tblV (target M entries bodies) x .callByValueSeq clock) []
      (plain M bodies [] nullable) x.length=none :=
  (undefined_iff M entries bodies 1 checked.1 checked.2.1 nullable (by decide +kernel) x).mp
    (nullable_source x) clock

/-- The positive parameterized parser can itself receive a fresh argument
assembled from its caller's retained value and a new literal. -/
def retainedCapture : Arg := .user 0 (.seq (.param 0) (.lit ['b']))
def retainedBody : Arg := .seq (.lit ['!']) (.seq (.param 0)
  (.seq (.alt (.seq (.lit [':']) (.user 1 retainedCapture)) (.lit []))
    (.seq (.lit ['?']) (.param 0))))
def retainedBodies : List Arg := [parser,retainedBody]
def retainedInput : List Char := "ab!ab:abb!abb?abb?ab".toList

theorem retained_checked : sourceSafe M entries retainedBodies 1=true ∧
    retainedBodies.all (check M retainedBodies 1)=true ∧
    check M retainedBodies 1 root=true := by decide +kernel

theorem retained_source :
    evV (source M entries retainedBodies) retainedInput .callByValuePar
      (tblV (source M entries retainedBodies) retainedInput .callByValuePar 14) []
      (sourceExpr M root) retainedInput.length=some (some 0) := by decide +kernel

theorem retained_target : ∃ k,
    evV (target M entries retainedBodies) retainedInput .callByValueSeq
      (tblV (target M entries retainedBodies) retainedInput .callByValueSeq k) []
      (plain M retainedBodies [] root) retainedInput.length=some (some 0) :=
  (defined_iff M entries retainedBodies 1 retained_checked.1 retained_checked.2.1 root
    retained_checked.2.2 retainedInput (some 0)).mp ⟨14,retained_source⟩

/-- Replay users and users scanning from different states coexist in one
actual grammar. The certified argument parser itself replays its parameter
and queries an uncertified scanner user. -/
def mixedEntries : Entries 2
  | 2 => some 1
  | 3 => some 0
  | _ => none

def mixedParser : Arg := .seq (.notP (.param 0)) (.notP (.user 3 (.lit [])))
def mixedNext : Arg := .user 0 (.seq (.param 0) (.lit ['a']))
def mixedReplay : Arg := .seq
  (.alt (.seq (.lit [':']) (.user 2 mixedNext)) (.lit ['!']))
  (.seq (.lit ['?']) (.param 0))
def mixedScan : Arg := .seq (.lit ['!']) (.seq (.param 0)
  (.seq (.alt (.seq (.lit [':']) (.user 1 mixedNext)) (.lit []))
    (.seq (.lit ['?']) (.param 0))))
def mixedBodies : List Arg := [mixedParser,mixedReplay,mixedScan,.lit ['Z']]
def mixedRoot : Arg := .user 1 (.user 0 (.lit ['a','b']))
def mixedInput : List Char := "ab:abab!aba:abaa!?abaa?aba?ab".toList

theorem mixed_checked : sourceSafe M mixedEntries mixedBodies 1=true ∧
    mixedBodies.all (check M mixedBodies 1)=true ∧ check M mixedBodies 1 mixedRoot=true := by decide +kernel

theorem mixed_source :
    evV (source M mixedEntries mixedBodies) mixedInput .callByValuePar
      (tblV (source M mixedEntries mixedBodies) mixedInput .callByValuePar 18) []
      (sourceExpr M mixedRoot) mixedInput.length=some (some 0) := by decide +kernel

theorem mixed_target : ∃ k,
    evV (target M mixedEntries mixedBodies) mixedInput .callByValueSeq
      (tblV (target M mixedEntries mixedBodies) mixedInput .callByValueSeq k) []
      (plain M mixedBodies [] mixedRoot) mixedInput.length=some (some 0) :=
  (defined_iff M mixedEntries mixedBodies 1 mixed_checked.1 mixed_checked.2.1 mixedRoot
    mixed_checked.2.2 mixedInput (some 0)).mp ⟨18,mixed_source⟩

theorem mixed_language : ∃ (g : MGrammar) (e : MExp), g.FirstOrder ∧ e.FirstOrder ∧ ∀ x,
    SObs (source M mixedEntries mixedBodies) .callByValuePar (sourceExpr M mixedRoot) x (some []) ↔
      SObs g .callByValueSeq e x (some []) :=
  language_translation M mixedEntries mixedBodies 1 mixed_checked.1 mixed_checked.2.1
    mixedRoot mixed_checked.2.2

/-- The scan user starts at state 1, captures only aba, and consumes the
extra b before its tail. Resetting to state 0 has a different final state. -/
theorem mixed_resumption :
    StatefulScanner.advance M 1 "aba".toList=some 1 ∧
    StatefulScanner.run M 1 "b!aba".toList=(1,"!aba".toList) ∧
    StatefulScanner.run M 0 "abab!aba".toList=(0,"!aba".toList) := by decide +kernel

def mixedShortCopies : List (List Char) := [
  "ab:abab!ab:abaa!?abaa?aba?ab".toList,
  "ab:abab!aba:abaa!?aba?aba?ab".toList,
  "ab:abab!aba:abaa!?abaa?ab?ab".toList,
  "ab:abab!aba:abaa!?abaa?aba?a".toList]

theorem mixed_short_source : mixedShortCopies.all (fun x =>
    evV (source M mixedEntries mixedBodies) x .callByValuePar
      (tblV (source M mixedEntries mixedBodies) x .callByValuePar 18) []
      (sourceExpr M mixedRoot) x.length == some none)=true := by decide +kernel

theorem mixed_short_target (x : List Char) (hx : x∈mixedShortCopies) : ∃ k,
    evV (target M mixedEntries mixedBodies) x .callByValueSeq
      (tblV (target M mixedEntries mixedBodies) x .callByValueSeq k) []
      (plain M mixedBodies [] mixedRoot) x.length=some none := by
  have h := (List.all_eq_true.mp mixed_short_source) x hx
  have hv : evV (source M mixedEntries mixedBodies) x .callByValuePar
      (tblV (source M mixedEntries mixedBodies) x .callByValuePar 18) []
      (sourceExpr M mixedRoot) x.length=some none := by simpa using h
  exact (defined_iff M mixedEntries mixedBodies 1 mixed_checked.1 mixed_checked.2.1
    mixedRoot mixed_checked.2.2 x none).mp ⟨18,hv⟩

/-- Here b is readable only from state 1. Closed scanner helpers are not
capture-safe, but actual argument paths only use the certified replay user. -/
def partialM : StatefulScanner.Machine 2 := ⟨fun q =>
  if q.val=0 then [('a',1)] else [('a',0),('b',1)]⟩
def partialRoot : Arg := .user 1 (.user 0 (.lit ['a']))
def partialInput : List Char := "a:aab!aa:aaa!?aaa?aa?a".toList

theorem partial_checked : helperSafe partialM=false ∧
    sourceSafe partialM mixedEntries mixedBodies 1=true ∧
    mixedBodies.all (check partialM mixedBodies 1)=true ∧
    check partialM mixedBodies 1 partialRoot=true ∧
    ParameterizedCaptureSafety.componentCheck partialM (source partialM mixedEntries mixedBodies)
      (offset partialM+1)=false := by decide +kernel

theorem partial_source :
    evV (source partialM mixedEntries mixedBodies) partialInput .callByValuePar
      (tblV (source partialM mixedEntries mixedBodies) partialInput .callByValuePar 18) []
      (sourceExpr partialM partialRoot) partialInput.length=some (some 0) := by decide +kernel

theorem partial_target : ∃ k,
    evV (target partialM mixedEntries mixedBodies) partialInput .callByValueSeq
      (tblV (target partialM mixedEntries mixedBodies) partialInput .callByValueSeq k) []
      (plain partialM mixedBodies [] partialRoot) partialInput.length=some (some 0) :=
  (defined_iff partialM mixedEntries mixedBodies 1 partial_checked.2.1 partial_checked.2.2.1
    partialRoot partial_checked.2.2.2.1 partialInput (some 0)).mp ⟨18,partial_source⟩

theorem partial_language : ∃ (g : MGrammar) (e : MExp), g.FirstOrder ∧ e.FirstOrder ∧ ∀ x,
    SObs (source partialM mixedEntries mixedBodies) .callByValuePar (sourceExpr partialM partialRoot) x (some []) ↔
      SObs g .callByValueSeq e x (some []) :=
  language_translation partialM mixedEntries mixedBodies 1 partial_checked.2.1 partial_checked.2.2.1
    partialRoot partial_checked.2.2.2.1

/-- Choosing the wrong initial state stops before b and rejects this same
original input. This is a check of the translation's configured entry. -/
def wrongEntries : Entries 2
  | 2 => some 0
  | i => mixedEntries i

theorem partial_state_matters :
    StatefulScanner.run partialM 1 "aab!aa".toList=(1,"!aa".toList) ∧
    StatefulScanner.run partialM 0 "aab!aa".toList=(0,"b!aa".toList) ∧
    evV (source partialM wrongEntries mixedBodies) partialInput .callByValuePar
      (tblV (source partialM wrongEntries mixedBodies) partialInput .callByValuePar 18) []
      (sourceExpr partialM partialRoot) partialInput.length=some none := by decide +kernel

/-- State 0 accepts only a first; a synchronizes both states to 1.
Thus every word consumed from 0 is total, although the b-helper is unsafe
and words consumed from 1 need not be total. -/
def syncM : StatefulScanner.Machine 2 := ⟨fun q =>
  if q.val=0 then [('a',1)] else [('a',1),('b',1)]⟩
def syncEntries : Entries 2
  | 0 => some 0
  | _ => some 1

def syncParser : Arg := .notP (.param 0)
def syncNext : Arg := .user 0 (.seq (.param 0) (.lit ['a']))
def syncBody : Arg := .seq (.lit ['!']) (.seq (.param 0)
  (.seq (.alt (.seq (.lit [':']) (.user 1 syncNext)) (.lit []))
    (.seq (.lit ['?']) (.param 0))))
def syncBodies : List Arg := [syncParser,syncBody]
def syncRoot : Arg := .user 1 (.user 0 (.lit ['a']))
def syncInput : List Char := "ab!ab:abaab!abaab?abaab?ab".toList

theorem sync_checked :
    helperSafe syncM=false ∧ primitive syncM 0=true ∧ primitive syncM 1=false ∧
    sourceSafe syncM syncEntries syncBodies 1=true ∧
    syncBodies.all (check syncM syncBodies 1)=true ∧ check syncM syncBodies 1 syncRoot=true ∧
    TotalCaptureSafety.wordCheck syncM ['b']=false ∧ TotalCaptureSafety.wordCheck syncM ['a','b']=true := by
  decide +kernel

/-- This actual positive argument call enters the partial scanner user,
not a replay user. The parent's ab contributes to the child's new argument
aba, and the scanner really captures the longer abaab. -/
theorem sync_source :
    evV (source syncM syncEntries syncBodies) syncInput .callByValuePar
      (tblV (source syncM syncEntries syncBodies) syncInput .callByValuePar 18) []
      (sourceExpr syncM syncRoot) syncInput.length=some (some 0) := by decide +kernel

theorem sync_target : ∃ k,
    evV (target syncM syncEntries syncBodies) syncInput .callByValueSeq
      (tblV (target syncM syncEntries syncBodies) syncInput .callByValueSeq k) []
      (plain syncM syncBodies [] syncRoot) syncInput.length=some (some 0) :=
  (defined_iff syncM syncEntries syncBodies 1 sync_checked.2.2.2.1 sync_checked.2.2.2.2.1
    syncRoot sync_checked.2.2.2.2.2.1 syncInput (some 0)).mp ⟨18,sync_source⟩

theorem sync_language : ∃ (g : MGrammar) (e : MExp), g.FirstOrder ∧ e.FirstOrder ∧ ∀ x,
    SObs (source syncM syncEntries syncBodies) .callByValuePar (sourceExpr syncM syncRoot) x (some []) ↔
      SObs g .callByValueSeq e x (some []) :=
  language_translation syncM syncEntries syncBodies 1 sync_checked.2.2.2.1 sync_checked.2.2.2.2.1
    syncRoot sync_checked.2.2.2.2.2.1

def syncShortCopies : List (List Char) := [
  "ab!ab:abaab!abaa?abaab?ab".toList,
  "ab!ab:abaab!abaab?abaa?ab".toList,
  "ab!ab:abaab!abaab?abaab?a".toList]

theorem sync_short_source : syncShortCopies.all (fun x =>
    evV (source syncM syncEntries syncBodies) x .callByValuePar
      (tblV (source syncM syncEntries syncBodies) x .callByValuePar 18) []
      (sourceExpr syncM syncRoot) x.length == some none)=true := by decide +kernel

theorem sync_short_target (x : List Char) (hx : x∈syncShortCopies) : ∃ k,
    evV (target syncM syncEntries syncBodies) x .callByValueSeq
      (tblV (target syncM syncEntries syncBodies) x .callByValueSeq k) []
      (plain syncM syncBodies [] syncRoot) x.length=some none := by
  have h := (List.all_eq_true.mp sync_short_source) x hx
  have hv : evV (source syncM syncEntries syncBodies) x .callByValuePar
      (tblV (source syncM syncEntries syncBodies) x .callByValuePar 18) []
      (sourceExpr syncM syncRoot) x.length=some none := by simpa using h
  exact (defined_iff syncM syncEntries syncBodies 1 sync_checked.2.2.2.1 sync_checked.2.2.2.2.1
    syncRoot sync_checked.2.2.2.2.2.1 x none).mp ⟨18,hv⟩

end Shallot.MacroPeg.CBV.RecursiveScannerProductExamples
