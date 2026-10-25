import MacroPeg.CBV.RecursiveScannerProductCorrespondence

namespace Shallot.MacroPeg.CBV.RecursiveScannerProductExamples
open RecursiveScannerProductCompiler
open RecursiveScannerProductCorrespondence

def M : StatefulScanner.Machine 2 := ⟨fun q => [('a',⟨1-q.val,by omega⟩),('b',q)]⟩

def entries : Entries 2 := fun _ => .scan 0

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
    bodiesCheck M entries bodies 1=true ∧ check M entries bodies 1 true root=true := by decide +kernel

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
    check M entries bodies 1 true chosenRoot=true ∧
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
    bodiesCheck M entries retainedBodies 1=true ∧
    check M entries retainedBodies 1 true root=true := by decide +kernel

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
  | 2 => .scan 1
  | 3 => .scan 0
  | _ => .safeReplay

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
    bodiesCheck M mixedEntries mixedBodies 1=true ∧ check M mixedEntries mixedBodies 1 true mixedRoot=true := by decide +kernel

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
    bodiesCheck partialM mixedEntries mixedBodies 1=true ∧
    check partialM mixedEntries mixedBodies 1 true partialRoot=true ∧
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
  | 2 => .scan 0
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
  | 0 => .scan 0
  | _ => .scan 1

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
    bodiesCheck syncM syncEntries syncBodies 1=true ∧ check syncM syncEntries syncBodies 1 true syncRoot=true ∧
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

/-- Arbitrary replay captures may contain characters outside M. A call
into a scanner builds a new safe argument, using the old value only in a
query; other replay calls freely assemble and retain new arbitrary words. -/
def arbitraryEntries : Entries 2
  | 1 => .scan 0
  | _ => .replay

def queriedArgument : Arg := .seq (.notP (.param 0)) (.lit ['a'])
def arbitraryNext : Arg := .user 2 (.seq (.param 0) (.lit ['z']))
def arbitraryBody : Arg := .seq (.lit ['!']) (.seq (.user 1 queriedArgument)
  (.seq (.alt (.seq (.lit [':']) (.user 0 arbitraryNext)) (.lit []))
    (.seq (.lit ['?']) (.param 0))))
def arbitraryBodies : List Arg := [arbitraryBody,.seq (.lit [':']) (.param 0),.lit []]
def arbitraryRoot : Arg := .user 0 (.user 2 (.seq (.star (.lit ['z'])) (.lit ['#'])))
def arbitraryInput : List Char := "z#!ab:a:z#z!ab:a?z#z?z#".toList

theorem arbitrary_checked :
    sourceSafe partialM arbitraryEntries arbitraryBodies 0=true ∧
    bodiesCheck partialM arbitraryEntries arbitraryBodies 0=true ∧
    check partialM arbitraryEntries arbitraryBodies 0 true arbitraryRoot=true ∧
    TotalCaptureSafety.wordCheck partialM ['z','#']=false ∧
    TotalCaptureSafety.wordCheck partialM ['z','#','z']=false := by decide +kernel

theorem arbitrary_source :
    evV (source partialM arbitraryEntries arbitraryBodies) arbitraryInput .callByValuePar
      (tblV (source partialM arbitraryEntries arbitraryBodies) arbitraryInput .callByValuePar 18) []
      (sourceExpr partialM arbitraryRoot) arbitraryInput.length=some (some 0) := by decide +kernel

theorem arbitrary_target : ∃ k,
    evV (target partialM arbitraryEntries arbitraryBodies) arbitraryInput .callByValueSeq
      (tblV (target partialM arbitraryEntries arbitraryBodies) arbitraryInput .callByValueSeq k) []
      (plain partialM arbitraryBodies [] arbitraryRoot) arbitraryInput.length=some (some 0) :=
  (defined_iff partialM arbitraryEntries arbitraryBodies 0 arbitrary_checked.1 arbitrary_checked.2.1
    arbitraryRoot arbitrary_checked.2.2.1 arbitraryInput (some 0)).mp ⟨18,arbitrary_source⟩

theorem arbitrary_language : ∃ (g : MGrammar) (e : MExp), g.FirstOrder ∧ e.FirstOrder ∧ ∀ x,
    SObs (source partialM arbitraryEntries arbitraryBodies) .callByValuePar (sourceExpr partialM arbitraryRoot) x (some []) ↔
      SObs g .callByValueSeq e x (some []) :=
  language_translation partialM arbitraryEntries arbitraryBodies 0 arbitrary_checked.1 arbitrary_checked.2.1
    arbitraryRoot arbitrary_checked.2.2.1

/-- Captured arbitrary values can be queried in safe arguments; consuming
them as scanner arguments is rejected, while replay forwarding is allowed. -/
theorem arbitrary_boundary :
    check partialM arbitraryEntries arbitraryBodies 0 false (.user 1 (.param 0))=false ∧
    check partialM arbitraryEntries arbitraryBodies 0 false (.user 1 queriedArgument)=true ∧
    check partialM arbitraryEntries arbitraryBodies 0 false (.user 0 (.param 0))=true := by decide +kernel

theorem arbitrary_query_parent :
    evV (source partialM arbitraryEntries arbitraryBodies) "ab:a".toList .callByValuePar
      (tblV (source partialM arbitraryEntries arbitraryBodies) "ab:a".toList .callByValuePar 0)
      [['a']] (sourceExpr partialM queriedArgument) 4=some none ∧
    evV (source partialM arbitraryEntries arbitraryBodies) "ab:a".toList .callByValuePar
      (tblV (source partialM arbitraryEntries arbitraryBodies) "ab:a".toList .callByValuePar 0)
      [['z','#']] (sourceExpr partialM queriedArgument) 4=some (some 3) := by decide +kernel

def arbitraryShortCopies : List (List Char) := [
  "z#!ab:a:z#!ab:a?z#z?z#".toList,
  "z#!ab:a:z#z!ab:a?z#?z#".toList,
  "z#!ab:a:z#z!ab:a?z#z?z".toList]

theorem arbitrary_short_source : arbitraryShortCopies.all (fun x =>
    evV (source partialM arbitraryEntries arbitraryBodies) x .callByValuePar
      (tblV (source partialM arbitraryEntries arbitraryBodies) x .callByValuePar 18) []
      (sourceExpr partialM arbitraryRoot) x.length == some none)=true := by decide +kernel

theorem arbitrary_short_target (x : List Char) (hx : x∈arbitraryShortCopies) : ∃ k,
    evV (target partialM arbitraryEntries arbitraryBodies) x .callByValueSeq
      (tblV (target partialM arbitraryEntries arbitraryBodies) x .callByValueSeq k) []
      (plain partialM arbitraryBodies [] arbitraryRoot) x.length=some none := by
  have h := (List.all_eq_true.mp arbitrary_short_source) x hx
  have hv : evV (source partialM arbitraryEntries arbitraryBodies) x .callByValuePar
      (tblV (source partialM arbitraryEntries arbitraryBodies) x .callByValuePar 18) []
      (sourceExpr partialM arbitraryRoot) x.length=some none := by simpa using h
  exact (defined_iff partialM arbitraryEntries arbitraryBodies 0 arbitrary_checked.1 arbitrary_checked.2.1
    arbitraryRoot arbitrary_checked.2.2.1 x none).mp ⟨18,hv⟩

def arbitraryNullable : Arg := .user 0 (.star (.lit []))

theorem arbitrary_nullable_source (x : List Char) (clock : Nat) :
    evV (source partialM arbitraryEntries arbitraryBodies) x .callByValuePar
      (tblV (source partialM arbitraryEntries arbitraryBodies) x .callByValuePar clock) []
      (sourceExpr partialM arbitraryNullable) x.length=none := by
  have he : evV (source partialM arbitraryEntries arbitraryBodies) x .callByValuePar
      (tblV (source partialM arbitraryEntries arbitraryBodies) x .callByValuePar clock) []
      (.star (.lit [])) x.length=none := by
    exact evStar_stuck (show evV (source partialM arbitraryEntries arbitraryBodies) x .callByValuePar
      (tblV (source partialM arbitraryEntries arbitraryBodies) x .callByValuePar clock) []
      (.lit []) x.length=some (some x.length) from by
        simp [evV,Shallot.stripPrefix?,length_sfx x (Nat.le_refl _)])
      (Nat.not_lt.mpr (Nat.le_refl _))
  rw [show sourceExpr partialM arbitraryNullable=.call (offset partialM+0) [.star (.lit [])] from rfl,
    evV_call_par (source_rule partialM arbitraryEntries arbitraryBodies 0 arbitraryBody (by rfl)) rfl]
  · simp only [evParArgs,he]
  · decide

theorem arbitrary_nullable_target (x : List Char) (clock : Nat) :
    evV (target partialM arbitraryEntries arbitraryBodies) x .callByValueSeq
      (tblV (target partialM arbitraryEntries arbitraryBodies) x .callByValueSeq clock) []
      (plain partialM arbitraryBodies [] arbitraryNullable) x.length=none :=
  (undefined_iff partialM arbitraryEntries arbitraryBodies 0 arbitrary_checked.1 arbitrary_checked.2.1
    arbitraryNullable (by decide +kernel) x).mp (arbitrary_nullable_source x) clock

/-- The initial arbitrary capture is input-dependent and unbounded,
obtained through a positive parameterized replay call. -/
def arbitraryLongInput : List Char := "zzzz#!ab:a:zzzz#z!ab:a?zzzz#z?zzzz#".toList

theorem arbitrary_long_source :
    evV (source partialM arbitraryEntries arbitraryBodies) arbitraryLongInput .callByValuePar
      (tblV (source partialM arbitraryEntries arbitraryBodies) arbitraryLongInput .callByValuePar 18) []
      (sourceExpr partialM arbitraryRoot) arbitraryLongInput.length=some (some 0) := by decide +kernel

theorem arbitrary_long_target : ∃ k,
    evV (target partialM arbitraryEntries arbitraryBodies) arbitraryLongInput .callByValueSeq
      (tblV (target partialM arbitraryEntries arbitraryBodies) arbitraryLongInput .callByValueSeq k) []
      (plain partialM arbitraryBodies [] arbitraryRoot) arbitraryLongInput.length=some (some 0) :=
  (defined_iff partialM arbitraryEntries arbitraryBodies 0 arbitrary_checked.1 arbitrary_checked.2.1
    arbitraryRoot arbitrary_checked.2.2.1 arbitraryLongInput (some 0)).mp ⟨18,arbitrary_long_source⟩

end Shallot.MacroPeg.CBV.RecursiveScannerProductExamples
