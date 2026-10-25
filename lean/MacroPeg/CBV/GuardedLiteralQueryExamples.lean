import MacroPeg.CBV.AlphabetCaptureProfiles

namespace Shallot.MacroPeg.CBV.GuardedLiteralQueryExamples
open RecursiveScannerProductCompiler
open RecursiveCaptureProfiles (scopeCheck)
open AlphabetCaptureProfiles
open CaptureTransitionProfile (profile)
open DynamicScannerCapture (observer)
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- State 0 supplies the alphabet frontier and the rotating a step.
States 1/2 observe how much of aa lies inside the actual capture. -/
def machine : StatefulScanner.Machine 3 := ⟨fun q => if q=0 then [('a',0)] else if q=1 then [('a',2)] else [('a',0)]⟩
def alphabet : List Char := ['a']
def labels : LiteralPrefixObservation.Labels 3 := fun q =>
  some (if q=1 then ['a','a'] else if q=2 then ['a'] else [])
def rotating : ScannerReplayResidual.Labels 3 := fun q => if q=0 then some ['a'] else none
def query : GuardedReplayControl.Expr 3 := .literalQuery alphabet 0 1 labels
def control : GuardedReplayControl.Expr 3 := .star (.seq query (.shift 0 rotating))
def entries : Entries 3 := fun i => if i=1 then .replay else if i=2 then .aligned (.star query) else .aligned control
def copyBody : Arg := .alt (.seq (.user 1 (.seq (.param 0) (.param 0))) (.param 0)) (.lit [])
def bodies : List Arg := [.lit [],copyBody,.lit []]
def argument : Arg := .user 1 (.lit ['a'])
def root : Arg := .user 0 argument

theorem checked : AlphabetCaptureProfiles.check machine entries bodies alphabet=true ∧
    scopeCheck bodies root=true ∧ literalCheck alphabet root=true := by decide +kernel

theorem universal_rejected : UniversalCaptureProfiles.check machine entries bodies=false := by decide +kernel

theorem raw_rule : ruleAtM (source machine entries bodies).rules (offset machine+0)=
    some ⟨1,.seq (.seq (.star (.seq (.andP (.lit ['a','a']))
      (.seq (.lit ['a']) (.andP (.param 0)))) ) (.param 0)) (.lit [])⟩ :=
  source_rule machine entries bodies 0 (.lit []) rfl

def sourceRun (e : Arg) (x : List Char) (k : Nat) :=
  evV (source machine entries bodies) x .callByValuePar (tblV (source machine entries bodies) x .callByValuePar k) [] (sourceExpr machine e) x.length

def targetRun (e : Arg) (x : List Char) (k : Nat) :=
  evV (target machine entries bodies) x .callByValueSeq (tblV (target machine entries bodies) x .callByValueSeq k) [] (plain machine bodies [] e) x.length

/-- The same real recursive argument produces different held lengths,
so aa is partly or wholly inside the capture on different calls. -/
theorem recursive_source_samples : ∀ n∈[1,2,3,4,5,6,10,11,12],
    sourceRun root (List.replicate n 'a') 4=some (some 0) := by decide +kernel

theorem recursive_target_samples : ∀ n∈[1,2,3,4,5,6,10,11,12],
    ∃ k, targetRun root (List.replicate n 'a') k=some (some 0) := by
  intro n hn
  exact (defined_iff machine entries bodies alphabet checked.1 root checked.2.1 checked.2.2 (List.replicate n 'a') (some 0)).mp
    ⟨4,recursive_source_samples n hn⟩

theorem target_direct : targetRun root "aaaaa".toList 8=some (some 0) ∧
    targetRun (.user 0 (.lit ['a','a'])) "aaaa".toList 2=some (some 0) := by decide +kernel

/-- Testing the unchanged literal at the capture endpoint loses one a;
the generated profile-controlled test correctly remembers it matched before. -/
theorem naive_endpoint_query_wrong :
    evV ⟨[]⟩ "aaaa".toList .callByValueSeq (fun _ _ => []) [['a','a']]
      (.star (.seq (.andP (.lit ['a','a'])) (.lit ['a']))) 2=some (some 1) := by decide +kernel

theorem empty_capture : sourceRun (.user 0 (.lit [])) "aaaa".toList 1=some (some 1) ∧
    targetRun (.user 0 (.lit [])) "aaaa".toList 2=some (some 1) := by decide +kernel

def productRoot : Arg := .user 1 (.user 0 (.lit ['a','a']))
theorem product_direct : sourceRun productRoot "aaaa".toList 2=some (some 0) ∧
    targetRun productRoot "aaaa".toList 3=some (some 0) := by decide +kernel

theorem language : ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
    SObs (source machine entries bodies) .callByValuePar (sourceExpr machine root) x (some []) ↔
      SObs g .callByValueSeq start x (some []) :=
  language_translation machine entries bodies alphabet checked.1 root checked.2.1 checked.2.2

theorem nullable_query_source (k : Nat) : sourceRun (.user 2 (.lit ['a'])) "aa".toList k=none := by
  have hr := source_rule machine entries bodies 2 (.lit []) (by rfl)
  have hb (T : ClockFreezing.Table) : evV (source machine entries bodies) "aa".toList .callByValuePar T [['a']]
      (.seq (sourceHeader (entries 2)) (.lit [])) 2=none := by
    have he := GuardedReplayControl.header_independent (source machine entries bodies) ⟨[]⟩ "aa".toList
      .callByValuePar .callByValuePar T (fun _ _ => []) [['a']] (.star query) 2
    have hn : evV ⟨[]⟩ "aa".toList .callByValuePar (fun _ _ => []) [['a']]
        (GuardedReplayControl.header (.star query)) 2=none := by decide +kernel
    exact evV_seq_none (he.trans hn)
  change evV (source machine entries bodies) "aa".toList .callByValuePar
    (tblV (source machine entries bodies) "aa".toList .callByValuePar k) []
    (.call (offset machine+2) [.lit ['a']]) 2=none
  rw [evV_call_par hr rfl (by decide)]
  change valAt (tblV (source machine entries bodies) "aa".toList .callByValuePar k (offset machine+2) [['a']]) 2=none
  cases k with
  | zero => rfl
  | succ k => rw [valAt_tblV_succ hr _ (by decide : 2≤"aa".toList.length)]; exact hb _

theorem nullable_query_target (k : Nat) : targetRun (.user 2 (.lit ['a'])) "aa".toList k=none :=
  (undefined_iff machine entries bodies alphabet checked.1 (.user 2 (.lit ['a'])) (by decide) (by decide) "aa".toList).mp nullable_query_source k

theorem invalid_frontier_rejected : GuardedReplayControl.check machine
    (.literalQuery alphabet 1 1 labels)=false := by decide +kernel

/- A nonperiodic, unbounded capture needs only its configured alphabet
frontier, not readability from every observation state. -/
namespace Opaque

def machine : StatefulScanner.Machine 3 := ⟨fun q =>
  if q=0 then [('a',0),('b',0)] else if q=1 then [('a',2)] else [('a',2),('b',2)]⟩
def alphabet : List Char := ['a','b']
def labels : LiteralPrefixObservation.Labels 3 := fun q =>
  if q=1 then some ['a'] else if q=2 then some [] else none
def query : GuardedReplayControl.Expr 3 := .literalQuery alphabet 0 1 labels
def control : GuardedReplayControl.Expr 3 := .star query
def entries : Entries 3 := fun _ => .aligned control
def bodies : List Arg := [.lit []]
def argument : Arg := .star (.alt (.lit ['a']) (.lit ['b']))
def root : Arg := .user 0 argument

theorem checked : AlphabetCaptureProfiles.check machine entries bodies alphabet=true ∧
    scopeCheck bodies root=true ∧ literalCheck alphabet root=true := by decide +kernel

theorem configured_frontier_suffices :
    ¬TotalCaptureSafety.Total machine "bba".toList ∧
    GuardedReplayControl.captureCheck (profile (observer machine) "bba".toList) control=true := by
  refine ⟨?_,by decide +kernel⟩
  intro h
  exact h 1 (by decide +kernel)

def sourceRun (e : Arg) (x : List Char) (k : Nat) :=
  evV (source machine entries bodies) x .callByValuePar (tblV (source machine entries bodies) x .callByValuePar k) [] (sourceExpr machine e) x.length

def targetRun (e : Arg) (x : List Char) (k : Nat) :=
  evV (target machine entries bodies) x .callByValueSeq (tblV (target machine entries bodies) x .callByValueSeq k) [] (plain machine bodies [] e) x.length

theorem source_nonperiodic_samples : ∀ n∈[1,2,4],
    sourceRun root (['b']++List.replicate n 'a'++['b']) 1=some (some 0) := by decide +kernel

theorem target_nonperiodic_samples : ∀ n∈[1,2,4],
    ∃ k, targetRun root (['b']++List.replicate n 'a'++['b']) k=some (some 0) := by
  intro n hn
  exact (defined_iff machine entries bodies alphabet checked.1 root checked.2.1 checked.2.2 _ (some 0)).mp
    ⟨1,source_nonperiodic_samples n hn⟩

theorem target_direct : targetRun (.user 0 (.lit "bba".toList)) "bba".toList 1=some (some 0) ∧
    targetRun (.user 0 (.lit "aab".toList)) "aab".toList 1=none := by decide +kernel

theorem language : ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
    SObs (source machine entries bodies) .callByValuePar (sourceExpr machine root) x (some []) ↔
      SObs g .callByValueSeq start x (some []) :=
  language_translation machine entries bodies alphabet checked.1 root checked.2.1 checked.2.2

end Opaque
end Shallot.MacroPeg.CBV.GuardedLiteralQueryExamples
