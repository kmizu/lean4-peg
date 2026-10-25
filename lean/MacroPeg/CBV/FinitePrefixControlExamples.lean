import MacroPeg.CBV.FinitePrefixControl

namespace Shallot.MacroPeg.CBV.FinitePrefixControlExamples
open FinitePrefixControl
open RecursiveScannerProductCompiler (Arg sourceExpr offset)
open ScannerOriginControl (Part)
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def machine : StatefulScanner.Machine 2 := ⟨fun q => [('a',q)]⟩
def residuals : ScannerReplayResidual.Labels 2 := fun q => some (List.replicate (q.val+1) 'a')
def read (w : List Char) := w.length
def copy (w : List Char) := 3+w.length
def parts : List (Part 2) := [⟨.replay,.lit [],true⟩,⟨.replay,.lit ['a'],true⟩,
  ⟨.replay,.lit ['a','a'],true⟩,⟨.replay,.lit [],false⟩,
  ⟨.shift 0 residuals,.lit [],false⟩,⟨.shift 1 residuals,.lit [],false⟩]
def first : Prefix := .alt (.lit ['a','a']) (.lit ['a'])
def committed : Prefix := .seq first (.query true)
def controlledPrefix : Prefix := .alt (.seq (.lit ['a']) (.seq (.query false) (.lit ['a']))) (.lit ['a'])
def dependent : Prefix := .seq controlledPrefix (.query true)
def nested : Prefix := .seq (.notP (.seq (.lit ['a']) (.query false))) (.lit ['a'])
def bodies : List Prefix := [committed,dependent,nested,.seq (.lit ['a']) (.query false),.query true,controlledPrefix]
def ps := plans read copy bodies
def probing : Arg := .seq (.lit ['a','a']) (.notP (.notP (.user 0 (.lit []))))
def root : Arg := .seq (.user 0 probing) (.lit ['a','a'])
def argument : Arg := .seq (.lit ['a']) (.seq (.star (.lit ['b'])) (.lit ['a']))
def negativeRoot : Arg := .seq (.user 3 argument) (.seq (.star (.lit ['b'])) (.lit ['a']))

theorem checked : check machine parts read copy bodies=true ∧
    ScannerOriginControl.scopeCheck ps root=true ∧ ScannerOriginControl.scopeCheck ps negativeRoot=true := by
  decide +kernel

def sourceRun (e : Arg) (x : List Char) (k : Nat) :=
  evV (source machine bodies) x .callByValuePar (tblV (source machine bodies) x .callByValuePar k) [] (sourceExpr machine e) x.length

def targetRun (e : Arg) (x : List Char) (k : Nat) :=
  evV (ScannerOriginControl.target machine parts ps) x .callByValueSeq
    (tblV (ScannerOriginControl.target machine parts ps) x .callByValueSeq k) []
    (ScannerOriginControl.targetExpr machine parts ps e) x.length

/-- The source really chooses its prefix before the retained-value query. -/
theorem raw_rule : ruleAtM (source machine bodies).rules (offset machine+0)=
    some ⟨1,.seq (.alt (.lit ['a','a']) (.lit ['a'])) (.andP (.param 0))⟩ := by
  exact source_rule machine bodies 0 committed rfl

/-- A body rewrite that distributes the final query reopens the prefix
choice and wrongly succeeds on aaa. Correct source and target reject. -/
theorem committed_query :
    sourceRun (.user 0 (.lit ['a','a'])) "aaa".toList 2=some none ∧
    targetRun (.user 0 (.lit ['a','a'])) "aaa".toList 8=some none ∧
    evV (source machine bodies) "aaa".toList .callByValuePar
      (tblV (source machine bodies) "aaa".toList .callByValuePar 2) [['a','a']]
      (.alt (.seq (.lit ['a','a']) (.andP (.param 0)))
        (.seq (.lit ['a']) (.andP (.param 0)))) 3=some (some 2) := by decide +kernel

/-- Capture-dependent internal rejection selects the shorter prefix.
Negation can itself contain consuming prefix/query control. -/
theorem value_dependent_prefix :
    sourceRun (.user 1 (.lit ['a','a','a'])) "aaaa".toList 2=some (some 3) ∧
    targetRun (.user 1 (.lit ['a','a','a'])) "aaaa".toList 8=some (some 3) ∧
    sourceRun (.user 2 (.lit ['a','a','a'])) "aaaa".toList 2=some (some 3) ∧
    targetRun (.user 2 (.lit ['a','a','a'])) "aaaa".toList 8=some (some 3) ∧
    sourceRun (.user 2 (.lit ['a','a','a'])) "aaa".toList 2=some none ∧
    targetRun (.user 2 (.lit ['a','a','a'])) "aaa".toList 8=some none := by decide +kernel

/-- On the same input, the retained value selects different successful
prefix lengths. This prefix is not a single capture-independent literal. -/
theorem capture_selects_length :
    sourceRun (.user 5 (.lit ['a','a'])) "aaa".toList 2=some (some 2) ∧
    targetRun (.user 5 (.lit ['a','a'])) "aaa".toList 8=some (some 2) ∧
    sourceRun (.user 5 (.lit ['a','a','a'])) "aaa".toList 2=some (some 1) ∧
    targetRun (.user 5 (.lit ['a','a','a'])) "aaa".toList 8=some (some 1) := by decide +kernel

/-- The actual argument probes the same raw-prefix user with a fresh
empty capture. The outer user subsequently queries its complete aa value. -/
theorem same_user_probe :
    sourceRun root "aaaa".toList 2=some (some 0) ∧ targetRun root "aaaa".toList 8=some (some 0) ∧
    sourceRun root "aaa".toList 2=some none ∧ targetRun root "aaa".toList 8=some none ∧
    sourceRun (.user 4 (.lit ['a','a'])) "aaa".toList 2=some (some 3) ∧
    targetRun (.user 4 (.lit ['a','a'])) "aaa".toList 8=some (some 3) := by decide +kernel

theorem variable_capture_samples : ∀ n∈[1,2,4],
    let x := ['a']++List.replicate n 'b'++['a']
    sourceRun negativeRoot x 2=some (some 0) ∧ targetRun negativeRoot x 8=some (some 0) := by decide +kernel

theorem language : ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
    SObs (source machine bodies) .callByValuePar (sourceExpr machine root) x (some []) ↔
      SObs g .callByValueSeq start x (some []) :=
  language_translation machine parts read copy bodies checked.1 root checked.2.1

theorem negative_language : ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
    SObs (source machine bodies) .callByValuePar (sourceExpr machine negativeRoot) x (some []) ↔
      SObs g .callByValueSeq start x (some []) :=
  language_translation machine parts read copy bodies checked.1 negativeRoot checked.2.2

def nullable : Arg := .user 0 (.star (.lit []))

theorem nullable_source (x : List Char) (k : Nat) : sourceRun nullable x k=none := by
  change evV (source machine bodies) x .callByValuePar (tblV (source machine bodies) x .callByValuePar k) []
    (.call (offset machine+0) [sourceExpr machine (.star (.lit []))]) x.length=none
  rw [evV_call_par raw_rule rfl (by decide)]
  have hloop : evV (source machine bodies) x .callByValuePar (tblV (source machine bodies) x .callByValuePar k) []
      (sourceExpr machine (.star (.lit []))) x.length=none := by
    apply evStar_stuck (j:=x.length) _ (Nat.lt_irrefl _)
    simp [sourceExpr,evV,Shallot.stripPrefix?,length_sfx x (Nat.le_refl _)]
  simp only [evParArgs,hloop]

theorem nullable_target (x : List Char) (k : Nat) : targetRun nullable x k=none :=
  (undefined_iff machine parts read copy bodies checked.1 nullable (by decide) x).mp (nullable_source x) k

theorem missing_prefix_link : checkAt parts read copy (.seq (.lit ['a','a']) (.lit ['a'])) []=false := by decide +kernel

end Shallot.MacroPeg.CBV.FinitePrefixControlExamples
