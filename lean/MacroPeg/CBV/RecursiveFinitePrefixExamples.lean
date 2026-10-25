import MacroPeg.CBV.RecursiveFinitePrefix

namespace Shallot.MacroPeg.CBV.RecursiveFinitePrefixExamples
open RecursiveFinitePrefix
open FinitePrefixControl (Prefix)
open RecursiveScannerProductCompiler (Arg sourceExpr offset)
open ScannerOriginControl (Part)
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def machine : StatefulScanner.Machine 2 := ⟨fun q => [('a',q)]⟩
def residuals : ScannerReplayResidual.Labels 2 := fun q => some (List.replicate (q.val+1) 'a')
def read (w : List Char) := w.length
def copy (w : List Char) := 3+w.length
def links (w : List Char) := 6+w.length
def failureLinks (w : List Char) := 9+w.length
def loopLinks (w : List Char) := 12+w.length

def head : Prefix := .alt (.seq (.lit ['a']) (.seq (.query true) (.lit ['a']))) (.lit ['a'])
/-- The child captures twice the parent's entire value. After it returns,
the question mark and the original parent value are consumed by the parent. -/
def tail : Arg := .alt (.seq (.lit [':']) (.seq (.user 0 (.seq (.param 0) (.param 0)))
  (.seq (.lit ['?']) (.param 0)))) (.lit [])
def parts : List (Part 2) := [⟨.replay,.lit [],true⟩,⟨.replay,.lit ['a'],true⟩,
  ⟨.replay,.lit ['a','a'],true⟩,⟨.replay,.lit [],false⟩,
  ⟨.shift 0 residuals,.lit [],false⟩,⟨.shift 1 residuals,.lit [],false⟩,
  ⟨.replay,tail,false⟩,⟨.shift 0 residuals,tail,false⟩,⟨.shift 1 residuals,tail,false⟩,
  ⟨.replay,.lit ['a'],false⟩,⟨.shift 0 residuals,.lit ['a'],false⟩,⟨.shift 1 residuals,.lit ['a'],false⟩,
  ⟨.replay,.star (.lit []),false⟩,⟨.shift 0 residuals,.star (.lit []),false⟩,⟨.shift 1 residuals,.star (.lit []),false⟩]
def bodies : List Body := [.resume head tail links,.finish (.seq (.lit ['a']) (.query false)),
  .resume head (.lit ['a']) failureLinks,.resume head (.star (.lit [])) loopLinks]
def ps := plans read copy bodies
/-- The actual first capture ends two characters before its a-run ends.
Its length comes from the input, not from a fixed argument word palette. -/
def argument : Arg := .seq (.star (.seq (.lit ['a']) (.notP (.notP (.lit ['a','a','a']))))) (.lit ['a'])
def root : Arg := .user 0 argument

theorem checked : check machine parts read copy bodies=true ∧ ScannerOriginControl.scopeCheck ps root=true := by
  decide +kernel

def input (m : Nat) : Nat → List Char
  | 0 => List.replicate (m+2) 'a'
  | d+1 => List.replicate (m+2) 'a'++[':']++input (2*m) d++['?']++List.replicate m 'a'

def sourceRun (e : Arg) (x : List Char) (k : Nat) :=
  evV (source machine bodies) x .callByValuePar (tblV (source machine bodies) x .callByValuePar k) [] (sourceExpr machine e) x.length

def targetRun (e : Arg) (x : List Char) (k : Nat) :=
  evV (ScannerOriginControl.target machine parts ps) x .callByValueSeq
    (tblV (ScannerOriginControl.target machine parts ps) x .callByValueSeq k) []
    (ScannerOriginControl.targetExpr machine parts ps e) x.length

/-- This source grammar has genuine same-user recursion in the actual
rule body, after the capture-dependent prefix and whole-value replay. -/
theorem raw_rule : ruleAtM (source machine bodies).rules (offset machine+0)=
    some ⟨1,.seq (FinitePrefixControl.raw head) (.seq (.param 0) (sourceExpr machine tail))⟩ :=
  source_rule machine bodies 0 (.resume head tail links) rfl

theorem actual_capture : ∀ m∈[1,2,4],
    evV (source machine bodies) (input m 2) .callByValuePar
      (tblV (source machine bodies) (input m 2) .callByValuePar 3) []
      (sourceExpr machine argument) (input m 2).length=some (some ((input m 2).length-m)) ∧
    pre (input m 2) (input m 2).length ((input m 2).length-m)=List.replicate m 'a' := by decide +kernel

/-- Capture length and actual recursive depth both vary in one fixed root.
Each child doubles the complete retained value, then both parents restore it. -/
theorem source_recursive_samples : ∀ m∈[1,2,4], ∀ d∈[0,1,2],
    sourceRun root (input m d) (d+1)=some (some 0) := by decide +kernel

theorem target_recursive_samples : ∀ m∈[1,2,4], ∀ d∈[0,1,2],
    ∃ k, targetRun root (input m d) k=some (some 0) := by
  intro m hm d hd
  exact (defined_iff machine parts read copy bodies checked.1 root checked.2 (input m d) (some 0)).mp
    ⟨d+1,source_recursive_samples m hm d hd⟩

theorem target_direct : targetRun root (input 1 1) 12=some (some 0) := by decide +kernel

/-- Prefix success commits before whole replay or the continuation.
Distributing that continuation over the prefix choice wrongly accepts aa. -/
theorem committed_replay_failure :
    sourceRun (.user 0 (.lit ['a'])) "aa".toList 2=some none ∧
    targetRun (.user 0 (.lit ['a'])) "aa".toList 12=some none ∧
    evV (source machine bodies) "aa".toList .callByValuePar
      (tblV (source machine bodies) "aa".toList .callByValuePar 2) [['a']]
      (.alt (.seq (.lit ['a','a']) (.seq (.param 0) (sourceExpr machine tail)))
        (.seq (.lit ['a']) (.seq (.param 0) (sourceExpr machine tail)))) 2=some (some 0) := by decide +kernel

/-- Here prefix and whole-value replay both succeed; the actual tail
fails. A naive retry of the shorter prefix would then wrongly succeed. -/
theorem committed_tail_failure :
    sourceRun (.user 2 (.lit ['a'])) "aaaX".toList 2=some none ∧
    targetRun (.user 2 (.lit ['a'])) "aaaX".toList 12=some none ∧
    evV (source machine bodies) "aaaX".toList .callByValuePar
      (tblV (source machine bodies) "aaaX".toList .callByValuePar 2) [['a']]
      (.alt (.seq (.lit ['a','a']) (.seq (.param 0) (.lit ['a'])))
        (.seq (.lit ['a']) (.seq (.param 0) (.lit ['a'])))) 4=some (some 1) := by decide +kernel

/-- A nullable continuation preserves undefinedness, after both prefix
and replay succeed. This is distinct from a nullable actual argument. -/
theorem looping_tail_source (k : Nat) : sourceRun (.user 3 (.lit ['a'])) "aaa".toList k=none := by
  have hr := source_rule machine bodies 3 (.resume head (.star (.lit [])) loopLinks) (by rfl)
  have hb (T : ClockFreezing.Table) : evV (source machine bodies) "aaa".toList .callByValuePar T [['a']]
      (rawBody machine (.resume head (.star (.lit [])) loopLinks)) 3=none := by
    have hh : evV (source machine bodies) "aaa".toList .callByValuePar T [['a']]
        (FinitePrefixControl.raw head) 3=some (some 1) := by rfl
    have hp : evV (source machine bodies) "aaa".toList .callByValuePar T [['a']]
        (.param 0) 1=some (some 0) := by rfl
    rw [rawBody,evV_seq_ok hh,evV_seq_ok hp]
    exact evStar_stuck rfl (Nat.lt_irrefl 0)
  change evV (source machine bodies) "aaa".toList .callByValuePar
    (tblV (source machine bodies) "aaa".toList .callByValuePar k) []
    (.call (offset machine+3) [.lit ['a']]) 3=none
  rw [evV_call_par hr rfl (by decide)]
  change valAt (tblV (source machine bodies) "aaa".toList .callByValuePar k (offset machine+3) [['a']]) 3=none
  cases k with
  | zero => rfl
  | succ k =>
    rw [valAt_tblV_succ hr _ (by decide : 3≤"aaa".toList.length)]
    exact hb _

theorem looping_tail_target (k : Nat) : targetRun (.user 3 (.lit ['a'])) "aaa".toList k=none :=
  (undefined_iff machine parts read copy bodies checked.1 (.user 3 (.lit ['a'])) (by decide) "aaa".toList).mp looping_tail_source k

/-- Missing the parent's restored copy, or shortening the child's whole
copy, leaves unconsumed input. Neither is accepted as a complete parse. -/
theorem short_copy_samples :
    sourceRun root "aaa:aaaa?".toList 3=some (some 6) ∧
    targetRun root "aaa:aaaa?".toList 12=some (some 6) ∧
    sourceRun root "aaa:aaa?a".toList 3=some (some 6) ∧
    targetRun root "aaa:aaa?a".toList 12=some (some 6) := by decide +kernel

theorem language : ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
    SObs (source machine bodies) .callByValuePar (sourceExpr machine root) x (some []) ↔
      SObs g .callByValueSeq start x (some []) :=
  language_translation machine parts read copy bodies checked.1 root checked.2

/-- Early-finishing queries and recursive resumption coexist as real
source users in the same grammar. -/
def early : Arg := .seq (.user 1 (.seq (.lit ['a']) (.seq (.star (.lit ['b'])) (.lit ['a']))))
  (.seq (.star (.lit ['b'])) (.lit ['a']))

theorem early_target : sourceRun early "abba".toList 2=some (some 0) ∧ targetRun early "abba".toList 12=some (some 0) := by decide +kernel

theorem early_language : ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
    SObs (source machine bodies) .callByValuePar (sourceExpr machine early) x (some []) ↔
      SObs g .callByValueSeq start x (some []) :=
  language_translation machine parts read copy bodies checked.1 early (by decide)

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

theorem invalid_resume : resumeCheck parts (.lit []) links ['a','a']=false ∧
    resumeCheck parts tail links ['a','a','a']=false := by decide +kernel

end Shallot.MacroPeg.CBV.RecursiveFinitePrefixExamples
