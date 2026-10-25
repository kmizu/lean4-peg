import MacroPeg.CBV.AutomaticOriginControl

namespace Shallot.MacroPeg.CBV.AutomaticOriginControlExamples
open AutomaticOriginControl
open RecursiveScannerProductCompiler (Arg sourceExpr offset)
open PrefixCaptureQuery (Body plans)
open ScannerOriginControl (Part)
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def machine : StatefulScanner.Machine 1 := ⟨fun _ => [('a',0)]⟩
def residuals : ScannerReplayResidual.Labels 1 := fun _ => some ['a']
def continuation : Arg := .alt (.seq (.user 2 (.seq (.param 0) (.param 0))) (.param 0)) (.lit [])
def parts : List (Part 1) := [⟨.replay,.lit ['a'],true⟩,⟨.shift 0 residuals,.lit [],false⟩,⟨.replay,continuation,false⟩]
def link : PrefixCaptureQuery.Link := ⟨0,1⟩
def bodies : List Body := [.after false link,.after true link,.guard (.after false link) (.leaf 2)]
def argument : Arg := .seq (.lit ['a']) (.seq (.star (.lit ['b'])) (.lit ['a']))
def negative : Arg := .user 0 argument
def positive : Arg := .user 1 (.lit ['a','a','a'])
def root : Arg := .user 2 argument
def negativeRoot : Arg := .seq negative (.seq (.star (.lit ['b'])) (.lit ['a']))

theorem checked : prefixCheck machine parts bodies=true ∧
    ScannerOriginControl.scopeCheck (plans bodies) root=true ∧
    ScannerOriginControl.scopeCheck (plans bodies) negativeRoot=true ∧
    ScannerOriginControl.scopeCheck (plans bodies) positive=true := by decide +kernel

/-- These are raw source queries, before body normalization or generation. -/
theorem raw_rules :
    ruleAtM (PrefixCaptureQuery.source machine parts bodies).rules (offset machine+0)=
      some ⟨1,.seq (.lit ['a']) (.notP (.param 0))⟩ ∧
    ruleAtM (PrefixCaptureQuery.source machine parts bodies).rules (offset machine+1)=
      some ⟨1,.seq (.lit ['a']) (.andP (.param 0))⟩ := by constructor <;> rfl

def sourceRun (e : Arg) (x : List Char) (clock : Nat) :=
  evV (PrefixCaptureQuery.source machine parts bodies) x .callByValuePar
    (tblV (PrefixCaptureQuery.source machine parts bodies) x .callByValuePar clock) [] (sourceExpr machine e) x.length

def targetRun (e : Arg) (x : List Char) (clock : Nat) :=
  evV (ScannerOriginControl.target machine parts (plans bodies)) x .callByValueSeq
    (tblV (ScannerOriginControl.target machine parts (plans bodies)) x .callByValueSeq clock) []
    (ScannerOriginControl.targetExpr machine parts (plans bodies) e) x.length

/-- The complete abba capture is retained, but the raw negative query
consumes only a. The positive query requires the complete aaa copy. -/
theorem early_query :
    sourceRun negative "abba".toList 2=some (some 3) ∧
    sourceRun negativeRoot "abba".toList 2=some (some 0) ∧
    sourceRun positive "aaaa".toList 2=some (some 3) ∧
    sourceRun positive "aaa".toList 2=some none := by decide +kernel

theorem complete_capture :
    evV (PrefixCaptureQuery.source machine parts bodies) "abba".toList .callByValuePar
      (tblV (PrefixCaptureQuery.source machine parts bodies) "abba".toList .callByValuePar 2) []
      (sourceExpr machine argument) 4=some (some 0) ∧
    pre "abba".toList 4 0="abba".toList := by decide +kernel

/-- Concrete ordinary Seq executions, including finite query failure. -/
theorem target_direct :
    targetRun negative "abba".toList 8=some (some 3) ∧
    targetRun negativeRoot "abba".toList 8=some (some 0) ∧
    targetRun positive "aaaa".toList 8=some (some 3) ∧
    targetRun positive "aaa".toList 8=some none := by decide +kernel

def word (n : Nat) := ['a']++List.replicate n 'b'++['a']
def input (n copies : Nat) := (List.replicate copies (word n)).flatten

/-- The raw query is a guard in a body with real same-user recursive
recapture and parent-value restoration. Captures are outside the a-fragment
family, have input-dependent length, and double at each recursive entry. -/
theorem source_recursive_samples : ∀ n∈[1,2,4],
    sourceRun root (input n 4) 3=some (some 0) ∧ sourceRun root (input n 10) 4=some (some 0) := by decide +kernel

theorem target_recursive_samples : ∀ n∈[1,2,4],
    (∃ k, targetRun root (input n 4) k=some (some 0)) ∧
    (∃ k, targetRun root (input n 10) k=some (some 0)) := by
  intro n hn
  obtain ⟨h4,h10⟩ := source_recursive_samples n hn
  exact ⟨(prefix_defined_iff machine parts bodies checked.1 root checked.2.1 (input n 4) (some 0)).mp ⟨3,h4⟩,
    (prefix_defined_iff machine parts bodies checked.1 root checked.2.1 (input n 10) (some 0)).mp ⟨4,h10⟩⟩

theorem language : ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
    SObs (PrefixCaptureQuery.source machine parts bodies) .callByValuePar (sourceExpr machine root) x (some []) ↔
      SObs g .callByValueSeq start x (some []) :=
  prefix_language_translation machine parts bodies checked.1 root checked.2.1

theorem negative_language : ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
    SObs (PrefixCaptureQuery.source machine parts bodies) .callByValuePar (sourceExpr machine negativeRoot) x (some []) ↔
      SObs g .callByValueSeq start x (some []) :=
  prefix_language_translation machine parts bodies checked.1 negativeRoot checked.2.2.1

/-- A failed actual argument precedes the raw negative query, even though
that query could succeed at the caller origin. -/
theorem argument_failure :
    sourceRun (.user 0 (.lit ['a','b','b','a'])) "ab".toList 2=some none ∧
    targetRun (.user 0 (.lit ['a','b','b','a'])) "ab".toList 8=some none := by decide +kernel

def nullable : Arg := .user 0 (.star (.lit []))

theorem nullable_source (x : List Char) (clock : Nat) : sourceRun nullable x clock=none := by
  change evV (PrefixCaptureQuery.source machine parts bodies) x .callByValuePar
    (tblV (PrefixCaptureQuery.source machine parts bodies) x .callByValuePar clock) []
    (.call (offset machine+0) [sourceExpr machine (.star (.lit []))]) x.length=none
  rw [evV_call_par raw_rules.1 rfl (by decide)]
  have hloop : evV (PrefixCaptureQuery.source machine parts bodies) x .callByValuePar
      (tblV (PrefixCaptureQuery.source machine parts bodies) x .callByValuePar clock) []
      (sourceExpr machine (.star (.lit []))) x.length=none := by
    apply evStar_stuck (j:=x.length) _ (Nat.lt_irrefl _)
    simp [sourceExpr,evV,Shallot.stripPrefix?,length_sfx x (Nat.le_refl _)]
  simp only [evParArgs,hloop]

theorem nullable_target (x : List Char) (clock : Nat) : targetRun nullable x clock=none :=
  (prefix_undefined_iff machine parts bodies checked.1 nullable (by decide) x).mp (nullable_source x) clock

theorem invalid_source_checks :
    prefixCheck machine [({ entry := .replay,body := .param 0,closed := true } : Part 1)] [.leaf 0]=false ∧
    prefixCheck machine [({ entry := .scan 0,body := .lit [],closed := false } : Part 1)] [.leaf 0]=false := by
  decide +kernel

end Shallot.MacroPeg.CBV.AutomaticOriginControlExamples
