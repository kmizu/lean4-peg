import MacroPeg.CBV.UniversalCaptureProfiles
import MacroPeg.CBV.RotatedGuardedReplayExamples

namespace Shallot.MacroPeg.CBV.GuardedReplayControlExamples
open RecursiveScannerProductCompiler
open UniversalCaptureProfiles
open RecursiveCaptureProfiles (scopeCheck)
set_option maxHeartbeats 0
set_option maxRecDepth 100000

abbrev machine := RotatedGuardedReplayExamples.machine
abbrev short : GuardedReplayControl.Expr 2 := .shift 0 RotatedGuardedReplayExamples.residuals
def longLabels : ScannerReplayResidual.Labels 2 := fun q =>
  some (if q=0 then ['a','b','a','b'] else ['b','a','b','a'])
def long : GuardedReplayControl.Expr 2 := .shift 0 longLabels
/-- Each iteration chooses a long step or a guarded short fallback. -/
def control : GuardedReplayControl.Expr 2 := .star (.alt long (.seq (.notP long) short))
/-- Failure of the final short step rolls the whole outer iteration back;
it cannot retry a shorter successful inner repetition. -/
def nestedControl : GuardedReplayControl.Expr 2 := .star (.seq (.star long) short)
def nullableControl : GuardedReplayControl.Expr 2 := .star (.notP long)
def entries : Entries 2 := fun i =>
  if i=2 then .replay else if i=3 then .aligned nestedControl else
  if i=4 then .aligned nullableControl else .aligned control
def bodies : List Arg := [RotatedGuardedReplayExamples.tail,.star (.lit []),.lit [],.lit [],.lit []]
def root : Arg := .user 0 (.lit ['a','b','a'])

theorem checked : UniversalCaptureProfiles.check machine entries bodies=true ∧ scopeCheck bodies root=true := by decide +kernel

theorem raw_rule : ruleAtM (source machine entries bodies).rules (offset machine)=
    some ⟨1,.seq (GuardedReplayControl.header control) (sourceExpr machine RotatedGuardedReplayExamples.tail)⟩ :=
  source_rule machine entries bodies 0 RotatedGuardedReplayExamples.tail rfl

def sourceRun (e : Arg) (x : List Char) (k : Nat) :=
  evV (source machine entries bodies) x .callByValuePar (tblV (source machine entries bodies) x .callByValuePar k) [] (sourceExpr machine e) x.length

def targetRun (e : Arg) (x : List Char) (k : Nat) :=
  evV (target machine entries bodies) x .callByValueSeq (tblV (target machine entries bodies) x .callByValueSeq k) [] (plain machine bodies [] e) x.length

theorem recursive_source_samples : ∀ n∈[1,2,3,5], ∀ d∈[0,1,2],
    sourceRun root (RotatedGuardedReplayExamples.input ['a','b','a'] n d) (d+1)=some (some 0) := by decide +kernel

theorem recursive_target_samples : ∀ n∈[1,2,3,5], ∀ d∈[0,1,2],
    ∃ k, targetRun root (RotatedGuardedReplayExamples.input ['a','b','a'] n d) k=some (some 0) := by
  intro n hn d hd
  exact (defined_iff machine entries bodies checked.1 root checked.2 (RotatedGuardedReplayExamples.input ['a','b','a'] n d) (some 0)).mp
    ⟨d+1,recursive_source_samples n hn d hd⟩

theorem target_direct : targetRun root (RotatedGuardedReplayExamples.input ['a','b','a'] 3 1) 8=some (some 0) := by decide +kernel

theorem fallback_after_query_failure : sourceRun root "ababa".toList 2=some (some 0) ∧
    targetRun root "ababa".toList 8=some (some 0) := by decide +kernel

/-- Grouping literals before their retained-value query is incorrect:
the first literal can succeed while its whole guarded step fails. -/
theorem naive_grouping_changes_consumption :
    evV ⟨[]⟩ "ababa".toList .callByValuePar (fun _ _ => []) [['a','b','a']]
      (.seq (.star (.seq (.alt (.lit ['a','b','a','b']) (.lit ['a','b'])) (.andP (.param 0)))) (.param 0)) 5=some (some 2) := by decide +kernel

theorem nested_repetition_commitment :
    sourceRun (.user 3 (.lit ['a','b','a'])) (RotatedGuardedReplayExamples.input ['a','b','a'] 3 0) 2=some (some 0) ∧
    targetRun (.user 3 (.lit ['a','b','a'])) (RotatedGuardedReplayExamples.input ['a','b','a'] 3 0) 8=some (some 0) ∧
    sourceRun (.user 3 (.lit ['a','b','a'])) (RotatedGuardedReplayExamples.input ['a','b','a'] 2 0) 2=some (some 4) ∧
    targetRun (.user 3 (.lit ['a','b','a'])) (RotatedGuardedReplayExamples.input ['a','b','a'] 2 0) 8=some (some 4) := by decide +kernel

def productRoot : Arg := .user 2 root
theorem product_argument : sourceRun productRoot (RotatedGuardedReplayExamples.input ['a','b','a'] 3 1) 4=some (some 0) ∧
    targetRun productRoot (RotatedGuardedReplayExamples.input ['a','b','a'] 3 1) 8=some (some 0) := by decide +kernel

theorem language : ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
    SObs (source machine entries bodies) .callByValuePar (sourceExpr machine root) x (some []) ↔
      SObs g .callByValueSeq start x (some []) :=
  language_translation machine entries bodies checked.1 root checked.2

def nonperiodic : Arg := RotatedGuardedReplayExamples.nonperiodic
theorem nonperiodic_samples : ∀ n∈[2,3,5],
    let x := ['a']++List.replicate n 'b'++['a']
    sourceRun nonperiodic x 2=some (some 0) ∧ targetRun nonperiodic x 8=some (some 0) := by decide +kernel

def nullable : Arg := .user 0 (.star (.lit []))
theorem nullable_source (x : List Char) (clock : Nat) : sourceRun nullable x clock=none := by
  change evV (source machine entries bodies) x .callByValuePar
    (tblV (source machine entries bodies) x .callByValuePar clock) []
    (.call (offset machine) [sourceExpr machine (.star (.lit []))]) x.length=none
  rw [evV_call_par raw_rule rfl (by decide)]
  have hloop : evV (source machine entries bodies) x .callByValuePar
      (tblV (source machine entries bodies) x .callByValuePar clock) []
      (sourceExpr machine (.star (.lit []))) x.length=none := by
    apply evStar_stuck (j:=x.length) _ (Nat.lt_irrefl _)
    simp [sourceExpr,evV,Shallot.stripPrefix?,length_sfx x (Nat.le_refl _)]
  simp only [evParArgs,hloop]

theorem nullable_target (x : List Char) (clock : Nat) : targetRun nullable x clock=none :=
  (undefined_iff machine entries bodies checked.1 nullable (by decide) x).mp (nullable_source x) clock

theorem nullable_control_source (k : Nat) : sourceRun (.user 4 (.lit ['a','b','a'])) "aba".toList k=none := by
  have hr := source_rule machine entries bodies 4 (.lit []) (by rfl)
  have hb (T : ClockFreezing.Table) : evV (source machine entries bodies) "aba".toList .callByValuePar T [['a','b','a']]
      (.seq (sourceHeader (entries 4)) (sourceExpr machine (.lit []))) 3=none := by
    have he := GuardedReplayControl.header_independent (source machine entries bodies) ⟨[]⟩ "aba".toList
      .callByValuePar .callByValuePar T (fun _ _ => []) [['a','b','a']] nullableControl 3
    have hn : evV ⟨[]⟩ "aba".toList .callByValuePar (fun _ _ => []) [['a','b','a']]
        (GuardedReplayControl.header nullableControl) 3=none := by decide +kernel
    exact evV_seq_none (he.trans hn)
  change evV (source machine entries bodies) "aba".toList .callByValuePar
    (tblV (source machine entries bodies) "aba".toList .callByValuePar k) []
    (.call (offset machine+4) [.lit ['a','b','a']]) 3=none
  rw [evV_call_par hr rfl (by decide)]
  change valAt (tblV (source machine entries bodies) "aba".toList .callByValuePar k (offset machine+4) [['a','b','a']]) 3=none
  cases k with
  | zero => rfl
  | succ k => rw [valAt_tblV_succ hr _ (by decide : 3≤"aba".toList.length)]; exact hb _

theorem nullable_control_target (k : Nat) : targetRun (.user 4 (.lit ['a','b','a'])) "aba".toList k=none :=
  (undefined_iff machine entries bodies checked.1 (.user 4 (.lit ['a','b','a'])) (by decide) "aba".toList).mp nullable_control_source k

theorem nullable_tail_source (k : Nat) : sourceRun (.user 1 (.lit ['a','b','a'])) "ababa".toList k=none := by
  have hr := source_rule machine entries bodies 1 (.star (.lit [])) (by rfl)
  have hb (T : ClockFreezing.Table) : evV (source machine entries bodies) "ababa".toList .callByValuePar T [['a','b','a']]
      (.seq (sourceHeader (entries 1)) (sourceExpr machine (.star (.lit [])))) 5=none := by
    have he := GuardedReplayControl.header_independent (source machine entries bodies) ⟨[]⟩ "ababa".toList
      .callByValuePar .callByValuePar T (fun _ _ => []) [['a','b','a']] control 5
    have hn : evV ⟨[]⟩ "ababa".toList .callByValuePar (fun _ _ => []) [['a','b','a']]
        (GuardedReplayControl.header control) 5=some (some 0) := by decide +kernel
    change evV (source machine entries bodies) "ababa".toList .callByValuePar T [['a','b','a']]
      (.seq (GuardedReplayControl.header control) (.star (.lit []))) 5=none
    rw [evV_seq_ok (he.trans hn)]
    exact evStar_stuck rfl (Nat.lt_irrefl 0)
  change evV (source machine entries bodies) "ababa".toList .callByValuePar
    (tblV (source machine entries bodies) "ababa".toList .callByValuePar k) []
    (.call (offset machine+1) [.lit ['a','b','a']]) 5=none
  rw [evV_call_par hr rfl (by decide)]
  change valAt (tblV (source machine entries bodies) "ababa".toList .callByValuePar k (offset machine+1) [['a','b','a']]) 5=none
  cases k with
  | zero => rfl
  | succ k => rw [valAt_tblV_succ hr _ (by decide : 5≤"ababa".toList.length)]; exact hb _

theorem nullable_tail_target (k : Nat) : targetRun (.user 1 (.lit ['a','b','a'])) "ababa".toList k=none :=
  (undefined_iff machine entries bodies checked.1 (.user 1 (.lit ['a','b','a'])) (by decide) "ababa".toList).mp nullable_tail_source k

theorem invalid_control_rejected : GuardedReplayControl.check machine
    (.star (.alt long (.notP (.shift 0 (fun _ => some [])))))=false := by decide +kernel

/- Different periods can occur within one retained-value loop. This
larger machine is certified without evaluating its entire generated table. -/
namespace DifferentPeriods

def machine : StatefulScanner.Machine 4 := ⟨fun q =>
  if q=0 then [('a',1)] else if q=1 then [('b',0)] else
  if q=2 then [('a',3)] else [('c',2)]⟩
def abLabels : ScannerReplayResidual.Labels 4 := fun q =>
  if q=0 then some ['a','b'] else if q=1 then some ['b','a'] else none
def acLabels : ScannerReplayResidual.Labels 4 := fun q =>
  if q=2 then some ['a','c'] else if q=3 then some ['c','a'] else none
def control : GuardedReplayControl.Expr 4 := .star (.alt (.shift 0 abLabels) (.shift 2 acLabels))
def entries : Entries 4 := fun _ => .aligned control
def bodies : List Arg := [.lit []]
def root : Arg := .user 0 (.lit ['a'])
theorem checked : UniversalCaptureProfiles.check machine entries bodies=true ∧ scopeCheck bodies root=true := by decide +kernel

def word (steps : List Bool) := (steps.flatMap (fun b => if b then ['a','b'] else ['a','c']))++['a']
theorem mixed_steps : ∀ steps∈[[true,false,true],[false,true,false,true],[true,false,false,true,false]],
    evV (source machine entries bodies) (word steps) .callByValuePar
      (tblV (source machine entries bodies) (word steps) .callByValuePar 1) []
      (sourceExpr machine root) (word steps).length=some (some 0) := by decide +kernel

theorem target_mixed_steps : ∀ steps∈[[true,false,true],[false,true,false,true],[true,false,false,true,false]],
    ∃ k, evV (target machine entries bodies) (word steps) .callByValueSeq
      (tblV (target machine entries bodies) (word steps) .callByValueSeq k) []
      (plain machine bodies [] root) (word steps).length=some (some 0) := by
  intro steps hs
  exact (defined_iff machine entries bodies checked.1 root checked.2 (word steps) (some 0)).mp
    ⟨1,mixed_steps steps hs⟩

theorem language : ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
    SObs (source machine entries bodies) .callByValuePar (sourceExpr machine root) x (some []) ↔
      SObs g .callByValueSeq start x (some []) :=
  language_translation machine entries bodies checked.1 root checked.2

end DifferentPeriods

end Shallot.MacroPeg.CBV.GuardedReplayControlExamples
