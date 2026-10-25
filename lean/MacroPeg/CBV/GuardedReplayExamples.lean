import MacroPeg.CBV.GuardedReplayCompiler

namespace Shallot.MacroPeg.CBV.GuardedReplayExamples
open GuardedReplayCompiler
open RecursiveScannerProductCompiler (Arg sourceExpr offset)
open ScannerOriginControl (Part)
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def machine : StatefulScanner.Machine 1 := ⟨fun _ => [('a',0)]⟩
def residuals : ScannerReplayResidual.Labels 1 := fun _ => some ['a']
def tail : Arg := .alt (.seq (.lit [':']) (.seq (.user 0 (.seq (.param 0) (.param 0)))
  (.seq (.lit ['?']) (.param 0)))) (.lit [])
def parts : List (Part 1) := [⟨.shift 0 residuals,.lit [],false⟩,
  ⟨.shift 0 residuals,.seq (.star (.lit ['a'])) tail,false⟩,⟨.replay,tail,false⟩,
  ⟨.replay,.lit [],true⟩,⟨.replay,.lit ['a'],true⟩,⟨.replay,.lit [],false⟩,
  ⟨.shift 0 residuals,.seq (.star (.lit ['a'])) (.star (.lit [])),false⟩,⟨.replay,.star (.lit []),false⟩]
def read (w : List Char) := 3+w.length
def copy (w : List Char) := if w=[] then 5 else 0
def bodies : List Body := [.repeated 'a' tail 0 1 2,
  .control (.finish (.seq (.lit ['a']) (.query false))),.repeated 'a' (.star (.lit [])) 0 6 7]
def ps := plans read copy bodies
def root : Arg := .user 0 (.lit ['a'])

theorem checked : check machine parts read copy bodies=true ∧ ScannerOriginControl.scopeCheck ps root=true := by decide +kernel

/-- This is a raw unbounded prefix with a retained-value query in every
iteration. It precedes whole replay and actual recursive recapture. -/
theorem raw_rule : ruleAtM (source machine bodies).rules (offset machine+0)=
    some ⟨1,.seq (.seq (.star (.seq (.lit ['a']) (.andP (.param 0)))) (.param 0)) (sourceExpr machine tail)⟩ :=
  source_rule machine bodies 0 (.repeated 'a' tail 0 1 2) rfl

def input (m extra : Nat) : Nat → List Char
  | 0 => List.replicate (m+extra) 'a'
  | d+1 => List.replicate (m+extra) 'a'++[':']++input (2*m) (extra+1) d++['?']++List.replicate m 'a'

def sourceRun (e : Arg) (x : List Char) (k : Nat) :=
  evV (source machine bodies) x .callByValuePar (tblV (source machine bodies) x .callByValuePar k) [] (sourceExpr machine e) x.length

def targetRun (e : Arg) (x : List Char) (k : Nat) :=
  evV (ScannerOriginControl.target machine parts ps) x .callByValueSeq
    (tblV (ScannerOriginControl.target machine parts ps) x .callByValueSeq k) []
    (ScannerOriginControl.targetExpr machine parts ps e) x.length

/-- Prefix iteration count and recursion depth vary independently in one
fixed grammar/root. Children double the old value and parents recover it. -/
theorem recursive_source_samples : ∀ n∈[1,2,4], ∀ d∈[0,1,2],
    sourceRun root (input 1 n d) (d+1)=some (some 0) := by decide +kernel

theorem recursive_target_samples : ∀ n∈[1,2,4], ∀ d∈[0,1,2],
    ∃ k, targetRun root (input 1 n d) k=some (some 0) := by
  intro n hn d hd
  exact (defined_iff machine parts read copy bodies checked.1 root checked.2 (input 1 n d) (some 0)).mp
    ⟨d+1,recursive_source_samples n hn d hd⟩

theorem target_direct : targetRun root (input 1 2 1) 12=some (some 0) := by decide +kernel

/-- A non-unary capture makes the first guarded iteration fail. Keeping
zero iterations and replaying the actual whole capture preserves success. -/
def nonUnary : Arg := .user 0 (.seq (.lit ['a']) (.seq (.star (.lit ['b'])) (.lit ['a'])))

theorem non_unary_samples : ∀ n∈[1,2,4],
    let x := ['a']++List.replicate n 'b'++['a']
    sourceRun nonUnary x 2=some (some 0) ∧ targetRun nonUnary x 12=some (some 0) := by decide +kernel

theorem language : ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
    SObs (source machine bodies) .callByValuePar (sourceExpr machine root) x (some []) ↔
      SObs g .callByValueSeq start x (some []) :=
  language_translation machine parts read copy bodies checked.1 root checked.2

theorem non_unary_language : ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
    SObs (source machine bodies) .callByValuePar (sourceExpr machine nonUnary) x (some []) ↔
      SObs g .callByValueSeq start x (some []) :=
  language_translation machine parts read copy bodies checked.1 nonUnary (by decide)

/-- Equality on arbitrary table environments would be false. b cannot be
captured at the origin of aba, and exactly that unreachable row disagrees. -/
theorem unreachable_environment :
    ¬CaptureOriginRewrite.Captured "aba".toList [['b']] 3 ∧
    evV (source machine bodies) "aba".toList .callByValuePar
      (tblV (source machine bodies) "aba".toList .callByValuePar 2) [['b']]
      (GuardedReplayIteration.header ['a']) 3=some (some 1) ∧
    evV (source machine bodies) "aba".toList .callByValuePar
      (tblV (source machine bodies) "aba".toList .callByValuePar 2) [['b']]
      (GuardedReplayIteration.normalized 'a' (.lit [])) 3=some (some 0) := by
  unfold CaptureOriginRewrite.Captured
  decide +kernel

/-- The generic iteration bridge also handles a noncommuting multi-byte
shift. Its residual is ba; naively scanning ab from the capture endpoint
would stop immediately. This tests the lemma, not a broader compiler claim. -/
theorem noncommuting_rotation :
    ['a','b']++['a','b','a']=['a','b','a']++['b','a'] ∧
    evV (source machine bodies) "ababababa".toList .callByValuePar
      (tblV (source machine bodies) "ababababa".toList .callByValuePar 2) [['a','b','a']]
      (GuardedReplayIteration.header ['a','b']) 9=some (some 0) ∧
    evV (source machine bodies) "ababababa".toList .callByValuePar
      (tblV (source machine bodies) "ababababa".toList .callByValuePar 2) [['a','b','a']]
      (.star (.lit ['b','a'])) 6=some (some 0) ∧
    evV (source machine bodies) "ababababa".toList .callByValuePar
      (tblV (source machine bodies) "ababababa".toList .callByValuePar 2) [['a','b','a']]
      (.star (.lit ['a','b'])) 6=some (some 6) := by decide +kernel

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

theorem invalid_tail : RecursiveFinitePrefix.resumeCheck parts (.lit []) (fun _ => 1) ['a']=false := by decide +kernel

/-- A successful unbounded prefix and replay do not conceal a stuck tail. -/
theorem looping_tail_source (k : Nat) : sourceRun (.user 2 (.lit ['a'])) "aaa".toList k=none := by
  have hr := source_rule machine bodies 2 (.repeated 'a' (.star (.lit [])) 0 6 7) (by rfl)
  have hb (T : ClockFreezing.Table) : evV (source machine bodies) "aaa".toList .callByValuePar T [['a']]
      (rawBody machine (.repeated 'a' (.star (.lit [])) 0 6 7)) 3=none := by
    have hh : evV (source machine bodies) "aaa".toList .callByValuePar T [['a']]
        (GuardedReplayIteration.header ['a']) 3=some (some 0) := by
      simp only [GuardedReplayIteration.header,GuardedReplayIteration.step,MExp.andP,evV]
      decide +kernel
    rw [rawBody,evV_seq_ok hh]
    exact evStar_stuck rfl (Nat.lt_irrefl 0)
  change evV (source machine bodies) "aaa".toList .callByValuePar
    (tblV (source machine bodies) "aaa".toList .callByValuePar k) []
    (.call (offset machine+2) [.lit ['a']]) 3=none
  rw [evV_call_par hr rfl (by decide)]
  change valAt (tblV (source machine bodies) "aaa".toList .callByValuePar k (offset machine+2) [['a']]) 3=none
  cases k with
  | zero => rfl
  | succ k => rw [valAt_tblV_succ hr _ (by decide : 3≤"aaa".toList.length)]; exact hb _

theorem looping_tail_target (k : Nat) : targetRun (.user 2 (.lit ['a'])) "aaa".toList k=none :=
  (undefined_iff machine parts read copy bodies checked.1 (.user 2 (.lit ['a'])) (by decide) "aaa".toList).mp looping_tail_source k

/-- The generic word-rotation lemma retains zero-consumption divergence;
the character-loop compiler itself deliberately uses nonempty steps. -/
theorem zero_step_source (x : List Char) (k : Nat) :
    evV (source machine bodies) x .callByValuePar (tblV (source machine bodies) x .callByValuePar k) [[]]
      (GuardedReplayIteration.header []) x.length=none := by
  have hs : evV (source machine bodies) x .callByValuePar (tblV (source machine bodies) x .callByValuePar k) [[]]
      (GuardedReplayIteration.step []) x.length=some (some x.length) := by
    simp [GuardedReplayIteration.step,MExp.andP,evV,Shallot.stripPrefix?,length_sfx x (Nat.le_refl _)]
  exact evV_seq_none (show evV (source machine bodies) x .callByValuePar
    (tblV (source machine bodies) x .callByValuePar k) [[]] (.star (GuardedReplayIteration.step [])) x.length=none from
      evStar_stuck hs (Nat.lt_irrefl _))

theorem zero_step_residual (x : List Char) (k : Nat) :
    evV (source machine bodies) x .callByValuePar (tblV (source machine bodies) x .callByValuePar k) [[]]
      (.star (.lit [])) x.length=none := by
  have hh := GuardedReplayIteration.rotate (source machine bodies) x .callByValuePar
    (tblV (source machine bodies) x .callByValuePar k) [] [] [] rfl x.length x.length (Nat.le_refl _)
    (by simp [evV,Shallot.stripPrefix?,length_sfx x (Nat.le_refl _)])
  exact hh.symm.trans (zero_step_source x k)

end Shallot.MacroPeg.CBV.GuardedReplayExamples
