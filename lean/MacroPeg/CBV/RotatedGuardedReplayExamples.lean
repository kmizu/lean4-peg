import MacroPeg.CBV.UniversalCaptureProfiles

namespace Shallot.MacroPeg.CBV.RotatedGuardedReplayExamples
open RecursiveScannerProductCompiler
open UniversalCaptureProfiles
open RecursiveCaptureProfiles (scopeCheck)
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Two phases of a complete ab residual machine. -/
def machine : StatefulScanner.Machine 2 := ⟨fun q => if q=0 then [('a',1)] else [('b',0)]⟩
def residuals : ScannerReplayResidual.Labels 2 := fun q =>
  some (if q=0 then ['a','b'] else ['b','a'])
def entries : Entries 2 := fun i => if i=2 then .replay else .iterate 0 residuals
/-- The child extends the whole old value. An odd capture rotates ab to ba;
an even child rotates it back to ab. Returning restores the parent value. -/
def extend : Arg := .seq (.param 0) (.alt (.lit ['b']) (.lit ['a','b']))
def tail : Arg := .alt (.seq (.lit [':']) (.seq (.user 0 extend)
  (.seq (.lit ['?']) (.param 0)))) (.lit [])
def bodies : List Arg := [tail,.star (.lit []),.lit []]
def root : Arg := .user 0 (.lit ['a','b','a'])

theorem checked : UniversalCaptureProfiles.check machine entries bodies=true ∧ scopeCheck bodies root=true := by decide +kernel

theorem raw_rule : ruleAtM (source machine entries bodies).rules (offset machine)=
    some ⟨1,.seq (.seq (.star (.seq (.lit ['a','b']) (.andP (.param 0)))) (.param 0)) (sourceExpr machine tail)⟩ :=
  source_rule machine entries bodies 0 tail rfl

theorem actual_phases :
    DynamicScannerBinding.resume (CaptureTransitionProfile.profile (DynamicScannerCapture.observer machine) ['a','b','a']) (0 : Fin 2)=some 1 ∧
    DynamicScannerBinding.resume (CaptureTransitionProfile.profile (DynamicScannerCapture.observer machine) ['a','b','a','b']) (0 : Fin 2)=some 0 := by decide +kernel

def nextWord (w : List Char) := w++(if w.length%2=0 then ['a','b'] else ['b'])
def input (w : List Char) (extra : Nat) : Nat → List Char
  | 0 => (List.replicate extra ['a','b']).flatten++w
  | d+1 => (List.replicate extra ['a','b']).flatten++w++[':']++
      input (nextWord w) (extra+1) d++['?']++w

def sourceRun (e : Arg) (x : List Char) (k : Nat) :=
  evV (source machine entries bodies) x .callByValuePar (tblV (source machine entries bodies) x .callByValuePar k) [] (sourceExpr machine e) x.length

def targetRun (e : Arg) (x : List Char) (k : Nat) :=
  evV (target machine entries bodies) x .callByValueSeq (tblV (target machine entries bodies) x .callByValueSeq k) [] (plain machine bodies [] e) x.length

theorem recursive_source_samples : ∀ n∈[1,2,4], ∀ d∈[0,1,2],
    sourceRun root (input ['a','b','a'] n d) (d+1)=some (some 0) := by decide +kernel

theorem recursive_target_samples : ∀ n∈[1,2,4], ∀ d∈[0,1,2],
    ∃ k, targetRun root (input ['a','b','a'] n d) k=some (some 0) := by
  intro n hn d hd
  exact (defined_iff machine entries bodies checked.1 root checked.2 (input ['a','b','a'] n d) (some 0)).mp
    ⟨d+1,recursive_source_samples n hn d hd⟩

theorem target_direct : targetRun root (input ['a','b','a'] 2 1) 8=some (some 0) := by decide +kernel

/-- This second root captures nonperiodic values of unbounded length.
No residual path exists, so the source takes zero guarded iterations. -/
def nonperiodic : Arg := .user 0 (.seq (.lit ['a']) (.seq (.star (.lit ['b'])) (.lit ['a'])))
theorem zero_iteration_samples : ∀ n∈[2,3,5],
    let x := ['a']++List.replicate n 'b'++['a']
    sourceRun nonperiodic x 2=some (some 0) ∧ targetRun nonperiodic x 8=some (some 0) := by decide +kernel

/-- A whole recursive user call is itself the next actual argument, so
its consumed word is checked through a generated product row. -/
def nested : Arg := .user 2 root
theorem product_argument : sourceRun nested (input ['a','b','a'] 2 1) 4=some (some 0) ∧
    targetRun nested (input ['a','b','a'] 2 1) 8=some (some 0) := by decide +kernel

theorem language : ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
    SObs (source machine entries bodies) .callByValuePar (sourceExpr machine root) x (some []) ↔
      SObs g .callByValueSeq start x (some []) :=
  language_translation machine entries bodies checked.1 root checked.2

theorem nonperiodic_language : ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
    SObs (source machine entries bodies) .callByValuePar (sourceExpr machine nonperiodic) x (some []) ↔
      SObs g .callByValueSeq start x (some []) :=
  language_translation machine entries bodies checked.1 nonperiodic (by decide)

/-- Following the repeated header, failure cannot retry a shorter star. -/
theorem committed_failure : sourceRun (.seq root (.lit ['a','b'])) "abababa".toList 2=some none ∧
    targetRun (.seq root (.lit ['a','b'])) "abababa".toList 8=some none := by decide +kernel

/-- The old value is unchanged after the child's phase changes. -/
theorem parent_copy_required :
    sourceRun root "abababa:ababababab?ab".toList 3=some (some 14) ∧
    targetRun root "abababa:ababababab?ab".toList 8=some (some 14) := by decide +kernel

theorem empty_capture : sourceRun (.user 0 (.lit [])) "ababab".toList 2=some (some 0) ∧
    targetRun (.user 0 (.lit [])) "ababab".toList 8=some (some 0) := by decide +kernel

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

theorem looping_tail_source (k : Nat) : sourceRun (.user 1 (.lit ['a','b','a'])) "abababa".toList k=none := by
  have hr := source_rule machine entries bodies 1 (.star (.lit [])) (by rfl)
  have hb (T : ClockFreezing.Table) : evV (source machine entries bodies) "abababa".toList .callByValuePar T [['a','b','a']]
      (.seq (sourceHeader (entries 1)) (sourceExpr machine (.star (.lit [])))) 7=none := by
    have hh : evV (source machine entries bodies) "abababa".toList .callByValuePar T [['a','b','a']]
        (sourceHeader (entries 1)) 7=some (some 0) := by
      change evV (source machine entries bodies) "abababa".toList .callByValuePar T [['a','b','a']]
        (GuardedReplayIteration.header ['a','b']) 7=some (some 0)
      simp only [GuardedReplayIteration.header,GuardedReplayIteration.step,MExp.andP,evV]
      decide +kernel
    rw [evV_seq_ok hh]
    exact evStar_stuck rfl (Nat.lt_irrefl 0)
  change evV (source machine entries bodies) "abababa".toList .callByValuePar
    (tblV (source machine entries bodies) "abababa".toList .callByValuePar k) []
    (.call (offset machine+1) [.lit ['a','b','a']]) 7=none
  rw [evV_call_par hr rfl (by decide)]
  change valAt (tblV (source machine entries bodies) "abababa".toList .callByValuePar k (offset machine+1) [['a','b','a']]) 7=none
  cases k with
  | zero => rfl
  | succ k => rw [valAt_tblV_succ hr _ (by decide : 7≤"abababa".toList.length)]; exact hb _

theorem looping_tail_target (k : Nat) : targetRun (.user 1 (.lit ['a','b','a'])) "abababa".toList k=none :=
  (undefined_iff machine entries bodies checked.1 (.user 1 (.lit ['a','b','a'])) (by decide) "abababa".toList).mp looping_tail_source k

theorem incomplete_rejected : headerCheck (⟨fun _ => []⟩ : StatefulScanner.Machine 2) (.iterate 0 residuals)=false := by decide +kernel

theorem empty_step_rejected : headerCheck machine (.iterate 0 (fun _ => some []))=false := by decide +kernel

end Shallot.MacroPeg.CBV.RotatedGuardedReplayExamples
