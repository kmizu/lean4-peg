import MacroPeg.CBV.AutomaticFinitePrefix

namespace Shallot.MacroPeg.CBV.AutomaticFinitePrefixExamples
open AutomaticFinitePrefix
open FinitePrefixControl (Prefix outputs)
open RecursiveScannerProductCompiler (Arg sourceExpr plain)
open RecursiveCaptureProfiles (scopeCheck)
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Only raw source syntax is supplied: no machine, residuals, or indices. -/
def scripts : List Control := [.star (.finite (.seq (.lit ['a']) (.notP (.query false)))),
  .retain,.star (.finite (.query true))]
def copyBody : Arg := .alt (.seq (.user 1 (.seq (.param 0) (.param 0))) (.param 0)) (.lit [])
def bodies : List Arg := [.lit [],copyBody,.lit []]
def root : Arg := .user 0 (.user 1 (.lit ['a']))
def letters := AutomaticFinitePrefix.alphabet scripts bodies root
def pool := AutomaticFinitePrefix.words scripts
def M := FinitePrefixMachines.machine letters pool

theorem scoped_ok : bodies.all (scopeCheck bodies)=true ∧ scopeCheck bodies root=true := by decide +kernel

theorem generated_shape : letters=['a'] ∧ FinitePrefixMachines.Size pool=3 := by decide +kernel

theorem checked : check letters scripts bodies=true := automatic_check scripts bodies root scoped_ok.1

theorem generated_certificates : GuardedFinitePrefix.check M (FinitePrefixMachines.read letters pool)
    (FinitePrefixMachines.finish pool) (controls letters scripts) bodies letters=true :=
  certificates letters scripts bodies checked

theorem raw_rule : ruleAtM (source letters scripts bodies).rules (RecursiveScannerProductCompiler.offset M)=
    some ⟨1,.seq (.seq (.star (.seq (.seq (.lit ['a']) (.notP (.notP (.param 0))))
      (.andP (.param 0)))) (.param 0)) (.lit [])⟩ := by
  simpa [M,pool,scriptAt,scripts,rawControl,FinitePrefixControl.raw,PrefixCaptureQuery.query,sourceExpr]
    using source_rule letters scripts bodies 0 (.lit []) rfl

def sourceRun (e : Arg) (x : List Char) (k : Nat) :=
  evV (source letters scripts bodies) x .callByValuePar
    (tblV (source letters scripts bodies) x .callByValuePar k) [] (sourceExpr M e) x.length

def targetRun (e : Arg) (x : List Char) (k : Nat) :=
  evV (compiled letters scripts bodies) x .callByValueSeq
    (tblV (compiled letters scripts bodies) x .callByValueSeq k) [] (plain M bodies [] e) x.length

theorem source_samples : ∀ n∈[1,2,3,4,5,6,10,11,12], sourceRun root (List.replicate n 'a') 4=some (some 0) := by decide +kernel

theorem target_samples : ∀ n∈[1,2,3,4,5,6,10,11,12], ∃ k, targetRun root (List.replicate n 'a') k=some (some 0) := by
  intro n hn
  exact (defined_iff letters scripts bodies checked root scoped_ok.2 (root_literal_checked scripts bodies root)
    (List.replicate n 'a') (some 0)).mp ⟨4,source_samples n hn⟩

theorem target_direct : targetRun root "aaaa".toList 8=some (some 0) := by decide +kernel

def productRoot : Arg := .user 1 (.user 0 (.lit ['a']))
theorem product_direct : sourceRun productRoot "aaaa".toList 2=some (some 0) ∧
    targetRun productRoot "aaaa".toList 3=some (some 0) := by decide +kernel

theorem empty_capture : sourceRun (.user 0 (.lit [])) "aaaa".toList 1=some (some 0) ∧
    targetRun (.user 0 (.lit [])) "aaaa".toList 2=some (some 0) := by decide +kernel

theorem outside_alphabet : sourceRun root "aab".toList 4=some (some 1) ∧
    ∃ k, targetRun root "aab".toList k=some (some 1) := by
  have hs : sourceRun root "aab".toList 4=some (some 1) := by decide +kernel
  exact ⟨hs,(defined_iff letters scripts bodies checked root scoped_ok.2
    (root_literal_checked scripts bodies root) "aab".toList (some 1)).mp ⟨4,hs⟩⟩

theorem language : ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
    SObs (source letters scripts bodies) .callByValuePar (sourceExpr M root) x (some []) ↔
      SObs g .callByValueSeq start x (some []) :=
  automatic_language_translation scripts bodies root scoped_ok.1 scoped_ok.2

theorem nullable_source (k : Nat) : sourceRun (.user 2 (.lit ['a'])) "aa".toList k=none := by
  have hr : ruleAtM (source letters scripts bodies).rules (RecursiveScannerProductCompiler.offset M+2)=
      some ⟨1,.seq (.seq (rawControl (scriptAt scripts 2)) (.param 0)) (.lit [])⟩ := by
    simpa only [M,pool,sourceExpr] using source_rule letters scripts bodies 2 (.lit []) (by rfl)
  have hb (T : ClockFreezing.Table) : evV (source letters scripts bodies) "aa".toList .callByValuePar T [['a']]
      (.seq (.seq (rawControl (scriptAt scripts 2)) (.param 0)) (.lit [])) 2=none := by
    have hs : evV (source letters scripts bodies) "aa".toList .callByValuePar T [['a']]
        (.star (.seq (.andP (.param 0)) (.andP (.param 0)))) 2=none := by
      rw [evV_star,evStar_stuck (show evV (source letters scripts bodies) "aa".toList .callByValuePar T [['a']]
        (.seq (.andP (.param 0)) (.andP (.param 0))) 2=some (some 2) from by
          simp only [MExp.andP,evV]; decide +kernel) (by omega)]
    exact evV_seq_none (evV_seq_none hs)
  change evV (source letters scripts bodies) "aa".toList .callByValuePar
    (tblV (source letters scripts bodies) "aa".toList .callByValuePar k) []
    (.call (RecursiveScannerProductCompiler.offset M+2) [.lit ['a']]) 2=none
  rw [evV_call_par hr rfl (by decide)]
  change valAt (tblV (source letters scripts bodies) "aa".toList .callByValuePar k
    (RecursiveScannerProductCompiler.offset M+2) [['a']]) 2=none
  cases k with
  | zero => rfl
  | succ k => rw [valAt_tblV_succ hr _ (by decide : 2≤"aa".toList.length)]; exact hb _

theorem nullable_target : ∀ k, targetRun (.user 2 (.lit ['a'])) "aa".toList k=none :=
  (undefined_iff letters scripts bodies checked (.user 2 (.lit ['a']))
    (by decide +kernel) (by decide +kernel) "aa".toList).mp nullable_source

theorem hidden_probe_collected : ['a','b']∈AutomaticFinitePrefix.words [.finite (.notP (.lit ['a','b']))] ∧
    outputs (.notP (.lit ['a','b']))=[[]] := by decide +kernel

theorem sequence_offsets_collected :
    ['a','c']∈support (.seq (.alt (.lit ['a']) (.lit ['b'])) (.lit ['c'])) [] ∧
    ['b','c']∈support (.seq (.alt (.lit ['a']) (.lit ['b'])) (.lit ['c'])) [] := by decide +kernel

theorem missing_alphabet_rejected : check ['a'] scripts [.lit ['b']]=false := by decide +kernel

theorem missing_user_rejected :
    check (AutomaticFinitePrefix.alphabet scripts [.user 9 (.lit [])] root) scripts [.user 9 (.lit [])]=false := by decide +kernel

namespace Binary

def scripts : List Control := [.star (.finite (.seq (.lit ['a','b']) (.query true))),.retain]
def bodies : List Arg := [.lit [],copyBody]
def root : Arg := .user 0 (.user 1 (.lit ['a','b']))
def letters := AutomaticFinitePrefix.alphabet scripts bodies root
def pool := AutomaticFinitePrefix.words scripts
def M := FinitePrefixMachines.machine letters pool

theorem scoped_ok : bodies.all (scopeCheck bodies)=true ∧ scopeCheck bodies root=true := by decide +kernel

theorem shape : letters=['a','b'] ∧ FinitePrefixMachines.Size pool=5 := by decide +kernel

theorem checked : check letters scripts bodies=true := automatic_check scripts bodies root scoped_ok.1

/-- A larger generated observer need not enumerate its profiles to prove
the grammar check: the general certificate theorem derives it. -/
theorem generated_certificates : GuardedFinitePrefix.check M (FinitePrefixMachines.read letters pool)
    (FinitePrefixMachines.finish pool) (controls letters scripts) bodies letters=true :=
  certificates letters scripts bodies checked

def sourceRun (e : Arg) (x : List Char) (k : Nat) :=
  evV (source letters scripts bodies) x .callByValuePar
    (tblV (source letters scripts bodies) x .callByValuePar k) [] (sourceExpr M e) x.length

theorem source_samples : ∀ n∈[1,2,3,4,5,6,10,11,12],
    sourceRun root (BlockCapture.copies ['a','b'] n) 4=some (some 0) := by decide +kernel

theorem target_samples : ∀ n∈[1,2,3,4,5,6,10,11,12],
    ∃ k, evV (compiled letters scripts bodies) (BlockCapture.copies ['a','b'] n) .callByValueSeq
      (tblV (compiled letters scripts bodies) (BlockCapture.copies ['a','b'] n) .callByValueSeq k)
      [] (plain M bodies [] root) (BlockCapture.copies ['a','b'] n).length=some (some 0) := by
  intro n hn
  exact (defined_iff letters scripts bodies checked root scoped_ok.2 (root_literal_checked scripts bodies root)
    (BlockCapture.copies ['a','b'] n) (some 0)).mp ⟨4,source_samples n hn⟩

theorem phase_change : StatefulScanner.advance M (FinitePrefixMachines.index pool (.rotating ['a','b'])) "aba".toList=
    some (FinitePrefixMachines.index pool (.rotating ['b','a'])) ∧
    FinitePrefixMachines.residuals pool (FinitePrefixMachines.index pool (.rotating ['b','a']))=some ['b','a'] := by decide +kernel

theorem noncommuting : ['a','b']++"aba".toList="aba".toList++['b','a'] ∧
    ['a','b']++"aba".toList≠"aba".toList++['a','b'] := by decide +kernel

/-- The literal finishes inside a longer capture; its query succeeds at
EOF using the generated state, while an unchanged endpoint query fails. -/
theorem literal_inside_capture :
    evV ⟨[]⟩ "ababa".toList .callByValueSeq (fun _ _ => []) [['a','b','a','b','a']]
      (LiteralPrefixObservation.query (CaptureTransitionProfile.profile (DynamicScannerCapture.observer M) "ababa".toList)
        (FinitePrefixMachines.index pool (.literal ['a','b'])) (FinitePrefixMachines.literals pool)) 0=some (some 0) ∧
    evV ⟨[]⟩ "ababa".toList .callByValueSeq (fun _ _ => []) [] (.andP (.lit ['a','b'])) 0=some none := by decide +kernel

theorem frontier_without_total :
    GuardedReplayControl.captureCheck (CaptureTransitionProfile.profile (DynamicScannerCapture.observer M) "bba".toList)
      (FinitePrefixMachines.read letters pool ['a','b'])=true ∧
    ¬TotalCaptureSafety.Total M "bba".toList := by
  refine ⟨by decide +kernel,?_⟩
  intro h
  exact h (FinitePrefixMachines.index pool (.literal ['a','b'])) (by decide +kernel)

theorem language : ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
    SObs (source letters scripts bodies) .callByValuePar (sourceExpr M root) x (some []) ↔
      SObs g .callByValueSeq start x (some []) :=
  automatic_language_translation scripts bodies root scoped_ok.1 scoped_ok.2

end Binary
end Shallot.MacroPeg.CBV.AutomaticFinitePrefixExamples
