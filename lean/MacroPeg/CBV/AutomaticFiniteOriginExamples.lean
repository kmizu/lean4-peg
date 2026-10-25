import MacroPeg.CBV.AutomaticFiniteOrigin

namespace Shallot.MacroPeg.CBV.AutomaticFiniteOriginExamples
open AutomaticFiniteOrigin
open RecursiveScannerProductCompiler (Arg sourceExpr offset)
open ReplayControlFusion (Plan)
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def loopControl : AutomaticFinitePrefix.Control :=
  .star (.finite (.seq (.lit ['a']) (.query true)))
def copyBody : Arg := .alt (.seq (.user 1 (.seq (.param 0) (.param 0))) (.param 0)) (.lit [])
def parts : List Part := [⟨loopControl,.lit ['b'],false⟩,⟨.retain,copyBody,false⟩,⟨.retain,.lit ['a'],true⟩]
def plans : List Plan := [.alt (.leaf 0) (.notP (.leaf 0)),.leaf 1,.leaf 2,.guard (.notP (.leaf 0)) (.leaf 2)]
def argument : Arg := .user 1 (.lit ['a'])
def root : Arg := .user 0 argument
def letters := AutomaticFiniteOrigin.alphabet parts root
def M := FinitePrefixMachines.machine letters (pool parts)

theorem ready : readyCheck parts plans=true ∧ ScannerOriginControl.scopeCheck plans root=true := by decide +kernel

theorem shape : letters=['a','b'] ∧ size parts=3 := by decide +kernel

theorem checked : check letters parts plans=true := automatic_check parts plans root ready.1

theorem generated_certificates : AlphabetOriginControl.check M (annotated letters parts) plans letters=true :=
  certificates letters parts plans checked

theorem old_universal_rejected : AutomaticOriginControl.check M (annotated letters parts) plans=false := by decide +kernel

def sourceRun (e : Arg) (x : List Char) (k : Nat) :=
  evV (source letters parts plans) x .callByValuePar (tblV (source letters parts plans) x .callByValuePar k)
    [] (sourceExpr M e) x.length

def targetRun (e : Arg) (x : List Char) (k : Nat) :=
  evV (compiled letters parts plans) x .callByValueSeq (tblV (compiled letters parts plans) x .callByValueSeq k)
    [] (targetExpr letters parts plans e) x.length

/-- These real recursive arguments retain lengths 1/4/10, using the
same user for the child and restoring the parent's whole value afterward. -/
theorem recursive_captures : ∀ n∈[1,4,10], sourceRun argument (List.replicate n 'a') 4=some (some 0) := by decide +kernel

theorem positive_source : ∀ n∈[1,2,4,5,10,11],
    sourceRun root (List.replicate n 'a'++['b']) 4=some (some 0) := by decide +kernel

/-- The failing loop leaf is negated at the caller origin. The successful
argument was nonempty, yet the whole user body returns before its endpoint. -/
theorem origin_source : ∀ n∈[1,2,4,5,10,11],
    sourceRun root (List.replicate n 'a'++['X']) 4=some (some (n+1)) := by decide +kernel

theorem positive_targets : ∀ n∈[1,2,4,5,10,11],
    ∃ k, targetRun root (List.replicate n 'a'++['b']) k=some (some 0) := by
  intro n hn
  exact (defined_iff letters parts plans checked root ready.2 (root_literal_checked parts root)
    (List.replicate n 'a'++['b']) (some 0)).mp ⟨4,positive_source n hn⟩

theorem origin_targets : ∀ n∈[1,2,4,5,10,11],
    ∃ k, targetRun root (List.replicate n 'a'++['X']) k=some (some (n+1)) := by
  intro n hn
  exact (defined_iff letters parts plans checked root ready.2 (root_literal_checked parts root)
    (List.replicate n 'a'++['X']) (some (n+1))).mp ⟨4,origin_source n hn⟩

theorem direct_loop_and_origin : targetRun (.user 0 (.lit ['a'])) "ab".toList 2=some (some 0) ∧
    targetRun (.user 0 (.lit ['a'])) "aX".toList 2=some (some 2) := by decide +kernel

/-- A user call returning through a closed leaf is an actual argument
of the dependent loop call. The checked product-row correspondence gives
ordinary-clock target executions without reducing the full profile grammar. -/
theorem origin_product_correspondence :
    sourceRun (.user 0 (.user 2 (.lit ['a']))) "ab".toList 2=some (some 0) ∧
    sourceRun (.user 0 (.user 2 (.lit ['a']))) "aX".toList 2=some (some 2) ∧
    (∃ k, targetRun (.user 0 (.user 2 (.lit ['a']))) "ab".toList k=some (some 0)) ∧
    ∃ k, targetRun (.user 0 (.user 2 (.lit ['a']))) "aX".toList k=some (some 2) := by
  have hp : sourceRun (.user 0 (.user 2 (.lit ['a']))) "ab".toList 2=some (some 0) := by decide +kernel
  have hn : sourceRun (.user 0 (.user 2 (.lit ['a']))) "aX".toList 2=some (some 2) := by decide +kernel
  exact ⟨hp,hn,
    (defined_iff letters parts plans checked (.user 0 (.user 2 (.lit ['a'])))
      (by decide +kernel) (by decide +kernel) "ab".toList (some 0)).mp ⟨2,hp⟩,
    (defined_iff letters parts plans checked (.user 0 (.user 2 (.lit ['a'])))
      (by decide +kernel) (by decide +kernel) "aX".toList (some 2)).mp ⟨2,hn⟩⟩

/-- The independent leaf consumes a single a while its argument consumes
all four a's. Its endpoint is strictly before the captured endpoint. -/
theorem closed_before_capture : sourceRun (.user 2 argument) "aaaa".toList 4=some (some 3) ∧
    targetRun (.user 2 argument) "aaaa".toList 8=some (some 3) := by decide +kernel

theorem guarded_origin : sourceRun (.user 3 argument) "aaaaX".toList 4=some (some 4) ∧
    sourceRun (.user 3 argument) "aaaab".toList 4=some none := by decide +kernel

/-- An independent leaf is still behind argument evaluation. Omitting
that preflight would accept a even though its b argument fails. -/
theorem failed_argument : sourceRun (.user 2 (.lit ['b'])) "a".toList 1=some none ∧
    targetRun (.user 2 (.lit ['b'])) "a".toList 2=some none ∧
    evV ⟨[]⟩ "a".toList .callByValueSeq (fun _ _ => []) [] (.lit ['a']) 1=some (some 0) := by decide +kernel

theorem empty_capture : sourceRun (.user 0 (.lit [])) "aab".toList 1=some (some 0) ∧
    targetRun (.user 0 (.lit [])) "aab".toList 2=some (some 0) := by decide +kernel

theorem language : ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
    SObs (source letters parts plans) .callByValuePar (sourceExpr M root) x (some []) ↔
      SObs g .callByValueSeq start x (some []) :=
  automatic_language_translation parts plans root ready.1 ready.2

def replayTail : Arg := .seq (.user 2 argument) (.star (.alt (.lit ['a']) (.lit ['b'])))

theorem closed_language : ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
    SObs (source (AutomaticFiniteOrigin.alphabet parts replayTail) parts plans) .callByValuePar
      (sourceExpr (FinitePrefixMachines.machine (AutomaticFiniteOrigin.alphabet parts replayTail) (pool parts)) replayTail)
      x (some []) ↔ SObs g .callByValueSeq start x (some []) :=
  automatic_language_translation parts plans replayTail ready.1 (by decide +kernel)

theorem invalid_closed_rejected : readyCheck [⟨.retain,.param 0,true⟩] [.leaf 0]=false := by decide +kernel

theorem invalid_plan_rejected : readyCheck parts [.leaf 9]=false := by decide +kernel

namespace Nullable

def parts : List Part := [⟨.star (.finite (.query true)),.lit [],false⟩,⟨.retain,.lit [],true⟩]
def nullablePlan : Plan := .alt (.notP (.leaf 0)) (.leaf 1)
def plans : List Plan := [nullablePlan]
def root : Arg := .user 0 (.lit ['a'])
def letters := AutomaticFiniteOrigin.alphabet parts root
def M := FinitePrefixMachines.machine letters (pool parts)

theorem ready : readyCheck parts plans=true ∧ ScannerOriginControl.scopeCheck plans root=true := by decide +kernel

theorem checked : check letters parts plans=true := automatic_check parts plans root ready.1

def sourceRun (x : List Char) (k : Nat) :=
  evV (source letters parts plans) x .callByValuePar (tblV (source letters parts plans) x .callByValuePar k)
    [] (sourceExpr M root) x.length

def targetRun (x : List Char) (k : Nat) :=
  evV (compiled letters parts plans) x .callByValueSeq (tblV (compiled letters parts plans) x .callByValueSeq k)
    [] (targetExpr letters parts plans root) x.length

theorem source_none (k : Nat) : sourceRun "aa".toList k=none := by
  have hr : ruleAtM (source letters parts plans).rules (offset M)=
      some ⟨1,nullablePlan.exp (rawLeaf letters parts)⟩ := by
    simpa only [M,Nat.add_zero] using source_rule letters parts plans 0 nullablePlan (by rfl)
  have hb (T : ClockFreezing.Table) : evV (source letters parts plans) "aa".toList .callByValuePar T [['a']]
      (nullablePlan.exp (rawLeaf letters parts)) 2=none := by
    rw [Plan.exp_eval]
    have hl : evV (source letters parts plans) "aa".toList .callByValuePar T [['a']] (rawLeaf letters parts 0) 2=none := by
      have hs : evV (source letters parts plans) "aa".toList .callByValuePar T [['a']]
          (.star (.seq (.andP (.param 0)) (.andP (.param 0)))) 2=none := by
        rw [evV_star,evStar_stuck (show evV (source letters parts plans) "aa".toList .callByValuePar T [['a']]
          (.seq (.andP (.param 0)) (.andP (.param 0))) 2=some (some 2) from by
            simp only [MExp.andP,evV]; decide +kernel) (by omega)]
      exact evV_seq_none (evV_seq_none hs)
    change ReplayFallbackFusion.orElse (match evV _ _ _ T _ (rawLeaf letters parts 0) 2 with
      | some (some _) => some none | some none => some (some 2) | none => none) _=none
    rw [hl]
    rfl
  change evV (source letters parts plans) "aa".toList .callByValuePar
    (tblV (source letters parts plans) "aa".toList .callByValuePar k) [] (.call (offset M) [.lit ['a']]) 2=none
  rw [evV_call_par hr rfl (by decide)]
  change valAt (tblV (source letters parts plans) "aa".toList .callByValuePar k (offset M) [['a']]) 2=none
  cases k with
  | zero => rfl
  | succ k => rw [valAt_tblV_succ hr _ (by decide : 2≤"aa".toList.length)]; exact hb _

theorem target_none : ∀ k, targetRun "aa".toList k=none :=
  (undefined_iff letters parts plans checked root ready.2 (root_literal_checked parts root) "aa".toList).mp source_none

theorem direct : targetRun "aa".toList 2=none := by decide +kernel

theorem failure_stays_failure : sourceRun "b".toList 1=some none ∧ targetRun "b".toList 2=some none := by decide +kernel

end Nullable
end Shallot.MacroPeg.CBV.AutomaticFiniteOriginExamples
