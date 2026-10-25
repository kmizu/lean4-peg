import MacroPeg.CBV.AlphabetCaptureProfiles

namespace Shallot.MacroPeg.CBV.AlphabetCaptureProfileExamples
open RecursiveScannerProductCompiler
open RecursiveCaptureProfiles (scopeCheck)
open AlphabetCaptureProfiles
open CaptureTransitionProfile (profile profiles)
open DynamicScannerCapture (observer)
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- State 0 scans the source alphabet. States 1/2 remember whether the
capture began with a, even when the rest of that capture is arbitrarily long. -/
def machine : StatefulScanner.Machine 3 := ⟨fun q =>
  if q=0 then [('a',0),('b',0)] else if q=1 then [('a',2)] else [('a',2),('b',2)]⟩
def alphabet : List Char := ['a','b']
def labels : LiteralPrefixObservation.Labels 3 := fun q =>
  if q=1 then some ['a'] else if q=2 then some [] else none
def entries : Entries 3 := fun i => if i=1 then .replay else .scan 0
def copyBody : Arg := .alt (.seq (.user 1 (.seq (.param 0) (.param 0))) (.param 0)) (.lit [])
def bodies : List Arg := [.lit [],copyBody,.star (.lit [])]
def argument : Arg := .user 1 (.lit ['a'])
def root : Arg := .user 0 argument

theorem checked : AlphabetCaptureProfiles.check machine entries bodies alphabet=true ∧
    scopeCheck bodies root=true ∧ literalCheck alphabet root=true := by decide +kernel

theorem literal_certificates : LiteralPrefixObservation.check machine alphabet labels=true ∧
    LiteralPrefixObservation.alphabetCheck machine alphabet 0=true := by decide +kernel

/-- The old all-profile entry frontend rejects an unconditional scanner.
The new domain is computed from the finite source alphabet, not supplied. -/
theorem refined_domain : UniversalCaptureProfiles.check machine entries bodies=false ∧
    (profiles (observer machine)).length=256 ∧ (domain (observer machine) alphabet).length=3 := by decide +kernel

def sourceRun (e : Arg) (x : List Char) (k : Nat) :=
  evV (source machine entries bodies) x .callByValuePar (tblV (source machine entries bodies) x .callByValuePar k) [] (sourceExpr machine e) x.length

def targetRun (e : Arg) (x : List Char) (k : Nat) :=
  evV (target machine entries bodies) x .callByValueSeq (tblV (target machine entries bodies) x .callByValueSeq k) [] (plain machine bodies [] e) x.length

def input (copies extra : Nat) := List.replicate copies 'a'++List.replicate extra 'b'

/-- The actual argument contains genuine same-user recursion, doubled
child captures, and the parent's original whole value after the child. -/
theorem recursive_source_samples : ∀ copies∈[1,4,10], ∀ extra∈[1,2,4],
    sourceRun root (input copies extra) (copies+extra+3)=some (some 0) := by decide +kernel

theorem recursive_target_samples : ∀ copies∈[1,4,10], ∀ extra∈[1,2,4],
    ∃ k, targetRun root (input copies extra) k=some (some 0) := by
  intro copies hc extra he
  exact (defined_iff machine entries bodies alphabet checked.1 root checked.2.1 checked.2.2 (input copies extra) (some 0)).mp
    ⟨copies+extra+3,recursive_source_samples copies hc extra he⟩

theorem target_direct : targetRun root (input 4 2) 12=some (some 0) := by decide +kernel

theorem language : ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
    SObs (source machine entries bodies) .callByValuePar (sourceExpr machine root) x (some []) ↔
      SObs g .callByValueSeq start x (some []) :=
  language_translation machine entries bodies alphabet checked.1 root checked.2.1 checked.2.2

/-- The formerly colliding values are separated by a real observation
state. Both remain actual words in the generated alphabet domain. -/
theorem formerly_colliding_values :
    profile (observer machine) "aab".toList≠profile (observer machine) "bba".toList ∧
    profile (observer machine) "aab".toList∈domain (observer machine) alphabet ∧
    profile (observer machine) "bba".toList∈domain (observer machine) alphabet := by decide +kernel

theorem literal_inside_capture :
    evV ⟨[]⟩ "aabz".toList .callByValuePar (fun _ _ => []) ["aab".toList] (.andP (.lit ['a'])) 4=some (some 4) ∧
    evV ⟨[]⟩ "aabz".toList .callByValueSeq (fun _ _ => []) ["aab".toList]
      (LiteralPrefixObservation.query (profile (observer machine) "aab".toList) 1 labels) 1=some (some 1) ∧
    evV ⟨[]⟩ "bbaz".toList .callByValuePar (fun _ _ => []) ["bba".toList] (.andP (.lit ['a'])) 4=some none ∧
    evV ⟨[]⟩ "bbaz".toList .callByValueSeq (fun _ _ => []) ["bba".toList]
      (LiteralPrefixObservation.query (profile (observer machine) "bba".toList) 1 labels) 1=some none := by decide +kernel

/-- No captured-word alphabet hypothesis is supplied: it follows from
finite source checks and this arbitrary successful recursive argument run. -/
theorem actual_probe (x : List Char) (k p q : Nat) (hp : p≤x.length)
    (hv : evV (source machine entries bodies) x .callByValuePar (sourceTable machine entries bodies x k) []
      (sourceExpr machine argument) p=some (some q)) (T U : ClockFreezing.Table) :
    let w := pre x p q
    GuardedReplayControl.Results (GuardedReplayControl.Aligned x w)
      (evV (source machine entries bodies) x .callByValuePar T [w] (.andP (.lit ['a'])) p)
      (evV (target machine entries bodies) x .callByValueSeq U [w]
        (LiteralPrefixObservation.query (profile (observer machine) w) 1 labels) q) :=
  actual_literal_probe machine entries bodies alphabet checked.1 0 literal_certificates.2
    labels literal_certificates.1 1 ['a'] (by decide) x k [] []
    (DependentCaptureFilter.environment_accurate _ _) (by intro P hp; cases hp)
    argument (by decide) (by decide) p q hp hv T U

def nullable : Arg := .user 0 (.star (.lit []))
theorem nullable_source (x : List Char) (k : Nat) : sourceRun nullable x k=none := by
  have hr := source_rule machine entries bodies 0 (.lit []) (by rfl)
  change evV (source machine entries bodies) x .callByValuePar
    (tblV (source machine entries bodies) x .callByValuePar k) []
    (.call (offset machine+0) [sourceExpr machine (.star (.lit []))]) x.length=none
  rw [evV_call_par hr rfl (by decide)]
  have hn : evV (source machine entries bodies) x .callByValuePar
      (tblV (source machine entries bodies) x .callByValuePar k) []
      (sourceExpr machine (.star (.lit []))) x.length=none := by
    apply evStar_stuck (j:=x.length) _ (Nat.lt_irrefl _)
    simp [sourceExpr,evV,Shallot.stripPrefix?,length_sfx x (Nat.le_refl _)]
  simp only [evParArgs,hn]

theorem nullable_target (x : List Char) (k : Nat) : targetRun nullable x k=none :=
  (undefined_iff machine entries bodies alphabet checked.1 nullable (by decide) (by decide) x).mp (nullable_source x) k

theorem missing_alphabet_rejected : AlphabetCaptureProfiles.check machine entries bodies ['a']=false := by decide +kernel

theorem unknown_argument_rejected : literalCheck alphabet (.user 0 (.lit ['c']))=false := by decide +kernel

theorem invalid_literal_labels_rejected : LiteralPrefixObservation.check machine alphabet
    (fun q => if q=1 then some ['b'] else if q=2 then some [] else none)=false := by decide +kernel

end Shallot.MacroPeg.CBV.AlphabetCaptureProfileExamples
