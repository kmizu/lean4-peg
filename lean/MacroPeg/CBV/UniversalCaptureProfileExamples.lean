import MacroPeg.CBV.UniversalCaptureProfiles

namespace Shallot.MacroPeg.CBV.UniversalCaptureProfileExamples
open RecursiveScannerProductCompiler
open UniversalCaptureProfiles
open RecursiveCaptureProfiles (scopeCheck)
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def machine : StatefulScanner.Machine 1 := ⟨fun _ => [('a',0)]⟩
def residuals : ScannerReplayResidual.Labels 1 := fun _ => some ['a']
def entries : Entries 1 := fun _ => .guard false (.shift 0 residuals) .replay
/-- New captures double the entire old value. The final param0 belongs
to the parent, even after the recursive child has retained twice as much. -/
def body : Arg := .alt (.seq (.user 0 (.seq (.param 0) (.param 0))) (.param 0)) (.lit [])
def bodies : List Arg := [body]
def argument : Arg := .seq (.star (.lit ['b'])) (.lit ['a'])
def root : Arg := .user 0 argument

theorem checked : UniversalCaptureProfiles.check machine entries bodies=true ∧ scopeCheck bodies root=true := by decide +kernel

/-- All annotation checks follow by theorem from the two source checks.
No output profiles, successful-capture shape, or fixed palette is supplied. -/
theorem automatic_certificates :
    RecursiveCaptureProfiles.scannerCheck machine (scannerSummary machine)=true ∧
    RecursiveCaptureProfiles.grammarCheck machine entries bodies (scannerSummary machine) (summary machine)=true ∧
    ProfileCheckedScannerCorrespondence.bodiesCheck machine entries bodies (summary machine) (inputs machine)=true ∧
    ProfileCheckedScannerCorrespondence.check machine entries bodies (summary machine) (inputs machine) [] root=true :=
  ⟨scanner_checked machine,grammar_checked machine entries bodies checked.1,
    bodies_checked machine entries bodies checked.1,
    expression_checked machine entries bodies checked.1 [] (by simp [AllIn]) root checked.2⟩

theorem raw_rule : ruleAtM (source machine entries bodies).rules (offset machine)=
    some ⟨1,.seq (.seq (.notP (.seq (.lit ['a']) (.param 0))) (.param 0)) (sourceExpr machine body)⟩ := by
  exact source_rule machine entries bodies 0 body rfl

def word (n : Nat) := List.replicate n 'b'++['a']
def input (n copies : Nat) := (List.replicate copies (word n)).flatten

theorem source_recursive_samples : ∀ n∈[1,2,4],
    evV (source machine entries bodies) (input n 4) .callByValuePar
      (tblV (source machine entries bodies) (input n 4) .callByValuePar 3) []
      (sourceExpr machine root) (input n 4).length=some (some 0) ∧
    evV (source machine entries bodies) (input n 10) .callByValuePar
      (tblV (source machine entries bodies) (input n 10) .callByValuePar 4) []
      (sourceExpr machine root) (input n 10).length=some (some 0) := by decide +kernel

/-- The actual generated Seq grammar accepts the unchanged inputs, with
arbitrarily composed actual arguments and recursive parent-value reuse. -/
theorem target_recursive_samples : ∀ n∈[1,2,4],
    (∃ k, evV (target machine entries bodies) (input n 4) .callByValueSeq
      (tblV (target machine entries bodies) (input n 4) .callByValueSeq k) []
      (plain machine bodies [] root) (input n 4).length=some (some 0)) ∧
    (∃ k, evV (target machine entries bodies) (input n 10) .callByValueSeq
      (tblV (target machine entries bodies) (input n 10) .callByValueSeq k) []
      (plain machine bodies [] root) (input n 10).length=some (some 0)) := by
  intro n hn
  obtain ⟨h4,h10⟩ := source_recursive_samples n hn
  exact ⟨(defined_iff machine entries bodies checked.1 root checked.2 (input n 4) (some 0)).mp ⟨3,h4⟩,
    (defined_iff machine entries bodies checked.1 root checked.2 (input n 10) (some 0)).mp ⟨4,h10⟩⟩

/-- A concrete ordinary Seq run is also checked directly by the kernel,
independently of deriving existence from the language correspondence. -/
theorem target_direct :
    evV (target machine entries bodies) (input 1 4) .callByValueSeq
      (tblV (target machine entries bodies) (input 1 4) .callByValueSeq 5) []
      (plain machine bodies [] root) (input 1 4).length=some (some 0) := by decide +kernel

theorem language : ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
    SObs (source machine entries bodies) .callByValuePar (sourceExpr machine root) x (some []) ↔
      SObs g .callByValueSeq start x (some []) :=
  language_translation machine entries bodies checked.1 root checked.2

/-- A nullable actual argument blocks entry to the negative shift guard,
which would otherwise finitely succeed. -/
def nullable : Arg := .user 0 (.star (.lit []))

theorem nullable_source (x : List Char) (clock : Nat) :
    evV (source machine entries bodies) x .callByValuePar
      (tblV (source machine entries bodies) x .callByValuePar clock) []
      (sourceExpr machine nullable) x.length=none := by
  change evV (source machine entries bodies) x .callByValuePar
    (tblV (source machine entries bodies) x .callByValuePar clock) []
    (.call (offset machine+0) [sourceExpr machine (.star (.lit []))]) x.length=none
  rw [evV_call_par (source_rule machine entries bodies 0 body rfl) rfl (by decide)]
  have hloop : evV (source machine entries bodies) x .callByValuePar
      (tblV (source machine entries bodies) x .callByValuePar clock) []
      (sourceExpr machine (.star (.lit []))) x.length=none := by
    apply evStar_stuck (j:=x.length) _ (Nat.lt_irrefl _)
    simp [sourceExpr,evV,Shallot.stripPrefix?,length_sfx x (Nat.le_refl _)]
  simp only [evParArgs,hloop]

theorem nullable_target (x : List Char) (clock : Nat) :
    evV (target machine entries bodies) x .callByValueSeq
      (tblV (target machine entries bodies) x .callByValueSeq clock) []
      (plain machine bodies [] nullable) x.length=none :=
  (undefined_iff machine entries bodies checked.1 nullable (by decide) x).mp (nullable_source x) clock

/-- A scanner frontier cannot be accepted for all unrestricted arguments;
an incomplete shift machine is also rejected by the syntactic source check. -/
theorem invalid_entries :
    entryCheck machine (.scan 0)=false ∧
    entryCheck (StatefulScanner.Machine.mk (fun _ : Fin 1 => [])) (.shift 0 residuals)=false := by decide +kernel

end Shallot.MacroPeg.CBV.UniversalCaptureProfileExamples
