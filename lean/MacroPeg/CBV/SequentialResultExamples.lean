import MacroPeg.CBV.SequentialResultCompiler
import MacroPeg.CBV.RecursiveFieldProofs

namespace Shallot.MacroPeg.CBV.SequentialResultExamples
open SequentialResultSyntax SequentialResultCompiler
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def binary : MGrammar := ⟨[⟨2,.seq (.param 0) (.param 1)⟩]⟩

theorem zero_arguments_become_empty_values :
    evV (target binary) ['a'] .callByValueSeq (tblV (target binary) ['a'] .callByValueSeq 1) []
      (SequentialResultSyntax.zero (.call 0 [.eps,.eps])) 1=some (some 1) ∧
    (target binary).rules.map MRule.arity=[2,0] := by decide +kernel

theorem positive_argument_prevents_zero_call :
    evV binary ['a'] .callByValueSeq (tblV binary ['a'] .callByValueSeq 1) [] (.call 0 [.lit ['a'],.eps]) 1=some none ∧
    evV (target binary) ['a'] .callByValueSeq (tblV (target binary) ['a'] .callByValueSeq 1) []
      (SequentialResultSyntax.zero (.call 0 [.lit ['a'],.eps])) 1=some none := by decide +kernel

def ignores : MGrammar := ⟨[⟨1,.eps⟩]⟩
theorem zero_callee_can_have_consuming_call :
    evV ignores ['a'] .callByValueSeq (tblV ignores ['a'] .callByValueSeq 1) [] (.call 0 [.lit ['a']]) 1=some (some 0) ∧
    evV (target ignores) ['a'] .callByValueSeq (tblV (target ignores) ['a'] .callByValueSeq 1) []
      (SequentialResultSyntax.zero (.call 0 [.lit ['a']])) 1=some none ∧
    evV (target ignores) ['a'] .callByValueSeq (tblV (target ignores) ['a'] .callByValueSeq 1) []
      (positive (.call 0 [.lit ['a']])) 1=some (some 0) := by decide +kernel

theorem committed_choice_keeps_its_first_success :
    evV (target ⟨[]⟩) ['a'] .callByValueSeq (tblV (target ⟨[]⟩) ['a'] .callByValueSeq 0) []
      (SequentialResultSyntax.zero (.alt (.chr 'a') .eps)) 1=some none := by decide +kernel

theorem invalid_calls_and_parameters_preserve_failure :
    evV (target binary) ['a'] .callByValueSeq (tblV (target binary) ['a'] .callByValueSeq 2) []
      (SequentialResultSyntax.zero (.call 0 [.eps])) 1=some none ∧
    evV (target binary) ['a'] .callByValueSeq (tblV (target binary) ['a'] .callByValueSeq 2) []
      (SequentialResultSyntax.zero (.call 99 [])) 1=some none ∧
    evV (target binary) ['a'] .callByValueSeq (tblV (target binary) ['a'] .callByValueSeq 2) []
      (failure (.param 3)) 1=some (some 1) := by decide +kernel

theorem nullable_star_is_not_finite_failure :
    evV (target ⟨[]⟩) "aaa".toList .callByValueSeq (tblV (target ⟨[]⟩) "aaa".toList .callByValueSeq 0) [['a']]
      (SequentialResultSyntax.zero (.star (.alt (.param 0) .eps))) 3=none ∧
    evV (target ⟨[]⟩) "aaa".toList .callByValueSeq (tblV (target ⟨[]⟩) "aaa".toList .callByValueSeq 0) [['a']]
      (positive (.star (.alt (.param 0) .eps))) 3=none ∧
    evV (target ⟨[]⟩) "aaa".toList .callByValueSeq (tblV (target ⟨[]⟩) "aaa".toList .callByValueSeq 0) [['a']]
      (failure (.star (.alt (.param 0) .eps))) 3=none := by decide +kernel

def cycle : MGrammar := ⟨[⟨0,.call 0 []⟩]⟩
theorem cycle_firstOrder : cycle.FirstOrder := by
  intro r hr
  have hr : r=⟨0,.call 0 []⟩ := by simpa [cycle] using hr
  subst r; trivial

theorem cycle_undefined (x : List Char) (k p : Nat) (hp : p≤x.length) :
    evV cycle x .callByValueSeq (tblV cycle x .callByValueSeq k) [] (.call 0 []) p=none := by
  have hr : ruleAtM cycle.rules 0=some ⟨0,.call 0 []⟩ := rfl
  rw [evV_call_seq hr rfl,evSeq_nil]
  change valAt (tblV cycle x .callByValueSeq k 0 []) p=none
  induction k with
  | zero => rfl
  | succ k ih => rw [valAt_tblV_succ hr [] hp,evV_call_seq hr rfl,evSeq_nil]; exact ih

theorem skipped_call_divergence_is_preserved (k : Nat) :
    evV (target cycle) ['a'] .callByValueSeq (tblV (target cycle) ['a'] .callByValueSeq k) []
      (SequentialResultSyntax.zero (.seq (.chr 'a') (.call 0 []))) 1=none := by
  have hsource : evV cycle ['a'] .callByValueSeq (tblV cycle ['a'] .callByValueSeq k) []
      (.seq (.chr 'a') (.call 0 [])) 1=none := by
    rw [evV_seq_ok (show evV cycle ['a'] .callByValueSeq (tblV cycle ['a'] .callByValueSeq k) [] (.chr 'a') 1=some (some 0) from rfl)]
    exact cycle_undefined ['a'] k 0 (by decide)
  rw [(physical cycle cycle_firstOrder ['a'] [] (.seq (.chr 'a') (.call 0 [])) ⟨True.intro,True.intro⟩ k 1 (by decide)).2,hsource]
  rfl

theorem arbitrary_depth_and_fresh_values (n depth : Nat) :
    let g := RecursiveFieldExamples.generated
    let e := RecursiveFieldExamples.generatedRoot
    let x := RecursiveFieldExamples.tree n depth
    evV (target g) x .callByValueSeq (tblV (target g) x .callByValueSeq (depth+1)) [] (normal e) x.length=some (some 0) ∧
    evV (target g) x .callByValueSeq (tblV (target g) x .callByValueSeq (depth+1)) [] (SequentialResultSyntax.zero e) x.length=some none ∧
    evV (target g) x .callByValueSeq (tblV (target g) x .callByValueSeq (depth+1)) [] (positive e) x.length=some (some 0) := by
  intro g e x
  have hfo := RecursiveFieldCompiler.firstOrder RecursiveFieldExamples.original RecursiveFieldExamples.root [] 2 '#'
    RecursiveFieldExamples.pattern RecursiveFieldExamples.body RecursiveFieldExamples.root RecursiveFieldExamples.checked
  have hg : g.FirstOrder := hfo.2.2.1
  have he : e.FirstOrder := hfo.2.2.2
  have hs := (RecursiveFieldProofs.source_and_target_all_trees n depth).2
  have hx : x≠[] := by
    cases depth <;> simp [x,RecursiveFieldExamples.tree,RecursiveFieldExamples.block,
      RecursiveFieldExamples.pattern,DelimitedWordPattern.encode,RecursiveFieldExamples.words,RecursiveFieldExamples.long]
  have hlen : 0≠x.length := by have := List.length_pos_iff.mpr hx; omega
  obtain ⟨hn,hz⟩ := physical g hg x [] e he (depth+1) x.length (Nat.le_refl _)
  rw [hs] at hn hz
  have hp := positive_physical g hg x [] e he (depth+1) x.length (Nat.le_refl _)
  rw [hs] at hp
  exact ⟨hn,by simpa [EmptyResultObservation.project,hlen] using hz,by simpa [positiveProject,hlen] using hp⟩

end Shallot.MacroPeg.CBV.SequentialResultExamples
