import MacroPeg.CBV.ContinuationGrammar
import MacroPeg.CBV.LeafContinuation

namespace Shallot.MacroPeg.CBV.ContinuationExamples
open ReplayControlFusion (Plan)
open ContinuationPlan
open ContinuationGrammar

def rs : List Rule := [
  ⟨1,[.param 0,.seq (.param 0) (.lit ['b']),
    .seq (.lit ['#']) (.seq (.call 1 [.seq (.param 0) (.param 0)]) (.seq (.lit ['?']) (.param 0)))],
    .alt (.leaf 0) (.leaf 1),.leaf 2⟩,
  ⟨1,[.seq (.param 0) (.alt (.call 1 [.param 0]) (.lit [])),.lit []],.leaf 0,.leaf 1⟩]

def entry : MExp := .call 0 [.lit ['a','a']]
def good : List Char := "aa#aaaa?aa".toList
def bad : List Char := "aab#aaaa?aa".toList

theorem valid : ∀ r∈rs, r.Valid := by simp [rs,Rule.Valid,Plan.All]
theorem firstOrder : ContinuationGrammar.FirstOrder rs := by
  simp [ContinuationGrammar.FirstOrder,rs,MExp.FirstOrder,MExp.FirstOrderArgs]

/-- Parent aa, child aaaa, then parent aa again. The child executes its
recursive branch and backs out only when its own argument fails. -/
theorem source_execution :
    evV (source rs) good .callByValuePar (tblV (source rs) good .callByValuePar 6) [] entry good.length=some (some 0) ∧
    evV (source rs) bad .callByValuePar (tblV (source rs) bad .callByValuePar 6) [] entry bad.length=some none := by decide +kernel

theorem normalized_observations (x : List Char) (rest : Option (List Char)) :
    SObs (source rs) .callByValuePar entry x rest ↔ SObs (normalized rs) .callByValuePar entry x rest :=
  observations_iff rs valid firstOrder .callByValuePar (by decide) entry (by simp [entry,MExp.FirstOrder,MExp.FirstOrderArgs]) x rest

/-- Distributing sequence across priority choice would accept this input
by switching from the successful short replay to the long replay. -/
def short : MExp := .param 0
def long : MExp := .seq (.param 0) (.lit ['b'])
def tail : MExp := .lit ['#']
def L : Nat → MExp | 0 => short | 1 => long | _ => tail

theorem commitment :
    evV ⟨[]⟩ "ab#".toList .callByValuePar (fun _ _ => []) [['a']]
      (.seq (.alt short long) tail) 3=some none ∧
    evV ⟨[]⟩ "ab#".toList .callByValuePar (fun _ _ => []) [['a']]
      (.alt (.seq short tail) (.seq long tail)) 3=some (some 0) ∧
    evV ⟨[]⟩ "ab#".toList .callByValuePar (fun _ _ => []) [['a']]
      ((bind 3 (.alt (.leaf 0) (.leaf 1)) (.leaf 2)).exp (expressions 3 L (.leaf 2))) 3=some none := by decide +kernel

/-- An undefined continuation after a successful branch cannot be converted
into failure or reopened choice. -/
theorem undefined_tail (g : MGrammar) (T : ClockFreezing.Table) :
    evV g ['a'] .callByValuePar T [['a']]
      ((bind 2 (.alt (.leaf 0) (.leaf 1)) (.leaf 1)).exp
        (expressions 2 (fun i => if i=0 then .param 0 else .star (.lit [])) (.leaf 1))) 1=none := by
  rw [expression_eq 2 _ _ _ (by simp [Plan.All]) (by simp [Plan.All])]
  change evV g ['a'] .callByValuePar T [['a']]
    (.seq (.alt (.param 0) (.star (.lit []))) (.star (.lit []))) 1=none
  have hs : evV g ['a'] .callByValuePar T [['a']] (.param 0) 1=some (some 0) := rfl
  rw [evV_seq_ok (evV_alt_ok hs)]
  exact evStar_stuck (j:=0) rfl (by omega)

end Shallot.MacroPeg.CBV.ContinuationExamples
