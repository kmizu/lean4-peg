import MacroPeg.CBV.LastCodewordHelperGrammar
import MacroPeg.CBV.RecursiveCodeExamples

/-! Recursive headers and recursive users select different unbounded
whole-string captures and restore the caller's value after return. -/
namespace Shallot.MacroPeg.CBV.LastCodewordHelperExamples
open LastCodewordHelperGrammar
open LastCodewordHelpers (argument)
open RecursiveCodeExamples (header)
open CodewordReplay (power)

def recursiveTail (mark : Char) (next : Nat) : MExp :=
  .alt (.seq (.lit [mark]) (.seq (.call next []) (.seq (.lit ['?']) (.param 0))))
    (.seq (.lit ['!']) (.param 0))
def tails : List MExp := [recursiveTail '@' 1,recursiveTail '%' 0]
def root : MExp := .call 0 []
def u : List Char := "aabb#".toList
def v : List Char := "ab#".toList
def z : List Char := ['#']
def grandInput : List Char := power z 3++['!']++power z 2++['?']++v++['?']++power u 3
def childInput : List Char := power v 2++['%']++grandInput
def good : List Char := power u 4++['@']++childInput

def shortParent : List Char := power u 4++['@']++power v 2++['%']++power z 3++['!']++power z 2++['?']++v++['?']++power u 2
def shortChild : List Char := power u 4++['@']++power v 2++['%']++power z 3++['!']++power z 2++['?']++['#']++['?']++power u 3
def unequalChild : List Char := power u 4++['@']++v++u++['%']++grandInput

/-- Actual ordinary source calls capture counts 3→1→2 with independently
recursive headers aabb#→ab#→#. The full parent and child strings survive. -/
theorem actual_captures :
    let g := source header tails
    let T := tblV g good .callByValuePar 8
    evV g good .callByValuePar T [] (argument header) good.length=
      some (some (u++['@']++childInput).length) ∧
    pre good good.length (u++['@']++childInput).length=power u 3 ∧
    evV g good .callByValuePar T [power u 3] (argument header) childInput.length=
      some (some (v++['%']++grandInput).length) ∧
    pre good childInput.length (v++['%']++grandInput).length=v ∧
    evV g good .callByValuePar T [v] (argument header) grandInput.length=
      some (some (z++['!']++power z 2++['?']++v++['?']++power u 3).length) ∧
    pre good grandInput.length (z++['!']++power z 2++['?']++v++['?']++power u 3).length=power z 2 := by
  decide +kernel

theorem executions :
    evV (source header tails) good .callByValuePar
      (tblV (source header tails) good .callByValuePar 12) [] (render header tails true root) good.length=some (some 0) ∧
    evV (target header tails) good .callByValueSeq
      (tblV (target header tails) good .callByValueSeq 12) [] (render header tails false root) good.length=some (some 0) ∧
    evV (source header tails) shortParent .callByValuePar
      (tblV (source header tails) shortParent .callByValuePar 12) [] (render header tails true root) shortParent.length=some none ∧
    evV (target header tails) shortParent .callByValueSeq
      (tblV (target header tails) shortParent .callByValueSeq 12) [] (render header tails false root) shortParent.length=some none ∧
    evV (source header tails) shortChild .callByValuePar
      (tblV (source header tails) shortChild .callByValuePar 12) [] (render header tails true root) shortChild.length=some none ∧
    evV (target header tails) shortChild .callByValueSeq
      (tblV (target header tails) shortChild .callByValueSeq 12) [] (render header tails false root) shortChild.length=some none ∧
    evV (source header tails) unequalChild .callByValuePar
      (tblV (source header tails) unequalChild .callByValuePar 12) [] (render header tails true root) unequalChild.length=some none ∧
    evV (target header tails) unequalChild .callByValueSeq
      (tblV (target header tails) unequalChild .callByValueSeq 12) [] (render header tails false root) unequalChild.length=some none := by
  decide +kernel

theorem all_inputs (x : List Char) (r : Option (List Char)) :
    SObs (source header tails) .callByValuePar (render header tails true root) x r ↔
      SObs (target header tails) .callByValueSeq (render header tails false root) x r :=
  observations_iff header tails root x r

/-- A nonproductive actual helper satisfies the code certificate vacuously;
its undefinedness must remain undefined before user or verifier queries. -/
def cyclicHeader : RecursiveCodeGrammar.Header where
  bodies := RecursiveCodeExamples.bodies
  valid := RecursiveCodeExamples.bodies_valid
  head := .call 0 []
  lexical := by change 0<2; omega
  code := fun _ => False
  prefixFree := by intro u v hu; cases hu
  captured := by
    intro x p q hp hv
    have hn := RecursiveParserStability.cycle_undefined
      (g:=RecursiveParserStability.grammar RecursiveCodeExamples.bodies) (by rfl) x .callByValuePar
      (RecursiveParserStability.floor RecursiveCodeExamples.bodies x) [] p hp
    change evV _ x .callByValuePar (tblV _ x .callByValuePar (RecursiveParserStability.floor _ x)) [] (.call 0 []) p=some (some q) at hv
    rw [hn] at hv
    cases hv

theorem cyclic_source_undefined (x : List Char) (k p : Nat) (hp : p≤x.length) :
    evV (source cyclicHeader [.eps]) x .callByValuePar
      (tblV (source cyclicHeader [.eps]) x .callByValuePar k) []
      (render cyclicHeader [.eps] true root) p=none := by
  let g := source cyclicHeader [.eps]
  have hr : ruleAtM g.rules 3=some ⟨1,.seq (.seq (.call 0 []) (.param 0)) .eps⟩ := rfl
  change evV g x .callByValuePar (tblV g x .callByValuePar k) [] (.call 3 [argument cyclicHeader]) p=none
  rw [evV_call_par hr rfl (by decide)]
  have hh : evV g x .callByValuePar (tblV g x .callByValuePar k) [] (.call 0 []) p=none :=
    RecursiveParserStability.cycle_undefined (by rfl) x .callByValuePar k [] p hp
  have hb : evV g x .callByValuePar (tblV g x .callByValuePar k) [] (argument cyclicHeader) p=none := by
    rw [argument,LastCodewordRotation.argument,evV_star]
    exact evStar_none (evV_seq_none hh)
  simp only [evParArgs,hb]

theorem cyclic_no_observations (x : List Char) (r : Option (List Char)) :
    ¬SObs (target cyclicHeader [.eps]) .callByValueSeq (render cyclicHeader [.eps] false root) x r := by
  rw [←observations_iff cyclicHeader [.eps] root x r,
    ←decideObsV_iff (source_firstOrder cyclicHeader [.eps]) (by decide) (render_firstOrder cyclicHeader [.eps] true root)]
  simp [decideObsV,cyclic_source_undefined x _ x.length (Nat.le_refl _)]

end Shallot.MacroPeg.CBV.LastCodewordHelperExamples
