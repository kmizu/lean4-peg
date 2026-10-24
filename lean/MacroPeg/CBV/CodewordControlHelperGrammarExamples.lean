import MacroPeg.CBV.CodewordControlHelperGrammar
import MacroPeg.CBV.CodewordControlHelperExamples

/-! Recursive headers and nested recursive tests combined with actual
mutual user calls, disjoint retained parts, and whole parent restoration. -/
namespace Shallot.MacroPeg.CBV.CodewordControlHelperGrammarExamples
open CodewordControlHelperGrammar
open CodewordControlHelpers (Header argument rest)
open CodewordReplay (power)

def header : Header := CodewordControlHelperExamples.header
def u : List Char := "aabb#".toList
def v : List Char := "ab#".toList
def z : List Char := ['#']
def recursiveTail (mark : Char) (next : Nat) : MExp :=
  .alt (.seq (.lit [mark]) (.seq (.call next []) (.seq (.lit ['?']) (.param 0))))
    (.seq (.lit ['!']) (.param 0))
def tails : List MExp := [recursiveTail '@' 1,recursiveTail '%' 0]
def root : MExp := .call 0 []
def grandInput : List Char := power z 3++['!']++power z 2++['?']++power v 1++['?']++power u 3
def childInput : List Char := power v 2++['%']++grandInput
def good : List Char := power u 4++['@']++childInput

def shortParent : List Char := power u 4++['@']++power v 2++['%']++
  power z 3++['!']++power z 2++['?']++power v 1++['?']++power u 2
def shortChild : List Char := power u 4++['@']++power v 2++['%']++
  power z 3++['!']++power z 2++['?']++['?']++power u 3
def unequalChild : List Char := power u 4++['@']++v++u++v++['%']++grandInput

/-- The actual target arguments are the first header and the rest of each
original selected capture, including an empty second part in the child. -/
theorem actual_captures :
    let g := source header tails
    let h := target header tails
    let T := tblV g good .callByValuePar 8
    let U := tblV h good .callByValueSeq 8
    evV g good .callByValuePar T [] (argument header) good.length=
      some (some (u++['@']++childInput).length) ∧
    pre good good.length (u++['@']++childInput).length=power u 3 ∧
    evSeqArgs h good .callByValueSeq U [] [header.head,rest header] good.length=
      some (some ([u,power u 2],(u++['@']++childInput).length)) ∧
    evSeqArgs h good .callByValueSeq U [u,power u 2] [header.head,rest header] childInput.length=
      some (some ([v,[]],(v++['%']++grandInput).length)) ∧
    evSeqArgs h good .callByValueSeq U [v,[]] [header.head,rest header] grandInput.length=
      some (some ([z,z],(z++['!']++power z 2++['?']++power v 1++['?']++power u 3).length)) := by
  decide +kernel

/-- Capture counts 3→1→2 and lengths 5→3→1 survive return through both
callers. These are executions of the ordinary grammars and physical tables. -/
theorem executions :
    let eval := fun (x : List Char) =>
      (evV (source header tails) x .callByValuePar
        (tblV (source header tails) x .callByValuePar 12) [] (render header tails true root) x.length,
       evV (target header tails) x .callByValueSeq
        (tblV (target header tails) x .callByValueSeq 12) [] (render header tails false root) x.length)
    eval good=(some (some 0),some (some 0)) ∧
    eval shortParent=(some none,some none) ∧
    eval shortChild=(some none,some none) ∧
    eval unequalChild=(some none,some none) := by
  decide +kernel

theorem all_inputs (x : List Char) (r : Option (List Char)) :
    SObs (source header tails) .callByValuePar (render header tails true root) x r ↔
      SObs (target header tails) .callByValueSeq (render header tails false root) x r :=
  observations_iff header tails root x r

/-- First-header failure and finite failure before a user continuation
are retained after helper evaluation. -/
theorem early_failures :
    let eval := fun (text : String) =>
      let x := text.toList
      (evV (source header tails) x .callByValuePar (tblV (source header tails) x .callByValuePar 8) []
        (render header tails true root) x.length,
       evV (target header tails) x .callByValueSeq (tblV (target header tails) x .callByValueSeq 8) []
        (render header tails false root) x.length)
    eval "Z"=(some none,some none) ∧
    eval "ab#!ab#"=(some none,some none) := by
  decide +kernel

def cyclicHeader : Header := CodewordControlHelperExamples.cyclicHeader

/-- A nonproductive recursive header stays undefined at every input,
position and ordinary stage in the actual generated source and target. -/
theorem cyclic_header_undefined (x : List Char) (k p : Nat) (hp : p≤x.length)
    (E F : List (List Char)) :
    evV (source cyclicHeader tails) x .callByValuePar (tblV (source cyclicHeader tails) x .callByValuePar k)
      E (render cyclicHeader tails true root) p=none ∧
    evV (target cyclicHeader tails) x .callByValueSeq (tblV (target cyclicHeader tails) x .callByValueSeq k)
      F (render cyclicHeader tails false root) p=none := by
  apply undefined_argument cyclicHeader tails 0 (recursiveTail '@' 1) rfl x p _ _ E F
  · apply evV_seq_none
    exact RecursiveParserStability.cycle_undefined (by rfl) x .callByValuePar k E p hp
  · apply evV_seq_none
    exact RecursiveParserStability.cycle_undefined (by rfl) x .callByValueSeq k F p hp

theorem cyclic_header_no_observations (x : List Char) (r : Option (List Char)) :
    ¬SObs (source cyclicHeader tails) .callByValuePar (render cyclicHeader tails true root) x r ∧
    ¬SObs (target cyclicHeader tails) .callByValueSeq (render cyclicHeader tails false root) x r := by
  have hn : ¬SObs (source cyclicHeader tails) .callByValuePar (render cyclicHeader tails true root) x r := by
    rw [←decideObsV_iff (source_firstOrder cyclicHeader tails) (by decide)
      (render_firstOrder cyclicHeader tails true root)]
    simp only [decideObsV,(cyclic_header_undefined x _ x.length (Nat.le_refl _) [] []).1]
    simp
  exact ⟨hn,fun h => hn ((observations_iff cyclicHeader tails root x r).mpr h)⟩

end Shallot.MacroPeg.CBV.CodewordControlHelperGrammarExamples
