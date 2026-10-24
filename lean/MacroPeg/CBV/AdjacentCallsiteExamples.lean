import MacroPeg.CBV.AdjacentCallsiteRecursive
import MacroPeg.CBV.RuntimePrefixExamples

namespace Shallot.MacroPeg.CBV.AdjacentCallsiteExamples
open AdjacentCallsiteRecursive
open RuntimeShiftFilter (block)
open CodewordReplay (power)

def header : Header := RuntimePrefixExamples.header

def two : Argument header where
  control := .token
  controlSyntax := LastCodewordGrammar.pure_syntax _ header.pure

def three : Argument header where
  control := .seq .token .token
  controlSyntax := ⟨LastCodewordGrammar.pure_syntax _ header.pure,
    LastCodewordGrammar.pure_syntax _ header.pure⟩

def dynamic : Argument header where
  control := .alt (.seq (.test (.param 0)) .eps) (.seq .token (.test header.head))
  controlSyntax := ⟨⟨True.intro,True.intro⟩,LastCodewordGrammar.pure_syntax _ header.pure,
    LastCodewordGrammar.pure_syntax _ header.pure⟩

def tails : List (Body header) := [
  .alt (.seq (.chr '@') (.seq (.call 1 dynamic) (.seq (.chr '?') (.param 0))))
    (.seq (.chr '!') (.param 0)),
  .seq (.lit (block 1)) (.seq (.chr '%') (.seq (.call 0 three) (.seq (.chr '?') (.param 0))))]
def root : Body header := .call 0 two

def grandInput : List Char := power (block 2) 4++['!']++power (block 2) 3++
  ['?']++block 1++['?']++power (block 1) 2
def childInput : List Char := power (block 1) 3++['%']++grandInput
def good : List Char := power (block 1) 3++['@']++childInput

/-- The same source user is called with two and three captured words at
different sites, with a parent-dependent single-word child between them. -/
theorem executions :
    let eval := fun (x : List Char) =>
      (evV (original header tails) x .callByValuePar
        (tblV (original header tails) x .callByValuePar 6) [] (sourceExpr header root) x.length,
       evV (target header tails) x .callByValueSeq
        (tblV (target header tails) x .callByValueSeq 6) [] (render header tails false root) x.length)
    eval good=(some (some 0),some (some 0)) ∧
    eval (good.take (good.length-2))=(some none,some none) ∧
    eval (power (block 1) 3++['@']++power (block 1) 3++['%']++power (block 2) 4++
      ['!']++power (block 2) 2++['?']++block 1++['?']++power (block 1) 2)=(some none,some none) := by
  decide +kernel

/-- Actual argument sourceExpr at each site, evaluated under its retained
parent, produces the three different splits (u,u), (u,eps), (v,v²). -/
theorem actual_captures :
    let h := target header tails
    let U := tblV h good .callByValueSeq 1
    evSeqArgs h good .callByValueSeq U [] [header.head,CodewordControlFilter.wholeView (rest header two)] good.length=
      some (some ([block 1,block 1],(block 1++['@']++childInput).length)) ∧
    evSeqArgs h good .callByValueSeq U [block 1,block 1]
      [header.head,CodewordControlFilter.wholeView (rest header dynamic)] childInput.length=
      some (some ([block 1,[]],(power (block 1) 2++['%']++grandInput).length)) ∧
    evSeqArgs h good .callByValueSeq U [block 1,[]]
      [header.head,CodewordControlFilter.wholeView (rest header three)] grandInput.length=
      some (some ([block 2,power (block 2) 2],(block 2++['!']++power (block 2) 3++
        ['?']++block 1++['?']++power (block 1) 2).length)) := by
  decide +kernel

/-- This argument's endpoint depends on the retained parent even though
other sites in the same grammar use their own fixed-count arguments. -/
theorem parent_controls_argument :
    let x := "a#a#a#!".toList
    let g := original header tails
    let T := tblV g x .callByValuePar 0
    evV g x .callByValuePar T [] (argument header dynamic) x.length=some (some 3) ∧
    evV g x .callByValuePar T [power (block 1) 2] (argument header dynamic) x.length=some (some 5) ∧
    evV g x .callByValuePar T [block 2] (argument header dynamic) x.length=some (some 3) := by
  decide +kernel

private theorem tails_scoped : ∀ b∈tails, Scoped tails.length b := by
  intro b hb
  simp only [tails,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl <;> simp [Scoped,tails]

def undefinedArgument : Argument header where
  control := .seq .token (.test (.star (.lit [])))
  controlSyntax := ⟨LastCodewordGrammar.pure_syntax _ header.pure,True.intro⟩

/-- Unequal early words cannot hide an undefined later argument node.
The call site's preflight preserves None at all ordinary source/target stages. -/
theorem undefined_stages (k m : Nat) :
    let x := "a#aa#".toList
    evV (original header tails) x .callByValuePar
      (tblV (original header tails) x .callByValuePar k) []
      (sourceExpr header (.call 0 undefinedArgument)) x.length=none ∧
    evV (target header tails) x .callByValueSeq
      (tblV (target header tails) x .callByValueSeq m) []
      (render header tails false (.call 0 undefinedArgument)) x.length=none := by
  let x := "a#aa#".toList
  let g := source header tails
  let h := target header tails
  let T := tblV g x .callByValuePar k
  let U := tblV h x .callByValueSeq m
  have hzero : evV g x .callByValuePar (tblV g x .callByValuePar 0) []
      (argument header undefinedArgument) x.length=none := by decide +kernel
  have harg := (LastCodewordGrammar.syntax_eval g g x .callByValuePar .callByValuePar
    (tblV g x .callByValuePar 0) T (tblV_ok g x .callByValuePar 0) [] _
    (argument_syntax header undefinedArgument) x.length (Nat.le_refl _)).symm.trans hzero
  have hh := undefined_call header tails undefinedArgument 0 tails[0] rfl x T U
    (tblV_ok g x .callByValuePar k) [] [] (parameters_empty header tails x T U)
    x.length (Nat.le_refl _) harg
  dsimp only [T,U,g,h] at hh
  rw [source_eq_original header tails tails_scoped,
    source_syntax header tails (.call 0 undefinedArgument) (by simp [Scoped,tails])] at hh
  exact hh

theorem all_inputs (x : List Char) (r : Option (List Char)) :
    SObs (original header tails) .callByValuePar (sourceExpr header root) x r ↔
      SObs (target header tails) .callByValueSeq (render header tails false root) x r := by
  apply original_observations header tails _ root _ x r
  · exact tails_scoped
  · simp [Scoped,tails,root]

end Shallot.MacroPeg.CBV.AdjacentCallsiteExamples
