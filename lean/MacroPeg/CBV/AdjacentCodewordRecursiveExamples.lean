import MacroPeg.CBV.AdjacentCodewordRecursive
import MacroPeg.CBV.RuntimePrefixExamples

/-! Parent-dependent capture selection through mutually recursive users. -/
namespace Shallot.MacroPeg.CBV.AdjacentCodewordRecursiveExamples
open AdjacentCodewordRecursive
open RuntimeShiftFilter (block)
open CodewordReplay (power)

def header : Header where
  toHeader := RuntimePrefixExamples.header
  control := .alt (.seq (.test (.param 0)) .eps) (.seq .token (.test RuntimeShiftFilter.scanner))
  controlSyntax := ⟨⟨True.intro,True.intro⟩,
    LastCodewordGrammar.pure_syntax _ RuntimePrefixExamples.header.pure,
    LastCodewordGrammar.pure_syntax _ RuntimePrefixExamples.header.pure⟩

def tails : List MExp := [
  .alt (.seq (.chr '@') (.seq (.call 1 []) (.seq (.chr '?') (.param 0))))
    (.seq (.chr '!') (.param 0)),
  .seq RuntimeShiftFilter.scanner (.seq (.chr '%') (.seq (.call 0 []) (.seq (.chr '?') (.param 0))))]
def root : MExp := .call 0 []
def grandInput : List Char := power (block 2) 3++['!']++power (block 2) 2++
  ['?']++block 1++['?']++power (block 1) 2
def childInput : List Char := power (block 1) 3++['%']++grandInput
def good : List Char := power (block 1) 3++['@']++childInput

theorem executions :
    let eval := fun (x : List Char) =>
      (evV (source header tails) x .callByValuePar
        (tblV (source header tails) x .callByValuePar 6) [] (render header tails true root) x.length,
       evV (target header tails) x .callByValueSeq
        (tblV (target header tails) x .callByValueSeq 6) [] (render header tails false root) x.length)
    eval good=(some (some 0),some (some 0)) ∧
    eval (good.take (good.length-2))=(some none,some none) := by
  decide +kernel

/-- The same argument input selects two words without a parent, one word
with a matching two-word parent, and two words with a different parent. -/
theorem parent_dependent_capture :
    let x := "a#a#a#!".toList
    let g := source header tails
    let T := tblV g x .callByValuePar 1
    evV g x .callByValuePar T [] (argument header) x.length=some (some 3) ∧
    evV g x .callByValuePar T [power (block 1) 2] (argument header) x.length=some (some 5) ∧
    evV g x .callByValuePar T [block 2] (argument header) x.length=some (some 3) := by
  decide +kernel

/-- Actual Seq arguments split the source whole captures into pairs
(u,u), (u,eps), (v,v), including the caller-side view of each parent. -/
theorem actual_captures :
    let h := target header tails
    let U := tblV h good .callByValueSeq 1
    let args := [header.head,CodewordControlFilter.wholeView (rest header)]
    evSeqArgs h good .callByValueSeq U [] args good.length=
      some (some ([block 1,block 1],(block 1++['@']++childInput).length)) ∧
    evSeqArgs h good .callByValueSeq U [block 1,block 1] args childInput.length=
      some (some ([block 1,[]],(power (block 1) 2++['%']++grandInput).length)) ∧
    evSeqArgs h good .callByValueSeq U [block 1,[]] args grandInput.length=
      some (some ([block 2,block 2],(block 2++['!']++power (block 2) 2++
        ['?']++block 1++['?']++power (block 1) 2).length)) := by
  decide +kernel

/-- Reject malformed copies at all three recursion levels and an unequal
word inside the grandchild's selected two-word capture. -/
theorem rejects :
    let eval := fun (x : List Char) =>
      (evV (source header tails) x .callByValuePar
        (tblV (source header tails) x .callByValuePar 6) [] (render header tails true root) x.length,
       evV (target header tails) x .callByValueSeq
        (tblV (target header tails) x .callByValueSeq 6) [] (render header tails false root) x.length)
    let front :=  power (block 1) 3++['@']++power (block 1) 3++['%']
    eval (front++power (block 2) 3++['!']++block 2++
      ['?']++block 1++['?']++power (block 1) 2)=(some none,some none) ∧
    eval (front++power (block 2) 3++['!']++power (block 2) 2++
      ['?','?']++power (block 1) 2)=(some none,some none) ∧
    eval (front++block 2++block 1++block 2++['!']++power (block 2) 2++
      ['?']++block 1++['?']++power (block 1) 2)=(some none,some none) := by
  decide +kernel

def nullableHeader : Header where
  toHeader := RuntimePrefixExamples.header
  control := .star (.test (.param 0))
  controlSyntax := True.intro

/-- A successful nullable parent test loops inside the original argument.
Preflight preserves undefinedness even for arbitrary recursive tables. -/
theorem undefined_argument (T U : ClockFreezing.Table) :
    let x := "a#aa#".toList
    evV (source nullableHeader tails) x .callByValuePar T [[]]
      (render nullableHeader tails true root) x.length=none ∧
    evV (target nullableHeader tails) x .callByValueSeq U [[],[]]
      (render nullableHeader tails false root) x.length=none := by
  let x := "a#aa#".toList
  let g := source nullableHeader tails
  let h := target nullableHeader tails
  let Z := tblV g x .callByValuePar 0
  have hz : evV g x .callByValuePar Z [[]] (argument nullableHeader) x.length=none := by
    decide +kernel
  have hs := LastCodewordGrammar.syntax_eval g g x .callByValuePar .callByValuePar Z T
    (tblV_ok g x .callByValuePar 0) [[]] _ (argument_syntax nullableHeader) x.length (Nat.le_refl _)
  have ht := LastCodewordGrammar.syntax_eval g h x .callByValuePar .callByValueSeq Z U
    (tblV_ok g x .callByValuePar 0) [[]] _ (argument_syntax nullableHeader) x.length (Nat.le_refl _)
  constructor
  · change evV g x .callByValuePar T [[]] (.call 1 [argument nullableHeader]) x.length=none
    rw [evV_call_par (show ruleAtM g.rules 1=some
      ⟨1,.seq (.seq nullableHeader.head (.param 0)) (render nullableHeader tails true tails[0])⟩ from rfl)
      rfl (by decide)]
    simp only [evParArgs,hs.symm.trans hz]
  · apply evV_seq_none
    rw [CallLookahead.evV_peek,
      CodewordControlFilter.wholeView_eval h x .callByValueSeq U [] []
        (argument nullableHeader) (argument_firstOrder nullableHeader) x.length]
    simp only [List.nil_append]
    rw [ht.symm.trans hz]
    rfl

theorem all_inputs (x : List Char) (r : Option (List Char)) :
    SObs (source header tails) .callByValuePar (render header tails true root) x r ↔
      SObs (target header tails) .callByValueSeq (render header tails false root) x r :=
  observations_iff header tails root x r

end Shallot.MacroPeg.CBV.AdjacentCodewordRecursiveExamples
