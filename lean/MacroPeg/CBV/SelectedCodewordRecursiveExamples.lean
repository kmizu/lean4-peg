import MacroPeg.CBV.SelectedCodewordRecursive
import MacroPeg.CBV.RuntimePrefixExamples

/-! Selected stops, changing captures, mutual recursion, and parent reuse. -/
namespace Shallot.MacroPeg.CBV.SelectedCodewordRecursiveExamples
open SelectedCodewordRecursive
open RuntimeShiftFilter (block)
open CodewordReplay (power)

def header : Header where
  toHeader := RuntimePrefixExamples.header
  condition := .notP (.alt (.lit ['@']) (.alt (.lit ['%']) (.lit ['!'])))
  conditionPure := ⟨True.intro,True.intro,True.intro⟩

def recursiveTail (mark : Char) (next : Nat) : MExp :=
  .seq header.head
    (.alt (.seq (.lit [mark]) (.seq (.call next []) (.seq (.lit ['?']) (.param 0))))
      (.seq (.lit ['!']) (.param 0)))
def tails : List MExp := [recursiveTail '@' 1,recursiveTail '%' 0]
def root : MExp := .call 0 []

def grandInput : List Char := power (block 0) 3++block 1++['!']++power (block 0) 2++
  ['?']++power (block 2) 1++['?']++power (block 1) 3
def childInput : List Char := power (block 2) 2++block 0++['%']++grandInput
def good : List Char := power (block 1) 4++block 2++['@']++childInput

def shortParent : List Char := power (block 1) 4++block 2++['@']++
  power (block 2) 2++block 0++['%']++power (block 0) 3++block 1++['!']++power (block 0) 2++
  ['?']++power (block 2) 1++['?']++power (block 1) 2
def shortChild : List Char := power (block 1) 4++block 2++['@']++
  power (block 2) 2++block 0++['%']++power (block 0) 3++block 1++['!']++power (block 0) 2++
  ['?']++power (block 1) 1++['?']++power (block 1) 3
def unequalChild : List Char := power (block 1) 4++block 2++['@']++
  block 2++block 1++block 0++['%']++grandInput
def zeroGrandchild : List Char := power (block 1) 4++block 2++['@']++
  power (block 2) 2++block 0++['%']++block 0++block 1++['!']++
  ['?']++power (block 2) 1++['?']++power (block 1) 3

/-- Each capture stops before a final header and a later unequal header.
Counts 3→1→2 and lengths 2→3→1 are selected by the actual input. -/
theorem actual_captures :
    let g := source header tails
    let T := tblV g good .callByValuePar 1
    evV g good .callByValuePar T [] (argument header) good.length=
      some (some (block 1++block 2++['@']++childInput).length) ∧
    pre good good.length (block 1++block 2++['@']++childInput).length=power (block 1) 3 ∧
    evV g good .callByValuePar T [power (block 1) 3] (argument header) childInput.length=
      some (some (block 2++block 0++['%']++grandInput).length) ∧
    pre good childInput.length (block 2++block 0++['%']++grandInput).length=power (block 2) 1 ∧
    evV g good .callByValuePar T [power (block 2) 1] (argument header) grandInput.length=
      some (some (block 0++block 1++['!']++power (block 0) 2++['?']++power (block 2) 1++['?']++power (block 1) 3).length) ∧
    pre good grandInput.length
      (block 0++block 1++['!']++power (block 0) 2++['?']++power (block 2) 1++['?']++power (block 1) 3).length=power (block 0) 2 := by
  decide +kernel

/-- Ordinary physical tables, including return and whole parent reuse. -/
theorem executions :
    let eval := fun (x : List Char) =>
      (evV (source header tails) x .callByValuePar
        (tblV (source header tails) x .callByValuePar 6) [] (render header tails true root) x.length,
       evV (target header tails) x .callByValueSeq
        (tblV (target header tails) x .callByValueSeq 6) [] (render header tails false root) x.length)
    eval good=(some (some 0),some (some 0)) ∧
    eval shortParent=(some none,some none) ∧
    eval shortChild=(some none,some none) ∧
    eval unequalChild=(some none,some none) ∧
    eval zeroGrandchild=(some (some 0),some (some 0)) := by
  decide +kernel

theorem all_inputs (x : List Char) (r : Option (List Char)) :
    SObs (source header tails) .callByValuePar (render header tails true root) x r ↔
      SObs (target header tails) .callByValueSeq (render header tails false root) x r :=
  observations_iff header tails root x r

/-- With no captured word, the step fails and the verifier guard passes,
but the actual header fails. Both seeds must retain that real failure. -/
theorem zero_capture_failed_head :
    let x := ['Z']
    argumentAt header x 1=some (some 1) ∧
    probe header x 1=some (some 1) ∧
    valAt (sourceTable header tails x 0 1 [[]]) 1=some none ∧
    valAt (targetTable header tails x 0 1 [[]]) 1=some none ∧
    evV (target header tails) x .callByValueSeq (targetTable header tails x 0) []
      (render header tails false root) 1=some none := by
  decide +kernel

/-- A selected nonempty capture with unequal shifted words is rejected
before either recursive tail, backed by its actual failed source prefix. -/
theorem unequal_seed :
    let x := "a#aa#aaa#!".toList
    valAt (sourceTable header tails x 0 1 [block 1]) x.length=some none ∧
    probe header x x.length=some none ∧
    evV (target header tails) x .callByValueSeq (targetTable header tails x 0) []
      (render header tails false root) x.length=some none := by
  decide +kernel

def undefinedHeader : Header where
  toHeader := header.toHeader
  condition := .alt header.condition (.star (.lit []))
  conditionPure := ⟨header.conditionPure,True.intro⟩

/-- A later undefined stop prevents even an early unequal-header rejection,
for every user table and retained environment on both recursive grammars. -/
theorem undefined_condition (T U : ClockFreezing.Table) (E : List (List Char)) :
    let x := "a#aa#aaa#!".toList
    evV (source undefinedHeader tails) x .callByValuePar T E
      (render undefinedHeader tails true root) x.length=none ∧
    evV (target undefinedHeader tails) x .callByValueSeq U E
      (render undefinedHeader tails false root) x.length=none := by
  exact undefined_argument undefinedHeader tails 0 (recursiveTail '@' 1) rfl _ _
    (by decide +kernel) T U E

def loopingTails : List MExp := [.star (.lit [])]

theorem undefined_stages (k : Nat) :
    evV (source header loopingTails) ['#'] .callByValuePar
      (tblV (source header loopingTails) ['#'] .callByValuePar k) []
      (render header loopingTails true root) 1=none := by
  let g := source header loopingTails
  have hr : ruleAtM g.rules 1=some ⟨1,.seq (.seq header.head (.param 0)) (.star (.lit []))⟩ := rfl
  have hb : argumentAt header ['#'] 1=some (some 1) := by decide +kernel
  change evV g ['#'] .callByValuePar (tblV g ['#'] .callByValuePar k) [] (.call 1 [argument header]) 1=none
  rw [evV_call_par hr rfl (by decide)]
  simp only [evParArgs,argument_eval,hb]
  cases k with
  | zero => rfl
  | succ k =>
    rw [valAt_tblV_succ hr _ (by decide)]
    change evV g ['#'] .callByValuePar (tblV g ['#'] .callByValuePar k) [[]]
      (.seq (.seq header.head (.param 0)) (.star (.lit []))) 1=none
    have hh : evV g ['#'] .callByValuePar (tblV g ['#'] .callByValuePar k) [[]]
        (.seq header.head (.param 0)) 1=some (some 0) := by
      rw [prefix_eval]
      decide +kernel
    rw [evV_seq_ok hh,evV_star]
    apply evStar_stuck (j:=0)
    · simp [evV,Shallot.stripPrefix?,sfx]
    · omega

theorem undefined_observations (r : Option (List Char)) :
    ¬SObs (source header loopingTails) .callByValuePar (render header loopingTails true root) ['#'] r ∧
    ¬SObs (target header loopingTails) .callByValueSeq (render header loopingTails false root) ['#'] r := by
  have hn : ¬SObs (source header loopingTails) .callByValuePar (render header loopingTails true root) ['#'] r := by
    rw [←decideObsV_iff (source_firstOrder header loopingTails) (by decide)
      (render_firstOrder header loopingTails true root)]
    simp [decideObsV,undefined_stages]
  exact ⟨hn,fun h => hn ((observations_iff header loopingTails root ['#'] r).mpr h)⟩

end Shallot.MacroPeg.CBV.SelectedCodewordRecursiveExamples
