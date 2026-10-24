import MacroPeg.CBV.LastCodewordRecursive
import MacroPeg.CBV.RuntimePrefixExamples

/-! Unbounded-count captures can pass through mutual recursion and return
to the unchanged whole parent capture. -/
namespace Shallot.MacroPeg.CBV.LastCodewordRecursiveExamples
open LastCodewordRecursive
open RuntimePrefixExamples (header)
open RuntimeShiftFilter (block)
open CodewordReplay (power)

def recursiveTail (mark : Char) (next : Nat) : MExp :=
  .alt (.seq (.lit [mark]) (.seq (.call next []) (.seq (.lit ['?']) (.param 0))))
    (.seq (.lit ['!']) (.param 0))
def tails : List MExp := [recursiveTail '@' 1,recursiveTail '%' 0]
def root : MExp := .call 0 []

def grandInput : List Char := power (block 0) 3++['!']++power (block 0) 2++
  ['?']++power (block 2) 1++['?']++power (block 1) 3
def childInput : List Char := power (block 2) 2++['%']++grandInput
def good : List Char := power (block 1) 4++['@']++childInput

def shortParent : List Char := "a#a#a#a#@aa#aa#%###!##?aa#?a#a#".toList
def shortChild : List Char := "a#a#a#a#@aa#aa#%###!##?a#?a#a#a#".toList
def unequalChild : List Char := "a#a#a#a#@aa#a#%###!##?aa#?a#a#a#".toList

/-- These are the actual source argument evaluations, at the three input
positions reached by recursive calls. Counts are 3→1→2 and runtime headers
are a#→aa#→#. All three values are retained as whole strings. -/
theorem actual_captures :
    let g := source header tails
    let T := tblV g good .callByValuePar 1
    evV g good .callByValuePar T [] (argument header) good.length=
      some (some (block 1++['@']++childInput).length) ∧
    pre good good.length (block 1++['@']++childInput).length=power (block 1) 3 ∧
    evV g good .callByValuePar T [power (block 1) 3] (argument header) childInput.length=
      some (some (block 2++['%']++grandInput).length) ∧
    pre good childInput.length (block 2++['%']++grandInput).length=power (block 2) 1 ∧
    evV g good .callByValuePar T [power (block 2) 1] (argument header) grandInput.length=
      some (some (block 0++['!']++power (block 0) 2++['?']++power (block 2) 1++['?']++power (block 1) 3).length) ∧
    pre good grandInput.length
      (block 0++['!']++power (block 0) 2++['?']++power (block 2) 1++['?']++power (block 1) 3).length=power (block 0) 2 := by
  decide +kernel

/-- Actual ordinary tables verify both directions through the recursive
calls, and reject short child/parent copies and unequal child headers. -/
theorem executions :
    evV (source header tails) good .callByValuePar
      (tblV (source header tails) good .callByValuePar 6) [] (render header tails true root) good.length=some (some 0) ∧
    evV (target header tails) good .callByValueSeq
      (tblV (target header tails) good .callByValueSeq 6) [] (render header tails false root) good.length=some (some 0) ∧
    evV (source header tails) shortParent .callByValuePar
      (tblV (source header tails) shortParent .callByValuePar 6) [] (render header tails true root) shortParent.length=some none ∧
    evV (target header tails) shortParent .callByValueSeq
      (tblV (target header tails) shortParent .callByValueSeq 6) [] (render header tails false root) shortParent.length=some none ∧
    evV (source header tails) shortChild .callByValuePar
      (tblV (source header tails) shortChild .callByValuePar 6) [] (render header tails true root) shortChild.length=some none ∧
    evV (target header tails) shortChild .callByValueSeq
      (tblV (target header tails) shortChild .callByValueSeq 6) [] (render header tails false root) shortChild.length=some none ∧
    evV (source header tails) unequalChild .callByValuePar
      (tblV (source header tails) unequalChild .callByValuePar 6) [] (render header tails true root) unequalChild.length=some none ∧
    evV (target header tails) unequalChild .callByValueSeq
      (tblV (target header tails) unequalChild .callByValueSeq 6) [] (render header tails false root) unequalChild.length=some none := by
  decide +kernel

/-- The example grammar's complete observations agree for every string,
not just the finite executions above. -/
theorem all_inputs (x : List Char) (r : Option (List Char)) :
    SObs (source header tails) .callByValuePar (render header tails true root) x r ↔
      SObs (target header tails) .callByValueSeq (render header tails false root) x r :=
  observations_iff header tails root x r

/-- The chosen source prefix has definitely rejected, so seeding is backed
by a real finite computation before either recursive tail is queried. -/
theorem unequal_seed :
    let x := "a#aa#!".toList
    valAt (sourceTable header tails x 0 1 [block 1]) x.length=some none ∧
    probe header x x.length=some none ∧
    evV (target header tails) x .callByValueSeq (targetTable header tails x 0) []
      (render header tails false root) x.length=some none := by
  decide +kernel

def loopingTails : List MExp := [.star (.lit [])]

/-- Successful last-header consumption followed by a nullable loop stays
undefined at every ordinary source stage, including the uninitialized row. -/
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
    have he := LastCodewordGrammar.syntax_eval g g ['#'] .callByValuePar .callByValuePar
      (tblV g ['#'] .callByValuePar k) (tblV g ['#'] .callByValuePar 0)
      (tblV_ok g ['#'] .callByValuePar k) [pre ['#'] 1 1]
      (.seq (.seq header.head (.param 0)) (.star (.lit [])))
      ⟨⟨LastCodewordGrammar.pure_syntax _ header.pure,True.intro⟩,True.intro⟩ 1 (by decide)
    rw [he]
    decide +kernel

theorem undefined_observations (r : Option (List Char)) :
    ¬SObs (source header loopingTails) .callByValuePar (render header loopingTails true root) ['#'] r ∧
    ¬SObs (target header loopingTails) .callByValueSeq (render header loopingTails false root) ['#'] r := by
  have hs : ¬SObs (source header loopingTails) .callByValuePar (render header loopingTails true root) ['#'] r := by
    rw [←decideObsV_iff (source_firstOrder header loopingTails) (by decide)
      (render_firstOrder header loopingTails true root)]
    simp [decideObsV,undefined_stages]
  exact ⟨hs,fun ht => hs ((observations_iff header loopingTails root ['#'] r).mpr ht)⟩

end Shallot.MacroPeg.CBV.LastCodewordRecursiveExamples
