import MacroPeg.CBV.PrefixCodeCapture

/-! Physical recursive examples for the runtime representation. The general
local entry identity is `two_header_entry`; these examples do not assert an
unbounded source/target grammar correspondence. -/
namespace Shallot.MacroPeg.CBV.PrefixCodeCaptureExamples
open PrefixCodeCapture (duplicate view)
open RuntimeShiftFilter (scanner)

def argument : MExp := .seq scanner scanner
def sourceCall : MExp := .call 0 [argument]
def targetCall : MExp := .seq (.andP argument) (.call 0 [scanner])

def tail (copy next : MExp) : MExp :=
  .alt (.seq (.lit ['@']) (.seq next (.seq (.lit ['?']) copy))) (.lit ['!'])

def source : MGrammar := ⟨[⟨1,.seq scanner (.seq (.param 0) (tail (.param 0) sourceCall))⟩]⟩
def target : MGrammar := ⟨[⟨1,.seq duplicate (tail duplicate targetCall)⟩]⟩

def good : List Char := "aa#aa#aa#@aaa#aaa#aaa#!?aa#aa#".toList
def shortParent : List Char := "aa#aa#aa#@aaa#aaa#aaa#!?aa#".toList
def unequalChild : List Char := "aa#aa#aa#@aaa#aa#aaa#!?aa#aa#".toList

/-- Parent and child have different unbounded runtime periods. Each source
capture crosses a delimiter; the original parent capture is reused after
the child returns. Both actual grammars accept the same unchanged string. -/
theorem recursive_execution :
    evV source good .callByValuePar (tblV source good .callByValuePar 6) [] sourceCall good.length=some (some 0) ∧
    evV target good .callByValueSeq (tblV target good .callByValueSeq 6) [] targetCall good.length=some (some 0) ∧
    evV source shortParent .callByValuePar (tblV source shortParent .callByValuePar 6) [] sourceCall shortParent.length=some none ∧
    evV target shortParent .callByValueSeq (tblV target shortParent .callByValueSeq 6) [] targetCall shortParent.length=some none ∧
    evV source unequalChild .callByValuePar (tblV source unequalChild .callByValuePar 6) [] sourceCall unequalChild.length=some none ∧
    evV target unequalChild .callByValueSeq (tblV target unequalChild .callByValueSeq 6) [] targetCall unequalChild.length=some none := by
  decide +kernel

end Shallot.MacroPeg.CBV.PrefixCodeCaptureExamples
