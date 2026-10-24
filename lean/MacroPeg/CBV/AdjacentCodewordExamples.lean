import MacroPeg.CBV.AdjacentCodewordControl

namespace Shallot.MacroPeg.CBV.AdjacentCodewordExamples
open RuntimeShiftFilter (scanner)
open CodewordControlFilter (wholeView)

def control : CodewordControlFilter.Expr := .star (.seq .token (.notP (.test (.param 0))))
def rest : MExp := CodewordControlFilter.render scanner control
def argument : MExp := .seq scanner rest

def tail : MExp := .seq
  (.alt (.chr '#') (.seq scanner (.chr '#')))
  (.seq (.chr '!') (.param 0))

def sourceChild : MExp := .call 2 [argument]
def targetChild : MExp := .seq (.andP argument)
  (.seq (.andP (AdjacentCodewordControl.filter scanner (.call 0 [scanner]) (.seq .token control)))
    (.call 2 [scanner,rest]))

def source : MGrammar := ⟨[
  ⟨1,.param 0⟩,
  ⟨1,.seq (.param 0) (.seq (.chr '@') sourceChild)⟩,
  ⟨1,.seq scanner (.seq (.param 0) tail)⟩]⟩
def target : MGrammar := ⟨[
  ⟨1,.param 0⟩,
  ⟨1,.seq (.chr '@') targetChild⟩,
  ⟨2,.seq (.param 0) (wholeView tail)⟩]⟩
def root : MExp := .call 1 [scanner]

def longer : List Char := "#@a#a#a##!a#a#".toList
def shorter : List Char := "a#@a#a#a##!a#".toList

/-- The parent's value is freshly captured from the input, and controls
whether the child retains one codeword or two. No parent parameter is
passed into the adjacent comparator rule. -/
theorem dynamic_parent_executions :
    let eval := fun (x : List Char) =>
      (evV source x .callByValuePar (tblV source x .callByValuePar 5) [] root x.length,
       evV target x .callByValueSeq (tblV target x .callByValueSeq 5) [] root x.length)
    eval longer=(some (some 0),some (some 0)) ∧
    eval shorter=(some (some 0),some (some 0)) ∧
    eval "#@a#a#a##!a#".toList=(some none,some none) ∧
    eval "a#@a#a#a##!".toList=(some none,some none) ∧
    eval "#@a#aa#a##!a#aa#".toList=(some none,some none) := by
  decide +kernel

/-- The same child input selects different actual captures solely because
its retained parent changes. The target keeps the corresponding two parts. -/
theorem actual_selected_parts :
    let x := "a#a#a##!a#a#".toList
    let T := tblV target x .callByValueSeq 5
    evSeqArgs target x .callByValueSeq T ["#".toList] [scanner,rest] x.length=
      some (some (["a#".toList,"a#".toList],8)) ∧
    evSeqArgs target x .callByValueSeq T ["a#".toList] [scanner,rest] x.length=
      some (some (["a#".toList,[]],10)) := by
  decide +kernel

/-- Original-argument preflight protects undefined nullable control before
an adjacent comparison could turn it into rejection. -/
theorem preflight_preserves_undefined :
    let d : CodewordControlFilter.Expr := .star (.test (.param 0))
    let B := .seq scanner (CodewordControlFilter.render scanner d)
    let x := "a#a#".toList
    let T := tblV target x .callByValueSeq 5
    evV target x .callByValueSeq T ["a#".toList] B x.length=none ∧
    evV target x .callByValueSeq T ["a#".toList]
      (.seq (.andP B) targetChild) x.length=none := by
  decide +kernel

end Shallot.MacroPeg.CBV.AdjacentCodewordExamples
