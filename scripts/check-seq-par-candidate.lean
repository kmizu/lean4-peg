import MacroPeg.CBV.ParSimulation.Compiler

open Shallot.MacroPeg
open Shallot.MacroPeg.CBV.ParSimulation

private def accepts (result : Option MOutcome) : Bool :=
  match result with
  | some (.ok _ []) => true
  | _ => false

private def cases : List (String × MGrammar × MExp × Nat) :=
  [("star", ⟨[]⟩, .star (.chr 'a'), 1),
   ("negation", ⟨[]⟩, .seq (.notP (.chr 'b')) .any, 1),
   ("capture", ⟨[⟨1, .param 0⟩]⟩, .call 0 [.any], 2),
   ("capture-all", ⟨[⟨1, .param 0⟩]⟩, .call 0 [.star .any], 2),
   ("recursive", ⟨[⟨0, .alt (.seq (.chr 'a') (.call 0 [])) .eps⟩]⟩, .call 0 [], 2),
   ("replay-twice", ⟨[⟨1, .seq (.param 0) (.param 0)⟩]⟩, .call 0 [.any], 2),
   ("two-arguments", ⟨[⟨2, .seq (.param 0) (.param 1)⟩]⟩, .call 0 [.any, .any], 2),
   ("nested-capture", ⟨[⟨1, .param 0⟩, ⟨1, .param 0⟩]⟩, .call 0 [.call 1 [.any]], 3),
   ("forward-captured", ⟨[⟨2, .seq (.param 0) (.param 1)⟩,
       ⟨1, .call 0 [.param 0, .any]⟩]⟩, .call 1 [.any], 3),
   ("failure-first", ⟨[⟨2, .eps⟩]⟩, .call 0 [.notP .eps, .any], 2),
   ("unused-capture", ⟨[⟨1, .eps⟩]⟩, .call 0 [.star .any], 2),
   ("left-recursive-bottom", ⟨[⟨0, .alt (.call 0 []) .eps⟩]⟩, .call 0 [], 2),
   ("empty-iteration-bottom", ⟨[]⟩, .star .eps, 1),
   ("range", ⟨[]⟩, .range 'a' 'b', 1),
   ("literal-choice", ⟨[]⟩, .alt (.lit ['a', 'b']) (.lit ['b', 'a']), 1),
   ("missing-rule", ⟨[]⟩, .call 9 [.any], 1),
   ("wrong-arity", ⟨[⟨1, .eps⟩]⟩, .call 0 [.any, .any], 1),
   ("missing-param", ⟨[⟨1, .param 1⟩]⟩, .call 0 [.any], 2),
   ("negative-call", ⟨[⟨1, .param 0⟩]⟩, .seq (.notP (.call 0 [.any])) (.star .any), 2)]

/-- Routing checks for the real generated Par grammar. Finite examples do
not establish language-class inclusion or general compiler correctness. -/
def main : IO Unit := do
  let inputs := ["", "a", "b", "aa", "ab", "ba", "bb", "aaa", "aab", "abab", "aaaa", "bbbb"]
  let mut checked := 0
  for (label, source, start, digits) in cases do
    let target := compileCandidate source start ['a', 'b'] digits
    for input in inputs do
      let expected := accepts (mpegRun source .callByValueSeq 400 start input.toList)
      let actual := mpegRun target .callByValuePar 2000 candidateStart input.toList
      if actual.isNone then
        throw (IO.userError s!"target fuel exhausted: {label}, input={input}")
      if accepts actual != expected then
        throw (IO.userError s!"acceptance mismatch: {label}, input={input}")
      checked := checked + 1
    IO.println s!"passed {label}"
  IO.println s!"Seq-to-Par candidate: {checked} comparisons passed; every target evaluation completed."
