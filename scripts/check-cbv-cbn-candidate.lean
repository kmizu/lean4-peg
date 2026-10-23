import MacroPeg.CBVtoCBN.CompilerPlan

open Shallot.MacroPeg Shallot.MacroPeg.CBVtoCBN

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
   ("left-recursive-bottom", ⟨[⟨0, .alt (.call 0 []) .eps⟩]⟩, .call 0 [], 2),
   ("empty-iteration-bottom", ⟨[]⟩, .star .eps, 1),
   ("range", ⟨[]⟩, .range 'a' 'b', 1),
   ("literal-choice", ⟨[]⟩, .alt (.lit ['a', 'b']) (.lit ['b', 'a']), 1)]

/-- Executable checks of the candidate's real routing and evaluation, independent of its local template proofs.
These bounded examples do not establish preservation for arbitrary grammars or inputs. -/
def main : IO Unit := do
  let inputs := ["", "a", "b", "aa", "ab", "ba", "bb", "aaa", "aab", "abab", "aaaa", "bbbb"]
  let mut checked := 0
  for (label, source, start, digits) in cases do
    for strategy in [Strategy.callByValuePar, Strategy.callByValueSeq] do
      let target := compileCandidate source strategy start ['a', 'b'] digits
      for input in inputs do
        let expected := accepts (mpegRun source strategy 400 start input.toList)
        let actual := mpegRun target .callByName 10000 candidateStart input.toList
        if actual.isNone then
          throw (IO.userError s!"target fuel exhausted: {label}, sequential={strategy == .callByValueSeq}, input={input}")
        if accepts actual != expected then
          throw (IO.userError s!"acceptance mismatch: {label}, sequential={strategy == .callByValueSeq}, input={input}")
        checked := checked + 1
  IO.println s!"CBV-to-CBN candidate: {checked} comparisons passed; every target evaluation completed."
