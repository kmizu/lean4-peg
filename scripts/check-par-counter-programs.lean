import MacroPeg.CBV.PrefixTupleSearch
import MacroPeg.CBV.PrefixSpans
open Shallot.MacroPeg
open Shallot.MacroPeg.CBV.PrefixCounters

private def result (out : Option MOutcome) : Option (Option (List Char)) := out.map MOutcome.restOf
private def conj : List MExp → MExp
  | [] => .eps
  | a :: as => .seq a (conj as)
private def leafBody (d : Nat) : MExp :=
  conj (((List.range d).map fun i => atPosition (.param i) (.chr (if i % 2 = 0 then 'a' else 'b'))) ++
    [atPosition (.param d) (.chr 'c')])

def main : IO Unit := do
  let inputs := ["", "a", "b", "c", "ab", "abc", "bca", "caab", "ababc", "cccc"]
  let mut checked := 0
  for d in [0, 1, 2, 3] do
    let g : MGrammar := ⟨tupleRules 0 (2*d) d 1 ++ [⟨d+1, leafBody d⟩]⟩
    for input in inputs do
      let x := input.toList
      for ctx in List.range (x.length + 1) do
        let e := tupleSearch 0 (2*d) d [.lit (x.take ctx)]
        let actual := result (mpegRun g .callByValuePar 1000 e x)
        let expected := (x[ctx]? == some 'c') &&
          ((List.range d).all fun i => x.any fun c => c == (if i % 2 = 0 then 'a' else 'b'))
        let want := some (if expected then some x else none)
        if actual != want then
          throw (IO.userError s!"tuple search mismatch: d={d}, input={input}, context={ctx}")
        checked := checked + 1
  IO.println s!"Par tuple search: {checked} original-input checks passed"
  let mut carries := 0
  for input in inputs do
    let x := input.toList
    let n := x.length
    for ds in [[], [0], [n], [n, 0], [n, n], [0, n], [n, n, 0]] do
      let d := ds.length
      let g : MGrammar := ⟨[⟨2, equalBody 0⟩, ⟨1+d+1, successorBody 0 2 3 d 1⟩,
        ⟨1+d+1, .seq (.param 1) (.param (d+1))⟩, ⟨1, .param 0⟩]⟩
      let ctx := [n]
      let actual := result (mpegRun g .callByValuePar 1000 (.call 1 (prefixValues x (n :: (ds ++ ctx)))) x)
      let expected := match succClock n ds with
        | none => result (mpegRun g .callByValuePar 1000 (.call 3 (prefixValues x ctx)) x)
        | some out => result (mpegRun g .callByValuePar 1000 (.call 2 (prefixValues x (n :: (out ++ ctx)))) x)
      if actual != expected || actual.isNone then
        throw (IO.userError s!"successor mismatch: input={input}, digits={ds}")
      carries := carries + 1
  IO.println s!"Par successor: {carries} carry/overflow/context checks passed"
