import MacroPeg.CBV.FragmentOriginRecursive
import MacroPeg.CBV.FragmentConsumingRecursiveExamples

namespace Shallot.MacroPeg.CBV.FragmentOriginExamples
open ReplayControlFusion (Plan)
open FragmentOriginRecursive
open PartialCodewordCapture (look eof)

def plans : List Plan := [.guard (.notP (.leaf 3)) (.alt (.leaf 3) (.leaf 0)),.leaf 1,.leaf 2]
def tails : List MExp := FragmentConsumingRecursiveExamples.tails++[.lit ['Q']]
def root : MExp := FragmentConsumingRecursiveExamples.root

theorem valid : Valid plans tails := by
  simp [Valid,plans,tails,FragmentConsumingRecursiveExamples.tails,Plan.All]

/-- Actual 0→1→0 calls retain different parent values while each user-0
body first executes negative origin control and a prioritized fallback. -/
theorem mutual_origin_control :
    let x := "a#aZaaa#aaa#aYaa#aa!aa?aaa#a?a".toList
    evV (source plans tails) x .callByValuePar (tblV (source plans tails) x .callByValuePar 3)
      [] (render plans true false root) x.length=some (some 0) ∧
    evV (target plans tails) x .callByValueSeq (tblV (target plans tails) x .callByValueSeq 3)
      [] (render plans false false root) x.length=some (some 0) := by
  decide +kernel

theorem short_copies_rejected :
    ∀ x ∈ ["a#aZaaa#aaa#aYaa#aa!a?aaa#a?a".toList,
      "a#aZaaa#aaa#aYaa#aa!aa?aaa#?a".toList,
      "a#aZaaa#aaa#aYaa#aa!aa?aaa#a?".toList],
    evV (source plans tails) x .callByValuePar (tblV (source plans tails) x .callByValuePar 3)
      [] (render plans true false root) x.length=some none ∧
    evV (target plans tails) x .callByValueSeq (tblV (target plans tails) x .callByValueSeq 3)
      [] (render plans false false root) x.length=some none := by
  decide +kernel

/-- The argument really captures a, but the negative body succeeds at the
original position even though A cannot find a delimiter on this input. -/
theorem rollback_before_capture_endpoint :
    let ps : List Plan := [.notP (.leaf 0)]
    let ts := [MExp.lit []]
    let x := "a!".toList
    let e := MExp.call 0 [.eps,.chr 'a']
    let start := MExp.seq e (.seq (.lit ['a','!']) eof)
    evV (source ps ts) x .callByValuePar (tblV (source ps ts) x .callByValuePar 1) []
      (ControlledFragmentReplay.argument .eps (.chr 'a')) 2=some (some 1) ∧
    evV (source ps ts) x .callByValuePar (tblV (source ps ts) x .callByValuePar 1) []
      (render ps true false e) 2=some (some 2) ∧
    evV (target ps ts) x .callByValueSeq (tblV (target ps ts) x .callByValueSeq 1) []
      (render ps false false e) 2=some (some 2) ∧
    evV (source ps ts) x .callByValuePar (tblV (source ps ts) x .callByValuePar 1) []
      (render ps true false start) 2=some (some 0) ∧
    evV (target ps ts) x .callByValueSeq (tblV (target ps ts) x .callByValueSeq 1) []
      (render ps false false start) 2=some (some 0) := by
  decide +kernel

/-- Without the outer argument preview, the negative body would turn
argument failure into success. Both compiled calls preserve finite failure. -/
theorem argument_guard_is_needed :
    let ps : List Plan := [.notP (.leaf 0)]
    let ts := [MExp.lit []]
    let x := "#".toList
    let e := MExp.call 0 [.eps,.chr 'a']
    evV (source ps ts) x .callByValuePar (tblV (source ps ts) x .callByValuePar 1) []
      (render ps true false e) 1=some none ∧
    evV (target ps ts) x .callByValueSeq (tblV (target ps ts) x .callByValueSeq 1) []
      (render ps false false e) 1=some none ∧
    evV (target ps ts) x .callByValueSeq (tblV (target ps ts) x .callByValueSeq 1) []
      (.notP (FragmentConsumingEntry.entry 2 3 .eps (.chr 'a'))) 1=some (some 1) := by
  decide +kernel

/-- A negative body must not run before an undefined argument. -/
theorem argument_none_precedes_negative_body :
    let ps : List Plan := [.notP (.leaf 0)]
    let ts := [MExp.lit []]
    let x := "aaZ".toList
    let e := MExp.call 0 [.eps,.seq (.chr 'a') (.star .eps)]
    evV (source ps ts) x .callByValuePar (tblV (source ps ts) x .callByValuePar 1) []
      (render ps true false e) 3=none ∧
    evV (target ps ts) x .callByValueSeq (tblV (target ps ts) x .callByValueSeq 1) []
      (render ps false false e) 3=none := by
  decide +kernel

/-- A nullable negative success inside a caller's star remains undefined,
while a missing mandatory fragment still fails before this loop. -/
theorem rollback_star_is_undefined :
    let ps : List Plan := [.notP (.leaf 0)]
    let ts := [MExp.lit []]
    let x := "a!".toList
    let e := MExp.star (.call 0 [.eps,.chr 'a'])
    evV (source ps ts) x .callByValuePar (tblV (source ps ts) x .callByValuePar 1) []
      (render ps true false e) 2=none ∧
    evV (target ps ts) x .callByValueSeq (tblV (target ps ts) x .callByValueSeq 1) []
      (render ps false false e) 2=none := by
  decide +kernel

theorem zero_clock_failure_and_no_row :
    let ps : List Plan := [.notP (.leaf 0)]
    let ts := [MExp.lit []]
    let e := MExp.call 0 [.eps,.chr 'a']
    evV (source ps ts) "#".toList .callByValuePar (tblV (source ps ts) "#".toList .callByValuePar 0) []
      (render ps true false e) 1=some none ∧
    evV (target ps ts) "#".toList .callByValueSeq (tblV (target ps ts) "#".toList .callByValueSeq 0) []
      (render ps false false e) 1=some none ∧
    evV (source ps ts) "a!".toList .callByValuePar (tblV (source ps ts) "a!".toList .callByValuePar 0) []
      (render ps true false e) 2=none ∧
    evV (target ps ts) "a!".toList .callByValueSeq (tblV (target ps ts) "a!".toList .callByValueSeq 0) []
      (render ps false false e) 2=none := by
  decide +kernel

end Shallot.MacroPeg.CBV.FragmentOriginExamples
