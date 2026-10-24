import MacroPeg.CBV.PartialCodewordRecursiveExamples

namespace Shallot.MacroPeg.CBV.PartialCodewordGuardExamples
open PartialCodewordRecursive
open PartialCodewordCapture (look argument)

/-- A singleton template argument denotes a caller-position test before B.
Both nested calls consult the parent's held value while selecting B. -/
def tails : List MExp := [
  .alt (.seq (.lit ['!']) (.param 0))
    (.seq (.lit ['Z']) (.seq (.call 1 [.param 0]) (.seq (.lit ['?']) (.param 0)))),
  .seq (.lit ['Y']) (.seq (.call 0 [.param 0]) (.seq (.lit ['?']) (.param 0)))]
def root : MExp := .seq (.call 0 []) PartialCodewordCapture.eof

/-- Parent a#a selects child a, child a selects grandchild aa; the
original parent values remain available after both returns. -/
theorem parent_dependent_returns :
    let x := "a#a#aZa#aYaa#aa!aa?a?a#a".toList
    evV (source tails) x .callByValuePar (tblV (source tails) x .callByValuePar 3)
      [] (render tails true root) x.length=some (some 0) ∧
    evV (target tails) x .callByValueSeq (tblV (target tails) x .callByValueSeq 3)
      [] (render tails false root) x.length=some (some 0) := by
  decide +kernel

/-- The same physical input and callee are accepted or rejected solely
because the caller's held value changes the actual argument test. -/
theorem retained_value_selects :
    let ts := [MExp.seq (.lit ['!']) (.param 0)]
    let x := "a#a!a".toList
    let e := MExp.call 0 [.param 0]
    evV (source ts) x .callByValuePar (tblV (source ts) x .callByValuePar 1)
      [['a']] (render ts true e) x.length=some (some 0) ∧
    evV (target ts) x .callByValueSeq (tblV (target ts) x .callByValueSeq 1)
      [['a']] (render ts false e) x.length=some (some 0) ∧
    evV (source ts) x .callByValuePar (tblV (source ts) x .callByValuePar 1)
      [['b']] (render ts true e) x.length=some none ∧
    evV (target ts) x .callByValueSeq (tblV (target ts) x .callByValueSeq 1)
      [['b']] (render ts false e) x.length=some none := by
  decide +kernel

/-- The test itself can call users, with fresh captures inside that test.
It returns to the caller origin before the actual argument is captured. -/
theorem recursive_argument_test :
    let x := "a#a#aZa#aYaa#aa!aa?a?a#a".toList
    let e := MExp.seq (.call 0 [.call 0 []]) PartialCodewordCapture.eof
    evV (source tails) x .callByValuePar (tblV (source tails) x .callByValuePar 3)
      [] (render tails true e) x.length=some (some 0) ∧
    evV (target tails) x .callByValueSeq (tblV (target tails) x .callByValueSeq 3)
      [] (render tails false e) x.length=some (some 0) := by
  decide +kernel

/-- A missing or short held copy in a nested argument causes real failure
before that callee runs, in both grammars. -/
theorem bad_nested_argument : ∀ x ∈
    ["a#a#aZaa#aaYaa#aa!aa?aa?a#a".toList,
      "a#a#aZa#aY##!#?a?a#a".toList],
    evV (source tails) x .callByValuePar (tblV (source tails) x .callByValuePar 3)
      [] (render tails true root) x.length=some none ∧
    evV (target tails) x .callByValueSeq (tblV (target tails) x .callByValueSeq 3)
      [] (render tails false root) x.length=some none := by
  decide +kernel

/-- Undefined argument tests run before even malformed-prefix rejection.
This holds for all inputs, positions, caller environments, and user tables. -/
theorem undefined_test (x : List Char) (p : Nat) (T U : ClockFreezing.Table)
    (E : List (List Char)) (hp : p≤x.length) :
    let e := MExp.call 0 [.star (.lit [])]
    evV (source tails) x .callByValuePar T E (render tails true e) p=none ∧
    evV (target tails) x .callByValueSeq U E (render tails false e) p=none := by
  have hlo (g : MGrammar) (s : Strategy) (V : ClockFreezing.Table) :
      evV g x s V E (look (.star (.lit []))) p=none := by
    change evV g x s V E (.andP (.star (.lit []))) p=none
    rw [CallLookahead.evV_peek]
    have hstar : evV g x s V E (.star (.lit [])) p=none := by
      rw [evV_star]
      apply evStar_stuck (j:=p)
      · simp [evV,Shallot.stripPrefix?,length_sfx x hp]
      · omega
    rw [hstar]; rfl
  constructor
  · change evV (source tails) x .callByValuePar T E
      (.call 0 [.seq (look (.star (.lit []))) argument]) p=none
    rw [ArgumentGuard.call_eq _ _ _ _ _ _ _ _ _ (source_rule tails 0 _ rfl),
      evV_seq_none (hlo _ _ _)]
  · change evV (target tails) x .callByValueSeq U E
      (.seq (look (.star (.lit []))) (PartialCodewordEntry.entry 1 2)) p=none
    exact evV_seq_none (hlo _ _ _)

end Shallot.MacroPeg.CBV.PartialCodewordGuardExamples
