import MacroPeg.CBV.PartialCodewordGuardExamples

namespace Shallot.MacroPeg.CBV.PartialCodewordSuffixExamples
open PartialCodewordRecursive
open PartialCodewordCapture (look argument runA)

/-- Both users inspect the parent's value after the child's actual B
endpoint. The test still has the caller environment, not the child's. -/
def endpointTest : MExp := .seq (.lit ['#']) (.param 0)
def tails : List MExp := [
  .alt (.seq (.lit ['!']) (.param 0))
    (.seq (.lit ['Z']) (.seq (.call 1 [.eps,endpointTest]) (.seq (.lit ['?']) (.param 0)))),
  .seq (.lit ['Y']) (.seq (.call 0 [.eps,endpointTest]) (.seq (.lit ['?']) (.param 0)))]
def root : MExp := .seq (.call 0 []) PartialCodewordCapture.eof

/-- Actual captures a, aa, aaa#aaa and both returns preserve each parent's
value, while both argument tests execute after the respective capture. -/
theorem endpoint_parent_returns :
    let x := "a#aZaa#aaYaaa#aaa#aaa!aaa#aaa?aa?a".toList
    evV (source tails) x .callByValuePar (tblV (source tails) x .callByValuePar 3)
      [] (render tails true root) x.length=some (some 0) ∧
    evV (target tails) x .callByValueSeq (tblV (target tails) x .callByValueSeq 3)
      [] (render tails false root) x.length=some (some 0) := by
  decide +kernel

/-- Testing the same parent's value at the caller origin gives a different
answer: the correct test must consume # at B's endpoint first. -/
theorem endpoint_selects :
    let ts := [MExp.seq (.lit ['!']) (.param 0)]
    let x := "a#a!a".toList
    let e := MExp.call 0 [.eps,endpointTest]
    evV (source ts) x .callByValuePar (tblV (source ts) x .callByValuePar 1)
      [['a']] (render ts true e) x.length=some (some 0) ∧
    evV (target ts) x .callByValueSeq (tblV (target ts) x .callByValueSeq 1)
      [['a']] (render ts false e) x.length=some (some 0) ∧
    evV (source ts) x .callByValuePar (tblV (source ts) x .callByValuePar 1)
      [['a','a']] (render ts true e) x.length=some none ∧
    evV (target ts) x .callByValueSeq (tblV (target ts) x .callByValueSeq 1)
      [['a','a']] (render ts false e) x.length=some none ∧
    evV (source ts) x .callByValuePar (tblV (source ts) x .callByValuePar 1)
      [['a']] (render ts true (.call 0 [endpointTest])) x.length=some none := by
  decide +kernel

/-- The after-capture test can parse a fresh recursive user call; that
preview returns before the actual outer callee and its children run. -/
theorem recursive_endpoint_test :
    let x := "a#aZaa#aaYaaa#aaa#aaa!aaa#aaa?aa?a".toList
    let test := MExp.seq (.lit ['#']) (.seq runA (.seq (.lit ['Z']) (.call 1 [])))
    let e := MExp.seq (.call 0 [.eps,test]) PartialCodewordCapture.eof
    evV (source tails) x .callByValuePar (tblV (source tails) x .callByValuePar 3)
      [['a']] (render tails true e) x.length=some (some 0) ∧
    evV (target tails) x .callByValueSeq (tblV (target tails) x .callByValueSeq 3)
      [['a']] (render tails false e) x.length=some (some 0) := by
  decide +kernel

/-- Neither a missing parent's copy nor a short replay after returning is
repaired by retrying a different capture branch. -/
theorem rejected_endpoint_copy : ∀ x ∈
    ["aa#aaZa#aYaaa#aaa#aaa!aaa#aaa?a?aa".toList,
      "a#aZaa#aaYaaa#aaa#aaa!aaa#aaa?a?a".toList],
    evV (source tails) x .callByValuePar (tblV (source tails) x .callByValuePar 3)
      [] (render tails true root) x.length=some none ∧
    evV (target tails) x .callByValueSeq (tblV (target tails) x .callByValueSeq 3)
      [] (render tails false root) x.length=some none := by
  decide +kernel

/-- A divergent post-capture test is observed before callee entry failure,
for every input, valid position, caller environment, and pair of tables. -/
theorem undefined_after_capture (x : List Char) (p : Nat) (hp : p≤x.length)
    (E : List (List Char)) (T U : ClockFreezing.Table) :
    let e := MExp.call 0 [.eps,.star (.lit [])]
    evV (source tails) x .callByValuePar T E (render tails true e) p=none ∧
    evV (target tails) x .callByValueSeq U E (render tails false e) p=none := by
  obtain ⟨j,hj⟩ := PartialCodewordTotality.argument_total ⟨[]⟩ x .callByValuePar
    (tblV ⟨[]⟩ x .callByValuePar 0) (tblV_ok _ _ _ 0) [] p hp
  have hjvalid := evV_ok (tblV_ok ⟨[]⟩ x .callByValuePar 0) argument p hp j hj
  have ha (g : MGrammar) (s : Strategy) (V : ClockFreezing.Table) :
      evV g x s V E argument p=some (some j) := by
    rw [PartialCodewordTotality.argument_context g ⟨[]⟩ x s .callByValuePar V
      (tblV ⟨[]⟩ x .callByValuePar 0) E [] p]
    exact hj
  have hloop (g : MGrammar) (s : Strategy) (V : ClockFreezing.Table) :
      evV g x s V E (.star (.lit [])) j=none := by
    rw [evV_star]
    apply evStar_stuck (j:=j)
    · simp [evV,Shallot.stripPrefix?,length_sfx x hjvalid]
    · omega
  have hlookloop (g : MGrammar) (s : Strategy) (V : ClockFreezing.Table) :
      evV g x s V E (look (.star (.lit []))) j=none := by
    change evV _ _ _ _ _ (.andP (.star (.lit []))) j=none
    rw [CallLookahead.evV_peek,hloop]; rfl
  have hpre (g : MGrammar) (s : Strategy) (V : ClockFreezing.Table) :
      evV g x s V E (look .eps) p=some (some p) := rfl
  constructor
  · change evV (source tails) x .callByValuePar T E
      (.call 0 [.seq (look .eps) (.seq argument (look (.star (.lit []))))]) p=none
    have harg : evV (source tails) x .callByValuePar T E
        (.seq (look .eps) (.seq argument (look (.star (.lit []))))) p=none := by
      rw [evV_seq_ok (hpre _ _ _),evV_seq_ok (ha _ _ _),hlookloop]
    rw [evV_call_par (source_rule tails 0 _ rfl) rfl (by decide)]
    simp only [evParArgs,harg]
  · change evV (target tails) x .callByValueSeq U E
      (.seq (look .eps) (.seq (look (.seq argument (.star (.lit []))))
        (PartialCodewordEntry.entry 1 2))) p=none
    have hpreview : evV (target tails) x .callByValueSeq U E
        (look (.seq argument (.star (.lit [])))) p=none := by
      change evV _ _ _ _ _ (.andP (.seq argument (.star (.lit [])))) p=none
      rw [CallLookahead.evV_peek,evV_seq_ok (ha _ _ _),hloop]; rfl
    rw [evV_seq_ok (hpre _ _ _),evV_seq_none hpreview]

end Shallot.MacroPeg.CBV.PartialCodewordSuffixExamples
