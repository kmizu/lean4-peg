import MacroPeg.CBV.FragmentConsumingRecursive

namespace Shallot.MacroPeg.CBV.FragmentConsumingRecursiveExamples
open FragmentConsumingRecursive
open PartialCodewordCapture (look eof)

def middle : MExp := .seq (.chr 'a') (.star (.seq (.chr 'a')
  (look (.notP (.call 2 [.eps,.star (.chr 'a')])))))
def choice : MExp := .alt (.lit ['a','a']) (.lit ['a'])
def tails : List MExp := [
  .alt (.seq (.lit ['!']) (.param 0))
    (.seq (.lit ['Z']) (.seq (.call 1 [.eps,middle])
      (.seq (.lit ['?']) (.param 0)))),
  .seq (.lit ['Y']) (.seq (.call 0 [.eps,choice]) (.seq (.lit ['?']) (.param 0))),
  .lit ['Y']]
def root : MExp := .seq (.call 0 [.eps,choice]) eof

/-- Different mandatory/choice fragments capture a → aaa#a → aa across
0→1→0 recursion. A recursive user-2 test stops the middle fragment;
the caller's entire value is reused after each return. -/
theorem mutual_returns :
    let x := "a#aZaaa#aaa#aYaa#aa!aa?aaa#a?a".toList
    evV (source tails) x .callByValuePar (tblV (source tails) x .callByValuePar 3)
      [] (render tails true false root) x.length=some (some 0) ∧
    evV (target tails) x .callByValueSeq (tblV (target tails) x .callByValueSeq 3)
      [] (render tails false false root) x.length=some (some 0) := by
  decide +kernel

/-- The actual child argument and real Seq pieces have the same endpoint;
the grandchild captures a different value in its own caller environment. -/
theorem actual_child_and_grandchild_captures :
    let x := "a#aZaaa#aaa#aYaa#aa!aa?aaa#a?a".toList
    let p := "aaa#aaa#aYaa#aa!aa?aaa#a?a".toList.length
    let q := p-5
    let r := "aa#aa!aa?aaa#a?a".toList.length
    let T := tblV (source tails) x .callByValuePar 2
    let U := tblV (target tails) x .callByValueSeq 2
    evV (source tails) x .callByValuePar T [['a']]
      (ControlledFragmentReplay.argument .eps (render tails true true middle)) p=some (some q) ∧
    pre x p q="aaa#a".toList ∧
    evSeqArgs (target tails) x .callByValueSeq U [['a']]
      [PartialCodewordCapture.runA,
        .seq (.lit ['#']) (.star (ControlledPartialCapture.step .eps)),
        render tails false true middle] p=some (some (["aaa".toList,['#'],['a']],q)) ∧
    evV (source tails) x .callByValuePar
      (tblV (source tails) x .callByValuePar 1) ["aaa#a".toList]
      (ControlledFragmentReplay.argument .eps (render tails true true choice)) r=some (some (r-2)) ∧
    pre x r (r-2)="aa".toList := by
  decide +kernel

theorem short_parent_child_grandchild_rejected :
    ∀ x ∈ ["a#aZaaa#aaa#aYaa#aa!a?aaa#a?a".toList,
      "a#aZaaa#aaa#aYaa#aa!aa?aaa#?a".toList,
      "a#aZaaa#aaa#aYaa#aa!aa?aaa#a?".toList],
    evV (source tails) x .callByValuePar (tblV (source tails) x .callByValuePar 3)
      [] (render tails true false root) x.length=some none ∧
    evV (target tails) x .callByValueSeq (tblV (target tails) x .callByValueSeq 3)
      [] (render tails false false root) x.length=some none := by
  decide +kernel

/-- The very same user is probed in the consuming H: its fresh short
capture succeeds, preventing another a from being added to the outer H. -/
theorem same_user_probe :
    let ts := [MExp.seq (.lit ['X','!']) (.param 0)]
    let H := MExp.seq (.chr 'a') (.star (.seq (.chr 'a')
      (look (.notP (.call 0 [.eps,.star (.chr 'a')])))))
    let e := MExp.seq (.call 0 [.eps,H]) eof
    let x := "aaa#aaa#aX!aaa#a".toList
    evV (source ts) x .callByValuePar (tblV (source ts) x .callByValuePar 2)
      [] (render ts true false e) x.length=some (some 0) ∧
    evV (target ts) x .callByValueSeq (tblV (target ts) x .callByValueSeq 2)
      [] (render ts false false e) x.length=some (some 0) := by
  decide +kernel

/-- The later replay cannot choose a instead of a successful aa fragment. -/
theorem consuming_choice_commit :
    let ts := [MExp.seq (.lit ['X','!']) (.param 0)]
    let e := MExp.seq (.call 0 [.eps,choice]) eof
    ∀ xp ∈ [("aaa#aaa#aaX!aaa#aa".toList,some (some 0)),
      ("aaa#aaa#aX!aaa#a".toList,some none)],
    evV (source ts) xp.1 .callByValuePar (tblV (source ts) xp.1 .callByValuePar 1)
      [] (render ts true false e) xp.1.length=xp.2 ∧
    evV (target ts) xp.1 .callByValueSeq (tblV (target ts) xp.1 .callByValueSeq 1)
      [] (render ts false false e) xp.1.length=xp.2 := by
  decide +kernel

/-- G selects a complete-word stop while mandatory H uses a parent-side
comparison to stop inside the next word. Both controls remain active. -/
theorem both_controls_and_parent :
    let ts := [MExp.seq RuntimeShiftFilter.scanner (.seq (.lit ['X','!']) (.param 0))]
    let H := MExp.seq (.chr 'a') (.star (.seq (.chr 'a') (look (.notP (.seq (.param 0) (.lit ['#']))))))
    let e := MExp.seq (.call 0 [.notP (.lit ['X']),H]) eof
    let x := "aaa#aaa#aaa#X!aaa#a".toList
    evV (source ts) x .callByValuePar (tblV (source ts) x .callByValuePar 1)
      [['a']] (render ts true false e) x.length=some (some 0) ∧
    evV (target ts) x .callByValueSeq (tblV (target ts) x .callByValueSeq 1)
      [['a']] (render ts false false e) x.length=some (some 0) := by
  decide +kernel

/-- Empty successful fragments and zero complete words still select
real unary/ternary branches and retain exactly the original whole value. -/
theorem empty_fragments :
    let ts := [MExp.seq (.lit ['X','!']) (.param 0)]
    let H := MExp.alt (.notP (.lit ['Z'])) (.chr 'a')
    let e := MExp.seq (.call 0 [.eps,H]) eof
    ∀ x ∈ ["#X!".toList,"aaa#aaa#X!aaa#".toList],
    evV (source ts) x .callByValuePar (tblV (source ts) x .callByValuePar 1)
      [] (render ts true false e) x.length=some (some 0) ∧
    evV (target ts) x .callByValueSeq (tblV (target ts) x .callByValueSeq 1)
      [] (render ts false false e) x.length=some (some 0) := by
  decide +kernel

/-- Actual argument failure remains observable at every ordinary clock,
including zero; no helper/callee row is consulted first. -/
theorem mandatory_failure (m : Nat) :
    let ts := [MExp.lit []]
    let e := MExp.call 0 [.eps,.chr 'a']
    let x := "#X!".toList
    evV (source ts) x .callByValuePar (tblV (source ts) x .callByValuePar m)
      [] (render ts true false e) x.length=some none ∧
    evV (target ts) x .callByValueSeq (tblV (target ts) x .callByValueSeq m)
      [] (render ts false false e) x.length=some none := by
  dsimp only []
  have hs : evV (source [.lit []]) "#X!".toList .callByValuePar
      (tblV (source [.lit []]) "#X!".toList .callByValuePar m) []
      (render [.lit []] true false (.call 0 [.eps,.chr 'a'])) 3=some none := by
    let g := source [MExp.lit []]
    let x := "#X!".toList
    let T := tblV g x .callByValuePar m
    have harg : evV g x .callByValuePar T []
        (ControlledFragmentReplay.argument .eps (.chr 'a')) 3=some none := by
      have hpure : ParserPrefixFusion.Pure (ControlledFragmentReplay.argument .eps (.chr 'a')) := by
        simp [ControlledFragmentReplay.argument,ControlledPartialCapture.step,look,RuntimeShiftFilter.scanner,
          NestedScannerArguments.scan,NestedScannerArguments.choice,MExp.failAlways,ParserPrefixFusion.Pure]
      rw [ParserPrefixFusion.pure_eval g ⟨[]⟩ x .callByValuePar .callByValuePar T
        (fun _ _ => []) [] [] _ hpure 3]
      decide +kernel
    change evV g x .callByValuePar T [] (.call 0 [ControlledFragmentReplay.argument .eps (.chr 'a')]) 3=some none
    rw [evV_call_par (source_rule [.lit []] 0 (.lit []) rfl) rfl (by decide)]
    change (match (match evV g x .callByValuePar T []
        (ControlledFragmentReplay.argument .eps (.chr 'a')) 3 with
      | some (some j) => some (some [pre x 3 j]) | some none => some none | none => none) with
      | some (some W) => valAt (T 0 W) 3 | some none => some none | none => none)=some none
    rw [harg]
  exact ⟨hs,(evaluator_eq [.lit []] "#X!".toList m false _ [] 3 (by decide)).symm.trans hs⟩

/-- Consuming a before a nested nullable loop preserves None before
any missing-delimiter failure, at every ordinary source/target clock. -/
theorem consuming_then_undefined (m : Nat) :
    let ts := [MExp.lit []]
    let e := MExp.call 0 [.eps,.seq (.chr 'a') (.star .eps)]
    let x := "aaZ".toList
    evV (source ts) x .callByValuePar (tblV (source ts) x .callByValuePar m)
      [] (render ts true false e) x.length=none ∧
    evV (target ts) x .callByValueSeq (tblV (target ts) x .callByValueSeq m)
      [] (render ts false false e) x.length=none := by
  dsimp only []
  have hs : evV (source [.lit []]) "aaZ".toList .callByValuePar
      (tblV (source [.lit []]) "aaZ".toList .callByValuePar m) []
      (render [.lit []] true false (.call 0 [.eps,.seq (.chr 'a') (.star .eps)])) 3=none := by
    let g := source [MExp.lit []]
    let x := "aaZ".toList
    let T := tblV g x .callByValuePar m
    have hstep : evV g x .callByValuePar T [] (ControlledPartialCapture.step .eps) 3=some none := by
      have hpure : ParserPrefixFusion.Pure (ControlledPartialCapture.step .eps) := by
        simp [ControlledPartialCapture.step,look,RuntimeShiftFilter.scanner,
          NestedScannerArguments.scan,NestedScannerArguments.choice,MExp.failAlways,ParserPrefixFusion.Pure]
      rw [ParserPrefixFusion.pure_eval g ⟨[]⟩ x .callByValuePar .callByValuePar T
        (fun _ _ => []) [] [] _ hpure 3]
      decide +kernel
    have hstar : evV g x .callByValuePar T [] (.star (ControlledPartialCapture.step .eps)) 3=
        some (some 3) := evStar_fail hstep
    have hloop : evV g x .callByValuePar T [] (.star .eps) 2=none :=
      evStar_stuck (j:=2) rfl (Nat.lt_irrefl 2)
    have hH : evV g x .callByValuePar T [] (.seq (.chr 'a') (.star .eps)) 3=none := by
      rw [evV_seq_ok (show evV g x .callByValuePar T [] (.chr 'a') 3=some (some 2) from rfl)]
      exact hloop
    have harg : evV g x .callByValuePar T []
        (ControlledFragmentReplay.argument .eps (.seq (.chr 'a') (.star .eps))) 3=none := by
      rw [ControlledFragmentReplay.argument,evV_seq_ok hstar]; exact hH
    change evV g x .callByValuePar T []
      (.call 0 [ControlledFragmentReplay.argument .eps (.seq (.chr 'a') (.star .eps))]) 3=none
    rw [evV_call_par (source_rule [.lit []] 0 (.lit []) rfl) rfl (by decide)]
    change (match (match evV g x .callByValuePar T []
        (ControlledFragmentReplay.argument .eps (.seq (.chr 'a') (.star .eps))) 3 with
      | some (some j) => some (some [pre x 3 j]) | some none => some none | none => none) with
      | some (some W) => valAt (T 0 W) 3 | some none => some none | none => none)=none
    rw [harg]
  exact ⟨hs,(evaluator_eq [.lit []] "aaZ".toList m false _ [] 3 (by decide)).symm.trans hs⟩

end Shallot.MacroPeg.CBV.FragmentConsumingRecursiveExamples
