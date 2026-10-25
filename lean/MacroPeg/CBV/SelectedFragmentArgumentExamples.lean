import MacroPeg.CBV.FragmentPrefixQueryExamples

namespace Shallot.MacroPeg.CBV.SelectedFragmentArgumentExamples
open FragmentPrefixQuery
open RuntimeShiftFilter (scanner)
open PartialCodewordCapture (eof)
set_option maxHeartbeats 0
set_option maxRecDepth 100000

abbrev tails := FragmentPrefixQueryExamples.tails
abbrev bodies := FragmentPrefixQueryExamples.bodies

def short : MExp := .seq .eps (.chr 'a')
def long : MExp := .seq .eps (.lit ['a','a'])
def choices : MExp := .alt long short
def selected : MExp := .call 0 [.eps,choices,.eps]
def endpoint : MExp := .call 0 [.eps,choices,.chr 'a']
def root : MExp := .seq selected (.seq scanner (.seq (.star (.chr 'a')) eof))

def sourceRun (e : MExp) (x : List Char) (k : Nat) :=
  evV (source tails bodies) x .callByValuePar
    (tblV (source tails bodies) x .callByValuePar k) [] (sourceRender tails bodies e) x.length

def targetRun (e : MExp) (x : List Char) (k : Nat) :=
  evV (target tails bodies) x .callByValueSeq
    (tblV (target tails bodies) x .callByValueSeq k) [] (targetRender tails bodies e) x.length

/-- Three surface templates still render to exactly one actual source
argument. The alternative is inside that argument, before the body. -/
theorem actual_unary : sourceRender tails bodies selected =
    .call 0 [.seq (PartialCodewordCapture.look .eps)
      (.seq (.alt (ControlledFragmentReplay.argument .eps (.seq (.chr 'a') (.seq (.chr 'a') .eps)))
                  (ControlledFragmentReplay.argument .eps (.chr 'a')))
        (PartialCodewordCapture.look .eps))] := by rfl

theorem selected_capture :
    evV (source tails bodies) "aa#aa#a".toList .callByValuePar
      (tblV (source tails bodies) "aa#aa#a".toList .callByValuePar 2) []
      (FragmentMixedRecursive.choiceArgument (tails.map Prod.fst) tails.length
        (plans tails bodies) true choices) 7=some (some 2) ∧
    pre "aa#aa#a".toList 7 2="aa#aa".toList := by decide +kernel

/-- The first capture succeeds with aa#aa. Its body fails, even though
retrying with aa#a would succeed. Distributing calls over alt is wrong. -/
theorem committed_body_failure :
    sourceRun selected "aa#aa#a".toList 2=some none ∧
    targetRun selected "aa#aa#a".toList 2=some none ∧
    targetRun (.alt (.call 0 [.eps,.lit ['a','a']]) (.call 0 [.eps,.chr 'a']))
      "aa#aa#a".toList 2=some (some 4) := by decide +kernel

/-- A failed endpoint test cannot change the selected capture either. -/
theorem committed_endpoint_failure :
    sourceRun endpoint "aa#aa#a".toList 2=some none ∧
    targetRun endpoint "aa#aa#a".toList 2=some none ∧
    targetRun (.alt (.call 0 [.eps,.eps,.lit ['a','a'],.chr 'a'])
      (.call 0 [.eps,.eps,.chr 'a',.chr 'a'])) "aa#aa#a".toList 2=some (some 4) := by decide +kernel

/-- Failure of the first argument itself permits the second candidate. -/
theorem fallback_and_first_success :
    sourceRun selected "a#a#a".toList 2=some (some 3) ∧
    targetRun selected "a#a#a".toList 2=some (some 3) ∧
    sourceRun selected "aa#aa#aa".toList 2=some (some 5) ∧
    targetRun selected "aa#aa#aa".toList 2=some (some 5) := by decide +kernel

/-- A selected fragment can call the same logical user with a fresh
capture before the caller queries its complete retained value. -/
def probe : MExp := .seq (.chr 'a') (.andP (.call 0 [.eps,.seq .eps .eps,.eps]))
def recursiveChoices : MExp := .alt (.seq .eps (.notP .eps)) (.alt (.seq .eps probe) short)
def recursiveSelected : MExp := .call 0 [.eps,recursiveChoices,.eps]
def recursiveRoot : MExp := .seq recursiveSelected (.seq scanner (.seq (.chr 'a') eof))

theorem recursive_probe :
    sourceRun recursiveSelected "aa#aa#a".toList 2=some (some 4) ∧
    targetRun recursiveSelected "aa#aa#a".toList 2=some (some 4) ∧
    sourceRun recursiveRoot "aa#aa#a".toList 2=some (some 0) ∧
    targetRun recursiveRoot "aa#aa#a".toList 2=some (some 0) := by decide +kernel

/-- One fixed grammar and start expression, on unchanged original input. -/
theorem language : ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
    SObs (source tails bodies) .callByValuePar (sourceRender tails bodies root) x (some []) ↔
      SObs g .callByValueSeq start x (some []) :=
  language_translation tails bodies FragmentPrefixQueryExamples.checked root

theorem recursive_language : ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
    SObs (source tails bodies) .callByValuePar (sourceRender tails bodies recursiveRoot) x (some []) ↔
      SObs g .callByValueSeq start x (some []) :=
  language_translation tails bodies FragmentPrefixQueryExamples.checked recursiveRoot

theorem whole_samples :
    sourceRun root "a#a#a".toList 2=some (some 0) ∧
    targetRun root "a#a#a".toList 2=some (some 0) ∧
    sourceRun root "aa#aa#aa".toList 2=some (some 0) ∧
    targetRun root "aa#aa#aa".toList 2=some (some 0) ∧
    sourceRun root "aa#aa#a".toList 2=some none ∧
    targetRun root "aa#aa#a".toList 2=some none := by decide +kernel

def loopingChoices : MExp := .alt (.seq .eps (.star .eps)) short
def nullable : MExp := .call 0 [.eps,loopingChoices,MExp.failAlways]
def masked : MExp := .call 0 [MExp.failAlways,loopingChoices,.eps]

/-- The first candidate's undefinedness blocks both the successful second
candidate and the endpoint test which would otherwise finitely fail. -/
theorem nullable_source (x : List Char) (clock : Nat) : sourceRun nullable x clock=none := by
  let g := source tails bodies
  let T := tblV g x .callByValuePar clock
  have hloop (q : Nat) : evV g x .callByValuePar T [] (.star .eps) q=none :=
    evStar_stuck rfl (Nat.lt_irrefl q)
  have harg : evV g x .callByValuePar T []
      (ControlledFragmentReplay.argument .eps (.star .eps)) x.length=none := by
    cases hs : evV g x .callByValuePar T [] (.star (ControlledPartialCapture.step .eps)) x.length with
    | none => exact evV_seq_none hs
    | some v => cases v with
      | none => exact False.elim (evStar_ne_fail _ hs)
      | some q => rw [ControlledFragmentReplay.argument,evV_seq_ok hs]; exact hloop q
  change evV g x .callByValuePar T []
    (.call 0 [.seq (PartialCodewordCapture.look .eps)
      (.seq (.alt (ControlledFragmentReplay.argument .eps (.star .eps))
        (ControlledFragmentReplay.argument .eps (.chr 'a')))
        (PartialCodewordCapture.look MExp.failAlways))]) x.length=none
  rw [evV_call_par (source_rule tails bodies 0 (.after true 0) rfl) rfl (by decide)]
  change evV (source tails bodies) x .callByValuePar T []
    (ControlledFragmentReplay.argument .eps (.star .eps)) x.length=none at harg
  simp only [evParArgs,PartialCodewordCapture.look,evV,harg]

theorem nullable_target (x : List Char) (clock : Nat) : targetRun nullable x clock=none :=
  (undefined_iff tails bodies FragmentPrefixQueryExamples.checked nullable x).mp (nullable_source x) clock

/-- Failure at the origin precedes even an undefined first candidate. -/
theorem origin_masks_loop (x : List Char) (clock : Nat) :
    sourceRun masked x clock=some none ∧ targetRun masked x clock=some none := by
  have hs : sourceRun masked x clock=some none := by
    change evV (source tails bodies) x .callByValuePar
      (tblV (source tails bodies) x .callByValuePar clock) []
      (.call 0 [.seq (PartialCodewordCapture.look MExp.failAlways)
        (.seq _ (PartialCodewordCapture.look .eps))]) x.length=some none
    rw [evV_call_par (source_rule tails bodies 0 (.after true 0) rfl) rfl (by decide)]
    simp only [evParArgs,PartialCodewordCapture.look,MExp.failAlways,evV]
  refine ⟨hs,?_⟩
  exact (physical tails bodies FragmentPrefixQueryExamples.checked x clock masked [] x.length
    (Nat.le_refl _)).symm.trans hs

end Shallot.MacroPeg.CBV.SelectedFragmentArgumentExamples
