import MacroPeg.CBV.PartialCodewordRecursive

namespace Shallot.MacroPeg.CBV.PartialCodewordRecursiveExamples
open PartialCodewordRecursive

/-- Templates denote fresh captures at every call; the concrete source
rules have ordinary unary calls with the actual argument B. -/
def tails : List MExp := [
  .alt (.seq (.lit ['!']) (.param 0))
    (.seq (.lit ['Z']) (.seq (.call 1 []) (.seq (.lit ['?']) (.param 0)))),
  .seq (.lit ['Y']) (.seq (.call 0 []) (.seq (.lit ['?']) (.param 0)))]
def root : MExp := .seq (.call 0 []) PartialCodewordCapture.eof

/-- The actual path is user 0 → 1 → 0, followed by both returns.
The captures are a#a, aa, ##: two pieces, one partial run, and two
empty-run codewords. Each parent reuses its own full value after return. -/
theorem mutual_returns :
    let x := "a#a#aZaa#aaY###!##?aa?a#a".toList
    evV (source tails) x .callByValuePar (tblV (source tails) x .callByValuePar 3)
      [] (render tails true root) x.length=some (some 0) ∧
    evV (target tails) x .callByValueSeq (tblV (target tails) x .callByValueSeq 3)
      [] (render tails false root) x.length=some (some 0) := by
  decide +kernel

/-- Empty captures on the inner and outer calls, plus the two branches
with nonempty captures, use the same pair of fixed grammars. -/
theorem empty_and_partial : ∀ x ∈
    ["#!".toList,"a#a!a".toList,"##!#".toList,"#Z#Y#!??".toList],
    evV (source tails) x .callByValuePar (tblV (source tails) x .callByValuePar 3)
      [] (render tails true root) x.length=some (some 0) ∧
    evV (target tails) x .callByValueSeq (tblV (target tails) x .callByValueSeq 3)
      [] (render tails false root) x.length=some (some 0) := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> (constructor <;> decide +kernel)

/-- A short parent copy, a short child copy, and a malformed initial
prefix are rejected by both actual evaluators. -/
theorem rejected_copies : ∀ x ∈
    ["a#a#aZaa#aaY###!##?aa?a#".toList,
      "a#a#aZaa#aaY###!##?a?a#a".toList,"#a#!#a".toList],
    evV (source tails) x .callByValuePar (tblV (source tails) x .callByValuePar 3)
      [] (render tails true root) x.length=some none ∧
    evV (target tails) x .callByValueSeq (tblV (target tails) x .callByValueSeq 3)
      [] (render tails false root) x.length=some none := by
  decide +kernel


def loopingTails : List MExp := [.star (.lit [])]

/-- The source reaches an empty-consuming repetition after a valid empty
capture. It has no result at any ordinary clock. -/
theorem undefined_stages (m : Nat) :
    evV (source loopingTails) ['#'] .callByValuePar
      (tblV (source loopingTails) ['#'] .callByValuePar m) []
      (render loopingTails true (.call 0 [])) 1=none := by
  let g := source loopingTails
  have hr : ruleAtM g.rules 0=some ⟨1,.seq RuntimeShiftFilter.scanner
      (.seq (.param 0) (.star (.lit [])))⟩ := rfl
  change evV g ['#'] .callByValuePar (tblV g ['#'] .callByValuePar m) []
    (.call 0 [PartialCodewordCapture.argument]) 1=none
  rw [evV_call_par hr rfl (by decide)]
  have ha : evV g ['#'] .callByValuePar (tblV g ['#'] .callByValuePar m) []
      PartialCodewordCapture.argument 1=some (some 1) := by
    rw [PartialCodewordTotality.argument_context g ⟨[]⟩ ['#'] .callByValuePar .callByValuePar
      (tblV g ['#'] .callByValuePar m) (fun _ _ => []) [] [] 1]
    decide +kernel
  simp only [evParArgs,ha]
  cases m with
  | zero => rfl
  | succ m =>
    rw [valAt_tblV_succ hr _ (by decide)]
    change evV g ['#'] .callByValuePar (tblV g ['#'] .callByValuePar m) [[]]
      (.seq RuntimeShiftFilter.scanner (.seq (.param 0) (.star (.lit [])))) 1=none
    have hh : evV g ['#'] .callByValuePar (tblV g ['#'] .callByValuePar m) [[]]
        RuntimeShiftFilter.scanner 1=some (some 0) := by
      rw [PartialCodewordPreflight.scanner_context g ⟨[]⟩ ['#'] .callByValuePar .callByValuePar
        (tblV g ['#'] .callByValuePar m) (fun _ _ => []) [[]] [] 1 (by decide)]
      decide +kernel
    rw [evV_seq_ok hh]
    have hp : evV g ['#'] .callByValuePar (tblV g ['#'] .callByValuePar m) [[]]
        (.param 0) 0=some (some 0) := rfl
    rw [evV_seq_ok hp,evV_star]
    apply evStar_stuck (j:=0)
    · simp [evV,Shallot.stripPrefix?,sfx]
    · omega

/-- Undefinedness survives both generated branches and every target clock. -/
theorem target_undefined_stages (m : Nat) :
    evV (target loopingTails) ['#'] .callByValueSeq
      (tblV (target loopingTails) ['#'] .callByValueSeq m) []
      (render loopingTails false (.call 0 [])) 1=none := by
  rw [←evaluator_eq loopingTails ['#'] m (.call 0 []) [] 1 (by decide)]
  exact undefined_stages m

end Shallot.MacroPeg.CBV.PartialCodewordRecursiveExamples
