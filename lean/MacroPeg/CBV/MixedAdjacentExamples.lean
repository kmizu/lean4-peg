import MacroPeg.CBV.MixedAdjacentSyntax
import MacroPeg.CBV.RuntimePrefixExamples

namespace Shallot.MacroPeg.CBV.MixedAdjacentExamples
open MixedAdjacentRecursive
open AdjacentCallsiteRecursive (Header Argument)
open RuntimeShiftFilter (block)
open CodewordReplay (power)

def header : Header := RuntimePrefixExamples.header

def two : Argument header where
  control := .token
  controlSyntax := LastCodewordGrammar.pure_syntax _ header.pure

def dynamic : Argument header where
  control := .alt (.seq (.test (.param 0)) .eps) (.seq .token (.test header.head))
  controlSyntax := ⟨⟨True.intro,True.intro⟩,LastCodewordGrammar.pure_syntax _ header.pure,
    LastCodewordGrammar.pure_syntax _ header.pure⟩

/-- This actual argument can consume a retained parent, a fresh delimiter,
and a recursive shifted user call. It need not be a codeword sequence. -/
def arbitraryArgument : Body header :=
  .seq (.param 0) (.seq (.chr ':') (.call 0 two))

def tails : List (Spec header) := [
  ⟨true,.alt (.seq (.chr '@') (.seq (.replay 1 arbitraryArgument) (.seq (.chr '?') (.param 0))))
    (.seq (.chr '!') (.param 0))⟩,
  ⟨false,.seq (.chr '~') (.seq (.call 0 dynamic) (.seq (.chr '?') (.param 0)))⟩]
def root : Body header := .call 0 two

def capturedArgument : List Char := power (block 1) 2++[':']++power (block 2) 3++['!']++power (block 2) 2
def childInput : List Char := capturedArgument++['~']++power (block 0) 3++['!']++power (block 0) 2++
  ['?']++capturedArgument++['?']++power (block 1) 2
def good : List Char := power (block 1) 3++['@']++childInput

/-- Both rule kinds occur in one mutual recursion. A shifted user runs
inside the general argument; its full non-codeword capture is reused
by the replay user after another shifted call returns. -/
theorem executions :
    let eval := fun (x : List Char) =>
      (evV (source header tails) x .callByValuePar
        (tblV (source header tails) x .callByValuePar 7) [] (render header tails true false root) x.length,
       evV (target header tails) x .callByValueSeq
        (tblV (target header tails) x .callByValueSeq 7) [] (render header tails false false root) x.length)
    eval good=(some (some 0),some (some 0)) ∧
    eval (good.take (good.length-2))=(some none,some none) ∧
    eval (power (block 1) 3++['@']++capturedArgument++['~']++power (block 0) 3++['!']++
      power (block 0) 2++['?']++capturedArgument.take (capturedArgument.length-3)++
      ['?']++power (block 1) 2)=(some none,some none) := by
  decide +kernel

/-- The arbitrary argument consumes the same bytes under the unary whole
parent and its binary Seq view, despite invoking a shifted user internally. -/
theorem actual_argument :
    let g := source header tails
    let h := target header tails
    evV g good .callByValuePar (tblV g good .callByValuePar 4) [power (block 1) 2]
      (render header tails true true arbitraryArgument) childInput.length=
        some (some (childInput.length-capturedArgument.length)) ∧
    evSeqArgs h good .callByValueSeq (tblV h good .callByValueSeq 4) [block 1,block 1]
      [render header tails false true arbitraryArgument] childInput.length=
        some (some ([capturedArgument],childInput.length-capturedArgument.length)) := by
  decide +kernel

/-- Empty arguments and recursive calls under predicates are ordinary
members of the same source/target construction. -/
theorem empty_and_predicate :
    let eval := fun (e : Body header) (x : List Char) =>
      (evV (source header tails) x .callByValuePar
        (tblV (source header tails) x .callByValuePar 7) [] (render header tails true false e) x.length,
       evV (target header tails) x .callByValueSeq
        (tblV (target header tails) x .callByValueSeq 7) [] (render header tails false false e) x.length)
    eval (.replay 1 .eps) "~##!#?".toList=(some (some 0),some (some 0)) ∧
    eval (.notP (.replay 1 (.star .eps))) "Z".toList=(none,none) ∧
    eval (.notP (.notP root)) good=(some (some good.length),some (some good.length)) := by
  decide +kernel

/-- A replay user itself runs inside another replay user's argument.
The outer capture includes a completed inner call, then survives a new
shifted call and is replayed as one whole value on return. -/
theorem nested_arguments :
    let e : Body header := .replay 1 (.replay 1 .eps)
    let word := "~##!#?".toList
    let x := word++"~###!##?".toList++word
    evV (source header tails) x .callByValuePar
      (tblV (source header tails) x .callByValuePar 7) [] (render header tails true false e) x.length=
        some (some 0) ∧
    evV (target header tails) x .callByValueSeq
      (tblV (target header tails) x .callByValueSeq 7) [] (render header tails false false e) x.length=
        some (some 0) := by
  decide +kernel

/-- An undefined general argument remains undefined under any tables,
environments, input, and position, before either user's body can run. -/
theorem undefined_argument (T U : ClockFreezing.Table) (E F : List (List Char))
    (x : List Char) (p : Nat) :
    evV (source header tails) x .callByValuePar T E
      (render header tails true false (.replay 1 (.star .eps))) p=none ∧
    evV (target header tails) x .callByValueSeq U F
      (render header tails false false (.replay 1 (.star .eps))) p=none := by
  let body : Body header := .seq (.chr '~') (.seq (.call 0 dynamic) (.seq (.chr '?') (.param 0)))
  have hs : ruleAtM (source header tails).rules 2=some
      ⟨1,.seq (.param 0) (render header tails true false body)⟩ := rfl
  have ht : ruleAtM (target header tails).rules 2=some
      ⟨1,.seq .eps (render header tails false false body)⟩ := rfl
  have hn (g : MGrammar) (s : Strategy) (V : ClockFreezing.Table) (W : List (List Char)) :
      evV g x s V W (.star .eps) p=none := by
    rw [evV_star]
    apply evStar_stuck (j:=p)
    · rfl
    · omega
  constructor
  · change evV (source header tails) x .callByValuePar T E (.call 2 [.star .eps]) p=none
    rw [evV_call_par hs rfl (by decide)]
    simp only [evParArgs,hn]
  · change evV (target header tails) x .callByValueSeq U F (.call 2 [.star .eps]) p=none
    rw [evV_call_seq ht rfl]
    simp only [evSeqArgs,hn]

private theorem tails_typed : ∀ r∈tails, MixedAdjacentSyntax.WellTyped tails r.body := by
  intro r hr
  simp only [tails,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl <;> simp [MixedAdjacentSyntax.WellTyped,tails,arbitraryArgument]

theorem direct_grammar : source header tails=MixedAdjacentSyntax.original header tails :=
  MixedAdjacentSyntax.source_eq_original header tails tails_typed

theorem direct_all_inputs (x : List Char) (r : Option (List Char)) :
    SObs (MixedAdjacentSyntax.original header tails) .callByValuePar
      (MixedAdjacentSyntax.sourceExpr header root) x r ↔
    SObs (target header tails) .callByValueSeq (render header tails false false root) x r := by
  apply MixedAdjacentSyntax.original_observations header tails tails_typed root _ x r
  simp [MixedAdjacentSyntax.WellTyped,tails,root]

theorem all_inputs (x : List Char) (r : Option (List Char)) :
    SObs (source header tails) .callByValuePar (render header tails true false root) x r ↔
      SObs (target header tails) .callByValueSeq (render header tails false false root) x r :=
  observations_iff header tails root x r

end Shallot.MacroPeg.CBV.MixedAdjacentExamples
