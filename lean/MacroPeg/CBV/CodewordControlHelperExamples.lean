import MacroPeg.CBV.CodewordControlHelpers
import MacroPeg.CBV.RecursiveCodeExamples

/-! Actual helper tables for recursive headers and tests, with exact
selected captures, mismatch rejection, and undefined helper recursion. -/
namespace Shallot.MacroPeg.CBV.CodewordControlHelperExamples
open CodewordControlHelpers

def header : Header where
  toHeader := RecursiveCodeExamples.header
  control := .star (.seq
    (.star (.seq .token (.test (.seq RecursiveCodeExamples.head RecursiveCodeExamples.head))))
    (.seq .token (.test RecursiveCodeExamples.head)))
  controlLexical := ⟨⟨True.intro,RecursiveCodeExamples.header.lexical,RecursiveCodeExamples.header.lexical⟩,
    True.intro,RecursiveCodeExamples.header.lexical⟩
def parser : MGrammar := RecursiveParserStability.grammar header.bodies
def tail : MExp := .seq (.lit ['!']) (.seq (.andP header.head) (.param 0))
def good : List Char := "ab#ab#ab#!ab#ab#".toList

theorem control_uses_recursive_tests :
    rest header=CodewordControlFilter.render header.head header.control ∧
    HelperArgument.Syntax header.bodies.length tail ∧
    ¬ParserPrefixFusion.Pure header.head := by
  constructor
  · rfl
  constructor
  · exact ⟨True.intro,LastCodewordHelpers.lexical_syntax _ _ header.lexical,True.intro⟩
  · simp [header,RecursiveCodeExamples.header,RecursiveCodeExamples.head,ParserPrefixFusion.Pure]

/-- Three input words leave one word for the shifted source replay. -/
theorem actual_parts :
    let T := tblV parser good .callByValuePar 6
    evV parser good .callByValuePar T [] (argument header) good.length=some (some 10) ∧
    pre good good.length 10="ab#ab#".toList ∧
    evSeqArgs parser good .callByValueSeq (tblV parser good .callByValueSeq 6) [] [header.head,rest header] good.length=
      some (some (["ab#".toList,"ab#".toList],10)) ∧
    evV parser good .callByValuePar T ["ab#".toList] (verifier header) 13=some (some 10) := by
  decide +kernel

/-- Both strategies use actual ordinary helper tables, with a recursive
helper in the continuation before the entire retained capture is reused. -/
theorem executions :
    let eval := fun (text : String) (u v : String) (q : Nat) =>
      let x := text.toList
      let T := tblV parser x .callByValuePar 6
      let U := tblV parser x .callByValueSeq 6
      (evV parser x .callByValuePar T [u.toList++v.toList]
        (.seq (.seq header.head (.param 0)) tail) x.length,
       evV parser x .callByValueSeq U [u.toList,v.toList]
        (.seq (.param 0) (CodewordControlFilter.wholeView tail)) q)
    eval "ab#ab#ab#!ab#ab#" "ab#" "ab#" 10=(some (some 0),some (some 0)) ∧
    eval "aabb#aabb#aabb#!aabb#aabb#" "aabb#" "aabb#" 16=(some (some 0),some (some 0)) ∧
    eval "ab#ab#ab#!ab#" "ab#" "ab#" 7=(some none,some none) := by
  decide +kernel

/-- A mismatching recursive codeword is a committed rejection, even
though the nested raw parser successfully selects that whole capture. -/
theorem unequal_capture :
    let x := "ab#aabb#ab#!ab#aabb#".toList
    let T := tblV parser x .callByValuePar 6
    evV parser x .callByValuePar T [] (argument header) x.length=some (some 12) ∧
    pre x x.length 12="ab#aabb#".toList ∧
    evV parser x .callByValuePar T ["ab#".toList] (verifier header) (x.length-3)=some none ∧
    evV parser x .callByValuePar T ["ab#aabb#".toList]
      (.seq (.seq header.head (.param 0)) tail) x.length=some none := by
  decide +kernel

/-- The cross-strategy theorem derives both parts from the actual source
argument on every input and at every pair of stabilized ordinary stages. -/
theorem all_actual_entries (x : List Char) (k m p q : Nat) (E : List (List Char))
    (hp : p≤x.length)
    (hb : evV parser x .callByValuePar
      (tblV parser x .callByValuePar (RecursiveParserStability.floor header.bodies x+k))
      E (argument header) p=some (some q)) :
    ∃ j, j≤x.length ∧ header.code (pre x p j) ∧ pre x p q=pre x p j++pre x j q ∧
      evV parser x .callByValuePar
        (tblV parser x .callByValuePar (RecursiveParserStability.floor header.bodies x+k))
        [pre x p q] (.seq (.seq header.head (.param 0)) tail) p=
        match check header x (pre x p j) j with
        | some (some _) => evV parser x .callByValueSeq
            (tblV parser x .callByValueSeq (RecursiveParserStability.floor header.bodies x+m))
            [pre x p j,pre x j q] (.seq (.param 0) (CodewordControlFilter.wholeView tail)) q
        | other => other :=
  physical_argument_entry_seq header parser parser (RecursiveParserStability.installed header.bodies)
    (RecursiveParserStability.installed header.bodies) RecursiveCodeExamples.helpers_firstOrder
    x k m E p q hp hb tail control_uses_recursive_tests.2.1

def cyclicControl : Header where
  toHeader := RecursiveCodeExamples.header
  control := .test (.call 0 [])
  controlLexical := by change 0<2; omega

/-- A nonproductive test remains undefined under every ordinary stage and
retained value; no comparison can turn it into finite failure. -/
theorem cyclic_test (x : List Char) (s : Strategy)
    (k p : Nat) (hp : p≤x.length) (E : List (List Char)) :
    evV parser x s (tblV parser x s k) E (rest cyclicControl) p=none ∧
    evV parser x s (tblV parser x s k) E (verifier cyclicControl) p=none := by
  have hr : ruleAtM parser.rules 0=some ⟨0,.call 0 []⟩ := rfl
  have hb : evV parser x s (tblV parser x s k) E (rest cyclicControl) p=none := by
    change evV parser x s (tblV parser x s k) E (.andP (.call 0 [])) p=none
    rw [CallLookahead.evV_peek]
    have he : evV parser x s (tblV parser x s k) E (.call 0 []) p=none :=
      RecursiveParserStability.cycle_undefined hr x s k E p hp
    rw [he]; rfl
  exact ⟨hb,CodewordControlFilter.filter_none parser x s _ E cyclicControl.head cyclicControl.control p hb⟩

def cyclicHeader : Header where
  bodies := RecursiveCodeExamples.bodies
  valid := RecursiveCodeExamples.bodies_valid
  head := .call 0 []
  lexical := by change 0<2; omega
  code := fun _ => False
  prefixFree := by intro _ _ h; exact False.elim h
  captured := by
    intro x p q hp hv
    have hn := RecursiveParserStability.cycle_undefined
      (g:=RecursiveParserStability.grammar RecursiveCodeExamples.bodies) (by rfl) x .callByValuePar
      (RecursiveParserStability.floor RecursiveCodeExamples.bodies x) [] p hp
    change evV (RecursiveParserStability.grammar RecursiveCodeExamples.bodies) x .callByValuePar
      (RecursiveCodeGrammar.canonical RecursiveCodeExamples.bodies x) [] (.call 0 []) p=none at hn
    rw [hn] at hv
    cases hv
  control := .star .token
  controlLexical := True.intro

/-- A nonproductive header is undefined on every input at every ordinary
stage; its argument and verifier cannot acquire a finite stopping point. -/
theorem cyclic_header (x : List Char) (s : Strategy) (k p : Nat)
    (hp : p≤x.length) (E : List (List Char)) :
    evV parser x s (tblV parser x s k) E (argument cyclicHeader) p=none ∧
    evV parser x s (tblV parser x s k) E (verifier cyclicHeader) p=none := by
  have hn : evV parser x s (tblV parser x s k) E cyclicHeader.head p=none :=
    RecursiveParserStability.cycle_undefined (by rfl) x s k E p hp
  have ha : evV parser x s (tblV parser x s k) E (argument cyclicHeader) p=none := evV_seq_none hn
  have hd : evV parser x s (tblV parser x s k) E (rest cyclicHeader) p=none := evStar_none hn
  exact ⟨ha,CodewordControlFilter.filter_none parser x s _ E cyclicHeader.head cyclicHeader.control p hd⟩

end Shallot.MacroPeg.CBV.CodewordControlHelperExamples
