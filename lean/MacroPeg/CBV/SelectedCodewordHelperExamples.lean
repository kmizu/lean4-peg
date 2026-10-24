import MacroPeg.CBV.SelectedCodewordHelperGrammar
import MacroPeg.CBV.RecursiveCodeExamples

/-! Selected stops using recursive headers and conditions, mutual user calls, and parent reuse. -/
namespace Shallot.MacroPeg.CBV.SelectedCodewordHelperExamples
open SelectedCodewordHelperGrammar
open SelectedCodewordHelpers (Header argument argumentAt probe)
open CodewordReplay (power)

def header : Header where
  toHeader := RecursiveCodeExamples.header
  condition := .andP RecursiveCodeExamples.header.head
  conditionLexical := RecursiveCodeExamples.header.lexical

def u : List Char := "aabb#".toList
def v : List Char := "ab#".toList
def z : List Char := ['#']

def continuationHeader : MExp :=
  .seq (.star (.alt (.lit ['a']) (.lit ['b']))) (.lit ['#'])

def recursiveTail (mark : Char) (next : Nat) : MExp :=
  .seq continuationHeader
    (.alt (.seq (.lit [mark]) (.seq (.call next []) (.seq (.lit ['?']) (.param 0))))
      (.seq (.lit ['!']) (.param 0)))
def tails : List MExp := [recursiveTail '@' 1,recursiveTail '%' 0]
def root : MExp := .call 0 []

def grandInput : List Char := power (z) 3++u++['!']++power (z) 2++
  ['?']++power (v) 1++['?']++power (u) 3
def childInput : List Char := power (v) 2++z++['%']++grandInput
def good : List Char := power (u) 4++v++['@']++childInput

def shortParent : List Char := power (u) 4++v++['@']++
  power (v) 2++z++['%']++power (z) 3++u++['!']++power (z) 2++
  ['?']++power (v) 1++['?']++power (u) 2
def shortChild : List Char := power (u) 4++v++['@']++
  power (v) 2++z++['%']++power (z) 3++u++['!']++power (z) 2++
  ['?']++power (u) 1++['?']++power (u) 3
def unequalChild : List Char := power (u) 4++v++['@']++
  v++u++z++['%']++grandInput
def zeroGrandchild : List Char := power (u) 4++v++['@']++
  power (v) 2++z++['%']++z++u++['!']++
  ['?']++power (v) 1++['?']++power (u) 3

/-- Each capture stops before a final header and a later unequal header.
Counts 3→1→2 and lengths 5→3→1 are selected by the actual input. -/
theorem actual_captures :
    let g := source header tails
    let T := tblV g good .callByValuePar 8
    evV g good .callByValuePar T [] (argument header) good.length=
      some (some (u++v++['@']++childInput).length) ∧
    pre good good.length (u++v++['@']++childInput).length=power (u) 3 ∧
    evV g good .callByValuePar T [power (u) 3] (argument header) childInput.length=
      some (some (v++z++['%']++grandInput).length) ∧
    pre good childInput.length (v++z++['%']++grandInput).length=power (v) 1 ∧
    evV g good .callByValuePar T [power (v) 1] (argument header) grandInput.length=
      some (some (z++u++['!']++power (z) 2++['?']++power (v) 1++['?']++power (u) 3).length) ∧
    pre good grandInput.length
      (z++u++['!']++power (z) 2++['?']++power (v) 1++['?']++power (u) 3).length=power (z) 2 := by
  decide +kernel

/-- Ordinary physical tables, including return and whole parent reuse. -/
theorem executions :
    let eval := fun (x : List Char) =>
      (evV (source header tails) x .callByValuePar
        (tblV (source header tails) x .callByValuePar 12) [] (render header tails true root) x.length,
       evV (target header tails) x .callByValueSeq
        (tblV (target header tails) x .callByValueSeq 12) [] (render header tails false root) x.length)
    eval good=(some (some 0),some (some 0)) ∧
    eval shortParent=(some none,some none) ∧
    eval shortChild=(some none,some none) ∧
    eval unequalChild=(some none,some none) ∧
    eval zeroGrandchild=(some (some 0),some (some 0)) := by
  decide +kernel

theorem all_inputs (x : List Char) (r : Option (List Char)) :
    SObs (source header tails) .callByValuePar (render header tails true root) x r ↔
      SObs (target header tails) .callByValueSeq (render header tails false root) x r :=
  observations_iff header tails root x r

/-- With no captured word, the step fails and the verifier guard passes,
but the actual header fails. Both seeds must retain that real failure. -/
theorem zero_capture_failed_head :
    let x := ['Z']
    argumentAt header x 1=some (some 1) ∧
    probe header x 1=some (some 1) ∧
    valAt (sourceTable header tails x 0 3 [[]]) 1=some none ∧
    valAt (targetTable header tails x 0 3 [[]]) 1=some none ∧
    evV (target header tails) x .callByValueSeq (targetTable header tails x 0) []
      (render header tails false root) 1=some none := by
  decide +kernel

/-- A selected nonempty capture with unequal shifted words is rejected
before either recursive tail, backed by its actual failed source prefix. -/
theorem unequal_seed :
    let x := "aabb#ab#aabb#!".toList
    valAt (sourceTable header tails x 0 3 [u]) x.length=some none ∧
    probe header x x.length=some none ∧
    evV (target header tails) x .callByValueSeq (targetTable header tails x 0) []
      (render header tails false root) x.length=some none := by
  decide +kernel

/-- The selected-stop condition itself calls the recursive balanced parser. -/
theorem recursive_condition :
    let g := source header tails
    evV g "aabb#".toList .callByValuePar (tblV g "aabb#".toList .callByValuePar 8) []
      header.condition 5=some (some 5) ∧
    evV g "aab#".toList .callByValuePar (tblV g "aab#".toList .callByValuePar 8) []
      header.condition 4=some none := by
  decide +kernel

def cyclicHeader : Header where
  condition := .eps
  conditionLexical := True.intro
  bodies := RecursiveCodeExamples.bodies
  valid := RecursiveCodeExamples.bodies_valid
  head := .call 0 []
  lexical := by change 0<2; omega
  code := fun _ => False
  prefixFree := by intro u v hu; cases hu
  captured := by
    intro x p q hp hv
    have hn := RecursiveParserStability.cycle_undefined
      (g:=RecursiveParserStability.grammar RecursiveCodeExamples.bodies) (by rfl) x .callByValuePar
      (RecursiveParserStability.floor RecursiveCodeExamples.bodies x) [] p hp
    change evV _ x .callByValuePar (tblV _ x .callByValuePar (RecursiveParserStability.floor _ x)) [] (.call 0 []) p=some (some q) at hv
    rw [hn] at hv
    cases hv

theorem cyclic_source_undefined (x : List Char) (k p : Nat) (hp : p≤x.length) :
    evV (source cyclicHeader [.eps]) x .callByValuePar
      (tblV (source cyclicHeader [.eps]) x .callByValuePar k) []
      (render cyclicHeader [.eps] true root) p=none := by
  let g := source cyclicHeader [.eps]
  have hr : ruleAtM g.rules 3=some ⟨1,.seq (.seq (.call 0 []) (.param 0)) .eps⟩ := rfl
  change evV g x .callByValuePar (tblV g x .callByValuePar k) [] (.call 3 [argument cyclicHeader]) p=none
  rw [evV_call_par hr rfl (by decide)]
  have hh : evV g x .callByValuePar (tblV g x .callByValuePar k) [] (.call 0 []) p=none :=
    RecursiveParserStability.cycle_undefined (by rfl) x .callByValuePar k [] p hp
  have hb : evV g x .callByValuePar (tblV g x .callByValuePar k) [] (argument cyclicHeader) p=none := by
    rw [argument,evV_star]
    change evStar (fun q => evV g x .callByValuePar (tblV g x .callByValuePar k) []
      (SelectedCodewordVerification.step cyclicHeader.head cyclicHeader.condition) q) p=none
    exact evStar_none (evV_seq_none hh)
  simp only [evParArgs,hb]

theorem cyclic_no_observations (x : List Char) (r : Option (List Char)) :
    ¬SObs (target cyclicHeader [.eps]) .callByValueSeq (render cyclicHeader [.eps] false root) x r := by
  rw [←observations_iff cyclicHeader [.eps] root x r,
    ←decideObsV_iff (source_firstOrder cyclicHeader [.eps]) (by decide) (render_firstOrder cyclicHeader [.eps] true root)]
  simp [decideObsV,cyclic_source_undefined x _ x.length (Nat.le_refl _)]

/-- A nullable header does not license a finite stop when the original
condition calls a nonproductive independent recursive helper. -/
def cyclicCondition : Header where
  toHeader := {
    bodies := RecursiveCodeExamples.bodies
    valid := RecursiveCodeExamples.bodies_valid
    head := .eps
    lexical := True.intro
    code := fun w => w=[]
    prefixFree := by intro u v hu hv _; exact hu.trans hv.symm
    captured := by
      intro x p q _ hv
      change some (some p)=some (some q) at hv
      have he : p=q := by simpa using hv
      subst q
      simp [pre] }
  condition := .call 0 []
  conditionLexical := by change 0<2; omega

theorem cyclic_condition_source_undefined (x : List Char) (k p : Nat) (hp : p≤x.length) :
    evV (source cyclicCondition [.eps]) x .callByValuePar
      (tblV (source cyclicCondition [.eps]) x .callByValuePar k) []
      (render cyclicCondition [.eps] true root) p=none := by
  let g := source cyclicCondition [.eps]
  let T := tblV g x .callByValuePar k
  have hr : ruleAtM g.rules 3=some ⟨1,.seq (.seq .eps (.param 0)) .eps⟩ := rfl
  change evV g x .callByValuePar T [] (.call 3 [argument cyclicCondition]) p=none
  rw [evV_call_par hr rfl (by decide)]
  have hh : evV g x .callByValuePar T [] (.call 0 []) p=none :=
    RecursiveParserStability.cycle_undefined (by rfl) x .callByValuePar k [] p hp
  have hb : evV g x .callByValuePar T [] (argument cyclicCondition) p=none := by
    rw [argument,evV_star]
    apply evStar_none
    change evV g x .callByValuePar T [] (.seq .eps (.andP (.seq .eps (.call 0 [])))) p=none
    rw [evV_seq_ok (show evV g x .callByValuePar T [] .eps p=some (some p) from rfl),
      CallLookahead.evV_peek,
      evV_seq_ok (show evV g x .callByValuePar T [] .eps p=some (some p) from rfl),hh]
    rfl
  simp only [evParArgs,hb]

theorem cyclic_condition_no_observations (x : List Char) (r : Option (List Char)) :
    ¬SObs (target cyclicCondition [.eps]) .callByValueSeq (render cyclicCondition [.eps] false root) x r := by
  rw [←observations_iff cyclicCondition [.eps] root x r,
    ←decideObsV_iff (source_firstOrder cyclicCondition [.eps]) (by decide)
      (render_firstOrder cyclicCondition [.eps] true root)]
  simp [decideObsV,cyclic_condition_source_undefined x _ x.length (Nat.le_refl _)]

end Shallot.MacroPeg.CBV.SelectedCodewordHelperExamples
