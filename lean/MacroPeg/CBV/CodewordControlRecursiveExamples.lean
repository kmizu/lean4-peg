import MacroPeg.CBV.CodewordControlRecursive
import MacroPeg.CBV.RuntimePrefixExamples

/-! Changing retained captures and restoring whole parent values after
mutual recursion through binary Seq user rows. -/
namespace Shallot.MacroPeg.CBV.CodewordControlRecursiveExamples
open CodewordControlRecursive
open RuntimeShiftFilter (block)
open CodewordReplay (power)

def header : Header where
  toHeader := RuntimePrefixExamples.header
  control := .star (.seq .token (.notP (.test (.alt (.lit ['@']) (.alt (.lit ['%']) (.lit ['!']))))))
  controlPure := ⟨True.intro,True.intro,True.intro,True.intro⟩

def recursiveTail (mark : Char) (next : Nat) : MExp :=
  .alt (.seq (.lit [mark]) (.seq (.call next []) (.seq (.lit ['?']) (.param 0))))
    (.seq (.lit ['!']) (.param 0))
def tails : List MExp := [recursiveTail '@' 1,recursiveTail '%' 0]
def root : MExp := .call 0 []
def grandInput : List Char := power (block 0) 3++['!']++power (block 0) 2++
  ['?']++power (block 2) 1++['?']++power (block 1) 3
def childInput : List Char := power (block 2) 2++['%']++grandInput
def good : List Char := power (block 1) 4++['@']++childInput

def shortParent : List Char := power (block 1) 4++['@']++power (block 2) 2++['%']++
  power (block 0) 3++['!']++power (block 0) 2++['?']++power (block 2) 1++['?']++power (block 1) 2
def shortChild : List Char := power (block 1) 4++['@']++power (block 2) 2++['%']++
  power (block 0) 3++['!']++power (block 0) 2++['?']++['?']++power (block 1) 3
def unequalChild : List Char := power (block 1) 4++['@']++block 2++block 1++block 2++['%']++grandInput

/-- Whole captures 3→1→2, and target pairs (u,u²)→(v,eps)→(w,w),
are selected by the actual input, without fixed word lengths or counts. -/
theorem actual_captures :
    let g := source header tails
    let h := target header tails
    let T := tblV g good .callByValuePar 1
    let U := tblV h good .callByValueSeq 1
    evV g good .callByValuePar T [] (argument header) good.length=
      some (some (block 1++['@']++childInput).length) ∧
    pre good good.length (block 1++['@']++childInput).length=power (block 1) 3 ∧
    evSeqArgs h good .callByValueSeq U [] [header.head,rest header] good.length=
      some (some ([block 1,power (block 1) 2],(block 1++['@']++childInput).length)) ∧
    evSeqArgs h good .callByValueSeq U [block 1,power (block 1) 2] [header.head,rest header] childInput.length=
      some (some ([block 2,[]],(block 2++['%']++grandInput).length)) ∧
    evSeqArgs h good .callByValueSeq U [block 2,[]] [header.head,rest header] grandInput.length=
      some (some ([block 0,block 0],(block 0++['!']++power (block 0) 2++
        ['?']++power (block 2) 1++['?']++power (block 1) 3).length)) := by
  decide +kernel

/-- Actual ordinary tables return from grandchild and child, then reuse
the original whole captures. Short parent/child and unequal captures fail. -/
theorem executions :
    let eval := fun (x : List Char) =>
      (evV (source header tails) x .callByValuePar
        (tblV (source header tails) x .callByValuePar 6) [] (render header tails true root) x.length,
       evV (target header tails) x .callByValueSeq
        (tblV (target header tails) x .callByValueSeq 6) [] (render header tails false root) x.length)
    eval good=(some (some 0),some (some 0)) ∧
    eval shortParent=(some none,some none) ∧
    eval shortChild=(some none,some none) ∧
    eval unequalChild=(some none,some none) := by
  decide +kernel

theorem all_inputs (x : List Char) (r : Option (List Char)) :
    SObs (source header tails) .callByValuePar (render header tails true root) x r ↔
      SObs (target header tails) .callByValueSeq (render header tails false root) x r :=
  observations_iff header tails root x r

/-- Failed initial headers and a successful single-header argument whose
shifted replay fails are both finite failures, rather than undefined calls. -/
theorem early_failures :
    let eval := fun (text : String) =>
      let x := text.toList
      (evV (source header tails) x .callByValuePar (tblV (source header tails) x .callByValuePar 1) []
        (render header tails true root) x.length,
       evV (target header tails) x .callByValueSeq (tblV (target header tails) x .callByValueSeq 1) []
        (render header tails false root) x.length)
    eval "Z"=(some none,some none) ∧
    eval "a#!a#"=(some none,some none) := by
  decide +kernel

def undefinedHeader : Header where
  toHeader := RuntimePrefixExamples.header
  control := .seq .token (.test (.star (.lit [])))
  controlPure := ⟨True.intro,True.intro⟩

/-- Even unequal early words cannot turn an undefined argument into
failure, for arbitrary recursive tables and retained environments. -/
theorem undefined_argument (T U : ClockFreezing.Table) (E : List (List Char)) :
    let x := "a#aa#".toList
    evV (source undefinedHeader tails) x .callByValuePar T E
      (render undefinedHeader tails true root) x.length=none ∧
    evV (target undefinedHeader tails) x .callByValueSeq U E
      (render undefinedHeader tails false root) x.length=none := by
  exact CodewordControlRecursive.undefined_argument undefinedHeader tails 0 (recursiveTail '@' 1) rfl _ _
    (by decide +kernel) T U E

def loopingTails : List MExp := [.star (.lit [])]

theorem undefined_stages (k : Nat) :
    evV (source header loopingTails) "##!#".toList .callByValuePar
      (tblV (source header loopingTails) "##!#".toList .callByValuePar k) []
      (render header loopingTails true root) 4=none := by
  let g := source header loopingTails
  let x := "##!#".toList
  have hr : ruleAtM g.rules 1=some ⟨1,.seq (.seq header.head (.param 0)) (.star (.lit []))⟩ := rfl
  have hb : argumentAt header x 4=some (some 3) := by decide +kernel
  change evV g x .callByValuePar (tblV g x .callByValuePar k) [] (.call 1 [argument header]) 4=none
  rw [evV_call_par hr rfl (by decide)]
  simp only [evParArgs,argument_eval,hb]
  cases k with
  | zero => rfl
  | succ k =>
    rw [valAt_tblV_succ hr _ (by decide)]
    change evV g x .callByValuePar (tblV g x .callByValuePar k) [['#']]
      (.seq (.seq header.head (.param 0)) (.star (.lit []))) 4=none
    have hh : evV g x .callByValuePar (tblV g x .callByValuePar k) [['#']]
        (.seq header.head (.param 0)) 4=some (some 2) := by
      rw [prefix_eval]
      decide +kernel
    rw [evV_seq_ok hh,evV_star]
    apply evStar_stuck (j:=2)
    · simp [evV,Shallot.stripPrefix?,sfx,x]
    · omega

theorem undefined_observations (r : Option (List Char)) :
    ¬SObs (source header loopingTails) .callByValuePar (render header loopingTails true root) "##!#".toList r ∧
    ¬SObs (target header loopingTails) .callByValueSeq (render header loopingTails false root) "##!#".toList r := by
  have hn : ¬SObs (source header loopingTails) .callByValuePar (render header loopingTails true root) "##!#".toList r := by
    rw [←decideObsV_iff (source_firstOrder header loopingTails) (by decide)
      (render_firstOrder header loopingTails true root)]
    simp only [decideObsV,show "##!#".toList.length=4 from rfl]
    rw [undefined_stages]
    simp
  exact ⟨hn,fun h => hn ((observations_iff header loopingTails root "##!#".toList r).mpr h)⟩

def nestedHeader : Header where
  toHeader := RuntimePrefixExamples.header
  control := .star (.seq
    (.star (.seq .token (.test (.seq RuntimePrefixExamples.header.head RuntimePrefixExamples.header.head))))
    (.seq .token (.test RuntimePrefixExamples.header.head)))
  controlPure := ⟨⟨True.intro,RuntimePrefixExamples.header.pure,RuntimePrefixExamples.header.pure⟩,
    True.intro,RuntimePrefixExamples.header.pure⟩

/-- Nested codeword control is used at every mutual-recursion level, with
whole capture restoration after returning through both callers. -/
theorem nested_executions :
    let eval := fun (x : List Char) =>
      (evV (source nestedHeader tails) x .callByValuePar
        (tblV (source nestedHeader tails) x .callByValuePar 6) [] (render nestedHeader tails true root) x.length,
       evV (target nestedHeader tails) x .callByValueSeq
        (tblV (target nestedHeader tails) x .callByValueSeq 6) [] (render nestedHeader tails false root) x.length)
    eval good=(some (some 0),some (some 0)) ∧
    eval shortParent=(some none,some none) ∧
    eval shortChild=(some none,some none) := by
  decide +kernel

theorem nested_all_inputs (x : List Char) (r : Option (List Char)) :
    SObs (source nestedHeader tails) .callByValuePar (render nestedHeader tails true root) x r ↔
      SObs (target nestedHeader tails) .callByValueSeq (render nestedHeader tails false root) x r :=
  observations_iff nestedHeader tails root x r

def emptyHeader : Header where
  head := .eps
  pure := True.intro
  code := fun w => w=[]
  prefixFree := by intro u v hu hv _; exact hu.trans hv.symm
  captured := by
    intro g x s T E p q _ hv
    change some (some p)=some (some q) at hv
    have he : p=q := by simpa using hv
    subst q
    simp [pre]
  control := .eps
  controlPure := True.intro

/-- The mandatory first header can itself capture the empty word; both
retained parts are empty and the source whole value remains empty. -/
theorem empty_capture :
    let users := [MExp.seq .any (.param 0)]
    let x := ['x']
    let g := source emptyHeader users
    let h := target emptyHeader users
    evSeqArgs h x .callByValueSeq (tblV h x .callByValueSeq 1) [] [emptyHeader.head,rest emptyHeader] 1=
      some (some ([[],[]],1)) ∧
    evV g x .callByValuePar (tblV g x .callByValuePar 1) [] (render emptyHeader users true root) 1=some (some 0) ∧
    evV h x .callByValueSeq (tblV h x .callByValueSeq 1) [] (render emptyHeader users false root) 1=some (some 0) := by
  decide +kernel

end Shallot.MacroPeg.CBV.CodewordControlRecursiveExamples
