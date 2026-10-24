import MacroPeg.CBV.AdjacentCodewordCalls
import MacroPeg.CBV.RuntimePrefixExamples

namespace Shallot.MacroPeg.CBV.AdjacentCodewordExamples
open RuntimeShiftFilter (scanner)
open CodewordControlFilter (wholeView)

def control : CodewordControlFilter.Expr := .star (.seq .token (.notP (.test (.param 0))))
def rest : MExp := CodewordControlFilter.render scanner control
def argument : MExp := .seq scanner rest

def tail : MExp := .seq
  (.alt (.chr '#') (.seq scanner (.chr '#')))
  (.seq (.chr '!') (.param 0))

def sourceChild : MExp := .call 2 [argument]
def targetChild : MExp := .seq (.andP argument)
  (.seq (.andP (AdjacentCodewordControl.filter scanner (.call 0 [scanner]) (.seq .token control)))
    (.call 2 [scanner,rest]))

def footer : MExp := .seq (.chr '?') (.param 0)

def source : MGrammar := ⟨[
  ⟨1,.param 0⟩,
  ⟨1,.seq (.param 0) (.seq (.chr '@') (.seq sourceChild footer))⟩,
  ⟨1,.seq scanner (.seq (.param 0) tail)⟩]⟩
def target : MGrammar := ⟨[
  ⟨1,.param 0⟩,
  ⟨1,.seq (.chr '@') (.seq targetChild footer)⟩,
  ⟨2,.seq (.param 0) (wholeView tail)⟩]⟩
def root : MExp := .call 1 [scanner]

def longer : List Char := "#@a#a#a##!a#a#?#".toList
def shorter : List Char := "a#@a#a#a##!a#?a#".toList

/-- The parent's value is freshly captured from the input, and controls
whether the child retains one codeword or two. No parent parameter is
passed into the adjacent comparator rule. -/
theorem dynamic_parent_executions :
    let eval := fun (x : List Char) =>
      (evV source x .callByValuePar (tblV source x .callByValuePar 5) [] root x.length,
       evV target x .callByValueSeq (tblV target x .callByValueSeq 5) [] root x.length)
    eval longer=(some (some 0),some (some 0)) ∧
    eval shorter=(some (some 0),some (some 0)) ∧
    eval "a#@a#a#a##!a#?a".toList=(some none,some none) ∧
    eval "#@a#a#a##!a#?#".toList=(some none,some none) ∧
    eval "a#@a#a#a##!?a#".toList=(some none,some none) ∧
    eval "#@a#aa#a##!a#aa#?#".toList=(some none,some none) := by
  decide +kernel

/-- The same child input selects different actual captures solely because
its retained parent changes. The target keeps the corresponding two parts. -/
theorem actual_selected_parts :
    let x := "a#a#a##!a#a#".toList
    let T := tblV target x .callByValueSeq 5
    evSeqArgs target x .callByValueSeq T ["#".toList] [scanner,rest] x.length=
      some (some (["a#".toList,"a#".toList],8)) ∧
    evSeqArgs target x .callByValueSeq T ["a#".toList] [scanner,rest] x.length=
      some (some (["a#".toList,[]],10)) := by
  decide +kernel

/-- Original-argument preflight protects undefined nullable control before
an adjacent comparison could turn it into rejection. -/
theorem preflight_preserves_undefined :
    let d : CodewordControlFilter.Expr := .star (.test (.param 0))
    let B := .seq scanner (CodewordControlFilter.render scanner d)
    let x := "a#a#".toList
    let T := tblV target x .callByValueSeq 5
    evV target x .callByValueSeq T ["a#".toList] B x.length=none ∧
    evV target x .callByValueSeq T ["a#".toList]
      (.seq (.andP B) targetChild) x.length=none := by
  decide +kernel

private theorem rest_syntax : HelperArgument.Syntax 0 rest := by
  simp [rest,control,CodewordControlFilter.render,HelperArgument.Syntax,MExp.andP,
    scanner,NestedScannerArguments.scan,NestedScannerArguments.choice,MExp.failAlways]

private theorem tail_syntax : HelperArgument.Syntax 0 tail := by
  simp [tail,HelperArgument.Syntax,scanner,NestedScannerArguments.scan,
    NestedScannerArguments.choice,MExp.failAlways]

theorem source_firstOrder : source.FirstOrder := by
  have hA := ParserPrefixFusion.pure_firstOrder scanner RuntimePrefixExamples.header.pure
  have hD := HelperArgument.firstOrder 0 rest rest_syntax
  have hb := HelperArgument.firstOrder 0 tail tail_syntax
  intro r hr
  simp only [source,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl
  · trivial
  · exact ⟨True.intro,True.intro,⟨⟨hA,hD⟩,True.intro⟩,True.intro,True.intro⟩
  · exact ⟨hA,True.intro,hb⟩

theorem target_firstOrder : target.FirstOrder := by
  have hA := ParserPrefixFusion.pure_firstOrder scanner RuntimePrefixExamples.header.pure
  have hD := HelperArgument.firstOrder 0 rest rest_syntax
  have hb := HelperArgument.firstOrder 0 tail tail_syntax
  have hf := AdjacentCodewordControl.filter_firstOrder scanner (.call 0 [scanner]) hA
    ⟨hA,True.intro⟩ (.seq .token control) ⟨hA,hD⟩
  intro r hr
  simp only [target,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl
  · trivial
  · exact ⟨True.intro,⟨⟨hA,hD⟩,hf,hA,hD,True.intro⟩,True.intro,True.intro⟩
  · exact ⟨True.intro,CodewordControlFilter.wholeView_firstOrder tail hb⟩

/-- Every child call agrees, for every actual parent value and input,
including rejected and undefined original arguments. -/
theorem child_agreement (x : List Char) (E : List (List Char)) (n m p : Nat) (hp : p≤x.length) :
    evV source x .callByValuePar (tblV source x .callByValuePar (n+1)) E sourceChild p=
      evV target x .callByValueSeq (tblV target x .callByValueSeq (m+1)) E targetChild p := by
  exact AdjacentCodewordCalls.physical_agreement source target source_firstOrder target_firstOrder
    2 2 0 scanner tail control rfl rfl rfl RuntimePrefixExamples.header.pure
    rest_syntax tail_syntax RuntimePrefixExamples.code_prefixFree
    (fun x p q hp h => RuntimePrefixExamples.scanner_captured source x .callByValuePar _ [] p q hp h)
    x E n m p hp

/-- Fresh input capture supplies the parent's value. Neither a literal
parent specialization nor a manually supplied environment is required. -/
theorem root_agreement (x : List Char) (n m p : Nat) (hp : p≤x.length) :
    evV source x .callByValuePar (tblV source x .callByValuePar (n+2)) [] root p=
      evV target x .callByValueSeq (tblV target x .callByValueSeq (m+2)) [] root p := by
  let TS := tblV source x .callByValuePar (n+2)
  let US := tblV target x .callByValueSeq (m+2)
  let T := tblV source x .callByValuePar (n+1)
  let U := tblV target x .callByValueSeq (m+1)
  have hs : ruleAtM source.rules 1=some ⟨1,.seq (.param 0) (.seq (.chr '@') (.seq sourceChild footer))⟩ := rfl
  have ht : ruleAtM target.rules 1=some ⟨1,.seq (.chr '@') (.seq targetChild footer)⟩ := rfl
  have hA : evV source x .callByValuePar TS [] scanner p=
      evV target x .callByValueSeq US [] scanner p :=
    ParserPrefixFusion.pure_eval source target x _ _ TS US [] [] scanner RuntimePrefixExamples.header.pure p
  change evV source x .callByValuePar TS [] (.call 1 [scanner]) p=
    evV target x .callByValueSeq US [] (.call 1 [scanner]) p
  rw [evV_call_par hs rfl (by decide),evV_call_seq ht rfl]
  simp only [evParArgs,evSeqArgs]
  rw [←hA]
  cases ha : evV source x .callByValuePar TS [] scanner p with
  | none => rfl
  | some result => cases result with
    | none => rfl
    | some q =>
      have hq := evV_ok (tblV_ok source x .callByValuePar (n+2)) scanner p hp q ha
      dsimp only []
      rw [valAt_tblV_succ hs _ hp,valAt_tblV_succ ht _ hq]
      have hsf := (WordStarFilter.success_prefix (by decide)
        (tblV_sound source_firstOrder (by decide : Strategy.callByValuePar≠.callByName) (n+2)) [] scanner
        (ParserPrefixFusion.pure_firstOrder scanner RuntimePrefixExamples.header.pure) p q hp ha).2
      have hparam : evV source x .callByValuePar T [pre x p q] (.param 0) p=some (some q) := by
        change evV source x .callByValuePar T [] (.lit (pre x p q)) p=_
        simpa only [length_sfx x hq] using
          LastCodewordCandidate.literal_at source x .callByValuePar T [] (pre x p q) (sfx x q) p hsf
      rw [evV_seq_ok hparam]
      have hc : evV source x .callByValuePar T [pre x p q] (.chr '@') q=
          evV target x .callByValueSeq U [pre x p q] (.chr '@') q := rfl
      change (match evV source x .callByValuePar T [pre x p q] (.chr '@') q with
        | some (some z) => evV source x .callByValuePar T [pre x p q] (.seq sourceChild footer) z
        | other => other)=(match evV target x .callByValueSeq U [pre x p q] (.chr '@') q with
        | some (some z) => evV target x .callByValueSeq U [pre x p q] (.seq targetChild footer) z
        | other => other)
      rw [←hc]
      cases he : evV source x .callByValuePar T [pre x p q] (.chr '@') q with
      | none => rfl
      | some result => cases result with
        | none => rfl
        | some z =>
          have hz := evV_ok (tblV_ok source x .callByValuePar (n+1)) (.chr '@') q hq z he
          have hchild := child_agreement x [pre x p q] n m z hz
          change (match evV source x .callByValuePar T [pre x p q] sourceChild z with
            | some (some w) => evV source x .callByValuePar T [pre x p q] footer w
            | other => other)=(match evV target x .callByValueSeq U [pre x p q] targetChild z with
            | some (some w) => evV target x .callByValueSeq U [pre x p q] footer w
            | other => other)
          rw [←hchild]
          cases hc : evV source x .callByValuePar T [pre x p q] sourceChild z with
          | none => rfl
          | some result => cases result with
            | none => rfl
            | some w =>
              exact LastCodewordGrammar.syntax_eval source target x _ _ T U (tblV_ok _ _ _ _)
                [pre x p q] footer ⟨True.intro,True.intro⟩ w
                (evV_ok (tblV_ok source x .callByValuePar (n+1)) sourceChild z hz w hc)


theorem all_inputs (x : List Char) (r : Option (List Char)) :
    SObs source .callByValuePar root x r ↔ SObs target .callByValueSeq root x r := by
  have heq := AdjacentCodewordCalls.stable_result_eq source target x .callByValuePar .callByValueSeq root root 2
    (fun n m => root_agreement x n m x.length (Nat.le_refl _))
  rw [←decideObsV_iff source_firstOrder (by decide) (show root.FirstOrder from ⟨ParserPrefixFusion.pure_firstOrder scanner RuntimePrefixExamples.header.pure,True.intro⟩),
    ←decideObsV_iff target_firstOrder (by decide) (show root.FirstOrder from ⟨ParserPrefixFusion.pure_firstOrder scanner RuntimePrefixExamples.header.pure,True.intro⟩)]
  simp only [decideObsV,heq]

theorem language_translation :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧
      ∀ x, SObs source .callByValuePar root x (some []) ↔ SObs g .callByValueSeq start x (some []) :=
  ⟨target,root,target_firstOrder,⟨ParserPrefixFusion.pure_firstOrder scanner RuntimePrefixExamples.header.pure,True.intro⟩,fun x => all_inputs x (some [])⟩

end Shallot.MacroPeg.CBV.AdjacentCodewordExamples
