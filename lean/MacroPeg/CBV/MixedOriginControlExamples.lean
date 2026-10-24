import MacroPeg.CBV.MixedOriginSyntax
import MacroPeg.CBV.MixedAdjacentExamples

namespace Shallot.MacroPeg.CBV.MixedOriginControlExamples
open AdjacentCallsiteRecursive (argument)
open MixedOriginControl
open MixedAdjacentRecursive (Body)
open MixedAdjacentExamples (header two dynamic good capturedArgument)
open RuntimeShiftFilter (block)
open CodewordReplay (power)

/-- Source user zero mutually recurses through user one, including a
shifted recursive call inside the latter's general argument. -/
def parts : List (Part header) := [
  ⟨true,.alt (.seq (.chr '@') (.seq (.replay 1 (.seq (.param 0) (.seq (.chr ':') (.call 0 two))))
      (.seq (.chr '?') (.param 0)))) (.seq (.chr '!') (.param 0)),false⟩,
  ⟨false,.seq (.chr '~') (.seq (.call 0 dynamic) (.seq (.chr '?') (.param 0))),false⟩,
  ⟨false,.seq (.chr 'Z') (.param 0),false⟩]

/-- User zero chooses between shifted and ordinary replay. Its first test
negates a whole ordinary replay leaf at the capture's origin. User two
negates the shifted leaf and can return before the argument's endpoint. -/
def specs : List Spec := [
  ⟨true,.alt (.guard (.notP (.leaf 2)) (.leaf 0)) (.leaf 2)⟩,
  ⟨false,.leaf 1⟩,
  ⟨true,.notP (.leaf 0)⟩]

theorem valid : Valid header parts specs := by
  simp only [Valid,specs,List.mem_cons,List.not_mem_nil,or_false]
  intro s hs
  rcases hs with rfl | rfl | rfl
  · exact ⟨⟨⟨parts[2],rfl,by decide⟩,parts[0],rfl,by decide⟩,parts[2],rfl,by decide⟩
  · exact ⟨parts[1],rfl,by decide⟩
  · exact ⟨parts[0],rfl,by decide⟩

def root : Body header := .call 0 two

theorem executions :
    let eval := fun (x : List Char) =>
      (evV (source header parts specs) x .callByValuePar
        (table (source header parts specs) x 9) [] (render header specs root) x.length,
       evV (target header parts specs) x .callByValueSeq
        (tblV (target header parts specs) x .callByValueSeq 9) [] (targetRender header parts specs root) x.length)
    eval good=(some (some 0),some (some 0)) ∧
    eval (good.take (good.length-2))=(some none,some none) ∧
    eval (power (block 1) 3++['@']++capturedArgument++['~']++power (block 0) 3++['!']++
      power (block 0) 2++['?']++capturedArgument.take (capturedArgument.length-3)++
      ['?']++power (block 1) 2)=(some none,some none) ∧
    eval (power (block 1) 2++['Z']++power (block 1) 2)=(some (some 0),some (some 0)) ∧
    eval (power (block 1) 2++['Z']++block 1)=(some none,some none) := by
  decide +kernel

/-- Negation of a shifted leaf succeeds at the original caller position,
although the actual argument first captured two whole codewords. -/
theorem rollback :
    let x := power (block 1) 2
    evV (source header parts specs) x .callByValuePar (table (source header parts specs) x 3)
      [] (render header specs (.call 2 two)) x.length=some (some x.length) ∧
    evV (target header parts specs) x .callByValueSeq (tblV (target header parts specs) x .callByValueSeq 4)
      [] (targetRender header parts specs (.call 2 two)) x.length=some (some x.length) := by
  decide +kernel

/-- A failed actual argument cannot be negated into success. -/
theorem failed_argument :
    let x := block 1
    evV (source header parts specs) x .callByValuePar (table (source header parts specs) x 3)
      [] (render header specs (.call 2 two)) x.length=some none ∧
    evV (target header parts specs) x .callByValueSeq (tblV (target header parts specs) x .callByValueSeq 4)
      [] (targetRender header parts specs (.call 2 two)) x.length=some none := by
  decide +kernel

/-- Empty-loop general arguments stay undefined even when the source
callee is a negative plan. This is independent of either recursion table. -/
def negativeSpecs : List Spec := [⟨false,.notP (.leaf 0)⟩]
def negativeParts : List (Part header) := [⟨false,.eps,false⟩]

theorem undefined_argument (x : List Char) (T U V : ClockFreezing.Table) (E F : List (List Char)) (p : Nat) :
    evV (source header negativeParts negativeSpecs) x .callByValuePar T E
      (render header negativeSpecs (.replay 0 (.star .eps))) p=none ∧
    evV (core header negativeParts negativeSpecs) x .callByValuePar U E
      (coreRender header negativeParts negativeSpecs false (.replay 0 (.star .eps))) p=none ∧
    evV (target header negativeParts negativeSpecs) x .callByValueSeq V F
      (targetRender header negativeParts negativeSpecs (.replay 0 (.star .eps))) p=none := by
  have hloop (g : MGrammar) (s : Strategy) (W : ClockFreezing.Table) (G : List (List Char)) :
      evV g x s W G (.star .eps) p=none := by
    rw [evV_star]
    apply evStar_stuck (j:=p)
    · rfl
    · omega
  refine ⟨?_,?_,?_⟩
  · rw [show render header negativeSpecs (.replay 0 (.star .eps))=.call 1 [.star .eps] from rfl]
    rw [evV_call_par (source_rule header negativeParts negativeSpecs 0 negativeSpecs[0] rfl) rfl (by decide)]
    simp only [evParArgs,hloop]
  · rw [coreRender_replay header negativeParts negativeSpecs false 0 negativeSpecs[0] rfl rfl]
    apply evV_seq_none
    rw [CallLookahead.evV_peek]
    change CallLookahead.peek p (evV _ _ _ _ E (.star .eps) p)=none
    rw [hloop]; rfl
  · change evV _ _ _ _ F (.seq (.andP (.star .eps)) _) p=none
    apply evV_seq_none
    rw [CallLookahead.evV_peek,hloop]; rfl

/-- The original source grammar contains the control plan in its user
body, not an obligatory leading replay. Its actual call uses A;A. -/
theorem direct_syntax :
    (source header parts specs).rules[1]?.map MRule.body = some
      (.alt (.seq (.andP (.notP (sourceLeaf header parts specs 2))) (sourceLeaf header parts specs 0))
        (sourceLeaf header parts specs 2)) ∧
    render header specs root=.call 1 [argument header two] := by
  constructor <;> rfl

theorem all_inputs (x : List Char) (r : Option (List Char)) :
    SObs (source header parts specs) .callByValuePar (render header specs root) x r ↔
    SObs (target header parts specs) .callByValueSeq (targetRender header parts specs root) x r :=
  observations_iff header parts specs valid root x r

private theorem parts_typed : ∀ r∈parts, MixedOriginSyntax.WellTyped specs r.body := by
  intro r hr
  simp only [parts,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl <;> simp [MixedOriginSyntax.WellTyped,specs]

theorem direct_grammar : source header parts specs=MixedOriginSyntax.original header parts specs :=
  MixedOriginSyntax.source_eq_original header parts specs parts_typed

theorem direct_all_inputs (x : List Char) (r : Option (List Char)) :
    SObs (MixedOriginSyntax.original header parts specs) .callByValuePar (MixedOriginSyntax.sourceExpr root) x r ↔
    SObs (target header parts specs) .callByValueSeq (targetRender header parts specs root) x r := by
  apply MixedOriginSyntax.original_observations header parts specs valid parts_typed root _ x r
  simp [MixedOriginSyntax.WellTyped,specs,root]

end Shallot.MacroPeg.CBV.MixedOriginControlExamples
