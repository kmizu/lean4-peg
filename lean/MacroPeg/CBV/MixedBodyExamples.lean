import MacroPeg.CBV.MixedBodyCompiler
import MacroPeg.CBV.MixedOriginControlExamples

namespace Shallot.MacroPeg.CBV.MixedBodyExamples
open MixedBodyCompiler
open MixedBodySyntax (Expression)
open MixedAdjacentRecursive (Body)
open MixedOriginControl (Part)
open MixedAdjacentExamples (header two dynamic)
open RuntimeShiftFilter (block)
open CodewordReplay (power)

def captured : Body header := .seq (.param 0) (.seq (.chr ':') (.call 0 two))
def shifted : Part header :=
  ⟨true,.seq (.chr '@') (.seq (.replay 1 captured) (.seq (.chr '?') (.param 0))),false⟩
def ordinary : Part header := ⟨false,.seq (.chr 'R') (.param 0),false⟩
def delimiter : Part header := ⟨false,.chr 'S',false⟩
def finalPart : Part header := ⟨true,.seq (.chr '!') (.param 0),false⟩

def nested : Expression header :=
  .seq (.star (.seq (.star (.alt (.leaf shifted) (.leaf ordinary))) (.leaf delimiter))) (.leaf finalPart)
def replayBody : Expression header :=
  .leaf ⟨false,.seq (.chr '~') (.seq (.call 0 dynamic) (.seq (.chr '?') (.param 0))),false⟩
def users : List (User header) := [⟨true,nested⟩,⟨false,replayBody⟩]
def root : Body header := .call 0 two

theorem valid : Valid header users := by
  apply valid_of_kinds
  intro u hu hs
  simp only [users,List.mem_cons,List.not_mem_nil,or_false] at hu
  rcases hu with rfl | rfl
  · cases hs
  · intro r hr
    change r∈[⟨false,_,false⟩] at hr
    obtain rfl := List.mem_singleton.mp hr
    exact Or.inl rfl

/-- Parent #² plus a fresh colon and a shifted a# child is a general
capture. User one captures it, invokes another shifted child, and returns
with the whole general parent and then the original #² still available. -/
def argumentWord : List Char := power (block 0) 2++[':']++power (block 1) 3++['!']++power (block 1) 2
def leftUnit : List Char := power (block 0) 3++['@']++argumentWord++['~']++power (block 0) 3++['!']++
  power (block 0) 2++['?']++argumentWord++['?']++power (block 0) 2
def good : List Char := leftUnit++power (block 0) 2++['R']++power (block 0) 2++
  power (block 0) 2++['S']++power (block 0) 2++['S']++power (block 0) 3++['!']++power (block 0) 2

/-- Inner repetition selects both leaf kinds. The second outer iteration
has zero inner iterations, and the last shifted replay is outside both
stars. All user calls are inside the original nested consuming body. -/
theorem source_execution :
    evV (source header users) good .callByValuePar (tblV (source header users) good .callByValuePar 7)
      [] (sourceRender header users root) good.length=some (some 0) := by
  decide +kernel

theorem target_execution :
    evV (target header users) good .callByValueSeq (tblV (target header users) good .callByValueSeq 9)
      [] (targetRender header users root) good.length=some (some 0) := by
  decide +kernel

theorem short_outer :
    let x := good.take (good.length-1)
    evV (source header users) x .callByValuePar (tblV (source header users) x .callByValuePar 7)
      [] (sourceRender header users root) x.length=some none ∧
    evV (target header users) x .callByValueSeq (tblV (target header users) x .callByValueSeq 9)
      [] (targetRender header users root) x.length=some none := by
  decide +kernel

theorem all_inputs (x : List Char) (r : Option (List Char)) :
    SObs (source header users) .callByValuePar (sourceRender header users root) x r ↔
    SObs (target header users) .callByValueSeq (targetRender header users root) x r :=
  observations_iff header users valid root x r

/-- The repeated operand has a negative, zero-consuming successful output.
It is intentionally not a Consumer plan. -/
def nullableUsers : List (User header) :=
  [⟨false,.star (.notP (.leaf ⟨false,.chr '!',false⟩))⟩]
def nullableRoot : Body header := .replay 0 (.lit ['a'])

theorem nullable_valid : Valid header nullableUsers := by
  apply valid_of_source_kinds
  intro u hu _
  obtain rfl := List.mem_singleton.mp hu
  exact Or.inl rfl

theorem nullable_executions :
    let eval := fun (x : List Char) =>
      (evV (source header nullableUsers) x .callByValuePar (tblV (source header nullableUsers) x .callByValuePar 3)
        [] (sourceRender header nullableUsers nullableRoot) x.length,
       evV (target header nullableUsers) x .callByValueSeq (tblV (target header nullableUsers) x .callByValueSeq 4)
        [] (targetRender header nullableUsers nullableRoot) x.length)
    eval ['a','!']=(some (some 2),some (some 2)) ∧
    eval ['a','?']=(none,none) ∧
    eval ['b','?']=(some none,some none) := by
  decide +kernel

theorem nullable_all_inputs (x : List Char) (r : Option (List Char)) :
    SObs (source header nullableUsers) .callByValuePar (sourceRender header nullableUsers nullableRoot) x r ↔
    SObs (target header nullableUsers) .callByValueSeq (targetRender header nullableUsers nullableRoot) x r :=
  observations_iff header nullableUsers nullable_valid nullableRoot x r

private theorem users_typed : ∀ u∈users, MixedOriginSyntax.WellTyped (specs users) u.body.body := by
  have hc (a : AdjacentCallsiteRecursive.Argument header) : MixedOriginSyntax.WellTyped (specs users) (.call 0 a) :=
    ⟨(specs users)[0],rfl,rfl⟩
  have hr : MixedOriginSyntax.WellTyped (specs users) (.replay 1 captured) :=
    ⟨⟨(specs users)[1],rfl,rfl⟩,⟨True.intro,True.intro,hc two⟩⟩
  have ha : MixedOriginSyntax.WellTyped (specs users) (MixedBodyLeaves.raw shifted) :=
    raw_typed header _ shifted ⟨True.intro,hr,True.intro,True.intro⟩
  have hb : MixedOriginSyntax.WellTyped (specs users) (MixedBodyLeaves.raw ordinary) :=
    raw_typed header _ ordinary ⟨True.intro,True.intro⟩
  have hd : MixedOriginSyntax.WellTyped (specs users) (MixedBodyLeaves.raw delimiter) :=
    raw_typed header _ delimiter True.intro
  have hf : MixedOriginSyntax.WellTyped (specs users) (MixedBodyLeaves.raw finalPart) :=
    raw_typed header _ finalPart ⟨True.intro,True.intro⟩
  intro u hu
  simp only [users,List.mem_cons,List.not_mem_nil,or_false] at hu
  rcases hu with rfl | rfl
  · exact ⟨⟨⟨ha,hb⟩,hd⟩,hf⟩
  · exact raw_typed header _ _ ⟨True.intro,hc dynamic,True.intro,True.intro⟩

theorem direct_grammar : source header users=original header users := source_eq_original header users users_typed

theorem direct_all_inputs (x : List Char) (r : Option (List Char)) :
    SObs (original header users) .callByValuePar (MixedOriginSyntax.sourceExpr root) x r ↔
    SObs (target header users) .callByValueSeq (targetRender header users root) x r := by
  have he : MixedOriginSyntax.WellTyped (specs users) root := ⟨(specs users)[0],rfl,rfl⟩
  rw [←direct_grammar,←MixedOriginSyntax.source_syntax header _ root he]
  exact all_inputs x r

def commitUsers : List (User header) := [⟨true,
  .seq (.alt (.leaf ⟨false,.eps,false⟩) (.leaf ⟨true,.eps,false⟩)) (.leaf ⟨false,.chr '!',false⟩)⟩]

/-- The short first branch succeeds but its continuation fails. Pushing
continuations through choice must not retry the longer shifted branch. -/
theorem commitment :
    let x := power (block 0) 5++['!']
    evV (source header commitUsers) x .callByValuePar (tblV (source header commitUsers) x .callByValuePar 3)
      [] (sourceRender header commitUsers root) x.length=some none ∧
    evV (target header commitUsers) x .callByValueSeq (tblV (target header commitUsers) x .callByValueSeq 4)
      [] (targetRender header commitUsers root) x.length=some none := by
  decide +kernel

def nestedStarUsers : List (User header) := [⟨false,.star (.star (.leaf ⟨false,.chr '!',false⟩))⟩]

theorem nested_star_executions :
    let eval := fun (x : List Char) =>
      (evV (source header nestedStarUsers) x .callByValuePar (tblV (source header nestedStarUsers) x .callByValuePar 3)
        [] (sourceRender header nestedStarUsers nullableRoot) x.length,
       evV (target header nestedStarUsers) x .callByValueSeq (tblV (target header nestedStarUsers) x .callByValueSeq 4)
        [] (targetRender header nestedStarUsers nullableRoot) x.length)
    eval ['a','!']=(none,none) ∧ eval ['a','?']=(none,none) := by
  decide +kernel

end Shallot.MacroPeg.CBV.MixedBodyExamples
