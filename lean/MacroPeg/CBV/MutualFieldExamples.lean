import MacroPeg.CBV.MutualFieldCompiler
import MacroPeg.CBV.RecursiveFieldExamples

namespace Shallot.MacroPeg.CBV.MutualFieldExamples
open MutualFieldSyntax
set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev short := RecursiveFieldExamples.short
abbrev long := RecursiveFieldExamples.long
abbrev words := RecursiveFieldExamples.words
abbrev pattern := RecursiveFieldExamples.pattern
abbrev block := RecursiveFieldExamples.block
abbrev doubled := RecursiveFieldExamples.doubled
abbrev base := RecursiveFieldExamples.base
abbrev restore := RecursiveFieldExamples.restore
abbrev actuals := RecursiveFieldExamples.actuals

def gArgs : List MExp := [doubled]
def fArgs : List MExp := [.param 0,.seq (.param 0) (.lit ['b'])]
def bodyF : MExp := .alt
  (.seq (.lit ['(']) (.seq (.call 1 gArgs) (.seq (.lit [')']) restore))) base
def bodyG : MExp := .seq (.call 0 fArgs) (.param 0)
def headers : List Header := [⟨2,pattern,bodyF⟩,⟨1,[0],bodyG⟩]
def root : MExp := .seq (.call 0 actuals) (.notP .any)
def original := source [] headers '#'
def generated := target [] headers '#'
def generatedRoot := emit 0 headers '#' root

def gBlock (n : Nat) : List Char := short n++['#']
def treeF (n : Nat) : Nat → List Char
  | 0 => block n++(short n++'!'::long n)
  | depth+1 => block n++'('::(gBlock (2*n)++(treeF (2*n) depth++
      (short (2*n)++')'::(long n++'!'::short n))))
def treeG (n depth : Nat) : List Char := gBlock n++(treeF n depth++short n)

theorem checked : MutualFieldCompiler.check original root [] headers '#' root=true := by decide +kernel

theorem source_and_target_arities :
    original.rules.map MRule.arity=[2,1] ∧ generated.rules.map MRule.arity=[1,1,6,1,2] := by decide +kernel

theorem different_source_and_target_addresses :
    address 0 headers 0=0 ∧ address 0 headers 1=3 ∧
    ruleAtM original.rules 1=some ⟨1,TupleFieldTransfer.sourceBody '#' [0] bodyG⟩ ∧
    ruleAtM generated.rules 4=some ⟨2,MExp.subst (CopyFieldCapture.views 1 [0]) (emit 0 headers '#' bodyG)⟩ := ⟨rfl,rfl,rfl,rfl⟩

theorem every_input_every_clock (x : List Char) (k : Nat) :
    evV original x .callByValuePar (tblV original x .callByValuePar k) [] root x.length=
      evV generated x .callByValueSeq (tblV generated x .callByValueSeq k) [] generatedRoot x.length :=
  MutualFieldCompiler.physical original root [] headers '#' root checked x k

theorem recursive_inputs :
    ([0,1,2].flatMap (fun n => [0,1,2,3].map (fun depth => (n,depth)))).all (fun (n,depth) =>
      evV original (treeF n depth) .callByValuePar (tblV original (treeF n depth) .callByValuePar (2*depth+1)) []
        root (treeF n depth).length==some (some 0))=true := by decide +kernel

theorem generated_recursive_inputs :
    ([0,1,2].flatMap (fun n => [0,1,2,3].map (fun depth => (n,depth)))).all (fun (n,depth) =>
      evV generated (treeF n depth) .callByValueSeq (tblV generated (treeF n depth) .callByValueSeq (2*depth+1)) []
        generatedRoot (treeF n depth).length==some (some 0))=true := by decide +kernel

def badParent : List Char := block 1++'('::(treeG 2 0++')'::(long 2++'!'::short 1))
theorem child_value_cannot_replace_the_parent :
    evV generated badParent .callByValueSeq (tblV generated badParent .callByValueSeq 3) [] generatedRoot badParent.length=some none := by decide +kernel

theorem malformed_declarations_and_actuals_are_rejected :
    MutualFieldSyntax.check [] [⟨2,[0],bodyF⟩,⟨1,[0],bodyG⟩] '#' root=false ∧
    MutualFieldSyntax.check [] headers '#' (.call 1 [.eps,.eps])=false ∧
    MutualFieldSyntax.check [] headers '#' (.call 0 [.lit ['#'],.eps])=false ∧
    MutualFieldSyntax.check [] [⟨2,pattern,.param 2⟩,⟨1,[0],bodyG⟩] '#' root=false ∧
    MutualFieldCompiler.check ⟨[]⟩ root [] headers '#' root=false := by decide +kernel

def nullableHeaders : List Header := [⟨2,pattern,bodyF⟩,⟨1,[0],.star .eps⟩]
def nullableSource := source [] nullableHeaders '#'
def nullableTarget := target [] nullableHeaders '#'
def nullableRoot : MExp := .call 1 [.lit ['a']]
theorem nullable_checked :
    MutualFieldCompiler.check nullableSource nullableRoot [] nullableHeaders '#' nullableRoot=true := by decide +kernel

theorem nullable_source_all_clocks (k : Nat) :
    evV nullableSource ['a','#'] .callByValuePar (tblV nullableSource ['a','#'] .callByValuePar k) [] nullableRoot 2=none := by
  have hr : ruleAtM nullableSource.rules 1=some ⟨1,TupleFieldTransfer.sourceBody '#' [0] (.star .eps)⟩ := rfl
  rw [nullableRoot,evV_call_par hr rfl (by decide),evPar_cons_ok (show
    evV nullableSource ['a','#'] .callByValuePar (tblV nullableSource ['a','#'] .callByValuePar k) [] (.lit ['a']) 2=some (some 1) from rfl),evPar_nil]
  change valAt (tblV nullableSource ['a','#'] .callByValuePar k 1 [['a']]) 2=none
  cases k with
  | zero => rfl
  | succ k =>
    rw [valAt_tblV_succ hr _ (by decide),TupleFieldTransfer.sourceBody]
    have ha : evV nullableSource ['a','#'] .callByValuePar (tblV nullableSource ['a','#'] .callByValuePar k) [['a']]
        (DelimiterTemplate.compile '#' (DelimitedWordPattern.sourceParts '#' [0])) 2=some (some 0) := rfl
    rw [evV_seq_ok ha,evV_star]
    exact evStar_stuck rfl (Nat.lt_irrefl _)

theorem nullable_target_all_clocks (k : Nat) :
    evV nullableTarget ['a','#'] .callByValueSeq (tblV nullableTarget ['a','#'] .callByValueSeq k) []
      (emit 0 nullableHeaders '#' nullableRoot) 2=none := by
  exact (MutualFieldCompiler.physical nullableSource nullableRoot [] nullableHeaders '#' nullableRoot nullable_checked ['a','#'] k).symm.trans
    (nullable_source_all_clocks k)

end Shallot.MacroPeg.CBV.MutualFieldExamples
