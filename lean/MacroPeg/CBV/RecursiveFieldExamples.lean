import MacroPeg.CBV.RecursiveFieldCompiler

namespace Shallot.MacroPeg.CBV.RecursiveFieldExamples
open RecursiveFieldSyntax DelimiterTemplate DelimitedWordPattern
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def short (n : Nat) : List Char := List.replicate n 'a'
def long (n : Nat) : List Char := short n++['b']
def words (n : Nat) : List (List Char) := [short n,long n]
def pattern : List Nat := [1,0,1]
def block (n : Nat) : List Char := encode '#' (words n) pattern
def doubled : MExp := .seq (.param 0) (.param 0)
def childArgs : List MExp := [doubled,.seq doubled (.lit ['b'])]
def base : MExp := .seq (.param 0) (.seq (.lit ['!']) (.param 1))
def restore : MExp := .seq (.param 1) (.seq (.lit ['!']) (.param 0))
def body : MExp := .alt
  (.seq (.lit ['(']) (.seq (.call 0 childArgs) (.seq (.lit [')']) restore))) base
def actuals : List MExp := [.star (.lit ['a']),.seq (.star (.lit ['a'])) (.lit ['b'])]
def root : MExp := .seq (.call 0 actuals) (.notP .any)
def original := source [] 2 '#' pattern body
def generated := target [] 2 '#' pattern body
def generatedRoot := emit 0 2 '#' pattern root

def tree (n : Nat) : Nat → List Char
  | 0 => block n++(short n++'!'::long n)
  | depth+1 => block n++'('::(tree (2*n) depth++')'::(long n++'!'::short n))

theorem checked : RecursiveFieldCompiler.check original root [] 2 '#' pattern body root=true := by decide +kernel

theorem every_input_every_clock (x : List Char) (k : Nat) :
    evV original x .callByValuePar (tblV original x .callByValuePar k) [] root x.length=
      evV generated x .callByValueSeq (tblV generated x .callByValueSeq k) [] generatedRoot x.length :=
  RecursiveFieldCompiler.physical original root [] 2 '#' pattern body root checked x k

theorem source_arities : original.rules.map MRule.arity=[2] := by decide
theorem generated_arities : generated.rules.map MRule.arity=[1,1,6] := by decide

theorem short_doubled (n : Nat) : short (2*n)=short n++short n := by
  simp [short,Nat.two_mul]

theorem fresh_child_values (n : Nat) :
    WordArguments.value (words n) doubled=some (short (2*n)) ∧
    WordArguments.value (words n) (.seq doubled (.lit ['b']))=some (long (2*n)) := by
  simp [WordArguments.value,words,doubled,long,short_doubled]

theorem word_at (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Nat → List (List Char) → Val) (E : List (List Char)) (e : MExp)
    (he : WordArguments.Word e) (w rest : List Char) (hv : WordArguments.value E e=some w)
    (p : Nat) (hx : sfx x p=w++rest) :
    evV g x s T E e p=some (some rest.length) := by
  rw [WordArguments.word_eval g x s T E e he p,hv,WordArguments.literal]
  simp only [evV,(CBVtoCBN.stripPrefix_exact _ _ _).mpr hx]

/-- Fresh recursive actuals capture doubled words at the child's real input
position, rather than reusing the parent tuple or a finite word palette. -/
theorem fresh_child_captures (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Nat → List (List Char) → Val) (n : Nat) (rest : List Char) (p : Nat)
    (hp : p≤x.length) (hx : sfx x p=long (2*n)++rest) :
    evParArgs g x s T (words n) childArgs p=some (some (words (2*n))) := by
  have hx0 : sfx x p=short (2*n)++'b'::rest := by simpa [long,List.append_assoc] using hx
  have h0 := word_at g x s T (words n) doubled ⟨True.intro,True.intro⟩ _ _ (fresh_child_values n).1 p hx0
  have h1 := word_at g x s T (words n) (.seq doubled (.lit ['b'])) ⟨⟨True.intro,True.intro⟩,True.intro⟩ _ _ (fresh_child_values n).2 p hx
  have hpre0 : pre x p ('b'::rest).length=short (2*n) := by
    simpa only [length_sfx x hp] using pre_eq (sfx_is_suffix x p) hx0
  have hpre1 : pre x p rest.length=long (2*n) := by
    simpa only [length_sfx x hp] using pre_eq (sfx_is_suffix x p) hx
  rw [childArgs,evPar_cons_ok h0,evPar_cons_ok h1,evPar_nil]
  simp only [hpre0,hpre1,words]

theorem recursive_inputs :
    ([0,1,2].flatMap (fun n => [0,1,2,3].map (fun depth => (n,depth)))).all (fun (n,depth) =>
      evV original (tree n depth) .callByValuePar (tblV original (tree n depth) .callByValuePar (depth+1)) [] root (tree n depth).length==some (some 0))=true := by decide +kernel

theorem generated_recursive_inputs :
    ([0,1,2].flatMap (fun n => [0,1,2,3].map (fun depth => (n,depth)))).all (fun (n,depth) =>
      evV generated (tree n depth) .callByValueSeq (tblV generated (tree n depth) .callByValueSeq (depth+1)) [] generatedRoot (tree n depth).length==some (some 0))=true := by decide +kernel

theorem bad_parent_restoration_rejected :
    evV generated "ab#a#ab#(aab#aa#aab#aa!aab)ab!aa".toList .callByValueSeq
      (tblV generated "ab#a#ab#(aab#aa#aab#aa!aab)ab!aa".toList .callByValueSeq 2) [] generatedRoot
      "ab#a#ab#(aab#aa#aab#aa!aab)ab!aa".toList.length=some none := by decide +kernel

theorem missing_component_rejected : RecursiveFieldSyntax.check [] 2 '#' [0] body root=false := by decide +kernel
theorem delimiter_in_actual_rejected : RecursiveFieldSyntax.check [] 2 '#' pattern
    (.call 0 [.lit ['#'],.param 1]) root=false := by decide +kernel
theorem unchecked_positive_producer_rejected : RecursiveFieldSyntax.check [] 2 '#' pattern
    (.call 0 [.call 0 [.param 0,.param 1],.param 1]) root=false := by decide +kernel
theorem actual_source_declaration_is_checked : RecursiveFieldCompiler.check
    ⟨[⟨2,.eps⟩]⟩ root [] 2 '#' pattern body root=false := by decide +kernel

theorem recursive_query_in_actual_is_checked : exprCheck 0 2 2 '#'
    (.call 0 [.seq (.notP (.call 0 [.param 0,.param 1])) (.param 0),.param 1])=true := by decide +kernel

def partialRoot : MExp := .call 0 [.star .eps,.lit ['b']]
theorem partial_actual_checked : RecursiveFieldCompiler.check original partialRoot [] 2 '#' pattern body partialRoot=true := by decide +kernel

theorem partial_actual_both_undefined (x : List Char) (k : Nat) :
    evV original x .callByValuePar (tblV original x .callByValuePar k) [] partialRoot x.length=none ∧
    evV generated x .callByValueSeq (tblV generated x .callByValueSeq k) [] (emit 0 2 '#' pattern partialRoot) x.length=none := by
  have hrow : ruleAtM original.rules 0=some ⟨2,TupleFieldTransfer.sourceBody '#' pattern body⟩ := rfl
  have hv : evV original x .callByValuePar (tblV original x .callByValuePar k) [] partialRoot x.length=none := by
    rw [partialRoot,evV_call_par hrow rfl (by decide),evPar_cons_none (by rw [evV_star,evStar_stuck (by rfl) (by omega)])]
  have he := RecursiveFieldCompiler.physical original partialRoot [] 2 '#' pattern body partialRoot partial_actual_checked x k
  exact ⟨hv,he.symm.trans hv⟩

def nullableBody : MExp := .star (.alt (.param 0) .eps)
def nullableSource := source [] 2 '#' pattern nullableBody
def nullableTarget := target [] 2 '#' pattern nullableBody
theorem value_dependent_nullable_body_checked : RecursiveFieldCompiler.check nullableSource root [] 2 '#' pattern nullableBody root=true := by decide +kernel

theorem empty_word_nullable_star_propagates :
    evV nullableSource "b##b#X".toList .callByValuePar (tblV nullableSource "b##b#X".toList .callByValuePar 1) [] root 6=none ∧
    evV nullableTarget "b##b#X".toList .callByValueSeq (tblV nullableTarget "b##b#X".toList .callByValueSeq 1) [] generatedRoot 6=none := by decide +kernel

end Shallot.MacroPeg.CBV.RecursiveFieldExamples
