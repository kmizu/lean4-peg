import MacroPeg.CBV.FiniteSuffixRecursiveCompiler

namespace Shallot.MacroPeg.CBV.FiniteSuffixRecursiveExamples
open FiniteSuffixRecursiveSyntax
open RegularCaptureProduct (Node)
abbrev Term := FiniteSuffixRecursiveSyntax.Expr
abbrev Spec := FiniteSuffixRecursiveSyntax.Rule
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def nodes : List Node := [.lit [],.lit ['a'],.lit ['b'],.seq 1 5,.seq 3 2,.alt 4 0,.star 0,.notP 0]
def region := [['a','b']]
def peek (e : Term) : Term := .notP (.notP e)
def skipToPair : Term := .star (.seq (peek (.seq .any (.seq .any .any))) .any)
def isA (i : Nat) : Term := peek (.seq skipToPair (.seq (.replay i) (.seq (.chr 'b') (.notP .any))))
def isAB (i : Nat) : Term := peek (.seq skipToPair (.seq (.replay i) (.notP .any)))
def parentTail : Term := .seq (isA 0) (isAB 1)
def parentPrefix : Term := .seq parentTail (.seq (.lit ['a','b','{'])
  (.seq (.alt (.user 1 [5,1]) .eps) (.chr '}')))
def parent : Term := .seq parentPrefix parentTail
def child : Term := .seq (isAB 0) (.seq (isA 1)
  (.seq (.lit ['a','b','[']) (.seq (.alt (.user 0 [1,5]) .eps)
    (.seq (.chr ']') (.seq (isAB 0) (isA 1))))))
def outer : Term := .seq (isAB 0) (.seq (.user 0 [1,5]) (.seq (isAB 0) (.replay 0)))
def specs : List Spec := [⟨2,parent⟩,⟨2,child⟩,⟨1,outer⟩]
def entry : Term := .user 2 [5]
abbrev original := source nodes region specs
abbrev generated := target nodes region specs
def root := render nodes region specs none entry
def targetRoot := render nodes region specs (some []) entry

def frame : Bool → Nat → List Char
  | first,0 => ['a','b',if first then '{' else '[',if first then '}' else ']']
  | first,n+1 => ['a','b',if first then '{' else '[']++frame (!first) n++[if first then '}' else ']']
def input (n : Nat) := frame true n++['a','b']

theorem nodes_valid : RegularCaptureProduct.Valid nodes := FiniteSuffixCallCompiler.nodes_checked nodes (by decide +kernel)

theorem checked : FiniteSuffixRecursiveCompiler.check original root nodes region specs entry=true := by decide +kernel

theorem source_arities : original.rules.map MRule.arity=[0,0,0,0,0,0,0,0,2,2,1] := by decide +kernel

theorem fixed_target_size : generated.rules.length=844 ∧ generated.rules.all (fun r => r.arity==0)=true := by decide +kernel

/-- Both old values are nonempty in both users, but their literal views
and argument positions differ. This is not just an emptiness-state test. -/
theorem reversed_content_views :
    FiniteSuffixReplay.views region [['a'],['a','b']]=[some ['a'],some ['a','b']] ∧
    FiniteSuffixReplay.views region [['a','b'],['a']]=[some ['a','b'],some ['a']] := by decide +kernel

theorem actual_parent_and_child_tuples :
    evParArgs original (input 1) .callByValuePar (tblV original (input 1) .callByValuePar 12) [] [.call 1 [],.call 5 []] (input 1).length=
      some (some [['a'],['a','b']]) ∧
    evParArgs original (input 1) .callByValuePar (tblV original (input 1) .callByValuePar 12) [] [.call 5 [],.call 1 []] ((input 1).length-3)=
      some (some [['a','b'],['a']]) := by decide +kernel

theorem source_runs : ∀ n∈[0,1,2],
    evV original (input n) .callByValuePar (tblV original (input n) .callByValuePar 12) [] root (input n).length=some (some 0) := by decide +kernel

theorem target_runs : ∀ n∈[0,1,2],
    evV generated (input n) .callByValueSeq (tblV generated (input n) .callByValueSeq 24) [] targetRoot (input n).length=some (some 0) := by decide +kernel

/-- The child's [ab,a] view would reject the parent's subsequent a/ab tests.
Thus this direct run checks that returning restores the actual parent view. -/
def leakedChildView : MExp := .seq
  (render nodes region specs (some [some ['a'],some ['a','b']]) parentPrefix)
  (render nodes region specs (some [some ['a','b'],some ['a']]) parentTail)

theorem leaking_child_view_is_wrong :
    evV generated (input 1) .callByValueSeq (tblV generated (input 1) .callByValueSeq 24) [] leakedChildView (input 1).length=some none := by decide +kernel

theorem wrong_tuple_order_rejected :
    evV original (input 0) .callByValuePar (tblV original (input 0) .callByValuePar 12) []
      (render nodes region specs none (.seq (.user 0 [5,1]) (.lit ['a','b']))) (input 0).length=some none ∧
    evV generated (input 0) .callByValueSeq (tblV generated (input 0) .callByValueSeq 24) []
      (render nodes region specs (some []) (.seq (.user 0 [5,1]) (.lit ['a','b']))) (input 0).length=some none := by decide +kernel

theorem parent_accepts_only_its_actual_view :
    evV original (input 0) .callByValuePar (tblV original (input 0) .callByValuePar 12) [['a'],['a','b']]
      (render nodes region specs none parent) (input 0).length=some (some 2) ∧
    evV original (input 0) .callByValuePar (tblV original (input 0) .callByValuePar 12) [['a','b'],['a']]
      (render nodes region specs none parent) (input 0).length=some none := by decide +kernel

theorem observations (x : List Char) (rest : Option (List Char)) :
    SObs original .callByValuePar root x rest ↔ SObs generated .callByValueSeq targetRoot x rest :=
  FiniteSuffixRecursiveCompiler.observations_iff original root nodes region specs entry checked x rest

theorem original_language : (fun x => SObs original .callByValuePar root x (some []))=
    (fun x => SObs generated .callByValueSeq targetRoot x (some [])) :=
  FiniteSuffixRecursiveCompiler.language_translation original root nodes region specs entry checked


theorem unchanged_source_under_seq_fails :
    evV original (input 0) .callByValueSeq (tblV original (input 0) .callByValueSeq 12) [] root (input 0).length=some none := by decide +kernel

def captureInput (n : Nat) := List.replicate n 'a'++List.replicate n 'b'++['{','}','a','b']
theorem actual_unbounded_family_samples : ∀ n∈[1,2,4],
    evParArgs original (captureInput n) .callByValuePar (tblV original (captureInput n) .callByValuePar 20) []
      [.call 5 [],.call 1 []] (captureInput n).length=
        some (some [List.replicate n 'a'++List.replicate n 'b',['a']]) := by decide +kernel

theorem epsilon_helper (rs : List Spec) (x : List Char) (k : Nat) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV (source nodes region rs) x .callByValuePar (tblV (source nodes region rs) x .callByValuePar (k+1)) E (.call 0 []) p=some (some p) := by
  have h0 : ruleAtM (source nodes region rs).rules 0=some ⟨0,.lit []⟩ := rfl
  rw [evV_call_par h0 rfl (by decide)]
  change valAt (tblV (source nodes region rs) x .callByValuePar (k+1) 0 []) p=some (some p)
  rw [valAt_tblV_succ h0 [] hp]
  simp [evV,Shallot.stripPrefix?,length_sfx x hp]

def cycleSpecs : List Spec := [⟨1,.user 0 [0]⟩]
def cycleEntry : Term := .user 0 [0]

theorem cycle_rows (x : List Char) (p : Nat) (hp : p≤x.length) : ∀ k,
    valAt (tblV (source nodes region cycleSpecs) x .callByValuePar k nodes.length [[]]) p=none := by
  intro k
  have hr : ruleAtM (source nodes region cycleSpecs).rules nodes.length=some ⟨1,render nodes region cycleSpecs none (.user 0 [0])⟩ := rfl
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [valAt_tblV_succ hr [[]] hp]
    change evV (source nodes region cycleSpecs) x .callByValuePar (tblV (source nodes region cycleSpecs) x .callByValuePar k)
      [[]] (.call nodes.length [.call 0 []]) p=none
    rw [evV_call_par hr rfl (by decide)]
    cases k with
    | zero => rfl
    | succ j =>
      rw [evPar_cons_ok (epsilon_helper cycleSpecs x j [[]] p hp),evPar_nil]
      simpa [pre] using ih

theorem cycle_source_all_inputs (x : List Char) (k : Nat) :
    evV (source nodes region cycleSpecs) x .callByValuePar (tblV (source nodes region cycleSpecs) x .callByValuePar k) []
      (render nodes region cycleSpecs none cycleEntry) x.length=none := by
  have hr : ruleAtM (source nodes region cycleSpecs).rules nodes.length=some ⟨1,render nodes region cycleSpecs none (.user 0 [0])⟩ := rfl
  change evV (source nodes region cycleSpecs) x .callByValuePar (tblV (source nodes region cycleSpecs) x .callByValuePar k) []
    (.call nodes.length [.call 0 []]) x.length=none
  rw [evV_call_par hr rfl (by decide)]
  cases k with
  | zero => rfl
  | succ j =>
    rw [evPar_cons_ok (epsilon_helper cycleSpecs x j [] x.length (Nat.le_refl _)),evPar_nil]
    simpa [pre] using cycle_rows x x.length (Nat.le_refl _) (j+1)

theorem cycle_target_all_inputs (x : List Char) (k : Nat) :
    evV (target nodes region cycleSpecs) x .callByValueSeq (tblV (target nodes region cycleSpecs) x .callByValueSeq k) []
      (render nodes region cycleSpecs (some []) cycleEntry) x.length=none :=
  (FiniteSuffixRecursiveCorrespondence.undefined_iff nodes nodes_valid region cycleSpecs cycleEntry x).mp (cycle_source_all_inputs x) k

def nullableSpecs : List Spec := [⟨1,.star (.replay 0)⟩]
def nullableEntry : Term := .user 0 [0]

theorem nullable_rows (k : Nat) :
    valAt (tblV (source nodes region nullableSpecs) ['a','b'] .callByValuePar k nodes.length [[]]) 2=none := by
  cases k with
  | zero => rfl
  | succ k =>
    have hr : ruleAtM (source nodes region nullableSpecs).rules nodes.length=some ⟨1,render nodes region nullableSpecs none (.star (.replay 0))⟩ := rfl
    rw [valAt_tblV_succ hr [[]] (by decide)]
    rw [show render nodes region nullableSpecs none (.star (.replay 0))=.star (.seq (FiniteSuffixReplay.guard region) (.param 0)) from rfl,evV_star]
    exact evStar_stuck (j := 2) rfl (by omega)

theorem nullable_source_all_clocks (k : Nat) :
    evV (source nodes region nullableSpecs) ['a','b'] .callByValuePar (tblV (source nodes region nullableSpecs) ['a','b'] .callByValuePar k) []
      (render nodes region nullableSpecs none nullableEntry) 2=none := by
  have hr : ruleAtM (source nodes region nullableSpecs).rules nodes.length=some ⟨1,render nodes region nullableSpecs none (.star (.replay 0))⟩ := rfl
  change evV (source nodes region nullableSpecs) ['a','b'] .callByValuePar (tblV (source nodes region nullableSpecs) ['a','b'] .callByValuePar k) []
    (.call nodes.length [.call 0 []]) 2=none
  rw [evV_call_par hr rfl (by decide)]
  cases k with
  | zero => rfl
  | succ j =>
    rw [evPar_cons_ok (epsilon_helper nullableSpecs ['a','b'] j [] 2 (by decide)),evPar_nil]
    simpa [pre] using nullable_rows (j+1)

theorem nullable_target_all_clocks (k : Nat) :
    evV (target nodes region nullableSpecs) ['a','b'] .callByValueSeq (tblV (target nodes region nullableSpecs) ['a','b'] .callByValueSeq k) []
      (render nodes region nullableSpecs (some []) nullableEntry) 2=none :=
  (FiniteSuffixRecursiveCorrespondence.undefined_iff nodes nodes_valid region nullableSpecs nullableEntry ['a','b']).mp nullable_source_all_clocks k

theorem undefined_helper (rs : List Spec) (x : List Char) (p k : Nat) (hp : p≤x.length) :
    evV (source nodes region rs) x .callByValuePar (tblV (source nodes region rs) x .callByValuePar k) [] (.call 6 []) p=none := by
  have hr : ruleAtM (source nodes region rs).rules 6=some ⟨0,.star (.call 0 [])⟩ := rfl
  rw [evV_call_par hr rfl (by decide)]
  cases k with
  | zero => rfl
  | succ k =>
    change valAt (tblV (source nodes region rs) x .callByValuePar (k+1) 6 []) p=none
    rw [valAt_tblV_succ hr [] hp,evV_star]
    cases k with
    | zero => exact evStar_none rfl
    | succ j => exact evStar_stuck (epsilon_helper rs x j [] p hp) (by omega)

def undefinedEntry : Term := .user 0 [6,7]

theorem undefined_argument_source_all_inputs (x : List Char) (k : Nat) :
    evV original x .callByValuePar (tblV original x .callByValuePar k) [] (render nodes region specs none undefinedEntry) x.length=none := by
  have hr : ruleAtM original.rules nodes.length=some ⟨2,render nodes region specs none parent⟩ := rfl
  change evV original x .callByValuePar (tblV original x .callByValuePar k) [] (.call nodes.length [.call 6 [],.call 7 []]) x.length=none
  rw [evV_call_par hr rfl (by decide),evPar_cons_none (undefined_helper specs x x.length k (Nat.le_refl _))]

theorem undefined_argument_target_all_inputs (x : List Char) (k : Nat) :
    evV generated x .callByValueSeq (tblV generated x .callByValueSeq k) [] (render nodes region specs (some []) undefinedEntry) x.length=none :=
  (FiniteSuffixRecursiveCorrespondence.undefined_iff nodes nodes_valid region specs undefinedEntry x).mp (undefined_argument_source_all_inputs x) k

theorem failure_before_undefined_argument :
    evV original ['a'] .callByValuePar (tblV original ['a'] .callByValuePar 12) []
      (render nodes region specs none (.user 0 [7,6])) 1=some none ∧
    evV generated ['a'] .callByValueSeq (tblV generated ['a'] .callByValueSeq 24) []
      (render nodes region specs (some []) (.user 0 [7,6])) 1=some none := by decide +kernel

theorem bypassing_preflight_changes_undefinedness :
    evV generated ['a'] .callByValueSeq (tblV generated ['a'] .callByValueSeq 24) []
      (.call (address nodes region specs 0 [none,none]) []) 1=some none := by decide +kernel


def overflowBody : Term := .seq (.helper 5) (.seq (.chr '!') (.seq (.notP (.replay 0)) (.lit ['a','b'])))
def overflowSpecs : List Spec := [⟨1,overflowBody⟩]
def overflowEntry : Term := .user 0 [5]
def overflowInput := ['a','a','b','b','!','a','b']

theorem other_view_preserves_negative_replay :
    evV (source nodes region overflowSpecs) overflowInput .callByValuePar
      (tblV (source nodes region overflowSpecs) overflowInput .callByValuePar 16) []
      (render nodes region overflowSpecs none overflowEntry) overflowInput.length=some (some 0) ∧
    evV (target nodes region overflowSpecs) overflowInput .callByValueSeq
      (tblV (target nodes region overflowSpecs) overflowInput .callByValueSeq 32) []
      (render nodes region overflowSpecs (some []) overflowEntry) overflowInput.length=some (some 0) := by decide +kernel

theorem short_view_changes_negative_replay :
    evV (source nodes region overflowSpecs) ['a','b','!','a','b'] .callByValuePar
      (tblV (source nodes region overflowSpecs) ['a','b','!','a','b'] .callByValuePar 16) []
      (render nodes region overflowSpecs none overflowEntry) 5=some none ∧
    evV (target nodes region overflowSpecs) ['a','b','!','a','b'] .callByValueSeq
      (tblV (target nodes region overflowSpecs) ['a','b','!','a','b'] .callByValueSeq 32) []
      (render nodes region overflowSpecs (some []) overflowEntry) 5=some none := by decide +kernel

def replaySpecs : List Spec := [⟨1,.replay 0⟩]
def replayEntry : Term := .user 0 [5]
def unguarded : MGrammar := ⟨nodes.map (fun n => ⟨0,RegularCaptureProduct.body n⟩)++[⟨1,.param 0⟩]⟩

theorem omitted_guard_rejected : FiniteSuffixRecursiveCompiler.check unguarded
    (render nodes region replaySpecs none replayEntry) nodes region replaySpecs replayEntry=false := by decide +kernel

theorem invalid_calls_skip_undefined_actual : ∀ e∈[(.user 0 [6] : Term),.user 100 [6]],
    evV original ['a'] .callByValuePar (tblV original ['a'] .callByValuePar 0) [] (render nodes region specs none e) 1=some none ∧
    evV generated ['a'] .callByValueSeq (tblV generated ['a'] .callByValueSeq 0) [] (render nodes region specs (some []) e) 1=some none := by decide +kernel

end Shallot.MacroPeg.CBV.FiniteSuffixRecursiveExamples
