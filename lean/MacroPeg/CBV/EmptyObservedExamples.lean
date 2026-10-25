import MacroPeg.CBV.EmptyObservedCompiler

namespace Shallot.MacroPeg.CBV.EmptyObservedExamples
open EmptyObservedSyntax
abbrev Term := EmptyObservedSyntax.Expr
abbrev Spec := EmptyObservedSyntax.Rule
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Test the retained word's emptiness, while restoring the current position.
The actual source still reaches EOF and replays its real stored parameter. -/
def emptyTest (i : Nat) : Term := .notP (.notP (.seq (.star .any) (.atEnd i)))
def nonemptyTest (i : Nat) : Term := .notP (emptyTest i)
def balanced : Term := .alt (.seq (.chr 'a') (.seq (.call 0 []) (.chr 'b'))) .eps
def parent : Term := .seq (.notP (.notP (.chr 'a'))) (.seq (.call 0 []) (.seq (.chr '!')
  (.seq (.call 2 [emptyTest 1,.seq (nonemptyTest 0) (.alt (.chr '[') (.chr 'c'))])
  (.seq (.chr ':') (.seq (emptyTest 1) (nonemptyTest 0))))))
def child : Term := .seq (emptyTest 0) (.seq (nonemptyTest 1)
  (.seq (.alt (.seq (.chr '[') (.seq (.call 1 [.call 0 [],emptyTest 0]) (.chr ']'))) (.chr 'c'))
    (.seq (emptyTest 0) (nonemptyTest 1))))
def outer : Term := .seq (nonemptyTest 0) (.call 1 [.call 0 [],.eps])
def specs : List Spec := [⟨0,balanced⟩,⟨2,parent⟩,⟨2,child⟩,⟨1,outer⟩]
def entry : Term := .call 1 [.call 0 [],.eps]
def root : Term := .seq entry (.notP .any)
def argumentUser : Term := .seq (.call 3 [entry]) (.notP .any)
def actual : MGrammar := source specs

theorem checked : EmptyObservedCompiler.check actual specs=true := by decide +kernel

theorem root_checked : EmptyObservedCompiler.rootCheck (original root) root=true := by decide +kernel

theorem mixed_arities : actual.rules.map MRule.arity=[0,2,2,1] := by decide +kernel

theorem fixed_nullary_target : (target specs).rules.length=22 ∧ (target specs).rules.all (fun r => r.arity==0)=true := by decide +kernel

def word (n : Nat) := List.replicate n 'a'++List.replicate n 'b'
def sample (n : Nat) := word n++['!','c',':']
def nested (n m : Nat) := word n++['!','[']++sample m++[']',':']

theorem actual_balanced_captures : ∀ n∈[1,2,4],
    evParArgs actual (sample n) .callByValuePar (tblV actual (sample n) .callByValuePar 12) []
      ([.call 0 [],.eps].map original) (sample n).length=some (some [word n,[]]) := by decide +kernel

theorem source_runs : ∀ n∈[1,2,4],
    evV actual (sample n) .callByValuePar (tblV actual (sample n) .callByValuePar 12) []
      (original root) (sample n).length=some (some 0) := by decide +kernel

theorem target_runs : ∀ n∈[1,2,4],
    evV (target specs) (sample n) .callByValueSeq (tblV (target specs) (sample n) .callByValueSeq 12) []
      (emit specs [] false root) (sample n).length=some (some 0) := by decide +kernel

theorem nested_source : ∀ pair∈[(1,3),(3,1)],
    let x := nested pair.1 pair.2
    evV actual x .callByValuePar (tblV actual x .callByValuePar 12) [] (original root) x.length=some (some 0) := by decide +kernel

theorem nested_target : ∀ pair∈[(1,3),(3,1)],
    let x := nested pair.1 pair.2
    evV (target specs) x .callByValueSeq (tblV (target specs) x .callByValueSeq 12) [] (emit specs [] false root) x.length=some (some 0) := by decide +kernel

theorem user_call_inside_actual_source :
    evV actual (nested 1 2) .callByValuePar (tblV actual (nested 1 2) .callByValuePar 12) []
      (original argumentUser) (nested 1 2).length=some (some 0) := by decide +kernel

theorem user_call_inside_actual_target :
    evV (target specs) (nested 1 2) .callByValueSeq (tblV (target specs) (nested 1 2) .callByValueSeq 12) []
      (emit specs [] false argumentUser) (nested 1 2).length=some (some 0) := by decide +kernel

/-- An operational strategy difference, not language-class separation. -/
theorem unchanged_source_under_seq_fails :
    evV actual (sample 1) .callByValueSeq (tblV actual (sample 1) .callByValueSeq 12) []
      (original argumentUser) (sample 1).length=some none := by decide +kernel

theorem observations (x : List Char) (rest : Option (List Char)) :
    SObs actual .callByValuePar (original root) x rest ↔
      SObs (target specs) .callByValueSeq (emit specs [] false root) x rest :=
  EmptyObservedCompiler.observations_iff actual specs (original root) root checked root_checked x rest

theorem original_language : (fun x => SObs actual .callByValuePar (original root) x (some []))=
    (fun x => SObs (target specs) .callByValueSeq (emit specs [] false root) x (some [])) :=
  EmptyObservedCompiler.language_translation actual specs (original root) root checked root_checked

/-- The abstraction keeps emptiness, rather than the complete old word. -/
theorem foreign_same_view_agrees (x : List Char) (p k : Nat) (hp : p≤x.length) :
    evV actual x .callByValuePar (tblV actual x .callByValuePar k) [['a'],[]] (original parent) p=
      evV actual x .callByValuePar (tblV actual x .callByValuePar k) [['b','b','b'],[]] (original parent) p := by
  have ha := (EmptyObservedCorrespondence.physical specs x parent [['a'],[]] p k hp).1
  have hb := (EmptyObservedCorrespondence.physical specs x parent [['b','b','b'],[]] p k hp).1
  exact ha.symm.trans hb

/-- The source guard is essential: arbitrary replay distinguishes these
nonempty values at the same non-EOF position. -/
theorem unguarded_replay_cannot_use_only_empty_bits :
    evV actual ['a'] .callByValuePar (tblV actual ['a'] .callByValuePar 0) [['a']] (.param 0) 1=some (some 0) ∧
    evV actual ['a'] .callByValuePar (tblV actual ['a'] .callByValuePar 0) [['b']] (.param 0) 1=some none := by decide +kernel

def bad : MGrammar := ⟨[⟨1,.param 0⟩]⟩
theorem unchecked_direct_replay_rejected : EmptyObservedCompiler.check bad [⟨1,.atEnd 0⟩]=false := by decide +kernel

def recursion : List Spec := [⟨1,.call 0 [.atEnd 0]⟩]
def recursiveRoot : Term := .call 0 [.eps]

theorem recursive_source_all_clocks (k : Nat) :
    evV (source recursion) [] .callByValuePar (tblV (source recursion) [] .callByValuePar k) [] (original recursiveRoot) 0=none := by
  have hh : ∀ k, valAt (tblV (source recursion) [] .callByValuePar k 0 [[]]) 0=none := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [valAt_tblV_succ (show ruleAtM (source recursion).rules 0=some ⟨1,original (.call 0 [.atEnd 0])⟩ from rfl) [[]] (by decide)]
      simpa [original,originalArgs,evV,evParArgs,source_rule,recursion,Shallot.stripPrefix?,pre,sfx] using ih
  simpa [recursiveRoot,original,originalArgs,evV,evParArgs,source_rule,recursion,pre,sfx,Shallot.stripPrefix?] using hh k

theorem recursive_target_all_clocks (k : Nat) :
    evV (target recursion) [] .callByValueSeq (tblV (target recursion) [] .callByValueSeq k) []
      (emit recursion [] false recursiveRoot) 0=none :=
  (EmptyObservedCorrespondence.physical recursion [] recursiveRoot [] 0 k (by decide)).1.trans (recursive_source_all_clocks k)

def nullableSpecs : List Spec := [⟨1,.star (.atEnd 0)⟩]
def nullableRoot : Term := .call 0 [.eps]

theorem nullable_source_all_clocks (k : Nat) :
    evV (source nullableSpecs) [] .callByValuePar (tblV (source nullableSpecs) [] .callByValuePar k) [] (original nullableRoot) 0=none := by
  cases k with
  | zero => rfl
  | succ k =>
    change valAt (tblV (source nullableSpecs) [] .callByValuePar (k+1) 0 [[]]) 0=none
    rw [valAt_tblV_succ (show ruleAtM (source nullableSpecs).rules 0=some ⟨1,original (.star (.atEnd 0))⟩ from rfl) [[]] (by decide)]
    rw [original,evV_star]
    exact evStar_stuck (j := 0) rfl (by omega)

theorem nullable_target_all_clocks (k : Nat) :
    evV (target nullableSpecs) [] .callByValueSeq (tblV (target nullableSpecs) [] .callByValueSeq k) []
      (emit nullableSpecs [] false nullableRoot) 0=none :=
  (EmptyObservedCorrespondence.physical nullableSpecs [] nullableRoot [] 0 k (by decide)).1.trans (nullable_source_all_clocks k)


theorem any_star_eval (g : MGrammar) (x : List Char) (T : ClockFreezing.Table) (E : List (List Char)) :
    ∀ p, p≤x.length → evV g x .callByValuePar T E (.star .any) p=some (some 0) := by
  intro p
  induction p with
  | zero =>
    intro hp
    rw [evV_star,evStar_fail (show evV g x .callByValuePar T E .any 0=some none from by simp [evV,sfx])]
  | succ p ih =>
    intro hp
    have hl := length_sfx x hp
    cases hx : sfx x (p+1) with
    | nil => rw [hx] at hl; simp at hl
    | cons c rest =>
      rw [hx] at hl
      have he : rest.length=p := by simpa only [List.length_cons,Nat.add_right_cancel_iff] using hl
      have ha : evV g x .callByValuePar T E .any (p+1)=some (some p) := by simp [evV,hx,he]
      rw [evV_star,evStar_ok ha (by omega)]
      exact ih (by omega)

/-- The tuple alphabet and lengths have no finite bound in the compiler. -/
theorem captures_arbitrary_words (x : List Char) (k : Nat) :
    evParArgs actual x .callByValuePar (tblV actual x .callByValuePar k) []
      ([.star .any,.eps].map original) x.length=some (some [x,[]]) := by
  simp only [List.map_cons,List.map_nil,original]
  rw [evPar_cons_ok (any_star_eval actual x _ [] x.length (Nat.le_refl _)),
    evPar_cons_ok (show evV actual x .callByValuePar (tblV actual x .callByValuePar k) [] .eps x.length=some (some x.length) from rfl),evPar_nil]
  simp [pre,sfx]

def orderSpecs : List Spec := [⟨1,.call 0 [.atEnd 0]⟩,⟨2,.eps⟩]
def failing : Term := .notP .eps

theorem preflight_keeps_failure_before_divergence :
    evV (target orderSpecs) [] .callByValueSeq (tblV (target orderSpecs) [] .callByValueSeq 4) []
      (emit orderSpecs [] false (.call 1 [failing,recursiveRoot])) 0=some none ∧
    evV (target orderSpecs) [] .callByValueSeq (tblV (target orderSpecs) [] .callByValueSeq 4) []
      (emit orderSpecs [] false (.call 1 [recursiveRoot,failing])) 0=none := by decide +kernel

theorem skipping_preflight_wrongly_accepts :
    evV (target orderSpecs) [] .callByValueSeq (tblV (target orderSpecs) [] .callByValueSeq 4) []
      (.call (address orderSpecs 1 [false,false] false) []) 0=some (some 0) := by decide +kernel

theorem wrong_arity_skips_divergent_argument :
    evV (source recursion) [] .callByValuePar (tblV (source recursion) [] .callByValuePar 4) []
      (original (.call 0 [recursiveRoot,.eps])) 0=some none ∧
    evV (target recursion) [] .callByValueSeq (tblV (target recursion) [] .callByValueSeq 4) []
      (emit recursion [] false (.call 0 [recursiveRoot,.eps])) 0=some none := by decide +kernel

theorem out_of_range_call_skips_divergent_argument :
    evV (source recursion) [] .callByValuePar (tblV (source recursion) [] .callByValuePar 4) []
      (original (.call 100 [recursiveRoot])) 0=some none ∧
    evV (target recursion) [] .callByValueSeq (tblV (target recursion) [] .callByValueSeq 4) []
      (emit recursion [] false (.call 100 [recursiveRoot])) 0=some none := by decide +kernel


/-- Both old words really are captured from the same source input origin.
At a later ordinary position, their common nonempty bit is insufficient. -/
theorem actual_prefix_bits_are_incomplete :
    evParArgs actual ['a','b','!','a'] .callByValuePar (tblV actual ['a','b','!','a'] .callByValuePar 0) []
      [.chr 'a',.lit ['a','b']] 4=some (some [['a'],['a','b']]) ∧
    evV actual ['a','b','!','a'] .callByValuePar (tblV actual ['a','b','!','a'] .callByValuePar 0) [['a'],['a','b']]
      (.seq (.lit ['a','b','!']) (.param 0)) 4=some (some 0) ∧
    evV actual ['a','b','!','a'] .callByValuePar (tblV actual ['a','b','!','a'] .callByValuePar 0) [['a'],['a','b']]
      (.seq (.lit ['a','b','!']) (.param 1)) 4=some none := by decide +kernel

end Shallot.MacroPeg.CBV.EmptyObservedExamples
