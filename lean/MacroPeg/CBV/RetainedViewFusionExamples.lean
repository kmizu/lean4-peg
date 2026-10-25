import MacroPeg.CBV.RetainedViewFusionCompiler

namespace Shallot.MacroPeg.CBV.RetainedViewFusionExamples
open RetainedViewFusionSyntax
open SubstringCaptureView (region dictionary)
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def seeds := [['a']]
def R := region seeds
def peek (e : Term) : Term := .notP (.notP e)
def skipToLast : Term := .star (.seq (peek (.seq .any .any)) .any)
def queryOther (i : Nat) : Term := peek (.seq skipToLast (.seq (.replay i) (.notP .any)))
/-- The first actual calls a unary user and captures the old unbounded
payload plus a fresh a. The second actual calls a nullary user at the same origin. -/
def actuals : List Term := [.call 2 [.seq .retained (.chr 'a')],.seq (.call 1 []) (.chr 'a')]
def parentTail : Term := .seq (.chr ':') .retained
def body : Term := .seq (queryOther 1) (.seq (.chr ':') (.seq .retained (.seq (.chr '{')
  (.seq (.alt (.call 0 actuals) .eps) (.seq (.chr '}') (.seq (queryOther 1) parentTail))))))
def specs : List Spec := [⟨2,body⟩,⟨0,.eps⟩,⟨1,.eps⟩]
def scanner : Term := .star (.chr 'a')
def entry : Term := .seq (.call 0 [scanner,.chr 'a']) (.seq (.chr 'a') (.notP .any))
abbrev originalGrammar := source R specs
abbrev generated := target R specs
def sourceRoot := original R entry
def targetRoot := RetainedViewFusionCorrespondence.root seeds specs entry

def word (n : Nat) := List.replicate n 'a'
def frame (n : Nat) : Nat → List Char
  | 0 => word n++[':']++word n++['{','}',':']++word n
  | d+1 => word n++[':']++word n++['{']++frame (n+1) d++['}',':']++word n
def input (n d : Nat) := frame n d++['a']

theorem checked : RetainedViewFusionCompiler.check originalGrammar sourceRoot seeds specs entry=true := by decide +kernel

theorem source_arities : originalGrammar.rules.map MRule.arity=[2,0,1] := by decide +kernel

theorem target_layout : generated.rules.length=182 ∧ generated.rules.all (fun r => r.arity==1)=true := by decide +kernel

theorem source_runs : ∀ pair∈[(1,0),(2,1),(4,2)],
    evV originalGrammar (input pair.1 pair.2) .callByValuePar (tblV originalGrammar (input pair.1 pair.2) .callByValuePar 8) []
      sourceRoot (input pair.1 pair.2).length=some (some 0) := by decide +kernel

theorem generated_runs : ∀ pair∈[(1,0),(2,1),(4,2)],
    evV generated (input pair.1 pair.2) .callByValueSeq (tblV generated (input pair.1 pair.2) .callByValueSeq 8) []
      targetRoot (input pair.1 pair.2).length=some (some 0) := by decide +kernel

/-- Equal Other metadata still carries the two different actual words.
No finite view is used as a literal replacement for the main payload. -/
theorem actual_growing_capture :
    evParArgs originalGrammar (input 2 1) .callByValuePar (tblV originalGrammar (input 2 1) .callByValuePar 8) [word 2,['a']]
      (originalArgs R actuals) (frame 3 0++['}',':']++word 2++['a']).length=some (some [word 3,['a']]) ∧
    FiniteSuffixReplay.views R [word 2,['a']]=FiniteSuffixReplay.views R [word 3,['a']] := by decide +kernel

theorem other_payloads_remain_distinct : ∀ n∈[2,4,7],
    evV generated (word n++[':']) .callByValueSeq (tblV generated (word n++[':']) .callByValueSeq 8) [word n]
      (emit R specs [none,some ['a']] none .retained) (n+1)=some (some 1) := by decide +kernel

/-- The copied main word is replayed at a suffix outside the finite region. -/
theorem unguarded_payload_beyond_region :
    (word 4++['{','}',':']++word 4++['a'])∉R ∧
    evV generated (word 4++['{','}',':']++word 4++['a']) .callByValueSeq
      (tblV generated (word 4++['{','}',':']++word 4++['a']) .callByValueSeq 8) [word 4]
      (emit R specs [none,some ['a']] none .retained) (word 4++['{','}',':']++word 4++['a']).length=some (some 8) := by decide +kernel

def afterChild := ['}']++[':']++word 2++['a']
def finishParent : Term := .seq (.chr '}') (.seq parentTail (.seq (.chr 'a') (.notP .any)))
theorem leaking_child_payload_is_wrong :
    evV generated afterChild .callByValueSeq (tblV generated afterChild .callByValueSeq 8) [word 2]
      (emit R specs [none,some ['a']] none finishParent) afterChild.length=some (some 0) ∧
    evV generated afterChild .callByValueSeq (tblV generated afterChild .callByValueSeq 8) [word 3]
      (emit R specs [none,some ['a']] none finishParent) afterChild.length=some none := by decide +kernel

theorem no_unbounded_payload_replacement :
    evV generated (input 2 0) .callByValueSeq (tblV generated (input 2 0) .callByValueSeq 8) []
      (.call (address R specs 0 [none,some ['a']] none) [.eps]) ((input 2 0).length-2)=some none := by decide +kernel

theorem same_clock (x : List Char) (k : Nat) :
    evV originalGrammar x .callByValuePar (tblV originalGrammar x .callByValuePar k) [] sourceRoot x.length=
      evV generated x .callByValueSeq (tblV generated x .callByValueSeq k) [] targetRoot x.length :=
  RetainedViewFusionCompiler.physical originalGrammar sourceRoot seeds specs entry checked x k

theorem original_language : (fun x => SObs originalGrammar .callByValuePar sourceRoot x (some []))=
    (fun x => SObs generated .callByValueSeq targetRoot x (some [])) :=
  RetainedViewFusionCompiler.language_translation originalGrammar sourceRoot seeds specs entry checked

theorem unchanged_source_seq_fails :
    evV originalGrammar (input 2 0) .callByValueSeq (tblV originalGrammar (input 2 0) .callByValueSeq 8) [] sourceRoot (input 2 0).length=some none := by decide +kernel

/-- Prefix-only metadata cannot advance a DFA from an intermediate state. -/
theorem substring_metadata_needed :
    FiniteSuffixReplay.observe [['a','b']] ['b']=FiniteSuffixReplay.observe [['a','b']] ['c'] ∧
    SubstringCaptureView.observe [['a','b']] ['b']≠SubstringCaptureView.observe [['a','b']] ['c'] ∧
    RegularCaptureProduct.run (ExactWordCaptureMachine.machine ['a','b']) 1 ['b']=2 ∧
    RegularCaptureProduct.run (ExactWordCaptureMachine.machine ['a','b']) 1 ['c']=3 := by decide +kernel

/-- Unbounded words sharing Other metadata must not be identified for raw replay. -/
theorem finite_metadata_does_not_erase_payload :
    SubstringCaptureView.observe seeds (word 2)=SubstringCaptureView.observe seeds (word 3) ∧
    evV generated (word 2++[':']) .callByValueSeq (tblV generated (word 2++[':']) .callByValueSeq 8) [word 2] (.param 0) 3=some (some 1) ∧
    evV generated (word 2++[':']) .callByValueSeq (tblV generated (word 2++[':']) .callByValueSeq 8) [word 3] (.param 0) 3=some none := by decide +kernel

/-- The preserved main capture need not be the longest original argument. -/
def longerOtherBody : Term := .seq (.star (.chr 'a')) (.seq (.chr ':') (.seq .retained
  (.seq (.chr '?') (.seq (.notP (.replay 1)) (.seq (.chr 'a') (.notP .any))))))
def longerOtherSpecs : List Spec := [⟨2,longerOtherBody⟩]
def longerOtherEntry : Term := .call 0 [.chr 'a',scanner]
def longerOtherInput (n : Nat) := word n++[':','a','?','a']
theorem main_need_not_be_longest : ∀ n∈[2,4],
    evV (source R longerOtherSpecs) (longerOtherInput n) .callByValuePar
      (tblV (source R longerOtherSpecs) (longerOtherInput n) .callByValuePar 4) [] (original R longerOtherEntry) (longerOtherInput n).length=some (some 0) ∧
    evV (target R longerOtherSpecs) (longerOtherInput n) .callByValueSeq
      (tblV (target R longerOtherSpecs) (longerOtherInput n) .callByValueSeq 4) []
      (RetainedViewFusionCorrespondence.root seeds longerOtherSpecs longerOtherEntry) (longerOtherInput n).length=some (some 0) := by decide +kernel

theorem equal_short_other_changes_result :
    evV (source R longerOtherSpecs) (longerOtherInput 1) .callByValuePar
      (tblV (source R longerOtherSpecs) (longerOtherInput 1) .callByValuePar 4) [] (original R longerOtherEntry) (longerOtherInput 1).length=some none ∧
    evV (target R longerOtherSpecs) (longerOtherInput 1) .callByValueSeq
      (tblV (target R longerOtherSpecs) (longerOtherInput 1) .callByValueSeq 4) []
      (RetainedViewFusionCorrespondence.root seeds longerOtherSpecs longerOtherEntry) (longerOtherInput 1).length=some none := by decide +kernel

def abSeeds := [['a','b']]
def abR := region abSeeds
def abSpecs : List Spec := [⟨1,.eps⟩]
def composeAB : Term := .seq (.lit ['a']) .retained

theorem actual_filter_needs_substring_view :
    evV (target abR abSpecs) ['a','b'] .callByValueSeq (tblV (target abR abSpecs) ['a','b'] .callByValueSeq 1) [['b']]
      (emit abR abSpecs [some ['b']] (some (['a','b'],0,2)) composeAB) 2=some (some 0) ∧
    evV (target abR abSpecs) ['a','b'] .callByValueSeq (tblV (target abR abSpecs) ['a','b'] .callByValueSeq 1) [['b']]
      (emit abR abSpecs [none] (some (['a','b'],0,2)) composeAB) 2=some none := by decide +kernel

/-- Symbolic scanner evidence, with no bound on the retained word length. -/
theorem scan_prefix (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table) (E : List (List Char))
    (n : Nat) (tail : List Char) : ∀ p, p≤x.length → sfx x p=word n++':'::tail →
    evV g x s T E (.star (.chr 'a')) p=some (some (tail.length+1)) := by
  induction n with
  | zero =>
    intro p hp hx
    have hl := length_sfx x hp
    rw [hx] at hl
    have he : p=tail.length+1 := by simpa [word] using hl.symm
    rw [evV_star,evStar_fail (show evV g x s T E (.chr 'a') p=some none from by simp [evV,hx,word,Shallot.beqChar])]
    rw [he]
  | succ n ih =>
    intro p hp hx
    have hx' : sfx x p='a'::(word n++':'::tail) := by simpa [word,List.replicate_succ] using hx
    have hl := length_sfx x hp
    rw [hx',List.length_cons] at hl
    have hq : (word n++':'::tail).length<p := by omega
    have hs : sfx x (word n++':'::tail).length=word n++':'::tail := by
      obtain ⟨headPart,hprefix⟩ := sfx_is_suffix x p
      apply sfx_suffix (pre := headPart++['a'])
      rw [hx'] at hprefix
      simpa [List.append_assoc] using hprefix
    rw [evV_star,evStar_ok (show evV g x s T E (.chr 'a') p=some (some (word n++':'::tail).length) from by simp [evV,hx',Shallot.beqChar]) hq]
    exact ih _ (by omega) hs

theorem actual_captures_all_lengths (n k : Nat) :
    evParArgs originalGrammar (word (n+1)++[':']) .callByValuePar
      (tblV originalGrammar (word (n+1)++[':']) .callByValuePar k) []
      (originalArgs R [scanner,.chr 'a']) (word (n+1)++[':']).length=some (some [word (n+1),['a']]) := by
  have hscan := scan_prefix originalGrammar (word (n+1)++[':']) .callByValuePar
    (tblV originalGrammar (word (n+1)++[':']) .callByValuePar k) [] (n+1) [] _ (Nat.le_refl _) (sfx_self _)
  have hx : sfx (word (n+1)++[':']) (word (n+1)++[':']).length='a'::(word n++[':']) := by simp [sfx,word,List.replicate_succ]
  have hc : evV originalGrammar (word (n+1)++[':']) .callByValuePar
      (tblV originalGrammar (word (n+1)++[':']) .callByValuePar k) [] (.chr 'a') (word (n+1)++[':']).length=some (some (word n++[':']).length) := by
    simp only [evV,hx]
    rfl
  rw [show originalArgs R [scanner,.chr 'a']=[.star (.chr 'a'),.chr 'a'] from rfl,evPar_cons_ok hscan,evPar_cons_ok hc,evPar_nil]
  dsimp only []
  simp only [List.length_nil,Nat.zero_add]
  have hpre : pre (word (n+1)++[':']) (word (n+1)++[':']).length 1=word (n+1) := by
    simp [pre,sfx,word,List.take_append]
  rw [hpre,FiniteSuffixObservedAtoms.pre_character _ _ (Nat.le_refl _) 'a' (word n++[':']) hx]

def nullableSpecs : List Spec := [⟨2,.star .retained⟩]
def nullableEntry : Term := .call 0 [.eps,.eps]
theorem nullable_payload_rows (x : List Char) (p : Nat) (hp : p≤x.length) : ∀ k,
    valAt (tblV (source R nullableSpecs) x .callByValuePar k 0 [[],[]]) p=none
  | 0 => rfl
  | k+1 => by
    have hr := RetainedViewFusionDeclarations.source_rule R nullableSpecs 0 ⟨2,.star .retained⟩ rfl
    rw [valAt_tblV_succ hr [[],[]] hp]
    change evV (source R nullableSpecs) x .callByValuePar (tblV (source R nullableSpecs) x .callByValuePar k) [[],[]]
      (.seq (.param 0) (.star (.param 0))) p=none
    have hh : evV (source R nullableSpecs) x .callByValuePar (tblV (source R nullableSpecs) x .callByValuePar k) [[],[]] (.param 0) p=some (some p) := by
      simp [evV,Shallot.stripPrefix?,length_sfx x hp]
    rw [evV_seq_ok hh,evV_star]
    exact evStar_stuck hh (by omega)

theorem nullable_payload_source (x : List Char) (k : Nat) :
    evV (source R nullableSpecs) x .callByValuePar (tblV (source R nullableSpecs) x .callByValuePar k) [] (original R nullableEntry) x.length=none := by
  have hr := RetainedViewFusionDeclarations.source_rule R nullableSpecs 0 ⟨2,.star .retained⟩ rfl
  rw [show original R nullableEntry=.call 0 [.eps,.eps] from rfl,evV_call_par hr rfl (by decide),evPar_cons_ok rfl,evPar_cons_ok rfl,evPar_nil]
  simpa [pre] using nullable_payload_rows x x.length (Nat.le_refl _) k

theorem nullable_payload_target (x : List Char) (k : Nat) :
    evV (target R nullableSpecs) x .callByValueSeq (tblV (target R nullableSpecs) x .callByValueSeq k) []
      (RetainedViewFusionCorrespondence.root seeds nullableSpecs nullableEntry) x.length=none :=
  (RetainedViewFusionCorrespondence.physical seeds nullableSpecs nullableEntry x k).symm.trans (nullable_payload_source x k)

/-- The complete checker also checks the real leading replay, not just tails. -/
def noHead : MGrammar := ⟨[⟨2,.eps⟩]⟩
theorem missing_head_rejected : RetainedViewFusionCompiler.check noHead (original R (.call 0 [.eps,.eps])) seeds [⟨2,.eps⟩] (.call 0 [.eps,.eps])=false := by decide +kernel

end Shallot.MacroPeg.CBV.RetainedViewFusionExamples
