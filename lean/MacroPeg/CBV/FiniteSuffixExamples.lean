import MacroPeg.CBV.FiniteSuffixCallCompiler

namespace Shallot.MacroPeg.CBV.FiniteSuffixExamples
open FiniteSuffixBody (Body)
open FiniteSuffixCallCompiler
open RegularCaptureProduct (Node)
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def nodes : List Node := [.lit [],.lit ['a'],.lit ['b'],.alt 1 2,.seq 3 5,.alt 4 0,.star 0,.notP 0]
def region := [['a'],['b']]
def ids := [3,5]
def body : Body := .seq (.helper 5) (.seq (.chr '!')
  (.alt (.replay 1) (.seq (.notP (.replay 1)) (.replay 0))))
def original := source nodes region ids body
def root := sourceStart nodes ids

theorem nodes_valid : RegularCaptureProduct.Valid nodes := nodes_checked nodes (by decide +kernel)

theorem arguments_valid : ∀ i∈ids, i<nodes.length := by decide +kernel

theorem checked : check original root nodes region ids body=true := by decide +kernel

theorem source_size : original.rules.length=9 := by decide +kernel

theorem target_size : (target nodes region).rules.length=656 := by decide +kernel

theorem actual_captures :
    evParArgs original ['a','b','!','a'] .callByValuePar (tblV original ['a','b','!','a'] .callByValuePar 12) []
      (ids.map (fun i => .call i [])) 4=some (some [['a'],['a','b']]) := by decide +kernel

theorem source_accepts : ∀ x∈[['a','!','a'],['b','!','b'],['a','b','!','a'],['b','a','!','b']],
    evV original x .callByValuePar (tblV original x .callByValuePar 12) [] root x.length=some (some 0) := by decide +kernel

theorem target_accepts : ∀ x∈[['a','!','a'],['b','!','b'],['a','b','!','a'],['b','a','!','b']],
    evV (target nodes region) x .callByValueSeq (tblV (target nodes region) x .callByValueSeq 24) []
      (targetStart nodes region ids body) x.length=some (some 0) := by decide +kernel

theorem source_rejects_wrong_content : ∀ x∈[['a','!','b'],['b','!','a'],['a','b','!','b'],['b','a','!','a']],
    evV original x .callByValuePar (tblV original x .callByValuePar 12) [] root x.length=some none := by decide +kernel

theorem target_rejects_wrong_content : ∀ x∈[['a','!','b'],['b','!','a'],['a','b','!','b'],['b','a','!','a']],
    evV (target nodes region) x .callByValueSeq (tblV (target nodes region) x .callByValueSeq 24) []
      (targetStart nodes region ids body) x.length=some none := by decide +kernel

/-- Both captures are nonempty; the long one is outside the palette while
its one-character prefix still matches at a non-EOF position. -/
theorem finite_content_view :
    FiniteSuffixReplay.views region [['a'],['a','b']]=[some ['a'],none] ∧
    FiniteSuffixReplay.views region [['b'],['b','a']]=[some ['b'],none] := by decide +kernel

theorem nonempty_at_nonEOF_position :
    evV original ['a','b','!','a'] .callByValuePar (tblV original ['a','b','!','a'] .callByValuePar 0) [['a'],['a','b']]
      (.seq (FiniteSuffixReplay.guard region) (.param 0)) 1=some (some 0) ∧
    evV original ['a','b','!','a'] .callByValuePar (tblV original ['a','b','!','a'] .callByValuePar 0) [['a'],['a','b']]
      (.seq (.notP .any) (.param 0)) 1=some none := by decide +kernel

theorem large_retained_word_is_not_rejected_early :
    evV original ['a','a','a','a','!','a'] .callByValuePar (tblV original ['a','a','a','a','!','a'] .callByValuePar 20) [] root 6=some (some 0) := by decide +kernel

theorem observations (x : List Char) (rest : Option (List Char)) :
    SObs original .callByValuePar root x rest ↔
      SObs (target nodes region) .callByValueSeq (targetStart nodes region ids body) x rest :=
  checked_observations original root nodes region ids body checked x rest

theorem original_language : (fun x => SObs original .callByValuePar root x (some []))=
    (fun x => SObs (target nodes region) .callByValueSeq (targetStart nodes region ids body) x (some [])) :=
  checked_language original root nodes region ids body checked

/-- The finite word machine remembers exact termination, including empty. -/
theorem exact_word_is_not_periodic :
    RegularCaptureProduct.run (ExactWordCaptureMachine.machine ['a']) 0 ['a']=1 ∧
    RegularCaptureProduct.run (ExactWordCaptureMachine.machine ['a']) 0 ['a','a']=2 ∧
    RegularCaptureProduct.run (ExactWordCaptureMachine.machine []) 0 []=0 ∧
    RegularCaptureProduct.run (ExactWordCaptureMachine.machine []) 0 ['a']=1 := by decide +kernel

/-- Omitting the guard would incorrectly discard a real longer match. -/
theorem guard_is_essential :
    evV original ['a','b'] .callByValuePar (tblV original ['a','b'] .callByValuePar 0) [['a','b']]
      (.param 0) 2=some (some 0) ∧
    evV original ['a','b'] .callByValueSeq (tblV original ['a','b'] .callByValueSeq 0) []
      (FiniteSuffixReplay.literal (FiniteSuffixReplay.views region [['a','b']]) 0) 2=some none := by decide +kernel

/-- A suffix outside the finite alphabet remains a real finite failure. -/
theorem alphabet_boundary :
    evV original ['a','!','X'] .callByValuePar (tblV original ['a','!','X'] .callByValuePar 12) [] root 3=some none ∧
    evV (target nodes region) ['a','!','X'] .callByValueSeq (tblV (target nodes region) ['a','!','X'] .callByValueSeq 24) []
      (targetStart nodes region ids body) 3=some none := by decide +kernel


def twoRegion := [['a','b']]
def partialBody : Body := .seq (.helper 5) (.seq (.chr '!') (.seq (.replay 0) (.chr 'b')))

theorem distinct_nonempty_contents_retained :
    FiniteSuffixReplay.views twoRegion [['a'],['a','b']]=[some ['a'],some ['a','b']] := by decide +kernel

theorem partial_replay_leaves_nonempty_suffix :
    evV original ['a','b','!','a','b'] .callByValuePar (tblV original ['a','b','!','a','b'] .callByValuePar 0) [['a'],['a','b']]
      (.seq (FiniteSuffixReplay.guard twoRegion) (.param 0)) 2=some (some 1) := by decide +kernel

theorem partial_source_run :
    evV (source nodes twoRegion ids partialBody) ['a','b','!','a','b'] .callByValuePar
      (tblV (source nodes twoRegion ids partialBody) ['a','b','!','a','b'] .callByValuePar 12) [] root 5=some (some 0) := by decide +kernel

theorem partial_target_run :
    evV (target nodes twoRegion) ['a','b','!','a','b'] .callByValueSeq
      (tblV (target nodes twoRegion) ['a','b','!','a','b'] .callByValueSeq 24) []
      (targetStart nodes twoRegion ids partialBody) 5=some (some 0) := by decide +kernel

theorem unchanged_source_under_seq_leaves_input :
    evV original ['a','!','a'] .callByValueSeq (tblV original ['a','!','a'] .callByValueSeq 12) [] root 3=some (some 1) := by decide +kernel

theorem large_target_has_actual_finite_run :
    ∃ k, evV (target nodes region) ['a','a','a','a','!','a'] .callByValueSeq (tblV (target nodes region) ['a','a','a','a','!','a'] .callByValueSeq k) []
      (targetStart nodes region ids body) 6=some (some 0) :=
  (defined_iff nodes nodes_valid region ids arguments_valid body _ _).mp ⟨20,large_retained_word_is_not_rejected_early⟩

def nullableBody : Body := .seq (.chr '!') (.star (.replay 0))
def nullableSource := source nodes region [0] nullableBody

theorem nullable_rows_all_clocks (k : Nat) :
    valAt (tblV nullableSource ['!','a'] .callByValuePar k nodes.length [[]]) 2=none := by
  cases k with
  | zero => rfl
  | succ k =>
    have hs : ruleAtM nullableSource.rules nodes.length=some ⟨1,FiniteSuffixBody.render nodes.length region none nullableBody⟩ :=
      source_rule nodes region [0] nullableBody
    rw [valAt_tblV_succ hs [[]] (by decide)]
    rw [show FiniteSuffixBody.render nodes.length region none nullableBody=
      .seq (.chr '!') (.star (.seq (FiniteSuffixReplay.guard region) (.param 0))) from rfl]
    rw [evV_seq_ok (j := 1) rfl,evV_star]
    exact evStar_stuck (j := 1) rfl (by omega)

theorem nullable_source_all_clocks (k : Nat) :
    evV nullableSource ['!','a'] .callByValuePar (tblV nullableSource ['!','a'] .callByValuePar k) [] (sourceStart nodes [0]) 2=none := by
  cases k with
  | zero => rfl
  | succ k =>
    have he : ruleAtM nullableSource.rules 0=some ⟨0,.lit []⟩ := rfl
    have ha : evV nullableSource ['!','a'] .callByValuePar (tblV nullableSource ['!','a'] .callByValuePar (k+1)) [] (.call 0 []) 2=some (some 2) := by
      rw [evV_call_par he rfl (by decide)]
      change valAt (tblV nullableSource ['!','a'] .callByValuePar (k+1) 0 []) 2=some (some 2)
      rw [valAt_tblV_succ he [] (by decide)]
      rfl
    have hs : ruleAtM nullableSource.rules nodes.length=some ⟨1,FiniteSuffixBody.render nodes.length region none nullableBody⟩ :=
      source_rule nodes region [0] nullableBody
    simp only [sourceStart,List.map_cons,List.map_nil]
    rw [evV_call_par hs rfl (by decide),evPar_cons_ok ha,evPar_nil]
    simpa [pre] using nullable_rows_all_clocks (k+1)

theorem nullable_target_all_clocks (k : Nat) :
    evV (target nodes region) ['!','a'] .callByValueSeq (tblV (target nodes region) ['!','a'] .callByValueSeq k) []
      (targetStart nodes region [0] nullableBody) 2=none :=
  (undefined_iff nodes nodes_valid region [0] (by
    intro i hi
    have he : i=0 := by simpa using hi
    subst i
    decide) nullableBody ['!','a']).mp nullable_source_all_clocks k

theorem evaluation_order_preserved :
    evV (source nodes region [6,7] body) ['a'] .callByValuePar (tblV (source nodes region [6,7] body) ['a'] .callByValuePar 12) []
      (sourceStart nodes [6,7]) 1=none ∧
    evV (source nodes region [7,6] body) ['a'] .callByValuePar (tblV (source nodes region [7,6] body) ['a'] .callByValuePar 12) []
      (sourceStart nodes [7,6]) 1=some none ∧
    evV (target nodes region) ['a'] .callByValueSeq (tblV (target nodes region) ['a'] .callByValueSeq 24) []
      (targetStart nodes region [6,7] body) 1=none ∧
    evV (target nodes region) ['a'] .callByValueSeq (tblV (target nodes region) ['a'] .callByValueSeq 24) []
      (targetStart nodes region [7,6] body) 1=some none := by decide +kernel


theorem nullable_argument_none (R : List (List Char)) (args : List Nat) (B : Body) (x : List Char) (p k : Nat) (hp : p≤x.length) :
    evV (source nodes R args B) x .callByValuePar (tblV (source nodes R args B) x .callByValuePar k) [] (.call 6 []) p=none := by
  have h6 : ruleAtM (source nodes R args B).rules 6=some ⟨0,.star (.call 0 [])⟩ := rfl
  have h0 : ruleAtM (source nodes R args B).rules 0=some ⟨0,.lit []⟩ := rfl
  rw [evV_call_par h6 rfl (by decide)]
  cases k with
  | zero => rfl
  | succ k =>
    change valAt (tblV (source nodes R args B) x .callByValuePar (k+1) 6 []) p=none
    rw [valAt_tblV_succ h6 [] hp,evV_star]
    cases k with
    | zero => exact evStar_none rfl
    | succ k =>
      have he : evV (source nodes R args B) x .callByValuePar (tblV (source nodes R args B) x .callByValuePar (k+1)) [] (.call 0 []) p=some (some p) := by
        rw [evV_call_par h0 rfl (by decide)]
        change valAt (tblV (source nodes R args B) x .callByValuePar (k+1) 0 []) p=some (some p)
        rw [valAt_tblV_succ h0 [] hp]
        simp [evV,Shallot.stripPrefix?,length_sfx x hp]
      exact evStar_stuck he (by omega)

theorem undefined_argument_source_all_inputs (x : List Char) (k : Nat) :
    evV (source nodes region [6,7] body) x .callByValuePar (tblV (source nodes region [6,7] body) x .callByValuePar k) []
      (sourceStart nodes [6,7]) x.length=none := by
  rw [sourceStart,evV_call_par (source_rule nodes region [6,7] body) (by simp) (by decide)]
  simp only [List.map_cons,List.map_nil]
  rw [evPar_cons_none (nullable_argument_none region [6,7] body x x.length k (Nat.le_refl _))]

theorem undefined_argument_target_all_inputs (x : List Char) (k : Nat) :
    evV (target nodes region) x .callByValueSeq (tblV (target nodes region) x .callByValueSeq k) []
      (targetStart nodes region [6,7] body) x.length=none :=
  (undefined_iff nodes nodes_valid region [6,7] (by decide +kernel) body x).mp (undefined_argument_source_all_inputs x) k

def unguardedSource : MGrammar := ⟨nodes.map (fun n => ⟨0,RegularCaptureProduct.body n⟩)++[⟨2,.param 0⟩]⟩
theorem missing_guard_rejected : check unguardedSource root nodes region ids (.replay 0)=false := by decide +kernel

theorem empty_dictionary :
    evV (source nodes [] [5] (.seq (.notP (.replay 0)) (.star .any))) ['X'] .callByValuePar
      (tblV (source nodes [] [5] (.seq (.notP (.replay 0)) (.star .any))) ['X'] .callByValuePar 8) [] (sourceStart nodes [5]) 1=some (some 0) ∧
    evV (target nodes []) ['X'] .callByValueSeq (tblV (target nodes []) ['X'] .callByValueSeq 12) []
      (targetStart nodes [] [5] (.seq (.notP (.replay 0)) (.star .any))) 1=some (some 0) := by decide +kernel


def balancedNodes : List Node := [.lit [],.lit ['a'],.lit ['b'],.seq 1 5,.seq 3 2,.alt 4 0]
def balancedInput (n : Nat) := List.replicate n 'a'++List.replicate n 'b'++['!','a','b']

theorem balanced_actual_captures : ∀ n∈[1,2,4],
    evParArgs (source balancedNodes twoRegion [1,5] partialBody) (balancedInput n) .callByValuePar
      (tblV (source balancedNodes twoRegion [1,5] partialBody) (balancedInput n) .callByValuePar 20) []
      [.call 1 [],.call 5 []] (balancedInput n).length=
        some (some [['a'],List.replicate n 'a'++List.replicate n 'b']) := by decide +kernel

theorem balanced_source_run :
    evV (source balancedNodes twoRegion [1,5] partialBody) (balancedInput 2) .callByValuePar
      (tblV (source balancedNodes twoRegion [1,5] partialBody) (balancedInput 2) .callByValuePar 20) []
      (sourceStart balancedNodes [1,5]) (balancedInput 2).length=some (some 0) := by decide +kernel

theorem balanced_target_run :
    evV (target balancedNodes twoRegion) (balancedInput 2) .callByValueSeq
      (tblV (target balancedNodes twoRegion) (balancedInput 2) .callByValueSeq 32) []
      (targetStart balancedNodes twoRegion [1,5] partialBody) (balancedInput 2).length=some (some 0) := by decide +kernel

end Shallot.MacroPeg.CBV.FiniteSuffixExamples
