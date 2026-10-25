import MacroPeg.CBV.DelimitedCopyCompiler
import MacroPeg.CBV.FiniteResidualControl

namespace Shallot.MacroPeg.CBV.DelimitedCopyExamples
open DelimitedCopySyntax DelimitedCopyCompiler
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def bodies : List MExp := [FiniteResidualControl.balancedBody,FiniteResidualControl.consumePrefix,.call 2 [],.notP .eps]
def alphabet := ['a','b','c']
def d := '#'
def A : MExp := .call 1 []
def B : MExp := .call 0 []
def copy : Term := .copy A B
def entry : Term := .seq copy (.notP .any)
abbrev original := source bodies d
abbrev generated := target bodies d
def originalRoot := render bodies true entry
def generatedRoot := render bodies false entry

def short (n : Nat) := List.replicate n 'a'++['b']
def long (n : Nat) := short n++List.replicate n 'c'
def block (n : Nat) := long n++[d]++short n++[d]++long n++[d]

theorem checked : DelimitedCopyCompiler.check original originalRoot bodies alphabet d entry=true := by decide +kernel

theorem grammar_layout : original.rules.map MRule.arity=[0,0,0,0,2] ∧ generated.rules.map MRule.arity=[0,0,0,0,1,1] := by decide +kernel

theorem actual_parallel_captures : ∀ n∈[0,1,2,4],
    evParArgs original (block n) .callByValuePar (tblV original (block n) .callByValuePar 12) [] [A,B] (block n).length=
      some (some [short n,long n]) := by decide +kernel

theorem source_runs : ∀ n∈[0,1,2,4],
    evV original (block n) .callByValuePar (tblV original (block n) .callByValuePar 12) [] originalRoot (block n).length=some (some 0) := by decide +kernel

theorem generated_runs : ∀ n∈[0,1,2,4],
    evV generated (block n) .callByValueSeq (tblV generated (block n) .callByValueSeq 12) [] generatedRoot (block n).length=some (some 0) := by decide +kernel

theorem unchanged_source_seq_fails :
    evV original (block 2) .callByValueSeq (tblV original (block 2) .callByValueSeq 12) [] originalRoot (block 2).length=some none := by decide +kernel

def wrongShort := long 2++[d]++short 3++[d]++long 2++[d]
def wrongLong := long 2++[d]++short 2++[d]++long 3++[d]
def wrongBalance := short 2++List.replicate 3 'c'++[d]++short 2++[d]++long 2++[d]
theorem rejected_copies_and_balance : ∀ x∈[wrongShort,wrongLong,wrongBalance],
    evV original x .callByValuePar (tblV original x .callByValuePar 12) [] originalRoot x.length=some none ∧
    evV generated x .callByValueSeq (tblV generated x .callByValueSeq 12) [] generatedRoot x.length=some none := by decide +kernel

/-- The copy block need not end the input. Both projections return the
actual suffix, rather than merely preserving whole-input acceptance. -/
theorem actual_residual_preserved :
    evV original (block 2++['!','X']) .callByValuePar (tblV original (block 2++['!','X']) .callByValuePar 12) []
      (render bodies true copy) (block 2++['!','X']).length=some (some 2) ∧
    evV generated (block 2++['!','X']) .callByValueSeq (tblV generated (block 2++['!','X']) .callByValueSeq 12) []
      (render bodies false copy) (block 2++['!','X']).length=some (some 2) := by decide +kernel

def repeated : Term := .seq (.star copy) (.notP .any)
theorem different_blocks_in_star :
    evV original (block 1++block 3) .callByValuePar (tblV original (block 1++block 3) .callByValuePar 12) [] (render bodies true repeated) (block 1++block 3).length=some (some 0) ∧
    evV generated (block 1++block 3) .callByValueSeq (tblV generated (block 1++block 3) .callByValueSeq 12) [] (render bodies false repeated) (block 1++block 3).length=some (some 0) := by decide +kernel

def contextual : Term := .seq (.notP (.lit ['X'])) (.seq (.alt (.seq (.chr '!') copy) copy) (.seq (.lit ['!','X']) (.notP .any)))
theorem contextual_continuation :
    evV original (block 2++['!','X']) .callByValuePar (tblV original (block 2++['!','X']) .callByValuePar 12) []
      (render bodies true contextual) (block 2++['!','X']).length=some (some 0) ∧
    evV generated (block 2++['!','X']) .callByValueSeq (tblV generated (block 2++['!','X']) .callByValueSeq 12) []
      (render bodies false contextual) (block 2++['!','X']).length=some (some 0) := by decide +kernel

theorem same_clock (x : List Char) (k : Nat) :
    evV original x .callByValuePar (tblV original x .callByValuePar k) [] originalRoot x.length=
      evV generated x .callByValueSeq (tblV generated x .callByValueSeq k) [] generatedRoot x.length :=
  DelimitedCopyCompiler.physical original originalRoot bodies alphabet d entry checked x k

theorem original_language : (fun x => SObs original .callByValuePar originalRoot x (some []))=
    (fun x => SObs generated .callByValueSeq generatedRoot x (some [])) :=
  DelimitedCopyCompiler.language_translation original originalRoot bodies alphabet d entry checked

/-- Delimiter freedom is an actual necessary frontend condition. -/
def badDelimiter : Term := .copy (.lit [d]) .eps
theorem unsafe_capture_rejected : termCheck bodies alphabet d badDelimiter=false := by decide +kernel

theorem omitting_delimiter_condition_is_wrong :
    evV original [d,d,d,d] .callByValuePar (tblV original [d,d,d,d] .callByValuePar 4) [] (render bodies true badDelimiter) 4=some (some 0) ∧
    evV generated [d,d,d,d] .callByValueSeq (tblV generated [d,d,d,d] .callByValueSeq 4) [] (render bodies false badDelimiter) 4=some none := by decide +kernel

theorem cycle_rows (g : MGrammar) (s : Strategy) (hr : ruleAtM g.rules 2=some ⟨0,.call 2 []⟩)
    (x : List Char) (p : Nat) (hp : p≤x.length) : ∀ k, valAt (tblV g x s k 2 []) p=none
  | 0 => rfl
  | k+1 => by
    rw [valAt_tblV_succ hr [] hp]
    cases s <;> simpa only [evV,hr,evParArgs,evSeqArgs,List.length_nil,ite_true] using cycle_rows g _ hr x p hp k

theorem cycle_eval (g : MGrammar) (s : Strategy) (hr : ruleAtM g.rules 2=some ⟨0,.call 2 []⟩)
    (x : List Char) (k p : Nat) (hp : p≤x.length) : evV g x s (tblV g x s k) [] (.call 2 []) p=none := by
  cases s <;> simpa only [evV,hr,evParArgs,evSeqArgs,List.length_nil,ite_true] using cycle_rows g _ hr x p hp k

def divergent : Term := .copy .eps (.call 2 [])
theorem divergent_checked : DelimitedCopyCompiler.check original (render bodies true divergent) bodies alphabet d divergent=true := by decide +kernel

theorem ordered_divergence_source (x : List Char) (k : Nat) :
    evV original x .callByValuePar (tblV original x .callByValuePar k) [] (render bodies true divergent) x.length=none := by
  have hr : ruleAtM original.rules 2=some ⟨0,.call 2 []⟩ := rfl
  rw [show render bodies true divergent=.call bodies.length [.eps,.call 2 []] from rfl,
    evV_call_par (source_rule bodies d) rfl (by decide),evPar_cons_ok rfl,
    evPar_cons_none (cycle_eval original .callByValuePar hr x k x.length (Nat.le_refl _))]

theorem ordered_divergence_target (x : List Char) (k : Nat) :
    evV generated x .callByValueSeq (tblV generated x .callByValueSeq k) [] (render bodies false divergent) x.length=none :=
  (DelimitedCopyCompiler.physical original (render bodies true divergent) bodies alphabet d divergent divergent_checked x k).symm.trans (ordered_divergence_source x k)

/-- Without ordered preflight, the first pure projection fails before the
original undefined second argument is evaluated. -/
def noPreflight : MExp := .seq (.andP (.call bodies.length [.eps])) (.call (bodies.length+1) [.call 2 []])
theorem skipping_preflight_changes_undefinedness :
    evV generated ['a'] .callByValueSeq (tblV generated ['a'] .callByValueSeq 4) [] noPreflight 1=some none := by decide +kernel

def failureFirst : Term := .copy (.call 3 []) (.call 2 [])
theorem failure_before_divergence :
    evV original ['a'] .callByValuePar (tblV original ['a'] .callByValuePar 4) [] (render bodies true failureFirst) 1=some none ∧
    evV generated ['a'] .callByValueSeq (tblV generated ['a'] .callByValueSeq 4) [] (render bodies false failureFirst) 1=some none := by decide +kernel

/-- Capture analysis proves alphabet safety, not a maximal endpoint. -/
theorem shorter_capture_not_at_scanner_frontier :
    (short 2).length<(long 2).length ∧
    evV original (block 2) .callByValuePar (tblV original (block 2) .callByValuePar 12) [] A (block 2).length≠
      evV original (block 2) .callByValuePar (tblV original (block 2) .callByValuePar 12) [] (NestedScannerArguments.scan alphabet) (block 2).length := by decide +kernel


/-- The actual recursive parser is the same balanced-prefix parser used in
FiniteResidualControl's impossibility theorem, with arbitrary later input. -/
theorem balanced_capture (n : Nat) : ∀ tail,
    SObs original .callByValuePar B (long n++tail) (some tail) := by
  have enter (x rest : List Char) (h : SObs original .callByValuePar FiniteResidualControl.balancedBody x (some rest)) :
      SObs original .callByValuePar B x (some rest) := by
    obtain ⟨o,hd,ho⟩ := h
    have hs : MDerives original .callByValuePar (MExp.subst [] FiniteResidualControl.balancedBody) x o := by
      simpa [FiniteResidualControl.balancedBody,MExp.subst,MExp.substArgs] using hd
    simpa [B,ho] using call0_obs (show ruleAtM original.rules 0=some ⟨0,FiniteResidualControl.balancedBody⟩ from rfl) rfl hs
  induction n with
  | zero =>
    intro tail
    apply enter
    apply RootObservation.alt_right
    · exact RootObservation.seq_fail ⟨_,.chrFail 'a' 'b' tail (by decide),rfl⟩
    · exact ⟨_,.chrOk 'b' 'b' tail (by decide),rfl⟩
  | succ n ih =>
    intro tail
    have hna : short (n+1)='a'::short n := by simp [short,List.replicate_succ]
    have hnc : List.replicate (n+1) 'c'=List.replicate n 'c'++['c'] := List.replicate_succ'
    have hx : long (n+1)++tail='a'::(long n++'c'::tail) := by simp [long,hna,hnc,List.append_assoc]
    apply enter
    rw [hx]
    apply RootObservation.alt_left
    exact RootObservation.seq_ok ⟨_,.chrOk 'a' 'a' _ (by decide),rfl⟩
      (RootObservation.seq_ok (ih ('c'::tail)) ⟨_,.chrOk 'c' 'c' tail (by decide),rfl⟩)

theorem short_capture (n : Nat) (tail : List Char) :
    SObs original .callByValuePar A (long n++tail) (some (List.replicate n 'c'++tail)) := by
  have hstar : ∀ n tail, ∃ t, MDerives original .callByValuePar (.star (.chr 'a'))
      (List.replicate n 'a'++'b'::tail) (.ok t ('b'::tail)) := by
    intro n
    induction n with
    | zero => intro tail; exact ⟨_,.starNil _ _ (.chrFail 'a' 'b' tail (by decide))⟩
    | succ n ih =>
      intro tail
      obtain ⟨t,ht⟩ := ih tail
      exact ⟨_,.starCons _ _ _ _ _ _ (.chrOk 'a' 'a' _ (by decide)) ht⟩
  obtain ⟨t,ht⟩ := hstar n (List.replicate n 'c'++tail)
  have hbody : SObs original .callByValuePar FiniteResidualControl.consumePrefix (long n++tail)
      (some (List.replicate n 'c'++tail)) := by
    exact ⟨_,.seqOk _ _ _ _ _ _ _ (by simpa [long,short,List.append_assoc] using ht) (.chrOk 'b' 'b' _ (by decide)),rfl⟩
  obtain ⟨o,hd,ho⟩ := hbody
  have hs : MDerives original .callByValuePar (MExp.subst [] FiniteResidualControl.consumePrefix) (long n++tail) o := by
    simpa [FiniteResidualControl.consumePrefix,MExp.subst,MExp.substArgs] using hd
  simpa [A,ho] using call0_obs (show ruleAtM original.rules 1=some ⟨0,FiniteResidualControl.consumePrefix⟩ from rfl) rfl hs

theorem both_unbounded_actuals (n : Nat) (tail : List Char) :
    DerivesArgsPar original .callByValuePar (long n++tail) [A,B] [.lit (short n),.lit (long n)] := by
  obtain ⟨oa,ha,hea⟩ := short_capture n tail
  obtain ⟨ta,rfl⟩ := restOf_eq_some hea
  obtain ⟨ob,hb,heb⟩ := balanced_capture n tail
  obtain ⟨tb,rfl⟩ := restOf_eq_some heb
  exact .cons A [B] _ (short n) _ ta _ ha (by simp [long,List.append_assoc])
    (.cons B [] _ (long n) _ tb [] hb rfl (.nil _))

theorem copy_block_all_lengths (n : Nat) (tail : List Char) :
    SObs original .callByValuePar (root bodies A B) (block n++tail) (some tail) := by
  let input := block n++tail
  let parts := DelimitedCopyTemplates.sourceBlockParts d
  let body := DelimiterTemplate.compile d parts
  have hr : DelimiterTemplate.run d [short n,long n] parts input=some tail :=
    (DelimitedCopyTemplates.source_block d (short n) (long n) input tail).mpr (by simp [input,block,List.append_assoc])
  have hbodyFO : body.FirstOrder := DelimiterTemplate.compile_firstOrder d parts
  have hsourceFO : original.FirstOrder := source_firstOrder bodies d (DelimitedCopyCompiler.checked original originalRoot bodies alphabet d entry checked).1
  have hv : evV original input .callByValuePar (tblV original input .callByValuePar 0) []
      (MExp.subst [.lit (short n),.lit (long n)] body) input.length=some (some tail.length) := by
    have hs := evV_subst (g := original) (x := input) (s := .callByValuePar)
      (T := tblV original input .callByValuePar 0) (E := []) [short n,long n] body hbodyFO input.length
    have he := DelimiterTemplate.compile_eval original input .callByValuePar
      (tblV original input .callByValuePar 0) [short n,long n] d parts input.length (Nat.le_refl _)
    simpa only [sfx_self,hr,Option.map_some,List.map_cons,List.map_nil] using hs.trans he
  obtain ⟨o,hd,ho⟩ := evV_sound (by decide) (tblV_sound hsourceFO (by decide) 0)
    _ (firstOrder_subst (firstOrderArgs_lits [short n,long n]) body hbodyFO) _ (Nat.le_refl _) _ hv
  obtain ⟨t,rest,rfl,hlen⟩ := obsR_ok ho
  have hre : rest=tail := by
    have hs := rest_eq_sfx' hd
    rw [hlen] at hs
    have ht : sfx input tail.length=tail := sfx_suffix (pre := block n) rfl
    exact hs.symm.trans ht
  subst rest
  have hargs : DerivesArgsPar original .callByValuePar input [A,B] [.lit (short n),.lit (long n)] := by
    simpa [input,block,List.append_assoc] using both_unbounded_actuals n ([d]++short n++[d]++long n++[d]++tail)
  have hcall := MDerives.callParOk bodies.length [A,B] ⟨2,body⟩ input tail [.lit (short n),.lit (long n)] t rfl (source_rule bodies d) rfl hargs
    (by simpa [sfx] using hd)
  exact ⟨_,hcall,rfl⟩

theorem source_and_target_accept_all_lengths (n : Nat) :
    SObs original .callByValuePar originalRoot (block n) (some []) ∧
    SObs generated .callByValueSeq generatedRoot (block n) (some []) := by
  have hc : SObs original .callByValuePar (root bodies A B) (block n) (some []) := by simpa using copy_block_all_lengths n []
  have hs : SObs original .callByValuePar originalRoot (block n) (some []) :=
    RootObservation.seq_ok hc (RootObservation.not_fail ⟨_,.anyFail,rfl⟩)
  exact ⟨hs,(DelimitedCopyCompiler.observations_iff original originalRoot bodies alphabet d entry checked (block n) (some [])).mp hs⟩


theorem unbounded_both_values (bound : Nat) :
    ∃ n, bound<(short n).length ∧ bound<(long n).length ∧
      DerivesArgsPar original .callByValuePar (long n) [A,B] [.lit (short n),.lit (long n)] := by
  refine ⟨bound+1,?_,?_,?_⟩
  · simp [short]; omega
  · simp [long,short]; omega
  · simpa using both_unbounded_actuals (bound+1) []

def pureCopy : Term := .copy (.lit ['a']) (.lit ['a','b'])
def pureInput := ['a','b',d,'a',d,'a','b',d]
theorem physical_clock_zero_and_one :
    evV original pureInput .callByValuePar (tblV original pureInput .callByValuePar 0) [] (render bodies true pureCopy) pureInput.length=none ∧
    evV generated pureInput .callByValueSeq (tblV generated pureInput .callByValueSeq 0) [] (render bodies false pureCopy) pureInput.length=none ∧
    evV original pureInput .callByValuePar (tblV original pureInput .callByValuePar 1) [] (render bodies true pureCopy) pureInput.length=some (some 0) ∧
    evV generated pureInput .callByValueSeq (tblV generated pureInput .callByValueSeq 1) [] (render bodies false pureCopy) pureInput.length=some (some 0) := by decide +kernel

def wrongDeclaration : MGrammar := ⟨bodies.map (fun b => ⟨0,b⟩)++[⟨2,.eps⟩]⟩
theorem wrong_actual_body_rejected : DelimitedCopyCompiler.check wrongDeclaration originalRoot bodies alphabet d entry=false := by decide +kernel

end Shallot.MacroPeg.CBV.DelimitedCopyExamples
