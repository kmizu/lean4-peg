import MacroPeg.CBV.ChangedWordPrefix

namespace Shallot.MacroPeg.CBV.ChangedWordPrefixExamples
open LeadingReplayStar (User sourceRender)
open ExpressionContext (Context plug)
abbrev Arg := LeadingReplayStar.Arg
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def continuation (a : Arg) : Arg := .alt
  (.seq (.lit ['!']) (.seq (.user 0 (.seq a a)) a)) (.lit ['d'])
def actualBody : Arg := continuation (.param 0)
def actualArgument (V : Arg) : Arg := .seq (.param 0) V
def inlinedBody (V : Arg) : Arg := .seq V (continuation (actualArgument V))
def users (V : Arg) : List User := [
  .repeated [] (inlinedBody V) (.lit ['z']),
  .control ⟨[⟨some [],actualBody⟩],.leaf 0,none⟩]
def normalized (V : Arg) := LeadingReplayStar.sourceGrammar [] (users V)
def C : Context := .seq (.seq (.star .hole) (.atom (.seq (.lit []) (.param 0)))) (.atom (.lit ['z']))
def ve (V : Arg) := sourceRender [] (users V) V
def be (V : Arg) := sourceRender [] (users V) actualBody
def raw (V : Arg) := ChangedWordPrefix.source (normalized V) 0 1 (ve V) C
def target (V : Arg) := LeadingReplayStar.targetGrammar [] (users V)
def entry : Arg := .user 0 (.lit ['a','b'])

theorem checked_dup : ChangedWordPrefix.check (normalized (.param 0)) 0 1 (ve (.param 0)) (be (.param 0)) C=true := by decide +kernel
theorem checked_append : ChangedWordPrefix.check (normalized (.lit ['b'])) 0 1 (ve (.lit ['b'])) (be (.lit ['b'])) C=true := by decide +kernel

theorem valid (V : Arg) (hv : OriginControlNormalization.Valid [] (LeadingReplayStar.specs (users V)) V) :
    LeadingReplayStar.Valid [] (users V) := by
  have hlen : ∀ us : List ContinuationFamily.User, (ContinuationFamily.specs us).length=us.length :=
    fun us => ContinuationFamily.emit_length 0 us
  simp [LeadingReplayStar.Valid,ContinuationFamily.Valid,ContinuationFamily.Shapes,ContinuationFamily.User.Shape,
    users,LeadingReplayStar.converted,User.toControl,OriginControlNormalization.LeavesValid,
    OriginControlNormalization.Valid,OriginControlNormalization.Closed,ReplayControlFusion.Plan.All,
    inlinedBody,actualBody,actualArgument,continuation,LeadingReplayStar.replay,hlen,hv]
  exact hv

theorem entry_valid (V : Arg) : OriginControlNormalization.Valid [] (LeadingReplayStar.specs (users V)) entry := by
  have hlen : (LeadingReplayStar.specs (users V)).length=2 :=
    (ContinuationFamily.emit_length 0 (LeadingReplayStar.converted (users V))).trans rfl
  simp [entry,OriginControlNormalization.Valid,hlen]

theorem raw_rules (V : Arg) :
    ruleAtM (raw V).rules 0=some ⟨1,plug (.call 1 [WordPrefixInlining.argument (ve V)]) C⟩ ∧
    ruleAtM (raw V).rules 1=some ⟨1,ReplayCallInlining.body (be V)⟩ := ⟨rfl,rfl⟩

def tree (more : List Char → List Char) (w : List Char) : Nat → List Char
  | 0 => w++['z']
  | d+1 => let v := w++more w
    v++['!']++tree more (v++v) d++v++w++['z']

def sourceRun (V : Arg) (x : List Char) (k : Nat) :=
  evV (raw V) x .callByValuePar (tblV (raw V) x .callByValuePar k) [] (sourceRender [] (users V) entry) x.length
def targetRun (V : Arg) (x : List Char) (k : Nat) :=
  evV (target V) x .callByValueSeq (tblV (target V) x .callByValueSeq k) [] (LeadingReplayStar.targetRender [] (users V) entry) x.length

theorem source_dup : ∀ d∈[0,1,2], sourceRun (.param 0) (tree id ['a','b'] d) 12=some (some 0) := by decide +kernel
theorem source_append : ∀ d∈[0,1,2], sourceRun (.lit ['b']) (tree (fun _ => ['b']) ['a','b'] d) 12=some (some 0) := by decide +kernel

theorem direct_targets : targetRun (.param 0) (tree id ['a','b'] 1) 12=some (some 0) ∧
    targetRun (.lit ['b']) (tree (fun _ => ['b']) ['a','b'] 1) 12=some (some 0) := by decide +kernel

theorem restoration_failures : ∀ x∈["abb!abbabbzababz".toList,"abdabz".toList],
    sourceRun (.lit ['b']) x 8=some none ∧ targetRun (.lit ['b']) x 12=some none := by decide +kernel

theorem captured_words : WordArguments.value [['a','b']] (WordPrefixInlining.argument (.param 0))=some ['a','b','a','b'] ∧
    WordArguments.value [['a','b']] (WordPrefixInlining.argument (.lit ['b']))=some ['a','b','b'] := by decide +kernel

theorem changed_call_clock : sourceRun (.lit ['b']) "abbdabz".toList 1=none ∧
    evV (normalized (.lit ['b'])) "abbdabz".toList .callByValuePar
      (tblV (normalized (.lit ['b'])) "abbdabz".toList .callByValuePar 1)
      [] (sourceRender [] (users (.lit ['b'])) entry) 7=some (some 0) := by decide +kernel

theorem new_word_preflight_required :
    let A := MExp.seq (.param 0) (.lit ['b'])
    let g : MGrammar := ⟨[⟨1,.lit []⟩]⟩
    evV g ['a'] .callByValuePar (tblV g ['a'] .callByValuePar 2) [['a']] (.call 0 [A]) 1=some none ∧
    evV g ['a'] .callByValuePar (tblV g ['a'] .callByValuePar 1) [['a']] (WordCallUnfolding.expanded A (.lit [])) 1=some none ∧
    evV g ['a'] .callByValuePar (tblV g ['a'] .callByValuePar 1) [['a']] (MExp.subst [A] (.lit [])) 1=some (some 1) := by decide +kernel

theorem language (V : Arg) (hv : OriginControlNormalization.Valid [] (LeadingReplayStar.specs (users V)) V)
    (hc : ChangedWordPrefix.check (normalized V) 0 1 (ve V) (be V) C=true) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
      SObs (raw V) .callByValuePar (sourceRender [] (users V) entry) x (some []) ↔ SObs g .callByValueSeq start x (some []) :=
  ChangedWordPrefix.language_translation [] (by simp [RegularCaptureProduct.Valid]) (users V) (valid V hv)
    0 1 (ve V) (be V) C hc entry (entry_valid V)

theorem duplicate_language : ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
    SObs (raw (.param 0)) .callByValuePar (sourceRender [] (users (.param 0)) entry) x (some []) ↔
      SObs g .callByValueSeq start x (some []) :=
  language (.param 0) True.intro checked_dup

theorem append_language : ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
    SObs (raw (.lit ['b'])) .callByValuePar (sourceRender [] (users (.lit ['b'])) entry) x (some []) ↔
      SObs g .callByValueSeq start x (some []) :=
  language (.lit ['b']) True.intro checked_append

/-- Input-dependent alternatives cannot be substituted as fixed words:
the second evaluation would choose b instead of replaying the captured a. -/
theorem parsing_argument_is_not_a_word :
    let A := MExp.alt (.lit ['a']) (.lit ['b'])
    let B := MExp.seq (.param 0) (.param 0)
    let g : MGrammar := ⟨[⟨1,B⟩]⟩
    evV g ['a','b'] .callByValuePar (tblV g ['a','b'] .callByValuePar 2) [] (.call 0 [A]) 2=some none ∧
    evV g ['a','b'] .callByValuePar (tblV g ['a','b'] .callByValuePar 1) [] (WordCallUnfolding.expanded A B) 2=some (some 0) ∧
    WordCallUnfolding.wordCheck A=false := by decide +kernel

theorem parameter_scope_preserved :
    let g : MGrammar := ⟨[⟨1,.param 1⟩]⟩
    evV g ['a'] .callByValuePar (tblV g ['a'] .callByValuePar 2) [['a'],['a']] (.call 0 [.param 0]) 1=some none ∧
    evV g ['a'] .callByValuePar (tblV g ['a'] .callByValuePar 1) [['a'],['a']] (WordCallUnfolding.expanded (.param 0) (.param 1)) 1=some none ∧
    evV g ['a'] .callByValuePar (tblV g ['a'] .callByValuePar 1) [['a'],['a']] (.param 1) 1=some (some 0) := by decide +kernel

end Shallot.MacroPeg.CBV.ChangedWordPrefixExamples
