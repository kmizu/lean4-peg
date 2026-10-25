import MacroPeg.CBV.ProducedPrefixFamilyCompiler

namespace Shallot.MacroPeg.CBV.ProducedPrefixFamilyExamples
open ProducedPrefixFamilyCompiler (check rootCheck)
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def first : MExp := .call 1 []
def second : MExp := .call 2 []
def headParser : MExp := .seq first second

def lexer (i : Nat) (c : Char) : MExp := .alt (.seq (.lit [c]) (.call i [])) .eps

def parentTail : MExp := .seq (.lit ['!']) (.seq (.param 0) (.seq (.lit [':']) (.seq (.param 1)
  (.seq (.lit ['?']) (.seq (.alt (.seq (.lit ['@']) (.call 0 [first,second])) .eps)
    (.seq (.lit ['/']) (.seq (.param 1) (.seq (.lit [':']) (.param 0)))))))))

def templates : List MRule := [⟨2,parentTail⟩,⟨0,lexer 1 'a'⟩,⟨0,lexer 2 'b'⟩]
def original : MGrammar := ⟨(PrefixFamilyFusion.parGrammar templates).rules.set 0
  ⟨2,.seq headParser (PrefixFamilyFusion.render true 2 parentTail)⟩⟩
def selected : SelectedProducerNormalization.Selection :=
  [some ⟨headParser,PrefixFamilyFusion.render true 2 parentTail⟩]
def root : MExp := .call 0 [first,second]

theorem checked : check original selected templates=true := by decide +kernel

theorem root_checked : rootCheck selected root=true := by decide +kernel

theorem actual_producer : ruleAtM original.rules 0=some
    ⟨2,.seq headParser (PrefixFamilyFusion.render true 2 parentTail)⟩ := by rfl

theorem original_arguments : PrefixFamilyFusion.render true 0 root=.call 0 [first,headParser] := by rfl

theorem consecutive_target_arguments : PrefixFamilyFusion.render false 0 root=.call 0 [first,second] := by rfl

theorem prepared_replay_slot : ruleAtM (SelectedProducerNormalization.target original selected).rules 0=some
    ⟨2,.seq (.param 1) (PrefixFamilyFusion.render true 2 parentTail)⟩ := by rfl

theorem target_layout : (PrefixFamilyFusion.seqGrammar templates).rules.map MRule.arity=[2,0,0] := by decide +kernel

theorem first_source_rule : ruleAtM original.rules 1=some ⟨0,.seq .eps (lexer 1 'a')⟩ := by rfl
theorem second_source_rule : ruleAtM original.rules 2=some ⟨0,.seq .eps (lexer 2 'b')⟩ := by rfl
theorem first_target_rule : ruleAtM (PrefixFamilyFusion.seqGrammar templates).rules 1=some ⟨0,lexer 1 'a'⟩ := by rfl
theorem second_target_rule : ruleAtM (PrefixFamilyFusion.seqGrammar templates).rules 2=some ⟨0,lexer 2 'b'⟩ := by rfl

theorem call0_derive (g : MGrammar) (s : Strategy) (i : Nat) (B : MExp)
    (hr : ruleAtM g.rules i=some ⟨0,B⟩) (hB : ReplayFallbackFusion.Closed B)
    (input rest : List Char) (t : MTree) (hd : MDerives g s B input (.ok t rest)) :
    ∃ trace, MDerives g s (.call i []) input (.ok trace rest) := by
  have hb : MDerives g s (MExp.subst [] B) input (.ok t rest) := by
    rw [ReplayFallbackFusion.subst_closed _ B hB]; exact hd
  cases s with
  | callByName => exact ⟨_,.callNameOk i [] ⟨0,B⟩ input rest t rfl hr rfl hb⟩
  | callByValuePar => exact ⟨_,.callParOk i [] ⟨0,B⟩ input rest [] t rfl hr rfl (.nil input) hb⟩
  | callByValueSeq => exact ⟨_,.callSeqOk i [] ⟨0,B⟩ input input rest [] t rfl hr rfl (.nil input) hb⟩

theorem lexer_capture (g : MGrammar) (s : Strategy) (i : Nat) (c : Char) (wrapped : Bool)
    (hr : ruleAtM g.rules i=some ⟨0,if wrapped then .seq .eps (lexer i c) else lexer i c⟩)
    (n : Nat) (rest : List Char) (hf : Shallot.stripPrefix? [c] rest=none) :
    ∃ trace, MDerives g s (.call i []) (List.replicate n c++rest) (.ok trace rest) := by
  have hlex : ReplayFallbackFusion.Closed (lexer i c) := by trivial
  have enter (input tail : List Char) (t : MTree) (hd : MDerives g s (lexer i c) input (.ok t tail)) :
      ∃ trace, MDerives g s (.call i []) input (.ok trace tail) := by
    cases wrapped with
    | false => exact call0_derive g s i _ hr hlex input tail t hd
    | true =>
      exact call0_derive g s i _ hr ⟨True.intro,hlex⟩ input tail _
        (.seqOk _ _ input input tail _ t (.eps input) hd)
  induction n with
  | zero => exact enter rest rest _ (.altR _ _ _ _ _ (.seqFail₁ _ _ _ (.litFail [c] rest hf)) (.eps rest))
  | succ n ih =>
    obtain ⟨t,ht⟩ := ih
    have hin : List.replicate (n+1) c++rest=c::(List.replicate n c++rest) := by simp [List.replicate_succ]
    rw [hin]
    exact enter _ rest _ (.altL _ _ _ _ _ (.seqOk _ _ _ _ _ _ _ (.litOk [c] _ _ (by simp [Shallot.stripPrefix?,Shallot.beqChar])) ht))

def short (n : Nat) := List.replicate n 'a'
def word (n m : Nat) := short n++List.replicate m 'b'
/-- Both original arguments start at the same origin, for every pair of lengths. -/
theorem actual_parallel_captures (n m : Nat) (rest : List Char) :
    DerivesArgsPar original .callByValuePar (word n m++'!'::rest)
      [first,headParser] [.lit (short n),.lit (word n m)] := by
  have hf : Shallot.stripPrefix? ['a'] (List.replicate m 'b'++'!'::rest)=none := by
    cases m <;> rfl
  obtain ⟨ta,ha⟩ := lexer_capture original .callByValuePar 1 'a' true first_source_rule n
    (List.replicate m 'b'++'!'::rest) hf
  obtain ⟨tb,hb⟩ := lexer_capture original .callByValuePar 2 'b' true second_source_rule m ('!'::rest) rfl
  have ha' : MDerives original .callByValuePar first (word n m++'!'::rest)
      (.ok ta (List.replicate m 'b'++'!'::rest)) := by
    simpa only [first,word,short,List.append_assoc] using ha
  have hd : MDerives original .callByValuePar headParser (word n m++'!'::rest)
      (.ok (.seq ta tb) ('!'::rest)) := by
    exact .seqOk first second _ _ _ ta tb ha' hb
  exact .cons first [headParser] _ (short n) _ ta _ ha'
    (by simp only [word,List.append_assoc])
    (.cons headParser [] _ (word n m) _ (.seq ta tb) [] hd rfl (.nil _))

/-- The target discovers consecutive pieces rather than enumerating possible values. -/
theorem actual_sequential_chunks (n m : Nat) (rest : List Char) :
    DerivesArgsSeq (PrefixFamilyFusion.seqGrammar templates) .callByValueSeq
      (word n m++'!'::rest) [first,second]
      [.lit (short n),.lit (List.replicate m 'b')] ('!'::rest) := by
  have hf : Shallot.stripPrefix? ['a'] (List.replicate m 'b'++'!'::rest)=none := by
    cases m <;> rfl
  obtain ⟨ta,ha⟩ := lexer_capture (PrefixFamilyFusion.seqGrammar templates) .callByValueSeq
    1 'a' false first_target_rule n (List.replicate m 'b'++'!'::rest) hf
  obtain ⟨tb,hb⟩ := lexer_capture (PrefixFamilyFusion.seqGrammar templates) .callByValueSeq
    2 'b' false second_target_rule m ('!'::rest) rfl
  have ha' : MDerives (PrefixFamilyFusion.seqGrammar templates) .callByValueSeq first
      (word n m++'!'::rest) (.ok ta (List.replicate m 'b'++'!'::rest)) := by
    simpa only [first,word,short,List.append_assoc] using ha
  exact .cons first [second] _ (short n) _ _ ta _ ha'
    (by simp only [word,List.append_assoc])
    (.cons second [] _ (List.replicate m 'b') _ _ tb [] hb rfl (.nil _))

theorem unbounded_chunks (bound : Nat) :
    ∃ n m, bound<(short n).length ∧ bound<(List.replicate m 'b').length := by
  exact ⟨bound+1,bound+2,by simp [short],by simp⟩

def beforeChild (n m : Nat) := word n m++['!']++short n++[':']++word n m++['?']
def restore (n m : Nat) := ['/']++word n m++[':']++short n

def simple (n m : Nat) := beforeChild n m++restore n m
def nested (n m k l : Nat) := beforeChild n m++['@']++simple k l++restore n m

def sourceRun (x : List Char) (clock : Nat) := evV original x .callByValuePar
  (tblV original x .callByValuePar clock) [] (PrefixFamilyFusion.render true 0 root) x.length

def targetRun (x : List Char) (clock : Nat) := evV (PrefixFamilyFusion.seqGrammar templates) x .callByValueSeq
  (tblV (PrefixFamilyFusion.seqGrammar templates) x .callByValueSeq clock) [] (PrefixFamilyFusion.render false 0 root) x.length

theorem source_simple : ∀ pair∈[(0,0),(0,2),(2,0),(1,3),(3,1)], sourceRun (simple pair.1 pair.2) 12=some (some 0) := by decide +kernel

theorem target_simple : ∀ pair∈[(0,0),(0,2),(2,0),(1,3),(3,1)], targetRun (simple pair.1 pair.2) 12=some (some 0) := by decide +kernel

theorem source_nested : ∀ pair∈[((1,3),(3,1)),((3,1),(1,3)),((2,2),(0,3))],
    sourceRun (nested pair.1.1 pair.1.2 pair.2.1 pair.2.2) 16=some (some 0) := by decide +kernel

theorem target_nested : ∀ pair∈[((1,3),(3,1)),((3,1),(1,3)),((2,2),(0,3))],
    targetRun (nested pair.1.1 pair.1.2 pair.2.1 pair.2.2) 16=some (some 0) := by decide +kernel

def shortParent := beforeChild 3 1++['@']++simple 1 3++['/']++word 3 0++[':']++short 3
def wrongFirst := beforeChild 3 1++['@']++simple 1 3++['/']++word 3 1++[':']++short 1
def shortChild := beforeChild 3 1++['@']++beforeChild 1 3++['/']++word 1 2++[':']++short 1++restore 3 1

theorem short_source : sourceRun shortParent 16=some none ∧ sourceRun wrongFirst 16=some none ∧ sourceRun shortChild 16=some none := by decide +kernel

theorem short_target : targetRun shortParent 16=some none ∧ targetRun wrongFirst 16=some none ∧ targetRun shortChild 16=some none := by decide +kernel

theorem observations (x : List Char) (rest : Option (List Char)) :
    SObs original .callByValuePar (PrefixFamilyFusion.render true 0 root) x rest ↔
      SObs (PrefixFamilyFusion.seqGrammar templates) .callByValueSeq (PrefixFamilyFusion.render false 0 root) x rest :=
  ProducedPrefixFamilyCompiler.observations_iff original selected templates checked root root_checked x rest


theorem wrong_last_argument_rejected : rootCheck selected (.call 0 [first,first])=false := by decide +kernel

def nullableTemplates : List MRule := [⟨2,parentTail⟩,⟨0,.star .eps⟩,⟨0,lexer 2 'b'⟩]
def nullableOriginal : MGrammar := ⟨(PrefixFamilyFusion.parGrammar nullableTemplates).rules.set 0
  ⟨2,.seq headParser (PrefixFamilyFusion.render true 2 parentTail)⟩⟩

theorem nullable_checked : check nullableOriginal selected nullableTemplates=true := by decide +kernel

theorem nullable_rule : ruleAtM nullableOriginal.rules 1=some ⟨0,.seq .eps (.star .eps)⟩ := by rfl

theorem nullable_rows (x : List Char) (k p : Nat) (hp : p≤x.length) :
    valAt (tblV nullableOriginal x .callByValuePar k 1 []) p=none := by
  cases k with
  | zero => rfl
  | succ k =>
    rw [valAt_tblV_succ nullable_rule [] hp]
    rw [evV_seq_ok (show evV nullableOriginal x .callByValuePar
      (tblV nullableOriginal x .callByValuePar k) [] .eps p=some (some p) from rfl),evV_star]
    exact evStar_stuck (j := p) rfl (by omega)

theorem nullable_source (x : List Char) (k : Nat) :
    evV nullableOriginal x .callByValuePar (tblV nullableOriginal x .callByValuePar k) []
      (PrefixFamilyFusion.render true 0 root) x.length=none := by
  have hd : evV nullableOriginal x .callByValuePar (tblV nullableOriginal x .callByValuePar k) [] first x.length=none := by
    change evV _ _ _ _ [] (.call 1 []) _=none
    rw [evV_call_par nullable_rule rfl (by decide)]
    simpa only [evParArgs] using nullable_rows x k x.length (Nat.le_refl _)
  have hr : ruleAtM nullableOriginal.rules 0=some
      ⟨2,.seq headParser (PrefixFamilyFusion.render true 2 parentTail)⟩ := rfl
  change evV _ _ _ _ [] (.call 0 [first,headParser]) _=none
  rw [evV_call_par hr rfl (by decide),evPar_cons_none hd]

theorem nullable_target (x : List Char) (k : Nat) :
    evV (PrefixFamilyFusion.seqGrammar nullableTemplates) x .callByValueSeq
      (tblV (PrefixFamilyFusion.seqGrammar nullableTemplates) x .callByValueSeq k) []
      (PrefixFamilyFusion.render false 0 root) x.length=none :=
  (ProducedPrefixFamilyCompiler.undefined_iff nullableOriginal selected nullableTemplates
    nullable_checked root root_checked x).mp (nullable_source x) k

end Shallot.MacroPeg.CBV.ProducedPrefixFamilyExamples
