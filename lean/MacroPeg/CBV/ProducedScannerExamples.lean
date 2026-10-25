import MacroPeg.CBV.ProducedScannerCompiler

namespace Shallot.MacroPeg.CBV.ProducedScannerExamples
open RecursiveScannerProductCompiler (Arg Entries source sourceExpr target plain offset)
open ProducedScannerCompiler (check rootCheck)
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def machine : StatefulScanner.Machine 1 := ⟨fun _ => [('a',0)]⟩
def labels : ScannerReplayResidual.Labels 1 := fun _ => some ['a']
def entries : Entries 1 := fun i => if i=2 then .shift 0 labels else .replay

def producer : Arg := .user 1 (.lit [])
def producerBody : Arg := .alt (.seq (.lit ['a']) producer) (.lit [])
def parentBody : Arg := .seq (.lit ['!']) (.seq (.user 2 (.param 0))
  (.seq (.lit ['?']) (.seq (.alt (.seq (.lit ['@']) (.user 0 producer)) (.lit [])) (.seq (.lit ['/']) (.param 0)))))
def shiftedTail : Arg := .seq (.lit [':']) (.param 0)
def bodies : List Arg := [parentBody,producerBody,shiftedTail]
def start : Arg := .user 0 producer

/-- Only the first user's replay header is replaced by its actual closed
recursive producer. Scanner helpers retain their original nullary arities. -/
def original : MGrammar := ⟨(source machine entries bodies).rules.set (offset machine)
  ⟨1,.seq (sourceExpr machine producer) (sourceExpr machine parentBody)⟩⟩
def selected : SelectedProducerNormalization.Selection := List.replicate (offset machine) none ++
  [some ⟨sourceExpr machine producer,sourceExpr machine parentBody⟩]

def D := DynamicScannerCapture.observer machine
def profiles := CaptureTransitionProfile.profiles D
def scannerSummary : RecursiveCaptureProfiles.ScannerSummary 1 := fun _ => profiles
def summary : RecursiveCaptureProfiles.Summary := fun _ _ => profiles
def inputs : ProfileCheckedScannerCorrespondence.Inputs := fun _ => profiles

theorem checked : check original selected machine entries bodies scannerSummary summary inputs=true := by decide +kernel

theorem root_checked : rootCheck selected machine entries bodies summary inputs start=true := by decide +kernel

theorem helper_arity_preserved : (ruleAtM original.rules 0).map MRule.arity=some 0 ∧
    (ruleAtM (SelectedProducerNormalization.target original selected).rules 0).map MRule.arity=some 0 := by exact ⟨rfl,rfl⟩

theorem actual_producer : ruleAtM original.rules (offset machine)=some
    ⟨1,.seq (sourceExpr machine producer) (sourceExpr machine parentBody)⟩ := by rfl

theorem actual_shift : ruleAtM original.rules (offset machine+2)=some
    ⟨1,.seq (.seq (.lit ['a']) (.param 0)) (.seq (.lit [':']) (.param 0))⟩ := by rfl

theorem target_size : (target machine entries bodies).rules.length=65 := by decide +kernel

def word (n : Nat) : List Char := List.replicate n 'a'
def simple (n : Nat) := word n++['!']++word (n+1)++[':']++word n++['?','/']++word n
def nested (n m : Nat) := word n++['!']++word (n+1)++[':']++word n++['?','@']++simple m++['/']++word n

def sourceRun (x : List Char) (k : Nat) := evV original x .callByValuePar (tblV original x .callByValuePar k) [] (sourceExpr machine start) x.length
def targetRun (x : List Char) (k : Nat) := evV (target machine entries bodies) x .callByValueSeq
  (tblV (target machine entries bodies) x .callByValueSeq k) [] (plain machine bodies [] start) x.length

theorem source_simple : ∀ n∈[0,1,2,4], sourceRun (simple n) 12=some (some 0) := by decide +kernel

theorem source_nested : ∀ pair∈[(1,3),(3,1),(2,4)], sourceRun (nested pair.1 pair.2) 16=some (some 0) := by decide +kernel

theorem target_simple : targetRun (simple 2) 8=some (some 0) := by decide +kernel

theorem target_nested_direct : targetRun (nested 1 3) 12=some (some 0) := by decide +kernel

theorem target_nested (n m : Nat) (hn : (n,m)∈[(1,3),(3,1),(2,4)]) : ∃ k, targetRun (nested n m) k=some (some 0) :=
  (ProducedScannerCompiler.defined_iff original selected machine entries bodies scannerSummary summary inputs checked start root_checked
    (nested n m) (some 0)).mp ⟨16,source_nested (n,m) hn⟩

theorem actual_recursive_rule : ruleAtM original.rules (offset machine+1)=some
    ⟨1,.seq (.param 0) (sourceExpr machine producerBody)⟩ := by rfl

theorem producer_call (input rest : List Char) (t : MTree)
    (hd : MDerives original .callByValuePar (sourceExpr machine producerBody) input (.ok t rest)) :
    ∃ trace, MDerives original .callByValuePar (sourceExpr machine producer) input (.ok trace rest) := by
  refine ⟨.nodeCall (offset machine+1) (.seq (.leaf []) t),MDerives.callParOk (offset machine+1) [.lit []]
    ⟨1,.seq (.param 0) (sourceExpr machine producerBody)⟩ input rest [.lit []] (.seq (.leaf []) t) rfl actual_recursive_rule rfl ?_ ?_⟩
  · exact .cons _ _ input [] input _ [] (.litOk [] input input rfl) rfl (.nil input)
  · have hclosed : ReplayFallbackFusion.Closed (sourceExpr machine producerBody) := by trivial
    simp only [MExp.subst,List.getElem?_cons_zero,ReplayFallbackFusion.subst_closed _ _ hclosed]
    exact .seqOk _ _ input input rest _ _ (.litOk [] input input rfl) hd

/-- All lengths are actual source captures in one fixed recursive grammar. -/
theorem producer_ok (n : Nat) (rest : List Char) :
    ∃ trace, MDerives original .callByValuePar (sourceExpr machine producer)
      (word n++'!'::rest) (.ok trace ('!'::rest)) := by
  induction n with
  | zero =>
    apply producer_call
    exact .altR _ _ _ _ _ (.seqFail₁ _ _ _ (.litFail ['a'] ('!'::rest) rfl)) (.litOk [] _ _ rfl)
  | succ n ih =>
    obtain ⟨t,ht⟩ := ih
    have hh : word (n+1)++'!'::rest='a'::(word n++'!'::rest) := by simp [word,List.replicate_succ]
    rw [hh]
    exact producer_call _ _ _ (.altL _ _ _ _ _ (.seqOk _ _ _ _ _ _ _ (.litOk ['a'] _ _ rfl) ht))

theorem actual_argument_capture (n : Nat) (rest : List Char) :
    DerivesArgsPar original .callByValuePar (word n++'!'::rest) [sourceExpr machine producer] [.lit (word n)] := by
  obtain ⟨t,ht⟩ := producer_ok n rest
  exact .cons _ _ _ (word n) _ t [] ht rfl (.nil _)

theorem unbounded_lengths : ∀ bound, ∃ n, (word n).length>bound := by
  intro bound
  exact ⟨bound+1,by simp [word]⟩

theorem word_succ (n : Nat) : word (n+1)=word n++['a'] := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [word,List.replicate_succ,List.cons_append] using congrArg (List.cons 'a') ih

theorem shorter_actual_prefix (n : Nat) (hn : 2≤n) :
    let x := word (n+1)++['?']
    evV original x .callByValuePar (tblV original x .callByValuePar 0) [word n] (.param 0) x.length=some (some 2) ∧
    evV original x .callByValuePar (tblV original x .callByValuePar 0) [word n] (.lit ['a']) x.length=some (some (n+1)) ∧
    2<n+1 := by
  dsimp only
  have hw := word_succ n
  have ha : evV original (word (n+1)++['?']) .callByValuePar
      (tblV original (word (n+1)++['?']) .callByValuePar 0) [word n] (.param 0) (word (n+1)++['?']).length=some (some 2) := by
    simp only [evV,List.getElem?_cons_zero]
    have hs : Shallot.stripPrefix? (word n) (sfx (word (n+1)++['?']) (word (n+1)++['?']).length)=some ['a','?'] := by
      apply (CBVtoCBN.stripPrefix_exact _ _ _).mpr
      simp only [sfx,Nat.sub_self,List.drop_zero]
      rw [hw]
      simp only [List.append_assoc,List.cons_append,List.nil_append]
    rw [hs]
    rfl
  refine ⟨ha,?_,by omega⟩
  simp [evV,sfx,word,List.replicate_succ,Shallot.stripPrefix?,Shallot.beqChar]

def shortParent := word 3++['!']++word 4++[':']++word 3++['?','@']++simple 1++['/']++word 2
def shortChild := word 3++['!']++word 4++[':']++word 3++['?','@']++word 1++['!']++word 2++[':']++word 1++['?','/','/']++word 3

theorem short_source : sourceRun shortParent 16=some none ∧ sourceRun shortChild 16=some none := by decide +kernel

theorem short_target : targetRun shortParent 12=some none ∧ targetRun shortChild 12=some none := by decide +kernel

theorem unreadable_root_checked : rootCheck selected machine entries bodies summary inputs (.user 2 (.lit ['a','b']))=true := by decide +kernel

theorem unreadable_capture_fails :
    evV original ['a','b'] .callByValuePar (tblV original ['a','b'] .callByValuePar 8) []
      (sourceExpr machine (.user 2 (.lit ['a','b']))) 2=some none ∧
    evV (target machine entries bodies) ['a','b'] .callByValueSeq (tblV (target machine entries bodies) ['a','b'] .callByValueSeq 8) []
      (plain machine bodies [] (.user 2 (.lit ['a','b']))) 2=some none := by decide +kernel

theorem wrong_producer_argument_rejected : rootCheck selected machine entries bodies summary inputs (.user 0 (.lit ['a']))=false := by decide +kernel

theorem observations (x : List Char) (rest : Option (List Char)) :
    SObs original .callByValuePar (sourceExpr machine start) x rest ↔
      SObs (target machine entries bodies) .callByValueSeq (plain machine bodies [] start) x rest :=
  ProducedScannerCompiler.observations_iff original selected machine entries bodies scannerSummary summary inputs checked start root_checked x rest

def nullableBodies : List Arg := [parentBody,.star (.lit []),shiftedTail]
def nullableOriginal : MGrammar := ⟨(source machine entries nullableBodies).rules.set (offset machine)
  ⟨1,.seq (sourceExpr machine producer) (sourceExpr machine parentBody)⟩⟩

theorem nullable_checked : check nullableOriginal selected machine entries nullableBodies scannerSummary summary inputs=true := by decide +kernel
theorem nullable_root_checked : rootCheck selected machine entries nullableBodies summary inputs start=true := by decide +kernel

theorem nullable_rule : ruleAtM nullableOriginal.rules (offset machine+1)=some ⟨1,.seq (.param 0) (.star (.lit []))⟩ := by rfl

theorem nullable_rows (x : List Char) (k p : Nat) (hp : p≤x.length) :
    valAt (tblV nullableOriginal x .callByValuePar k (offset machine+1) [[]]) p=none := by
  cases k with
  | zero => rfl
  | succ k =>
    rw [valAt_tblV_succ nullable_rule [[]] hp]
    have hzero : evV nullableOriginal x .callByValuePar (tblV nullableOriginal x .callByValuePar k) [[]] (.param 0) p=some (some p) := by
      simp [evV,Shallot.stripPrefix?,length_sfx x hp]
    rw [evV_seq_ok hzero,evV_star]
    exact evStar_stuck (j := p) (by simp [evV,Shallot.stripPrefix?,length_sfx x hp]) (by omega)

theorem nullable_source (x : List Char) (k : Nat) :
    evV nullableOriginal x .callByValuePar (tblV nullableOriginal x .callByValuePar k) [] (sourceExpr machine start) x.length=none := by
  have hd : evV nullableOriginal x .callByValuePar (tblV nullableOriginal x .callByValuePar k) [] (sourceExpr machine producer) x.length=none := by
    change evV _ _ _ _ [] (.call (offset machine+1) [.lit []]) _=none
    rw [evV_call_par nullable_rule rfl (by decide)]
    simpa [evParArgs,evV,Shallot.stripPrefix?,length_sfx x (Nat.le_refl _),pre] using nullable_rows x k x.length (Nat.le_refl _)
  have hr : ruleAtM nullableOriginal.rules (offset machine)=some
      ⟨1,.seq (sourceExpr machine producer) (sourceExpr machine parentBody)⟩ := rfl
  change evV _ _ _ _ [] (.call (offset machine) [sourceExpr machine producer]) _=none
  rw [evV_call_par hr rfl (by decide),evPar_cons_none hd]

theorem nullable_target (x : List Char) (k : Nat) :
    evV (target machine entries nullableBodies) x .callByValueSeq (tblV (target machine entries nullableBodies) x .callByValueSeq k) []
      (plain machine nullableBodies [] start) x.length=none :=
  (ProducedScannerCompiler.undefined_iff nullableOriginal selected machine entries nullableBodies scannerSummary summary inputs
    nullable_checked start nullable_root_checked x).mp (nullable_source x) k

/-- The generic preparation also keeps non-selected multiple-argument
rules, rather than silently treating every declaration as unary. -/
def mixedHead : MExp := .call 1 []
def mixedTail : MExp := .seq (.lit ['!']) (.call 2 [.param 0,.param 0])
def mixed : MGrammar := ⟨[⟨1,.seq mixedHead mixedTail⟩,⟨0,.lit ['a']⟩,⟨2,.seq (.param 0) (.param 1)⟩]⟩
def mixedSelection : SelectedProducerNormalization.Selection := [some ⟨mixedHead,mixedTail⟩]

theorem mixed_checked : SelectedProducerNormalization.check mixed mixedSelection=true := by decide +kernel

theorem mixed_arities : ((SelectedProducerNormalization.target mixed mixedSelection).rules.map MRule.arity)=[1,0,2] := by decide +kernel

theorem mixed_execution : evV mixed "a!aa".toList .callByValuePar (tblV mixed "a!aa".toList .callByValuePar 4) [] (.call 0 [mixedHead]) 4=some (some 0) ∧
    evV (SelectedProducerNormalization.target mixed mixedSelection) "a!aa".toList .callByValuePar
      (tblV (SelectedProducerNormalization.target mixed mixedSelection) "a!aa".toList .callByValuePar 4) [] (.call 0 [mixedHead]) 4=some (some 0) := by decide +kernel

theorem mixed_distinct_values : evV (SelectedProducerNormalization.target mixed mixedSelection) ['a','a','a'] .callByValuePar
    (tblV (SelectedProducerNormalization.target mixed mixedSelection) ['a','a','a'] .callByValuePar 2) []
    (.call 2 [.lit ['a'],.lit ['a','a']]) 3=some (some 0) := by decide +kernel

theorem mixed_argument_order : evV (SelectedProducerNormalization.target mixed mixedSelection) ['a'] .callByValuePar
    (tblV (SelectedProducerNormalization.target mixed mixedSelection) ['a'] .callByValuePar 0) []
    (.call 2 [MExp.failAlways,.star (.lit [])]) 1=some none ∧
    evV (SelectedProducerNormalization.target mixed mixedSelection) ['a'] .callByValuePar
      (tblV (SelectedProducerNormalization.target mixed mixedSelection) ['a'] .callByValuePar 0) []
      (.call 2 [.star (.lit []),MExp.failAlways]) 1=none := by decide +kernel

theorem mixed_wrong_arity : evV mixed ['a'] .callByValuePar (tblV mixed ['a'] .callByValuePar 0) []
    (.call 0 [.star (.lit []),.eps]) 1=some none ∧
    evV (SelectedProducerNormalization.target mixed mixedSelection) ['a'] .callByValuePar
      (tblV (SelectedProducerNormalization.target mixed mixedSelection) ['a'] .callByValuePar 0) []
      (.call 0 [.star (.lit []),.eps]) 1=some none := by decide +kernel

theorem selecting_nullary_rejected : SelectedProducerNormalization.check mixed
    [none,some ⟨.lit ['a'],.eps⟩]=false := by decide +kernel

end Shallot.MacroPeg.CBV.ProducedScannerExamples
