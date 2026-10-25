import MacroPeg.CBV.FrontierCaptureCompiler
import MacroPeg.CBV.ProducedPrefixFamilyExamples

namespace Shallot.MacroPeg.CBV.FrontierCaptureExamples
open FrontierArgumentNormalization (Argument argument arguments scans guarded)
open NestedScannerArguments (scan)
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def lexer : MExp := .alt (.seq (.lit ['a']) (.call 0 [])) .eps
def balanced : MExp := .alt (.seq (.lit ['a']) (.seq (.call 1 []) (.lit ['c']))) (.lit ['b'])
def helpers : List MExp := [.seq .eps lexer,.seq .eps balanced]
def small : Argument := ⟨['a','b'],[.seq .eps lexer],.seq (.call 0 []) (.lit ['b'])⟩
def large : Argument := ⟨['a','b','c'],helpers,.call 1 []⟩
def ds : List Argument := [small,large]

def tail (args : List Argument) : MExp :=
  .seq (.lit ['!']) (.seq (.param 0) (.seq (.lit [':']) (.seq (.param 1) (.seq (.lit ['?'])
    (.seq (.alt (.seq (.lit ['@']) (.call 2 (arguments args))) .eps)
      (.seq (.lit ['/']) (.seq (.param 1) (.seq (.lit [':']) (.param 0)))))))))
def selection (args : List Argument) : FrontierArgumentCompiler.Selection := [none,none,some args]
def templates (args : List Argument) : List MRule :=
  [⟨0,lexer⟩,⟨0,balanced⟩,⟨2,FrontierArgumentCompiler.render (selection args) (tail args)⟩]
def original (args : List Argument) : MGrammar :=
  ⟨[⟨0,.seq .eps lexer⟩,⟨0,.seq .eps balanced⟩,⟨2,.seq (scan ['a','b','c']) (tail args)⟩]⟩
def producers (args : List Argument) : SelectedProducerNormalization.Selection :=
  [none,none,some ⟨scan ['a','b','c'],FrontierArgumentCompiler.render (selection args) (tail args)⟩]
def root (args : List Argument) : MExp := .call 2 (arguments args)
def templateRoot (args : List Argument) : MExp := guarded 2 args

theorem checked : FrontierCaptureCompiler.check (original ds) (selection ds) (producers ds) (templates ds)=true := by decide +kernel

theorem root_checked : FrontierCaptureCompiler.rootCheck (selection ds) (producers ds) (root ds) (templateRoot ds)=true := by decide +kernel

theorem small_checked : FrontierArgumentNormalization.check (original ds) small=true := by decide +kernel

theorem large_checked : FrontierArgumentNormalization.check (original ds) large=true := by decide +kernel

theorem independent_source_arguments : (root ds)=.call 2
    [.seq (.seq (.call 0 []) (.lit ['b'])) (.notP (NestedScannerArguments.choice ['a','b'])),
     .seq (.call 1 []) (.notP (NestedScannerArguments.choice ['a','b','c']))] := by rfl

theorem target_layout : (PrefixFamilyFusion.seqGrammar (templates ds)).rules.map MRule.arity=[0,0,2] := by decide +kernel

def leftWord (n : Nat) := List.replicate n 'a'++['b']
def value (n m : Nat) := leftWord n++List.replicate m 'c'
def beforeChild (n m : Nat) := value n m++['!']++leftWord n++[':']++value n m++['?']
def restore (n m : Nat) := ['/']++value n m++[':']++leftWord n
def simple (n m : Nat) := beforeChild n m++restore n m
def nested (n k : Nat) := beforeChild n n++['@']++simple k k++restore n n

def sourceRun (x : List Char) (clock : Nat) := evV (original ds) x .callByValuePar
  (tblV (original ds) x .callByValuePar clock) [] (root ds) x.length

def targetRun (x : List Char) (clock : Nat) := evV (PrefixFamilyFusion.seqGrammar (templates ds)) x .callByValueSeq
  (tblV (PrefixFamilyFusion.seqGrammar (templates ds)) x .callByValueSeq clock) []
    (PrefixFamilyFusion.render false 0 (templateRoot ds)) x.length

theorem source_simple : ∀ n∈[0,1,2,4], sourceRun (simple n n) 14=some (some 0) := by decide +kernel

theorem target_simple : ∀ n∈[0,1,2,4], targetRun (simple n n) 14=some (some 0) := by decide +kernel

theorem source_nested : ∀ pair∈[(0,3),(1,3),(3,1)], sourceRun (nested pair.1 pair.2) 18=some (some 0) := by decide +kernel

theorem target_nested : ∀ pair∈[(0,3),(1,3),(3,1)], targetRun (nested pair.1 pair.2) 18=some (some 0) := by decide +kernel

theorem unbalanced_source : ∀ pair∈[(0,1),(1,0),(1,2),(3,1)], sourceRun (simple pair.1 pair.2) 14=some none := by decide +kernel

theorem unbalanced_target : ∀ pair∈[(0,1),(1,0),(1,2),(3,1)], targetRun (simple pair.1 pair.2) 14=some none := by decide +kernel

theorem omitting_preflight_accepts_unbalanced :
    evV (PrefixFamilyFusion.seqGrammar (templates ds)) (simple 1 2) .callByValueSeq
      (tblV (PrefixFamilyFusion.seqGrammar (templates ds)) (simple 1 2) .callByValueSeq 14) []
      (.call 2 (scans ds)) (simple 1 2).length=some (some 0) := by decide +kernel

theorem observations (x : List Char) (rest : Option (List Char)) :
    SObs (original ds) .callByValuePar (root ds) x rest ↔
      SObs (PrefixFamilyFusion.seqGrammar (templates ds)) .callByValueSeq
        (PrefixFamilyFusion.render false 0 (templateRoot ds)) x rest :=
  FrontierCaptureCompiler.observations_iff (original ds) (selection ds) (producers ds) (templates ds)
    checked (root ds) (templateRoot ds) root_checked x rest

theorem first_rule : ruleAtM (original ds).rules 0=some ⟨0,.seq .eps lexer⟩ := by rfl
theorem second_rule : ruleAtM (original ds).rules 1=some ⟨0,.seq .eps balanced⟩ := by rfl

theorem value_succ (n : Nat) : value (n+1) (n+1)='a'::(value n n++['c']) := by
  have hc : List.replicate (n+1) 'c'=List.replicate n 'c'++['c'] := by
    induction n with
    | zero => rfl
    | succ n ih => simpa only [List.replicate_succ,List.cons_append] using congrArg (List.cons 'c') ih
  simp only [value,leftWord,List.replicate_succ,List.cons_append]
  rw [←List.replicate_succ,hc]
  simp only [List.append_assoc]

/-- The second actual argument executes a genuinely recursive balanced parser,
not a scanner or a cumulative spelling of the first argument. -/
theorem balanced_capture (n : Nat) (rest : List Char) :
    ∃ t, MDerives (original ds) .callByValuePar (.call 1 []) (value n n++rest) (.ok t rest) := by
  induction n generalizing rest with
  | zero =>
    apply ProducedPrefixFamilyExamples.call0_derive (original ds) .callByValuePar 1 _ second_rule
      ⟨True.intro,by trivial⟩ _ rest
    exact .seqOk _ _ _ _ _ _ _ (.eps _) (.altR _ _ _ _ _ (.seqFail₁ _ _ _ (.litFail ['a'] _ rfl))
      (.litOk ['b'] _ _ rfl))
  | succ n ih =>
    obtain ⟨t,ht⟩ := ih ('c'::rest)
    have hin : value (n+1) (n+1)++rest='a'::(value n n++'c'::rest) := by rw [value_succ]; simp [List.append_assoc]
    rw [hin]
    apply ProducedPrefixFamilyExamples.call0_derive (original ds) .callByValuePar 1 _ second_rule
      ⟨True.intro,by trivial⟩ _ rest
    exact .seqOk _ _ _ _ _ _ _ (.eps _) (.altL _ _ _ _ _ (.seqOk _ _ _ _ _ _ _
      (.litOk ['a'] _ _ rfl) (.seqOk _ _ _ _ _ _ _ ht (.litOk ['c'] _ _ rfl))))

theorem choice_failure (A : List Char) (c : Char) (rest : List Char)
    (hf : NestedScannerArguments.accepts A c=false) :
    MDerives (original ds) .callByValuePar (NestedScannerArguments.choice A) (c::rest) .fail := by
  induction A with
  | nil => exact .notOk .eps _ _ _ (.eps _)
  | cons a A ih =>
    have h := Bool.or_eq_false_iff.mp hf
    exact .altFail _ _ _ (.chrFail a c rest h.1) (ih h.2)

theorem actual_parallel_captures (n : Nat) (rest : List Char) :
    DerivesArgsPar (original ds) .callByValuePar (value n n++'!'::rest)
      (arguments ds) [.lit (leftWord n),.lit (value n n)] := by
  obtain ⟨ta,ha⟩ := ProducedPrefixFamilyExamples.lexer_capture (original ds) .callByValuePar
    0 'a' true first_rule n ('b'::(List.replicate n 'c'++'!'::rest)) rfl
  obtain ⟨tb,hb⟩ := balanced_capture n ('!'::rest)
  have ha' : MDerives (original ds) .callByValuePar (.call 0 []) (value n n++'!'::rest)
      (.ok ta ('b'::(List.replicate n 'c'++'!'::rest))) := by
    simpa only [value,leftWord,List.append_assoc,List.cons_append,List.nil_append] using ha
  have hstop : MDerives (original ds) .callByValuePar (NestedScannerArguments.choice ['a','b'])
      (List.replicate n 'c'++'!'::rest) .fail := by
    cases n <;> exact choice_failure _ _ _ rfl
  have hA : ∃ t, MDerives (original ds) .callByValuePar (argument small) (value n n++'!'::rest)
      (.ok t (List.replicate n 'c'++'!'::rest)) := by
    exact ⟨_,.seqOk _ _ _ _ _ _ _ (.seqOk _ _ _ _ _ _ _ ha' (.litOk ['b'] _ _ rfl))
      (.notFail _ _ hstop)⟩
  have hB : ∃ t, MDerives (original ds) .callByValuePar (argument large) (value n n++'!'::rest)
      (.ok t ('!'::rest)) := by
    exact ⟨_,.seqOk _ _ _ _ _ _ _ hb (.notFail _ _ (choice_failure _ '!' rest rfl))⟩
  obtain ⟨tA,hA⟩ := hA
  obtain ⟨tB,hB⟩ := hB
  exact .cons _ _ _ (leftWord n) _ tA _ hA (by simp [value,List.append_assoc])
    (.cons _ [] _ (value n n) _ tB [] hB rfl (.nil _))

theorem unbounded_source_values (bound : Nat) :
    ∃ n, bound<(leftWord n).length ∧ bound<(value n n).length := by
  refine ⟨bound+1,?_,?_⟩ <;> simp [leftWord,value] <;> omega

theorem choice_success (A : List Char) (c : Char) (rest : List Char)
    (hf : NestedScannerArguments.accepts A c=true) :
    ∃ t, MDerives (original ds) .callByValuePar (NestedScannerArguments.choice A) (c::rest) (.ok t rest) := by
  induction A with
  | nil => cases hf
  | cons a A ih =>
    by_cases h : Shallot.beqChar a c=true
    · exact ⟨_,.altL _ _ _ _ _ (.chrOk a c rest h)⟩
    · have ht : NestedScannerArguments.accepts A c=true := by simpa [NestedScannerArguments.accepts,h] using hf
      obtain ⟨t,hd⟩ := ih ht
      exact ⟨_,.altR _ _ _ _ _ (.chrFail a c rest (Bool.eq_false_iff.mpr h)) hd⟩

theorem scan_capture (A w rest : List Char) (hw : w.all (NestedScannerArguments.accepts A)=true)
    (hf : MDerives (original ds) .callByValuePar (NestedScannerArguments.choice A) rest .fail) :
    ∃ t, MDerives (original ds) .callByValuePar (scan A) (w++rest) (.ok t rest) := by
  induction w with
  | nil => exact ⟨_,.starNil _ _ hf⟩
  | cons c w ih =>
    obtain ⟨hc,ht⟩ := Bool.and_eq_true_iff.mp hw
    obtain ⟨t,hd⟩ := choice_success A c (w++rest) hc
    obtain ⟨ts,hs⟩ := ih ht
    exact ⟨_,.starCons _ _ _ _ t ts hd hs⟩

theorem prepend_literal (w : List Char) (e : MExp) (input rest : List Char)
    (h : ∃ t, MDerives (original ds) .callByValuePar e input (.ok t rest)) :
    ∃ t, MDerives (original ds) .callByValuePar (.seq (.lit w) e) (w++input) (.ok t rest) := by
  obtain ⟨t,ht⟩ := h
  exact ⟨_,.seqOk _ _ _ _ _ _ t (.litOk w _ _ ((CBVtoCBN.stripPrefix_exact _ _ _).mpr rfl)) ht⟩

theorem source_all_lengths (n : Nat) (rest : List Char) :
    SObs (original ds) .callByValuePar (root ds) (simple n n++rest) (some rest) := by
  have h0 : ∃ t, MDerives (original ds) .callByValuePar (.lit (leftWord n)) (leftWord n++rest) (.ok t rest) :=
    ⟨_,.litOk _ _ _ ((CBVtoCBN.stripPrefix_exact _ _ _).mpr rfl)⟩
  have h1 := prepend_literal [':'] _ _ _ h0
  have h2 := prepend_literal (value n n) _ _ _ h1
  have h3 := prepend_literal ['/'] _ _ _ h2
  obtain ⟨t3,h3⟩ := h3
  let suffix := ['/']++(value n n++([':']++(leftWord n++rest)))
  have hopt : MDerives (original ds) .callByValuePar
      (.alt (.seq (.lit ['@']) (.call 2 (arguments ds))) .eps) suffix (.ok (.choiceR (.leaf [])) suffix) :=
    .altR _ _ _ _ _ (.seqFail₁ _ _ _ (.litFail ['@'] _ rfl)) (.eps _)
  have h4 : ∃ t, MDerives (original ds) .callByValuePar
      (.seq (.alt (.seq (.lit ['@']) (.call 2 (arguments ds))) .eps)
        (.seq (.lit ['/']) (.seq (.lit (value n n)) (.seq (.lit [':']) (.lit (leftWord n)))))) suffix (.ok t rest) :=
    ⟨_,.seqOk _ _ _ _ _ _ t3 hopt h3⟩
  have h5 := prepend_literal ['?'] _ _ _ h4
  have h6 := prepend_literal (value n n) _ _ _ h5
  have h7 := prepend_literal [':'] _ _ _ h6
  have h8 := prepend_literal (leftWord n) _ _ _ h7
  have h9 := prepend_literal ['!'] _ _ _ h8
  obtain ⟨tt,ht⟩ := h9
  have hw : (value n n).all (NestedScannerArguments.accepts ['a','b','c'])=true := by
    simp [value,leftWord,List.all_append,List.all_replicate,NestedScannerArguments.accepts,Shallot.beqChar]
  obtain ⟨tp,hp⟩ := scan_capture ['a','b','c'] (value n n) ('!'::(leftWord n++(':'::(value n n++('?'::suffix))))) hw
    (choice_failure _ '!' _ rfl)
  have hb : MDerives (original ds) .callByValuePar
      (MExp.subst [.lit (leftWord n),.lit (value n n)] (.seq (scan ['a','b','c']) (tail ds)))
      (simple n n++rest) (.ok (.seq tp tt) rest) := by
    have hh := MDerives.seqOk _ _ _ _ _ tp tt hp ht
    simpa only [simple,beforeChild,restore,suffix,tail,MExp.subst,MExp.substArgs,scan,NestedScannerArguments.choice,
      MExp.failAlways,List.getElem?_cons_zero,List.getElem?_cons_succ,List.getElem?_nil,List.append_assoc,
      List.cons_append,List.nil_append,arguments,ds,small,large,argument,argAt,List.map_cons,List.map_nil] using hh
  have ha : DerivesArgsPar (original ds) .callByValuePar (simple n n++rest)
      (arguments ds) [.lit (leftWord n),.lit (value n n)] := by
    have hh := actual_parallel_captures n (leftWord n++(':'::(value n n++('?'::suffix))))
    simpa only [simple,beforeChild,restore,suffix,List.append_assoc,List.cons_append,List.nil_append] using hh
  exact ⟨_,.callParOk 2 _ _ _ rest _ (.seq tp tt) rfl rfl rfl ha hb,rfl⟩

theorem target_all_lengths (n : Nat) (rest : List Char) :
    SObs (PrefixFamilyFusion.seqGrammar (templates ds)) .callByValueSeq
      (PrefixFamilyFusion.render false 0 (templateRoot ds)) (simple n n++rest) (some rest) :=
  (observations _ _).mp (source_all_lengths n rest)

def stuck : Argument := ⟨['a','b'],[],.star .eps⟩
def nullableArgs : List Argument := [stuck,large]

theorem nullable_checked : FrontierCaptureCompiler.check (original nullableArgs) (selection nullableArgs)
    (producers nullableArgs) (templates nullableArgs)=true := by decide +kernel

theorem nullable_root_checked : FrontierCaptureCompiler.rootCheck (selection nullableArgs) (producers nullableArgs)
    (root nullableArgs) (templateRoot nullableArgs)=true := by decide +kernel

theorem nullable_source (x : List Char) (k : Nat) :
    evV (original nullableArgs) x .callByValuePar (tblV (original nullableArgs) x .callByValuePar k) []
      (root nullableArgs) x.length=none := by
  have harg : evV (original nullableArgs) x .callByValuePar (tblV (original nullableArgs) x .callByValuePar k) []
      (argument stuck) x.length=none := by
    have hs : evV (original nullableArgs) x .callByValuePar (tblV (original nullableArgs) x .callByValuePar k) []
        (.star .eps) x.length=none := by
      rw [evV_star]; exact evStar_stuck (j := x.length) rfl (by omega)
    exact evV_seq_none hs
  have hr : ruleAtM (original nullableArgs).rules 2=some ⟨2,.seq (scan ['a','b','c']) (tail nullableArgs)⟩ := rfl
  change evV _ _ _ _ [] (.call 2 [argument stuck,argument large]) _=none
  rw [evV_call_par hr rfl (by decide),evPar_cons_none harg]

theorem nullable_target (x : List Char) (k : Nat) :
    evV (PrefixFamilyFusion.seqGrammar (templates nullableArgs)) x .callByValueSeq
      (tblV (PrefixFamilyFusion.seqGrammar (templates nullableArgs)) x .callByValueSeq k) []
      (PrefixFamilyFusion.render false 0 (templateRoot nullableArgs)) x.length=none :=
  (FrontierCaptureCompiler.undefined_iff (original nullableArgs) (selection nullableArgs) (producers nullableArgs)
    (templates nullableArgs) nullable_checked (root nullableArgs) (templateRoot nullableArgs) nullable_root_checked x).mp
      (nullable_source x) k

theorem rejecting_unsafe_consumption : FrontierArgumentNormalization.check (original ds)
    ⟨['a','b'],helpers,.call 1 []⟩=false := by decide +kernel

theorem rejecting_incorrect_helper_layout : FrontierArgumentNormalization.check (original ds)
    ⟨['a','b','c'],[balanced],.call 0 []⟩=false := by decide +kernel

theorem missing_frontier_rejected : FrontierCaptureCompiler.rootCheck (selection ds) (producers ds)
    (.call 2 [small.parser,large.parser]) (templateRoot ds)=false := by decide +kernel

def rejected : Argument := ⟨['a','b'],[],MExp.failAlways⟩

theorem ordered_preflight :
    evV (original ds) ['!'] .callByValuePar (tblV (original ds) ['!'] .callByValuePar 0) []
      (FrontierArgumentNormalization.preflight [rejected,large]) 1=some none ∧
    evV (original ds) ['!'] .callByValuePar (tblV (original ds) ['!'] .callByValuePar 0) []
      (FrontierArgumentNormalization.preflight [large,rejected]) 1=none := by decide +kernel

end Shallot.MacroPeg.CBV.FrontierCaptureExamples
