import MacroPeg.CBV.CanonicalProducerCorrespondence

namespace Shallot.MacroPeg.CBV.CanonicalProducerExamples
open CanonicalProducerCompiler
open ReplayControlFusion (Part)
open RecursiveProducedCompiler (Entry)
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def argument : MExp := .call 1 [.lit []]
def argumentBody : MExp := .alt (.seq (.chr 'a') argument) (.alt (.chr 'b') (.chr 'z'))
def query : MExp := .alt (.andP (.chr 'a')) (.seq (.notP (.chr 'a')) (.seq (.notP (.chr 'b')) (.call 2 [.lit []])))
def producer : MExp := .seq (.call 2 [.lit []]) argument
def childArgument : MExp := .seq (.notP (.param 0)) argument
def continuation : MExp := .seq (.chr '!') (.seq (.call 3 [.param 0])
  (.seq (.alt (.seq (.chr '@') (.call 0 [childArgument])) .eps) (.param 0)))
def ps : List Part := [⟨false,argumentBody⟩,⟨false,query⟩]
def specs : List Entry := [.produced producer continuation,.origin (.leaf 0),.origin (.leaf 1),
  .growth ⟨3,3,.chr '#',.chr 'g'⟩]
def cores : List MExp := [argument]
abbrev grammar := source ps specs

def root : MExp := .seq (.call 0 [argument]) (.notP .any)

theorem checked : check ps specs cores=true := by decide +kernel

theorem root_checked : conforms ps specs cores root=true := by decide +kernel

theorem output_root_checked : RecursiveProducedCompiler.conforms (outputEntries specs) (render specs root)=true := by decide +kernel

theorem old_gate_rejects : RecursiveProducedCompiler.check ps specs=false := by decide +kernel

theorem distinct_parsers : argument≠producer := by decide +kernel

theorem actual_prefix : ruleAtM grammar.rules 0=some ⟨1,.seq producer continuation⟩ := by rfl

theorem actual_argument_rule : ruleAtM grammar.rules 1=some ⟨1,argumentBody⟩ := by rfl

theorem actual_query_rule : ruleAtM grammar.rules 2=some ⟨1,query⟩ := by rfl

theorem prefix_supported : EndpointSupport.check grammar producer argument=true := by decide +kernel

theorem target_size : (target ps specs).rules.length=26 := by decide +kernel

def word (n : Nat) := List.replicate n 'a'++['b']
def simple (w : List Char) := w++['!']++w++['g']++w
def nested (w v : List Char) := w++['!']++w++['g','@']++simple v++w

def sourceRun (e : MExp) (x : List Char) (k : Nat) := evV grammar x .callByValuePar (tblV grammar x .callByValuePar k) [] e x.length
def targetRun (e : MExp) (x : List Char) (k : Nat) := evV (target ps specs) x .callByValueSeq (tblV (target ps specs) x .callByValueSeq k) [] (entry ps specs e) x.length

theorem source_restores : ∀ pair∈[(1,4),(4,1),(2,3)], sourceRun root (nested (word pair.1) (word pair.2)) 16=some (some 0) := by decide +kernel

theorem target_restores : ∀ pair∈[(1,4),(4,1),(2,3)], targetRun root (nested (word pair.1) (word pair.2)) 16=some (some 0) := by decide +kernel

theorem short_parent_rejected : targetRun root (word 4++['!']++word 4++['g','@']++simple (word 1)++word 3) 16=some none := by decide +kernel

theorem same_child_rejected : sourceRun root (nested (word 1) (word 1)) 16=some none ∧
    targetRun root (nested (word 1) (word 1)) 16=some none := by decide +kernel

/-- A fails finitely on X even though D's leading query diverges there.
The generated preflight evaluates the original argument first. -/
theorem original_argument_first : sourceRun root ['X'] 16=some none ∧ targetRun root ['X'] 16=some none := by decide +kernel

theorem finite_prefix_failure : sourceRun root (simple (word 0)) 16=some none ∧
    targetRun root (simple (word 0)) 16=some none := by decide +kernel

theorem grammar_delay : CanonicalProducerCorrespondence.delay ps specs=1 := by decide +kernel

theorem root_ready : rootCheck ps specs cores root=true := by decide +kernel

theorem argument_call (input rest : List Char) (t : MTree)
    (hd : MDerives grammar .callByValuePar argumentBody input (.ok t rest)) :
    MDerives grammar .callByValuePar argument input (.ok (.nodeCall 1 t) rest) := by
  apply MDerives.callParOk 1 [.lit []] ⟨1,argumentBody⟩ input rest [.lit []] t rfl actual_argument_rule rfl
  · exact .cons _ _ input [] input _ [] (.litOk [] input input rfl) rfl (.nil input)
  · have hclosed : ReplayFallbackFusion.Closed argumentBody := by trivial
    simpa only [ReplayFallbackFusion.subst_closed _ argumentBody hclosed] using hd

theorem argument_ok (n : Nat) (rest : List Char) :
    ∃ t, MDerives grammar .callByValuePar argument (word n++rest) (.ok t rest) := by
  induction n with
  | zero =>
    exact ⟨_,argument_call _ _ _ (.altR _ _ _ _ _ (.seqFail₁ _ _ _ (.chrFail 'a' 'b' rest rfl))
      (.altL _ _ _ _ _ (.chrOk 'b' 'b' rest rfl)))⟩
  | succ n ih =>
    obtain ⟨t,ht⟩ := ih
    have hh : word (n+1)++rest='a'::(word n++rest) := by simp [word,List.replicate_succ]
    rw [hh]
    exact ⟨_,argument_call _ _ _ (.altL _ _ _ _ _ (.seqOk _ _ _ _ _ _ _ (.chrOk 'a' 'a' _ rfl) ht))⟩

theorem actual_argument_capture (n : Nat) (rest : List Char) :
    DerivesArgsPar grammar .callByValuePar (word n++rest) [argument] [.lit (word n)] := by
  obtain ⟨t,ht⟩ := argument_ok n rest
  exact .cons argument [] _ (word n) rest t [] ht rfl (.nil _)

theorem capture_lengths : ∀ bound, ∃ n, (word n).length>bound := by
  intro bound
  exact ⟨bound,by simp [word]⟩

/-- The common core succeeds on z, but its distinct producer diverges.
Dropping the producer preflight would invent a finite acceptance. -/
theorem query_rows_other (c : Char) (ha : Shallot.beqChar 'a' c=false) (hb : Shallot.beqChar 'b' c=false)
    (rest : List Char) (k : Nat) (E : List (List Char)) :
    valAt (tblV grammar (c::rest) .callByValuePar k 2 E) (rest.length+1)=none := by
  induction k generalizing E with
  | zero => simp [tblV,valAt]
  | succ k ih =>
    rw [valAt_tblV_succ actual_query_rule E (by simp)]
    simpa [query,evV,MExp.andP,actual_query_rule,evParArgs,Shallot.stripPrefix?,sfx,ha,hb,pre] using ih [[]]

theorem query_rows (rest : List Char) (k : Nat) (E : List (List Char)) :
    valAt (tblV grammar ('z'::rest) .callByValuePar k 2 E) (rest.length+1)=none :=
  query_rows_other 'z' rfl rfl rest k E

theorem producer_none (rest : List Char) (k : Nat) (E : List (List Char)) :
    evV grammar ('z'::rest) .callByValuePar (tblV grammar ('z'::rest) .callByValuePar k) E producer (rest.length+1)=none := by
  have hq : evV grammar ('z'::rest) .callByValuePar (tblV grammar ('z'::rest) .callByValuePar k) E
      (.call 2 [.lit []]) (rest.length+1)=none := by
    rw [evV_call_par actual_query_rule rfl (by decide)]
    simpa [evParArgs,evV,Shallot.stripPrefix?,sfx,pre] using query_rows rest k [[]]
  exact evV_seq_none hq

theorem client_rows_none (rest : List Char) (k : Nat) (E : List (List Char)) :
    valAt (tblV grammar ('z'::rest) .callByValuePar k 0 E) (rest.length+1)=none := by
  cases k with
  | zero => simp [tblV,valAt]
  | succ k => rw [valAt_tblV_succ actual_prefix E (by simp),evV_seq_none (producer_none rest k E)]

theorem argument_on_z (rest : List Char) (k : Nat) (E : List (List Char)) :
    evV grammar ('z'::rest) .callByValuePar (tblV grammar ('z'::rest) .callByValuePar (k+1)) E argument
      (rest.length+1)=some (some rest.length) := by
  change evV grammar _ _ _ E (.call 1 [.lit []]) _=_
  rw [ProducerArgumentRewrite.call_ok grammar _ _ E 1 _ actual_argument_rule rfl (.lit []) (rest.length+1) (rest.length+1)
    (by simp [evV,Shallot.stripPrefix?,sfx]),valAt_tblV_succ actual_argument_rule _ (by simp)]
  simp [argumentBody,evV,sfx,Shallot.beqChar]

theorem source_diverges (rest : List Char) (k : Nat) : sourceRun (.call 0 [argument]) ('z'::rest) k=none := by
  cases k with
  | zero => simp [sourceRun,evV,actual_prefix,argument,actual_argument_rule,evParArgs,Shallot.stripPrefix?,tblV,valAt]
  | succ k =>
    change evV grammar ('z'::rest) .callByValuePar (tblV grammar ('z'::rest) .callByValuePar (k+1)) []
      (.call 0 [argument]) (rest.length+1)=none
    rw [ProducerArgumentRewrite.call_ok grammar _ _ [] 0 _ actual_prefix rfl argument _ _ (argument_on_z rest k [])]
    exact client_rows_none rest (k+1) _

theorem target_diverges (rest : List Char) (k : Nat) : targetRun (.call 0 [argument]) ('z'::rest) k=none :=
  (CanonicalProducerCorrespondence.undefined_iff ps specs cores checked (.call 0 [argument]) (by trivial)
    (by decide +kernel) (by decide +kernel) ('z'::rest)).mp (source_diverges rest) k

theorem reversed_order_none (k : Nat) :
    sourceRun (.seq (.andP producer) (.call 0 [argument])) ['X'] k=none := by
  have hq : evV grammar ['X'] .callByValuePar (tblV grammar ['X'] .callByValuePar k) [] (.call 2 [.lit []]) 1=none := by
    rw [evV_call_par actual_query_rule rfl (by decide)]
    simpa [evParArgs,evV,Shallot.stripPrefix?,sfx,pre] using query_rows_other 'X' rfl rfl [] k [[]]
  have hd : evV grammar ['X'] .callByValuePar (tblV grammar ['X'] .callByValuePar k) [] producer 1=none := evV_seq_none hq
  have hpeek : evV grammar ['X'] .callByValuePar (tblV grammar ['X'] .callByValuePar k) [] (.andP producer) 1=none := by
    rw [CallLookahead.evV_peek,hd]; rfl
  exact evV_seq_none hpeek

theorem missing_preflight_accepts :
    evV (RecursiveProducedCompiler.target ps specs) "z!zgz".toList .callByValueSeq
      (tblV (RecursiveProducedCompiler.target ps specs) "z!zgz".toList .callByValueSeq 16) []
      (RecursiveProducedCompiler.render ps specs (.call 0 [argument])) 5=some (some 0) := by decide +kernel

theorem shifted_endpoint_rejected : conforms ps specs cores (.call 0 [.seq argument (.chr '!')])=false := by decide +kernel

def tiny : List Entry := [.produced (.chr 'a') (.param 0)]
def tinyRoot : MExp := .call 0 [.any]

theorem tiny_checked : check [] tiny [.any]=true := by decide +kernel

theorem tiny_root_ready : rootCheck [] tiny [.any] tinyRoot=true := by decide +kernel

/-- Distinct consuming parsers, rather than just two ASTs for one parser:
the canonical character may fail where the original wildcard succeeds. -/
theorem wildcard_capture : evV (source [] tiny) ['a','a'] .callByValuePar
    (tblV (source [] tiny) ['a','a'] .callByValuePar 1) [] tinyRoot 2=some (some 0) ∧
    evV (target [] tiny) ['a','a'] .callByValueSeq (tblV (target [] tiny) ['a','a'] .callByValueSeq 1) []
      (entry [] tiny tinyRoot) 2=some (some 0) := by decide +kernel

/-- The local reverse delay is necessary even when neither parser calls a
user: moving the failing prefix into the argument exposes failure earlier. -/
theorem strict_clock_delay :
    evV (source [] tiny) ['b'] .callByValuePar (tblV (source [] tiny) ['b'] .callByValuePar 0) [] tinyRoot 1=none ∧
    evV (source [] tiny) ['b'] .callByValuePar (tblV (source [] tiny) ['b'] .callByValuePar 0) [] (render tiny tinyRoot) 1=some none ∧
    evV (source [] tiny) ['b'] .callByValuePar (tblV (source [] tiny) ['b'] .callByValuePar 1) [] tinyRoot 1=some none := by decide +kernel

theorem wildcard_failure : evV (target [] tiny) ['b','b'] .callByValueSeq
    (tblV (target [] tiny) ['b','b'] .callByValueSeq 1) [] (entry [] tiny tinyRoot) 2=some none ∧
    evV (RecursiveProducedCompiler.target [] tiny) ['b','b'] .callByValueSeq
      (tblV (RecursiveProducedCompiler.target [] tiny) ['b','b'] .callByValueSeq 1) []
      (RecursiveProducedCompiler.render [] tiny tinyRoot) 2=some (some 0) := by decide +kernel

theorem observations (e : MExp) (he : e.FirstOrder) (hc : conforms ps specs cores e=true)
    (ho : RecursiveProducedCompiler.conforms (outputEntries specs) (render specs e)=true)
    (x : List Char) (rest : Option (List Char)) :
    SObs grammar .callByValuePar e x rest ↔ SObs (target ps specs) .callByValueSeq (entry ps specs e) x rest :=
  CanonicalProducerCorrespondence.observations_iff ps specs cores checked e he hc ho x rest

theorem root_language (x : List Char) :
    SObs grammar .callByValuePar root x (some []) ↔ SObs (target ps specs) .callByValueSeq (entry ps specs root) x (some []) :=
  CanonicalProducerCorrespondence.checked_observations ps specs cores checked root root_ready x (some [])

end Shallot.MacroPeg.CBV.CanonicalProducerExamples
