import MacroPeg.CBV.ForwardQueryScan

/-! One fixed first-order Seq grammar evaluates forward Boolean reference
programs directly from their original serialization. References are captured
at runtime; successful queries consume only the reference, and their bodies
search and evaluate later definitions under lookahead. -/
namespace Shallot.MacroPeg.CBV.ForwardBooleanProgram
open ForwardQueryScan RootObservation

inductive Gate where
  | yes | no | neg (child : Nat) | both (left right : Nat)
  deriving DecidableEq, Repr

abbrev Node := Nat × Gate

def gateWord : Gate → List Char
  | .yes => ['1']
  | .no => ['0']
  | .neg i => '!' :: identifier i
  | .both i j => '&' :: identifier i ++ ',' :: identifier j

def encode : List Node → List Char
  | [] => []
  | (i,b)::P => header i ++ gateWord b ++ ';' :: encode P

def gateValue (f : Nat → Bool) : Gate → Bool
  | .yes => true
  | .no => false
  | .neg i => !(f i)
  | .both i j => f i && f j

/-- Lookup uses the first later definition. Its operands are evaluated in the
strict tail after that definition; missing references have value false. -/
def value : List Node → Nat → Bool
  | [], _ => false
  | (j,b)::P, i => if i=j then gateValue (value P) b else value P i

def readId : MExp := .seq (.star (.chr 'a')) (.chr 'b')
def query : MExp := .call 0 [readId]
def gateExpr : MExp := .alt (.chr '1')
  (.alt (.seq (.chr '!') (.notP query)) (.seq (.chr '&') (.seq query (.seq (.chr ',') query))))
def body : MExp := .andP (.seq (seek key) gateExpr)
def grammar : MGrammar := ⟨[⟨1,body⟩]⟩

theorem grammar_firstOrder : grammar.FirstOrder := by
  intro r hr
  simp only [grammar,List.mem_cons,List.not_mem_nil,or_false] at hr
  subst r
  trivial

theorem query_firstOrder : query.FirstOrder := by trivial

theorem gateWord_no_marker (b : Gate) : '[' ∉ gateWord b := by
  cases b <;> simp [gateWord,identifier]

private theorem readId_star (g : MGrammar) (s : Strategy) (rest : List Char) : ∀ n,
    ∃ t, MDerives g s (.star (.chr 'a')) (identifier n ++ rest) (.ok t ('b'::rest))
  | 0 => ⟨_,.starNil _ _ (.chrFail 'a' 'b' rest (by decide))⟩
  | n+1 => by
    obtain ⟨t,ht⟩ := readId_star g s rest n
    exact ⟨_,.starCons _ _ _ _ _ _ (.chrOk 'a' 'a' _ (by decide)) ht⟩

theorem readId_obs (g : MGrammar) (s : Strategy) (n : Nat) (rest : List Char) :
    SObs g s readId (identifier n ++ rest) (some rest) := by
  obtain ⟨t,ht⟩ := readId_star g s rest n
  exact ⟨_,.seqOk _ _ _ _ _ _ _ ht (.chrOk 'b' 'b' rest (by decide)),rfl⟩

theorem body_subst (n : Nat) : MExp.subst [.lit (identifier n)] body =
    .andP (.seq (seek (closedKey n)) gateExpr) := by
  simp [body,seek,closedKey,key,gateExpr,query,readId,SequentialCallLookahead.sequenceArgs,
    MExp.andP,MExp.subst,MExp.substArgs,argAt]

/-- A finite raw search result supplies a total query, while the Seq call
keeps its reference as a runtime value and consumes exactly that reference. -/
theorem query_of_search (n : Nat) (rest : List Char) (b : Bool)
    (h : ∃ r, SObs grammar .callByValueSeq (.seq (seek (closedKey n)) gateExpr) rest r ∧ r.isSome=b) :
    SObs grammar .callByValueSeq query (identifier n ++ rest) (if b then some rest else none) := by
  have ha : DerivesArgsSeq grammar .callByValueSeq (identifier n ++ rest) [readId]
      [.lit (identifier n)] rest := by
    obtain ⟨o,hd,ho⟩ := readId_obs grammar .callByValueSeq n rest
    cases o with
    | fail => cases ho
    | ok t out =>
      cases ho
      exact .cons _ _ _ (identifier n) rest rest t _ hd rfl (.nil rest)
  obtain ⟨r,hr,hb⟩ := h
  cases r with
  | none =>
    simp only [Option.isSome_none] at hb
    subst b
    have ht := peek_failure hr
    obtain ⟨o,hd,ho⟩ := ht
    cases o with
    | ok _ _ => cases ho
    | fail =>
      refine ⟨_,.callSeqFail 0 [readId] ⟨1,body⟩ _ rest _ rfl rfl rfl ha ?_,rfl⟩
      simpa only [body_subst] using hd
  | some out =>
    simp only [Option.isSome_some] at hb
    subst b
    have ht := peek_success hr
    obtain ⟨o,hd,ho⟩ := ht
    cases o with
    | fail => cases ho
    | ok t final =>
      cases ho
      exact ⟨_,.callSeqOk 0 [readId] ⟨1,body⟩ _ rest rest _ t rfl rfl rfl ha
        (by simpa only [body_subst] using hd),rfl⟩

theorem transport_seek {g : MGrammar} {s : Strategy} {test tail : MExp} {x y : List Char}
    {r : Option (List Char)} (h : ∀ result, SObs g s (seek test) x result → SObs g s (seek test) y result)
    (hx : SObs g s (.seq (seek test) tail) x r) : SObs g s (.seq (seek test) tail) y r := by
  rw [seq_iff] at hx ⊢
  rcases hx with ⟨mid,hs,ht⟩ | ⟨rfl,hs⟩
  · exact Or.inl ⟨mid,h _ hs,ht⟩
  · exact Or.inr ⟨rfl,h _ hs⟩

def QuerySpec (P : List Node) : Prop := ∀ n before, '[' ∉ before →
  SObs grammar .callByValueSeq query (identifier n ++ before ++ encode P)
    (if value P n then some (before ++ encode P) else none)

def SearchSpec (P : List Node) : Prop := ∀ n before, '[' ∉ before →
  ∃ r, SObs grammar .callByValueSeq (.seq (seek (closedKey n)) gateExpr) (before ++ encode P) r ∧
    r.isSome = value P n

theorem query_spec_of_search {P : List Node} (h : SearchSpec P) : QuerySpec P := by
  intro n before hc
  simpa only [List.append_assoc] using query_of_search n (before++encode P) (value P n) (h n before hc)

theorem gate_observation (P : List Node) (hq : QuerySpec P) (b : Gate) :
    ∃ r, SObs grammar .callByValueSeq gateExpr (gateWord b ++ ';' :: encode P) r ∧
      r.isSome = gateValue (value P) b := by
  let rest := ';' :: encode P
  cases b with
  | yes =>
    exact ⟨some rest,alt_left ⟨_,.chrOk '1' '1' rest (by decide),rfl⟩,rfl⟩
  | no =>
    exact ⟨none,alt_right ⟨_,.chrFail '1' '0' rest (by decide),rfl⟩
      (alt_right (seq_fail ⟨_,.chrFail '!' '0' rest (by decide),rfl⟩)
        (seq_fail ⟨_,.chrFail '&' '0' rest (by decide),rfl⟩)),rfl⟩
  | neg i =>
    have hi := hq i [';'] (by decide)
    simp only [List.append_assoc,List.cons_append,List.nil_append] at hi
    change SObs _ _ _ (identifier i ++ rest) (if value P i then some rest else none) at hi
    have hhead : SObs grammar .callByValueSeq (.chr '!') ('!' :: identifier i ++ rest)
        (some (identifier i ++ rest)) := ⟨_,.chrOk '!' '!' _ (by decide),rfl⟩
    have hfirst : SObs grammar .callByValueSeq (.chr '1') ('!' :: identifier i ++ rest) none :=
      ⟨_,.chrFail '1' '!' _ (by decide),rfl⟩
    cases hv : value P i with
    | false =>
      rw [hv] at hi
      exact ⟨some (identifier i ++ rest),alt_right hfirst (alt_left (seq_ok hhead (not_fail hi))),
        by simp [gateValue,hv]⟩
    | true =>
      rw [hv] at hi
      exact ⟨none,alt_right hfirst (alt_right (seq_ok hhead (not_ok hi))
        (seq_fail ⟨_,.chrFail '&' '!' _ (by decide),rfl⟩)),by simp [gateValue,hv]⟩
  | both i j =>
    have hi := hq i (',' :: identifier j ++ [';']) (by simp [identifier])
    have hj := hq j [';'] (by decide)
    simp only [List.cons_append,List.append_assoc,List.nil_append] at hi hj
    change SObs _ _ _ (identifier i ++ (',' :: (identifier j ++ rest)))
      (if value P i then some (',' :: (identifier j ++ rest)) else none) at hi
    change SObs _ _ _ (identifier j ++ rest) (if value P j then some rest else none) at hj
    have hhead : SObs grammar .callByValueSeq (.chr '&') ('&' :: (identifier i ++ (',' :: (identifier j ++ rest))))
        (some (identifier i ++ (',' :: (identifier j ++ rest)))) := ⟨_,.chrOk '&' '&' _ (by decide),rfl⟩
    have hchoose : ∀ r, SObs grammar .callByValueSeq
        (.seq (.chr '&') (.seq query (.seq (.chr ',') query)))
        ('&' :: (identifier i ++ (',' :: (identifier j ++ rest)))) r →
        SObs grammar .callByValueSeq gateExpr (gateWord (.both i j) ++ rest) r := by
      intro r hr
      simpa only [gateExpr,gateWord,List.cons_append,List.append_assoc] using
        alt_right ⟨_,.chrFail '1' '&' _ (by decide),rfl⟩
          (alt_right (seq_fail ⟨_,.chrFail '!' '&' _ (by decide),rfl⟩) hr)
    cases hv : value P i with
    | false =>
      rw [hv] at hi
      exact ⟨none,hchoose none (seq_ok hhead (seq_fail hi)),by simp [gateValue,hv]⟩
    | true =>
      rw [hv] at hi
      refine ⟨if value P j then some rest else none,?_,?_⟩
      · exact hchoose _ (seq_ok hhead (seq_ok hi (seq_ok
          ⟨_,.chrOk ',' ',' _ (by decide),rfl⟩ hj)))
      · cases hjv : value P j <;> simp [gateValue,hv,hjv]

/-- Every finite serialized program has a finite search-and-evaluation result.
The induction is over the strict declaration tail used by references. -/
theorem search_spec : ∀ P : List Node, SearchSpec P
  | [] => by
    intro n before hc
    exact ⟨none,seq_fail (seek_before hc (seek_empty grammar .callByValueSeq n)),rfl⟩
  | (label,b)::P => by
    intro n before hc
    have htail := search_spec P
    have hq := query_spec_of_search htail
    by_cases hn : n=label
    · subst label
      obtain ⟨r,hr,hb⟩ := gate_observation P hq b
      have hbase := seq_ok (seek_header_here grammar .callByValueSeq n (gateWord b ++ ';'::encode P)) hr
      refine ⟨r,?_,?_⟩
      · simpa only [encode,List.append_assoc] using transport_seek (fun result h => seek_before hc h) hbase
      · simpa only [value,ite_true] using hb
    · obtain ⟨r,hr,hb⟩ := htail n [] (by simp)
      have hbase : SObs grammar .callByValueSeq (.seq (seek (closedKey n)) gateExpr)
          (encode ((label,b)::P)) r := by
        simpa only [encode,List.append_assoc,List.cons_append,List.nil_append] using
          transport_seek (fun result h => seek_header_skip hn (payload := gateWord b ++ [';'])
            (by simp [gateWord_no_marker]) h) hr
      refine ⟨r,transport_seek (fun result h => seek_before hc h) hbase,?_⟩
      simpa only [value,if_neg hn] using hb

/-- One fixed first-order Seq grammar evaluates every finite forward Boolean
reference program, with unbounded captured identifiers and arbitrary sharing. -/
theorem query_observation (P : List Node) : QuerySpec P := query_spec_of_search (search_spec P)

/-- The same program can also be evaluated once from right to left, retaining
shared gate results. This connects the recursive query semantics to a finite
Boolean table, rather than an input-dependent grammar expansion. -/
def tableLookup : List (Nat × Bool) → Nat → Bool
  | [], _ => false
  | (j,b)::T, i => if i=j then b else tableLookup T i

def evaluateTable : List Node → List (Nat × Bool)
  | [] => []
  | (i,b)::P => let T := evaluateTable P; (i,gateValue (tableLookup T) b)::T

theorem table_correct (P : List Node) : tableLookup (evaluateTable P) = value P := by
  induction P with
  | nil => rfl
  | cons node P ih =>
    obtain ⟨i,b⟩ := node
    funext n
    simp only [evaluateTable,tableLookup,value,ih]

def start : MExp := .seq query (.star .any)

theorem start_firstOrder : start.FirstOrder := by trivial

private theorem all_chars (x : List Char) :
    ∃ t, MDerives grammar .callByValueSeq (.star .any) x (.ok t []) := by
  induction x with
  | nil => exact ⟨_,.starNil _ _ .anyFail⟩
  | cons c x ih =>
    obtain ⟨t,ht⟩ := ih
    exact ⟨_,.starCons _ _ _ _ _ _ (.anyOk c x) ht⟩

/-- Whole-input evaluation on every serialized finite program. This does not
characterize the parser's behavior on malformed, nonserialized inputs. -/
theorem program_observation (P : List Node) (n : Nat) :
    SObs grammar .callByValueSeq start (identifier n ++ encode P)
      (if value P n then some [] else none) := by
  have hq := query_observation P n [] (by simp)
  simp only [List.append_nil,List.nil_append] at hq
  cases hv : value P n with
  | false => rw [hv] at hq; exact seq_fail hq
  | true =>
    rw [hv] at hq
    obtain ⟨t,ht⟩ := all_chars (encode P)
    exact seq_ok hq ⟨_,ht,rfl⟩

theorem program_recognizes (P : List Node) (n : Nat) :
    SObs grammar .callByValueSeq start (identifier n ++ encode P) (some []) ↔ value P n = true := by
  cases hv : value P n with
  | false =>
    constructor
    · intro h
      have he := sObs_unique h (program_observation P n)
      simp [hv] at he
    · simp
  | true =>
    constructor
    · intro _; rfl
    · intro _; simpa only [hv,ite_true] using program_observation P n

theorem table_recognizes (P : List Node) (n : Nat) :
    SObs grammar .callByValueSeq start (identifier n ++ encode P) (some []) ↔
      tableLookup (evaluateTable P) n = true := by
  rw [table_correct,program_recognizes]

def baseGrammar : MGrammar := ⟨[⟨1,.seq (seek key) gateExpr⟩]⟩
def normalizedGrammar : MGrammar := SequentialCallLookahead.wrapped baseGrammar
def normalizedStart : MExp := SequentialCallLookahead.render start

theorem baseGrammar_firstOrder : baseGrammar.FirstOrder := by
  intro r hr
  simp only [baseGrammar,List.mem_cons,List.not_mem_nil,or_false] at hr
  subst r
  trivial

theorem normalized_firstOrder : normalizedGrammar.FirstOrder ∧ normalizedStart.FirstOrder :=
  ⟨SequentialCallLookahead.wrapped_firstOrder _,SequentialCallLookahead.render_firstOrder _⟩

/-- The body-test/call-probe transformation applies to this actual recursive
runtime lookup machine, preserving its observations on all character inputs. -/
theorem normalized_observations (x : List Char) (r : Option (List Char)) :
    SObs grammar .callByValueSeq start x r ↔ SObs normalizedGrammar .callByValueSeq normalizedStart x r :=
  SequentialCallLookahead.observations_iff baseGrammar_firstOrder start start_firstOrder x r

theorem normalized_program_recognizes (P : List Node) (n : Nat) :
    SObs normalizedGrammar .callByValueSeq normalizedStart (identifier n ++ encode P) (some []) ↔
      tableLookup (evaluateTable P) n = true := by
  rw [← normalized_observations,table_recognizes]

/-- The identifier used by an actually accepted query can exceed every fixed
length bound; it is not chosen from a finite capture palette. -/
theorem accepted_identifier_unbounded (bound : Nat) :
    ∃ (P : List Node) (n : Nat), (identifier n).length > bound ∧
      SObs grammar .callByValueSeq start (identifier n ++ encode P) (some []) := by
  refine ⟨[(bound,.yes)],bound,?_,?_⟩
  · simp [identifier]
  · apply (program_recognizes _ _).mpr
    simp [value,gateValue]

end Shallot.MacroPeg.CBV.ForwardBooleanProgram
