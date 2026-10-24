import MacroPeg.CBV.ForwardBooleanProgram

/-! Syntax validation for the forward Boolean evaluator. Successful validation
recovers a whole serialized program, including from otherwise arbitrary input. -/
namespace Shallot.MacroPeg.CBV.ForwardBooleanSyntax
open ForwardQueryScan ForwardBooleanProgram RootObservation

def gateSyntax : MExp := .alt (.chr '1') (.alt (.chr '0')
  (.alt (.seq (.chr '!') readId) (.seq (.chr '&') (.seq readId (.seq (.chr ',') readId)))))
def recordSyntax : MExp := .seq (.chr '[') (.seq readId (.seq (.chr ']') (.seq gateSyntax (.chr ';'))))
def validator : MExp := .seq readId (.seq (.star recordSyntax) (.notP .any))

theorem syntax_firstOrder : validator.FirstOrder := by trivial

private theorem seq_some {g : MGrammar} {s : Strategy} {a b : MExp} {x rest : List Char}
    (h : SObs g s (.seq a b) x (some rest)) :
    ∃ mid, SObs g s a x (some mid) ∧ SObs g s b mid (some rest) := by
  rcases seq_iff.mp h with h | ⟨he,_⟩
  · exact h
  · cases he

private theorem alt_some {g : MGrammar} {s : Strategy} {a b : MExp} {x rest : List Char}
    (h : SObs g s (.alt a b) x (some rest)) : SObs g s a x (some rest) ∨ SObs g s b x (some rest) := by
  rcases alt_iff.mp h with ⟨y,hy,ha⟩ | ⟨_,hb⟩
  · cases hy; exact Or.inl ha
  · exact Or.inr hb

private theorem char_some {g : MGrammar} {s : Strategy} {c : Char} {x rest : List Char}
    (h : SObs g s (.chr c) x (some rest)) : x = c :: rest := by
  obtain ⟨o,hd,ho⟩ := h
  cases hd with
  | chrOk _ d tail he =>
    have hc : c=d := by simpa [Shallot.beqChar,Char.toNat_inj] using he
    cases ho; subst d; rfl
  | chrFail _ _ _ _ => cases ho
  | chrEmpty _ => cases ho

private theorem char_obs (g : MGrammar) (s : Strategy) (c : Char) (rest : List Char) :
    SObs g s (.chr c) (c::rest) (some rest) :=
  ⟨_,.chrOk c c rest (by simp [Shallot.beqChar]),rfl⟩

private theorem a_star_sound {g : MGrammar} {s : Strategy} {x rest : List Char} {t : MTree}
    (h : MDerives g s (.star (.chr 'a')) x (.ok t rest)) :
    ∃ n, x = List.replicate n 'a' ++ rest := by
  induction t generalizing x rest with
  | starNil => cases h; exact ⟨0,rfl⟩
  | starCons hd ht _ ih =>
    cases h with
    | starCons _ _ mid _ _ _ ha hb =>
      cases ha with
      | chrOk _ d tail he =>
        have hc : 'a'=d := Char.toNat_inj.mp (by simpa [Shallot.beqChar] using he)
        subst d
        obtain ⟨n,hn⟩ := ih hb
        exact ⟨n+1,by rw [hn,List.replicate_succ]; rfl⟩
  | _ => cases h

theorem readId_sound {g : MGrammar} {s : Strategy} {x rest : List Char}
    (h : SObs g s readId x (some rest)) : ∃ n, x = identifier n ++ rest := by
  obtain ⟨mid,ha,hb⟩ := seq_some h
  have hm := char_some hb
  obtain ⟨o,hd,ho⟩ := ha
  cases o with
  | fail => cases ho
  | ok t out =>
    cases ho
    obtain ⟨n,hn⟩ := a_star_sound hd
    exact ⟨n,by simpa only [identifier,List.append_assoc,List.singleton_append] using hn.trans (congrArg (List.replicate n 'a' ++ ·) hm)⟩

theorem gateSyntax_sound {g : MGrammar} {s : Strategy} {x rest : List Char}
    (h : SObs g s gateSyntax x (some rest)) : ∃ b : Gate, x = gateWord b ++ rest := by
  rcases alt_some h with h1 | h
  · exact ⟨.yes,char_some h1⟩
  rcases alt_some h with h0 | h
  · exact ⟨.no,char_some h0⟩
  rcases alt_some h with hn | ha
  · obtain ⟨mid,hbang,hi⟩ := seq_some hn
    obtain ⟨n,he⟩ := readId_sound hi
    exact ⟨.neg n,by simpa only [gateWord,List.cons_append] using (char_some hbang).trans (congrArg ('!' :: ·) he)⟩
  · obtain ⟨x1,hamp,hrest⟩ := seq_some ha
    obtain ⟨x2,hi,hrest⟩ := seq_some hrest
    obtain ⟨x3,hcomma,hj⟩ := seq_some hrest
    obtain ⟨i,hei⟩ := readId_sound hi
    obtain ⟨j,hej⟩ := readId_sound hj
    refine ⟨.both i j,?_⟩
    rw [char_some hamp,hei,char_some hcomma,hej]
    simp only [gateWord,List.cons_append,List.append_assoc]

theorem recordSyntax_sound {g : MGrammar} {s : Strategy} {x rest : List Char}
    (h : SObs g s recordSyntax x (some rest)) :
    ∃ (n : Nat) (b : Gate), x = header n ++ gateWord b ++ ';' :: rest := by
  obtain ⟨x1,hopen,h⟩ := seq_some h
  obtain ⟨x2,hid,h⟩ := seq_some h
  obtain ⟨x3,hclose,h⟩ := seq_some h
  obtain ⟨x4,hgate,hsemi⟩ := seq_some h
  obtain ⟨n,hn⟩ := readId_sound hid
  obtain ⟨b,hb⟩ := gateSyntax_sound hgate
  refine ⟨n,b,?_⟩
  rw [char_some hopen,hn,char_some hclose,hb,char_some hsemi]
  simp only [header,List.cons_append,List.append_assoc,List.nil_append]

private theorem records_sound {g : MGrammar} {s : Strategy} {x rest : List Char} {t : MTree}
    (h : MDerives g s (.star recordSyntax) x (.ok t rest)) : ∃ P, x = encode P ++ rest := by
  induction t generalizing x rest with
  | starNil => cases h; exact ⟨[],rfl⟩
  | starCons hd ht _ ih =>
    cases h with
    | starCons _ _ mid _ _ _ ha hb =>
      obtain ⟨n,b,hn⟩ := recordSyntax_sound ⟨_,ha,rfl⟩
      obtain ⟨P,hP⟩ := ih hb
      exact ⟨(n,b)::P,by simp only [encode,List.append_assoc,List.cons_append] at *; rw [hn,hP]⟩
  | _ => cases h

private theorem end_sound {g : MGrammar} {s : Strategy} {x rest : List Char}
    (h : SObs g s (.notP .any) x (some rest)) : x=[] ∧ rest=[] := by
  obtain ⟨o,hd,ho⟩ := h
  cases hd with
  | notOk _ _ _ _ _ => cases ho
  | notFail _ _ ha =>
    cases ha
    cases ho
    exact ⟨rfl,rfl⟩

/-- Positive validation recovers the full serialization, with no promise on
the input's characters or its initial syntactic shape. -/
theorem syntax_sound {g : MGrammar} {s : Strategy} {x rest : List Char}
    (h : SObs g s validator x (some rest)) :
    ∃ (n : Nat) (P : List Node), x = identifier n ++ encode P ∧ rest=[] := by
  obtain ⟨mid,hid,h⟩ := seq_some h
  obtain ⟨last,hs,hend⟩ := seq_some h
  obtain ⟨n,hn⟩ := readId_sound hid
  obtain ⟨he,hr⟩ := end_sound hend
  obtain ⟨o,hd,ho⟩ := hs
  cases o with
  | fail => cases ho
  | ok t out =>
    cases ho
    obtain ⟨P,hP⟩ := records_sound hd
    exact ⟨n,P,by simpa [he] using hn.trans (congrArg (identifier n ++ ·) hP),hr⟩

theorem gateSyntax_complete (g : MGrammar) (s : Strategy) (b : Gate) (rest : List Char) :
    SObs g s gateSyntax (gateWord b ++ rest) (some rest) := by
  cases b with
  | yes => exact alt_left (char_obs g s '1' rest)
  | no => exact alt_right ⟨_,.chrFail '1' '0' _ (by decide),rfl⟩ (alt_left (char_obs g s '0' rest))
  | neg i =>
    exact alt_right ⟨_,.chrFail '1' '!' _ (by decide),rfl⟩
      (alt_right ⟨_,.chrFail '0' '!' _ (by decide),rfl⟩
        (alt_left (seq_ok (char_obs g s '!' _) (readId_obs g s i rest))))
  | both i j =>
    have hj := readId_obs g s j rest
    have hi := readId_obs g s i (',' :: (identifier j ++ rest))
    have hc := seq_ok hi (seq_ok (char_obs g s ',' _) hj)
    have hg := seq_ok (char_obs g s '&' _) hc
    simpa only [gateSyntax,gateWord,List.cons_append,List.append_assoc] using
      alt_right ⟨_,.chrFail '1' '&' _ (by decide),rfl⟩
        (alt_right ⟨_,.chrFail '0' '&' _ (by decide),rfl⟩
          (alt_right (seq_fail ⟨_,.chrFail '!' '&' _ (by decide),rfl⟩) hg))

theorem recordSyntax_complete (g : MGrammar) (s : Strategy) (n : Nat) (b : Gate) (rest : List Char) :
    SObs g s recordSyntax (header n ++ gateWord b ++ ';' :: rest) (some rest) := by
  have hg := gateSyntax_complete g s b (';'::rest)
  have he := seq_ok hg (char_obs g s ';' rest)
  have hc := seq_ok (char_obs g s ']' _) he
  have hi := seq_ok (readId_obs g s n _) hc
  simpa only [recordSyntax,header,List.cons_append,List.append_assoc,List.nil_append] using
    seq_ok (char_obs g s '[' _) hi

private theorem records_complete (g : MGrammar) (s : Strategy) (P : List Node) :
    ∃ t, MDerives g s (.star recordSyntax) (encode P) (.ok t []) := by
  induction P with
  | nil => exact ⟨_,.starNil _ _ (.seqFail₁ _ _ _ (.chrEmpty '['))⟩
  | cons node P ih =>
    obtain ⟨n,b⟩ := node
    obtain ⟨t,ht⟩ := ih
    obtain ⟨o,hd,ho⟩ := recordSyntax_complete g s n b (encode P)
    cases o with
    | fail => cases ho
    | ok tr out =>
      cases ho
      exact ⟨_,.starCons _ _ _ _ _ _ hd ht⟩

theorem syntax_complete (g : MGrammar) (s : Strategy) (n : Nat) (P : List Node) :
    SObs g s validator (identifier n ++ encode P) (some []) := by
  obtain ⟨t,ht⟩ := records_complete g s P
  exact seq_ok (readId_obs g s n _) (seq_ok ⟨_,ht,rfl⟩ ⟨_,.notFail _ _ .anyFail,rfl⟩)

/-- Exact syntax recognition on all original character strings. -/
theorem syntax_iff (g : MGrammar) (s : Strategy) (x : List Char) :
    SObs g s validator x (some []) ↔ ∃ (n : Nat) (P : List Node), x = identifier n ++ encode P := by
  constructor
  · intro h
    obtain ⟨n,P,hx,_⟩ := syntax_sound h
    exact ⟨n,P,hx⟩
  · rintro ⟨n,P,rfl⟩
    exact syntax_complete g s n P

private def Total (g : MGrammar) (s : Strategy) (e : MExp) : Prop := ∀ x, ∃ r, SObs g s e x r

private theorem total_char (g : MGrammar) (s : Strategy) (c : Char) : Total g s (.chr c) := by
  intro x
  cases x with
  | nil => exact ⟨none,_,.chrEmpty c,rfl⟩
  | cons d rest =>
    cases he : Shallot.beqChar c d with
    | false => exact ⟨none,_,.chrFail c d rest he,rfl⟩
    | true => exact ⟨some rest,_,.chrOk c d rest he,rfl⟩

private theorem total_seq {g : MGrammar} {s : Strategy} {a b : MExp}
    (ha : Total g s a) (hb : Total g s b) : Total g s (.seq a b) := by
  intro x
  obtain ⟨r,hr⟩ := ha x
  cases r with
  | none => exact ⟨none,seq_fail hr⟩
  | some mid =>
    obtain ⟨r,ht⟩ := hb mid
    exact ⟨r,seq_ok hr ht⟩

private theorem total_alt {g : MGrammar} {s : Strategy} {a b : MExp}
    (ha : Total g s a) (hb : Total g s b) : Total g s (.alt a b) := by
  intro x
  obtain ⟨r,hr⟩ := ha x
  cases r with
  | none =>
    obtain ⟨r,ht⟩ := hb x
    exact ⟨r,alt_right hr ht⟩
  | some mid => exact ⟨some mid,alt_left hr⟩

private theorem star_defined {g : MGrammar} {s : Strategy} {e : MExp} (ht : Total g s e)
    (hp : ∀ x rest, SObs g s e x (some rest) → rest.length < x.length) :
    ∀ x, ∃ t rest, MDerives g s (.star e) x (.ok t rest)
  | x => by
    obtain ⟨r,hr⟩ := ht x
    cases r with
    | none =>
      obtain ⟨o,hd,ho⟩ := hr
      cases o with
      | fail => exact ⟨_,x,.starNil e x hd⟩
      | ok _ _ => cases ho
    | some mid =>
      have hlen := hp x mid hr
      obtain ⟨t,rest,hstar⟩ := star_defined ht hp mid
      obtain ⟨o,hd,ho⟩ := hr
      cases o with
      | fail => cases ho
      | ok child out =>
        cases ho
        exact ⟨_,rest,.starCons _ _ _ _ _ _ hd hstar⟩
termination_by x => x.length

/-- Validation is a total parser on every input, so malformed strings fail
finitely rather than being left outside the termination proof. -/
theorem syntax_total (g : MGrammar) (s : Strategy) : ∀ x, ∃ r, SObs g s validator x r := by
  have hread : Total g s readId := by
    apply total_seq _ (total_char g s 'b')
    intro x
    obtain ⟨t,rest,ht⟩ := star_defined (total_char g s 'a')
      (fun x rest h => by rw [char_some h]; simp) x
    exact ⟨some rest,_,ht,rfl⟩
  have hgate : Total g s gateSyntax :=
    total_alt (total_char g s '1') (total_alt (total_char g s '0')
      (total_alt (total_seq (total_char g s '!') hread)
        (total_seq (total_char g s '&') (total_seq hread (total_seq (total_char g s ',') hread)))))
  have hrecord : Total g s recordSyntax := total_seq (total_char g s '[')
    (total_seq hread (total_seq (total_char g s ']') (total_seq hgate (total_char g s ';'))))
  have hrecords : Total g s (.star recordSyntax) := by
    intro x
    obtain ⟨t,rest,ht⟩ := star_defined hrecord (fun x rest h => by
      obtain ⟨n,b,he⟩ := recordSyntax_sound h
      rw [he]
      simp only [header,List.length_cons,List.length_append]
      omega) x
    exact ⟨some rest,_,ht,rfl⟩
  have hend : Total g s (.notP .any) := by
    intro x
    cases x with
    | nil => exact ⟨some [],_,.notFail _ _ .anyFail,rfl⟩
    | cons c rest => exact ⟨none,_,.notOk _ _ _ _ (.anyOk c rest),rfl⟩
  exact total_seq hread (total_seq hrecords hend)

private theorem peek_sound {g : MGrammar} {s : Strategy} {e : MExp} {x rest : List Char}
    (h : SObs g s (.andP e) x (some rest)) : rest=x ∧ ∃ out, SObs g s e x (some out) := by
  obtain ⟨o,hd,ho⟩ := h
  cases hd with
  | notOk _ _ _ _ _ => cases ho
  | notFail _ _ hneg =>
    cases hneg with
    | notOk _ _ out t he =>
      cases ho
      exact ⟨rfl,out,_,he,rfl⟩

def entry : MExp := .seq (.andP validator) start

theorem entry_firstOrder : entry.FirstOrder := ⟨syntax_firstOrder,start_firstOrder⟩

def ProgramLanguage (x : List Char) : Prop :=
  ∃ (n : Nat) (P : List Node), x = identifier n ++ encode P ∧ tableLookup (evaluateTable P) n = true

/-- The syntax guard closes the promise gap: on every character string,
acceptance is exactly serialization of a true finite forward program. -/
theorem language_iff (x : List Char) :
    SObs grammar .callByValueSeq entry x (some []) ↔ ProgramLanguage x := by
  constructor
  · intro h
    obtain ⟨mid,hguard,hstart⟩ := seq_some h
    obtain ⟨hmid,out,hparse⟩ := peek_sound hguard
    subst mid
    obtain ⟨n,P,hx,_⟩ := syntax_sound hparse
    refine ⟨n,P,hx,?_⟩
    rw [hx] at hstart
    exact (table_recognizes P n).mp hstart
  · rintro ⟨n,P,rfl,hvalue⟩
    exact seq_ok (peek_success (syntax_complete grammar .callByValueSeq n P))
      ((table_recognizes P n).mpr hvalue)

theorem entry_program_recognizes (P : List Node) (n : Nat) :
    SObs grammar .callByValueSeq entry (identifier n ++ encode P) (some []) ↔
      tableLookup (evaluateTable P) n = true := by
  rw [entry,seq_zero_iff (peek_success (syntax_complete grammar .callByValueSeq n P)),table_recognizes]

theorem nonserialization_not_accepted {x : List Char}
    (h : ¬ ∃ (n : Nat) (P : List Node), x = identifier n ++ encode P) :
    ¬ SObs grammar .callByValueSeq entry x (some []) := by
  intro hx
  obtain ⟨n,P,he,_⟩ := (language_iff x).mp hx
  exact h ⟨n,P,he⟩

theorem nonserialization_failure {x : List Char}
    (h : ¬ ∃ (n : Nat) (P : List Node), x = identifier n ++ encode P) :
    SObs grammar .callByValueSeq entry x none := by
  obtain ⟨r,hr⟩ := syntax_total grammar .callByValueSeq x
  cases r with
  | none => exact seq_fail (peek_failure hr)
  | some rest =>
    obtain ⟨n,P,he,_⟩ := syntax_sound hr
    exact False.elim (h ⟨n,P,he⟩)

theorem entry_total (x : List Char) : ∃ r, SObs grammar .callByValueSeq entry x r := by
  obtain ⟨r,hr⟩ := syntax_total grammar .callByValueSeq x
  cases r with
  | none => exact ⟨none,seq_fail (peek_failure hr)⟩
  | some rest =>
    obtain ⟨n,P,he,_⟩ := syntax_sound hr
    subst x
    exact ⟨_,seq_ok (peek_success hr) (program_observation P n)⟩

theorem entry_success_empty {x rest : List Char}
    (h : SObs grammar .callByValueSeq entry x (some rest)) : rest=[] := by
  obtain ⟨mid,hguard,hstart⟩ := seq_some h
  obtain ⟨hmid,out,hparse⟩ := peek_sound hguard
  subst mid
  obtain ⟨n,P,hx,_⟩ := syntax_sound hparse
  rw [hx] at hstart
  have he := sObs_unique hstart (program_observation P n)
  cases hv : value P n <;> simp [hv] at he
  exact he

/-- Every input has a finite Boolean decision, with no undefined result or
partially consumed success hidden outside the valid serialization domain. -/
theorem entry_decides (x : List Char) :
    ∃ b : Bool, SObs grammar .callByValueSeq entry x (if b then some [] else none) ∧
      (ProgramLanguage x ↔ b=true) := by
  obtain ⟨r,hr⟩ := entry_total x
  cases r with
  | none =>
    refine ⟨false,hr,?_⟩
    constructor
    · intro h
      have he := sObs_unique ((language_iff x).mpr h) hr
      cases he
    · intro h; cases h
  | some rest =>
    have he := entry_success_empty hr
    subst rest
    refine ⟨true,hr,?_⟩
    constructor
    · intro _; rfl
    · intro _; exact (language_iff x).mp hr

def normalizedEntry : MExp := SequentialCallLookahead.render entry

theorem normalizedEntry_firstOrder : normalizedEntry.FirstOrder := SequentialCallLookahead.render_firstOrder _

/-- The normalized call-probe machine has the same exact language on all
inputs, after adding syntax validation to the previous promised-input result. -/
theorem normalized_language_iff (x : List Char) :
    SObs normalizedGrammar .callByValueSeq normalizedEntry x (some []) ↔ ProgramLanguage x := by
  change SObs (SequentialCallLookahead.wrapped baseGrammar) .callByValueSeq
    (SequentialCallLookahead.render entry) x (some []) ↔ _
  rw [← SequentialCallLookahead.observations_iff baseGrammar_firstOrder entry entry_firstOrder]
  exact language_iff x

theorem normalized_entry_decides (x : List Char) :
    ∃ b : Bool, SObs normalizedGrammar .callByValueSeq normalizedEntry x (if b then some [] else none) ∧
      (ProgramLanguage x ↔ b=true) := by
  obtain ⟨b,hb,hLang⟩ := entry_decides x
  exact ⟨b,(SequentialCallLookahead.observations_iff baseGrammar_firstOrder entry entry_firstOrder x _).mp hb,hLang⟩

end Shallot.MacroPeg.CBV.ForwardBooleanSyntax
