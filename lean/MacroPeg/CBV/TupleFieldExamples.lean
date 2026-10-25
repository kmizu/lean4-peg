import MacroPeg.CBV.TupleFieldCompiler

namespace Shallot.MacroPeg.CBV.TupleFieldExamples
open TupleFieldCompiler DelimiterTemplate DelimitedWordPattern
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def short (n : Nat) : List Char := RepeatedWordArguments.copies ['a'] n
def long (n : Nat) : List Char := short n++['b']
def args : List MExp := [.star (.lit ['a']),.seq (.star (.lit ['a'])) (.chr 'b')]
def pattern : List Nat := [1,0,1]
def body : MExp := .seq (.param 0) (.seq (.chr '!') (.seq (.param 1) (.notP .any)))
def suffix (n : Nat) : List Char := short n++'!'::long n
def input (n : Nat) : List Char := encode '#' [short n,long n] pattern++suffix n
def src : MGrammar := source [] 2 '#' pattern body
def dst : MGrammar := target [] 2 '#' pattern body
def root : MExp := .call 0 args
def emitted : MExp := TupleFieldTransfer.head 0 2 '#' pattern args

theorem checked : check [] args ['a','b'] '#' pattern body=true := by decide

theorem all_physical_clocks (x : List Char) (k : Nat) :
    evV src x .callByValuePar (tblV src x .callByValuePar k) [] root x.length=
      evV dst x .callByValueSeq (tblV dst x .callByValueSeq k) [] emitted x.length :=
  TupleFieldCompiler.physical [] args ['a','b'] '#' pattern body checked x k _ (Nat.le_refl _)

theorem actual_captures (n : Nat) :
    evParArgs src (input n) .callByValuePar (tblV src (input n) .callByValuePar 1) [] args (input n).length=
      some (some [short n,long n]) := by
  let tail := '#'::(short n++'#'::(long n++'#'::suffix n))
  have hx : input n=short n++'b'::tail := by
    simp [input,pattern,encode,long,tail,List.append_assoc]
  have hscan : evV src (input n) .callByValuePar (tblV src (input n) .callByValuePar 1) []
      (.star (.lit ['a'])) (input n).length=some (some ('b'::tail).length) := by
    apply RecapturedCopyBlock.literal_copies _ _ _ _ _ ['a'] (by decide) ('b'::tail)
      (by simp [Shallot.stripPrefix?,Shallot.beqChar]) n _ (Nat.le_refl _)
    simpa only [short,sfx_self] using hx
  have hsfx : sfx (input n) ('b'::tail).length='b'::tail :=
    sfx_suffix hx
  have hb : evV src (input n) .callByValuePar (tblV src (input n) .callByValuePar 1) []
      (.chr 'b') ('b'::tail).length=some (some tail.length) := by
    simp only [evV,hsfx]; rfl
  have hl : input n=long n++tail := by simpa [long,List.append_assoc] using hx
  have hp0 : pre (input n) (input n).length ('b'::tail).length=short n := pre_eq ⟨[],by simp⟩ hx
  have hp1 : pre (input n) (input n).length tail.length=long n := pre_eq ⟨[],by simp⟩ hl
  rw [args,evPar_cons_ok hscan,evPar_cons_ok (evV_seq_ok hscan |>.trans hb),evPar_nil]
  simp only [hp0,hp1]

theorem source_accepts (n : Nat) :
    evV src (input n) .callByValuePar (tblV src (input n) .callByValuePar 1) [] root (input n).length=some (some 0) := by
  have hrow : ruleAtM src.rules 0=some ⟨2,TupleFieldTransfer.sourceBody '#' pattern body⟩ := rfl
  rw [root,evV_call_par hrow rfl (by decide),actual_captures]
  change valAt (tblV src (input n) .callByValuePar (0+1) 0 [short n,long n]) (input n).length=_
  rw [valAt_tblV_succ hrow [short n,long n] (Nat.le_refl _)]
  have hfirst : evV src (input n) .callByValuePar (tblV src (input n) .callByValuePar 0)
      [short n,long n] (compile '#' (sourceParts '#' pattern)) (input n).length=some (some (suffix n).length) := by
    rw [compile_eval _ _ _ _ _ _ _ _ (Nat.le_refl _),RecapturedCopyBlock.source_run]
    · simp only [sfx_self,(CBVtoCBN.stripPrefix_exact _ _ _).mpr (show input n=encode '#' [short n,long n] pattern++suffix n from rfl),Option.map_some]
    · intro i hi; simp only [List.length_cons,List.length_nil]; simp [pattern] at hi; omega
  have hrest : sfx (input n) (suffix n).length=suffix n :=
    sfx_suffix (show input n=encode '#' [short n,long n] pattern++suffix n from rfl)
  have hshort : evV src (input n) .callByValuePar (tblV src (input n) .callByValuePar 0)
      [short n,long n] (.param 0) (suffix n).length=some (some ('!'::long n).length) := by
    simp only [evV,List.getElem?_cons_zero,hrest]
    rw [(CBVtoCBN.stripPrefix_exact _ _ _).mpr (show suffix n=short n++'!'::long n from rfl)]
  have hbangsfx : sfx (input n) ('!'::long n).length='!'::long n :=
    sfx_suffix (suffix_trans (sfx_is_suffix (input n) (suffix n).length) ⟨short n,hrest⟩).choose_spec
  have hbang : evV src (input n) .callByValuePar (tblV src (input n) .callByValuePar 0)
      [short n,long n] (.chr '!') ('!'::long n).length=some (some (long n).length) := by
    simp only [evV,hbangsfx]; rfl
  have hlongsfx : sfx (input n) (long n).length=long n :=
    sfx_suffix (suffix_trans (sfx_is_suffix (input n) ('!'::long n).length) ⟨['!'],hbangsfx⟩).choose_spec
  have hlong : evV src (input n) .callByValuePar (tblV src (input n) .callByValuePar 0)
      [short n,long n] (.param 1) (long n).length=some (some 0) := by
    simp only [evV,List.getElem?_cons_succ,List.getElem?_cons_zero,hlongsfx]
    rw [(CBVtoCBN.stripPrefix_exact _ _ _).mpr (List.append_nil _).symm]
    rfl
  rw [TupleFieldTransfer.sourceBody,evV_seq_ok hfirst,body,evV_seq_ok hshort,evV_seq_ok hbang,evV_seq_ok hlong]
  simp [evV,sfx]

theorem source_and_target_accept (n : Nat) :
    evV src (input n) .callByValuePar (tblV src (input n) .callByValuePar 1) [] root (input n).length=some (some 0) ∧
    evV dst (input n) .callByValueSeq (tblV dst (input n) .callByValueSeq 1) [] emitted (input n).length=some (some 0) :=
  ⟨source_accepts n,(all_physical_clocks _ 1).symm.trans (source_accepts n)⟩

theorem short_free (n : Nat) : DelimitedCopyProjection.Free '#' (short n) := by
  induction n with
  | zero => simp [short,RepeatedWordArguments.copies,DelimitedCopyProjection.Free]
  | succ n ih => simpa [short,RepeatedWordArguments.copies,DelimitedCopyProjection.Free] using ih

theorem captured_fields (n : Nat) :
    evSeqArgs dst (input n) .callByValueSeq (tblV dst (input n) .callByValueSeq 1) []
      (CopyFieldCapture.scanArgs '#' pattern) (input n).length=
      some (some ([long n,['#'],short n,['#'],long n,['#']],(suffix n).length)) := by
  have hf : ∀ i, (hi : i<[short n,long n].length) → DelimitedCopyProjection.Free '#' ([short n,long n][i]) := by
    intro i hi
    cases i with
    | zero => exact short_free n
    | succ i =>
      have he : i=0 := by simp only [List.length_cons,List.length_nil] at hi; omega
      subst i
      simpa [long,DelimitedCopyProjection.Free] using short_free n
  have hs : ∀ i∈pattern, i<[short n,long n].length := by
    intro i hi; simp only [List.length_cons,List.length_nil]; simp [pattern] at hi; omega
  simpa [CopyFieldCapture.fields,pattern] using
    CopyFieldCapture.scan_encoded dst (input n) .callByValueSeq _ [] [short n,long n] '#' hf pattern hs
      (suffix n) (input n).length (Nat.le_refl _) (by simp only [sfx_self]; rfl)

theorem remaining_shorter_than_anchor (n : Nat) :
    (suffix n).length<(encode '#' [short n,long n] pattern).length := by
  simp [suffix,long,pattern,encode,List.length_append]

/-- At this continuation the opaque whole block cannot match at all, while
the independently recovered source words still succeed for every length. -/
theorem whole_block_fails_on_remaining_suffix (n : Nat) :
    evV dst (input n) .callByValueSeq (tblV dst (input n) .callByValueSeq 0)
      [encode '#' [short n,long n] pattern] (.param 0) (suffix n).length=some none := by
  have hr : sfx (input n) (suffix n).length=suffix n :=
    sfx_suffix (show input n=encode '#' [short n,long n] pattern++suffix n from rfl)
  have hs : Shallot.stripPrefix? (encode '#' [short n,long n] pattern) (suffix n)=none := by
    cases h : Shallot.stripPrefix? (encode '#' [short n,long n] pattern) (suffix n) with
    | none => rfl
    | some rest =>
      have he := congrArg List.length ((CBVtoCBN.stripPrefix_exact _ _ _).mp h)
      rw [List.length_append] at he
      have := remaining_shorter_than_anchor n
      omega
  simp only [evV,List.getElem?_cons_zero,hr,hs]

theorem missing_component_rejected : check [] args ['a','b'] '#' [1] body=false := by decide
theorem separator_in_alphabet_rejected : check [] args ['a','b','#'] '#' pattern body=false := by decide
theorem bad_parameter_rejected : check [] args ['a','b'] '#' pattern (.param 2)=false := by decide
theorem parameterized_body_call_rejected : check [] args ['a','b'] '#' pattern (.call 0 [.param 0])=false := by decide

theorem wrong_suffix_rejected :
    evV dst "ab#a#ab#X".toList .callByValueSeq (tblV dst "ab#a#ab#X".toList .callByValueSeq 1) [] emitted 9=some none := by decide +kernel

theorem first_anchor_verification_is_required :
    evV dst "ab#a#ba#a!ab".toList .callByValueSeq (tblV dst "ab#a#ba#a!ab".toList .callByValueSeq 1) [] emitted 12=some none ∧
    evV dst "ab#a#ba#a!ab".toList .callByValueSeq (tblV dst "ab#a#ba#a!ab".toList .callByValueSeq 1) []
      (.call 2 (CopyFieldCapture.scanArgs '#' pattern)) 12=some (some 0) := by decide +kernel

theorem nullable_star_checked : check [] args ['a','b'] '#' pattern (.star .eps)=true := by decide

theorem nullable_star_source_undefined (n k : Nat) :
    let g := source [] 2 '#' pattern (.star .eps)
    evV g (input n) .callByValuePar (tblV g (input n) .callByValuePar k) [] root (input n).length=none := by
  intro g
  have harg : evParArgs g (input n) .callByValuePar (tblV g (input n) .callByValuePar k) [] args (input n).length=
      some (some [short n,long n]) := by
    -- The argument parsers have no calls; their evaluation ignores the table.
    have h := actual_captures n
    simpa only [args,evParArgs,evV] using h
  have hrow : ruleAtM g.rules 0=some ⟨2,TupleFieldTransfer.sourceBody '#' pattern (.star .eps)⟩ := rfl
  rw [root,evV_call_par hrow rfl (by decide),harg]
  change valAt (tblV g (input n) .callByValuePar k 0 [short n,long n]) (input n).length=none
  cases k with
  | zero => rfl
  | succ k =>
    rw [valAt_tblV_succ hrow _ (Nat.le_refl _),TupleFieldTransfer.sourceBody]
    have hfirst : evV g (input n) .callByValuePar (tblV g (input n) .callByValuePar k)
        [short n,long n] (compile '#' (sourceParts '#' pattern)) (input n).length=some (some (suffix n).length) := by
      rw [compile_eval _ _ _ _ _ _ _ _ (Nat.le_refl _),RecapturedCopyBlock.source_run]
      · simp only [sfx_self,(CBVtoCBN.stripPrefix_exact _ _ _).mpr (show input n=encode '#' [short n,long n] pattern++suffix n from rfl),Option.map_some]
      · intro i hi; simp only [List.length_cons,List.length_nil]; simp [pattern] at hi; omega
    rw [evV_seq_ok hfirst,evV_star,evStar_stuck (by rfl) (by omega)]

theorem nullable_star_target_undefined (n k : Nat) :
    let h := target [] 2 '#' pattern (.star .eps)
    evV h (input n) .callByValueSeq (tblV h (input n) .callByValueSeq k) [] emitted (input n).length=none := by
  have he := TupleFieldCompiler.physical [] args ['a','b'] '#' pattern (.star .eps) nullable_star_checked
    (input n) k _ (Nat.le_refl _)
  exact he.symm.trans (nullable_star_source_undefined n k)

theorem generated_arities : src.rules.map MRule.arity=[2] ∧ dst.rules.map MRule.arity=[1,1,6] := by decide

theorem out_of_range_does_not_leak_fields (n p : Nat) :
    evV dst (input n) .callByValueSeq (tblV dst (input n) .callByValueSeq 0)
      (CopyFieldCapture.fields '#' [short n,long n] pattern)
      (MExp.subst (CopyFieldCapture.views 2 pattern) (.param 2)) p=some none := by
  rfl

def balanced : MExp := .alt
  (.seq (.chr '(') (.seq (.call 0 []) (.seq (.chr ')') (.call 0 [])))) .eps
def helperBody : MExp := .seq (.param 0) (.seq (.chr '!')
  (.seq (.call 0 []) (.seq (.param 1) (.notP .any))))
def helperSource := source [balanced] 2 '#' pattern helperBody
def helperTarget := target [balanced] 2 '#' pattern helperBody
def helperRoot := TupleFieldTransfer.head 1 2 '#' pattern args
def helperInput := "ab#a#ab#a!(())ab".toList

theorem recursive_helper_checked : check [balanced] args ['a','b'] '#' pattern helperBody=true := by decide +kernel

theorem recursive_helper_physical_clocks :
    evV helperSource helperInput .callByValuePar (tblV helperSource helperInput .callByValuePar 1) [] (.call 1 args) helperInput.length=none ∧
    evV helperTarget helperInput .callByValueSeq (tblV helperTarget helperInput .callByValueSeq 1) [] helperRoot helperInput.length=none ∧
    evV helperSource helperInput .callByValuePar (tblV helperSource helperInput .callByValuePar 6) [] (.call 1 args) helperInput.length=some (some 0) ∧
    evV helperTarget helperInput .callByValueSeq (tblV helperTarget helperInput .callByValueSeq 6) [] helperRoot helperInput.length=some (some 0) := by decide +kernel

def controlledBody : MExp := .seq (.param 0) (.seq (.chr '!')
  (.seq (.star (.seq (.param 1) (.chr '?'))) (.seq (.notP (.param 1)) (.chr 'X'))))

theorem individual_words_in_star_and_negation :
    check [] args ['a','b'] '#' pattern controlledBody=true ∧
    evV (target [] 2 '#' pattern controlledBody) "ab#a#ab#a!ab?ab?Xz".toList .callByValueSeq
      (tblV (target [] 2 '#' pattern controlledBody) "ab#a#ab#a!ab?ab?Xz".toList .callByValueSeq 1) []
      emitted "ab#a#ab#a!ab?ab?Xz".toList.length=some (some 1) := by decide +kernel

end Shallot.MacroPeg.CBV.TupleFieldExamples
