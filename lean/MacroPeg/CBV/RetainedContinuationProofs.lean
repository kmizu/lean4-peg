import MacroPeg.CBV.RetainedContinuationExamples

namespace Shallot.MacroPeg.CBV.RetainedContinuationProofs
open RetainedContinuationExamples
open DelimiterTemplate (compile compile_eval)
open DelimitedWordPattern (sourceParts encode)
open RetainedContinuationAlgebra (seq_assoc)

private theorem endpoint (x : List Char) (p : Nat) (u v : List Char) (hx : sfx x p=u++v) :
    sfx x v.length=v ∧ v.length≤x.length := by
  have hs := suffix_trans (sfx_is_suffix x p) ⟨u,hx⟩
  refine ⟨sfx_suffix hs.choose_spec,?_⟩
  obtain ⟨front,hfront⟩ := hs
  have := congrArg List.length hfront
  simp only [List.length_append] at this
  omega

private theorem word_at (x : List Char) (T : ClockFreezing.Table)
    (E : List (List Char)) (e : MExp) (he : WordArguments.Word e) (w rest : List Char)
    (hv : WordArguments.value E e=some w) (p : Nat) (hx : sfx x p=w++rest) :
    evV original x .callByValuePar T E e p=some (some rest.length) := by
  rw [WordArguments.word_eval original x .callByValuePar T E e he p,hv,WordArguments.literal]
  simp only [evV,(CBVtoCBN.stripPrefix_exact _ _ _).mpr hx]

private theorem anchor (x : List Char) (T : ClockFreezing.Table) (n : Nat)
    (d : Char) (rest : List Char) (p : Nat) (hp : p≤x.length) (hx : sfx x p=word n++d::rest) :
    evV original x .callByValuePar T [word n] (compile d (sourceParts d [0])) p=some (some rest.length) := by
  rw [compile_eval _ _ _ _ _ _ _ _ hp,RecapturedCopyBlock.source_run]
  · have he : encode d [word n] [0]=word n++[d] := by simp [encode]
    rw [he,(CBVtoCBN.stripPrefix_exact _ _ _).mpr (by simpa only [List.append_assoc,List.singleton_append] using hx)]; rfl
  · intro i hi; simp only [List.mem_singleton] at hi; subst i; simp

private theorem wrong_anchor (x : List Char) (T : ClockFreezing.Table) (n : Nat)
    (rest : List Char) (p : Nat) (hp : p≤x.length) (hx : sfx x p=word n++'@'::rest) :
    evV original x .callByValuePar T [word n] (compile '#' (sourceParts '#' [0])) p=some none := by
  rw [compile_eval _ _ _ _ _ _ _ _ hp,RecapturedCopyBlock.source_run]
  · have he : encode '#' [word n] [0]=word n++['#'] := by simp [encode]
    rw [he,hx]
    cases h : Shallot.stripPrefix? (word n++['#']) (word n++'@'::rest) with
    | none => rfl
    | some tail =>
      have hh := (CBVtoCBN.stripPrefix_exact _ _ _).mp h
      have ht : '@'::rest='#'::tail := List.append_cancel_left (as:=word n)
        (by simpa only [List.append_assoc,List.singleton_append] using hh)
      cases (List.cons.inj ht).1
  · intro i hi; simp only [List.mem_singleton] at hi; subst i; simp

theorem helper_call (x : List Char) (k n : Nat) (rest : List Char) (p : Nat)
    (hp : p≤x.length) (hx : sfx x p=word n++'?'::rest) :
    evV original x .callByValuePar (tblV original x .callByValuePar (k+1)) [word n] (.call 1 [.param 0]) p=
      some (some rest.length) := by
  have ha := word_at x (tblV original x .callByValuePar (k+1)) [word n] (.param 0) True.intro
    (word n) ('?'::rest) rfl p hx
  have hpre : pre x p ('?'::rest).length=word n := by
    simpa only [length_sfx x hp] using pre_eq (sfx_is_suffix x p) hx
  have hr : ruleAtM original.rules 1=some ⟨1,.seq (TupleFieldTransfer.sourceBody '?' [0] .eps) .eps⟩ := rfl
  rw [evV_call_par hr rfl (by decide),evPar_cons_ok ha,evPar_nil,hpre]
  change valAt (tblV original x .callByValuePar (k+1) 1 [word n]) p=_
  rw [valAt_tblV_succ hr _ hp,TupleFieldTransfer.sourceBody,seq_assoc,
    evV_seq_ok (anchor x _ n '?' rest p hp hx)]
  rfl

/-- This continuation starts strictly after the selected branch. It
consumes ';', calls another retained-value rule, then uses the original
parent capture again. No producer is re-run at that later position. -/
theorem continuation_at (x : List Char) (k n : Nat) (rest : List Char) (p : Nat)
    (hp : p≤x.length) (hx : sfx x p=ending n++rest) :
    evV original x .callByValuePar (tblV original x .callByValuePar (k+1)) [word n] after p=some (some rest.length) := by
  let afterHelper := word n++rest
  let afterMark := word n++'?'::afterHelper
  have hs : sfx x p=[';']++afterMark := by simpa [ending,afterMark,afterHelper,List.append_assoc] using hx
  have hmark := word_at x (tblV original x .callByValuePar (k+1)) [word n] (.lit [';']) True.intro
    [';'] afterMark rfl p hs
  have he := endpoint x p [';'] afterMark hs
  have hh := helper_call x k n afterHelper afterMark.length he.2 he.1
  have hep := endpoint x afterMark.length (word n++['?']) afterHelper
    (by simpa only [List.append_assoc,List.singleton_append] using he.1)
  rw [after,evV_seq_ok hmark,evV_seq_ok hh]
  exact word_at x _ [word n] (.param 0) True.intro (word n) rest rfl afterHelper.length hep.1

private theorem first_word (n depth : Nat) (rest : List Char) :
    ∃ c tail, Shallot.stripPrefix? ['a'] (c::tail)=none ∧ tree n depth++rest=word n++c::tail := by
  cases depth with
  | zero => exact ⟨'@','?'::(ending n++rest),rfl,by simp [tree,List.append_assoc]⟩
  | succ d => exact ⟨'#','('::(tree (2*n) d++')'::(ending n++rest)),rfl,by simp [tree,List.append_assoc]⟩

theorem fresh_doubled_capture (x : List Char) (T : ClockFreezing.Table) (n : Nat)
    (rest : List Char) (p : Nat) (hp : p≤x.length) (hx : sfx x p=word (2*n)++rest) :
    evParArgs original x .callByValuePar T [word n] [doubled] p=some (some [word (2*n)]) := by
  have hv : WordArguments.value [word n] doubled=some (word (2*n)) := by
    simp [WordArguments.value,doubled,word,Nat.two_mul]
  have ha := word_at x T [word n] doubled ⟨True.intro,True.intro⟩ _ rest hv p hx
  have he : pre x p rest.length=word (2*n) := by
    simpa only [length_sfx x hp] using pre_eq (sfx_is_suffix x p) hx
  rw [evPar_cons_ok ha,evPar_nil,he]

theorem producer_rows (depth extra : Nat) : ∀ n (x rest : List Char) p,
    p≤x.length → sfx x p=tree n depth++rest →
    valAt (tblV original x .callByValuePar (depth+extra+2) 0 [word n]) p=some (some rest.length) := by
  induction depth with
  | zero =>
    intro n x rest p hp hx
    let afterChoice := ending n++rest
    let afterAnchor := '?'::afterChoice
    have hs : sfx x p=word n++'@'::afterAnchor := by simpa [tree,afterAnchor,afterChoice,List.append_assoc] using hx
    have he := endpoint x p (word n++['@']) afterAnchor (by simpa only [List.append_assoc,List.singleton_append] using hs)
    have hfirst : evV original x .callByValuePar (tblV original x .callByValuePar (extra+1)) [word n]
        (FieldPlanSyntax.sourceLeaf parts 0) p=some none := evV_seq_fail (wrong_anchor x _ n afterAnchor p hp hs)
    have hmark := word_at x (tblV original x .callByValuePar (extra+1)) [word n] (.lit ['?']) True.intro
      ['?'] afterChoice rfl afterAnchor.length he.1
    have hsecond : evV original x .callByValuePar (tblV original x .callByValuePar (extra+1)) [word n]
        (FieldPlanSyntax.sourceLeaf parts 1) p=some (some afterChoice.length) := by
      change evV original x .callByValuePar _ _ (TupleFieldTransfer.sourceBody '@' [0] (.lit ['?'])) p=_
      rw [TupleFieldTransfer.sourceBody,evV_seq_ok (anchor x _ n '@' afterAnchor p hp hs)]
      exact hmark
    have hchoice : evV original x .callByValuePar (tblV original x .callByValuePar (extra+1)) [word n]
        (mainPlan.exp (FieldPlanSyntax.sourceLeaf parts)) p=some (some afterChoice.length) :=
      (evV_alt_fail hfirst).trans hsecond
    rw [show 0+extra+2=(extra+1)+1 by omega,valAt_tblV_succ (show ruleAtM original.rules 0=some
      ⟨1,.seq (mainPlan.exp (FieldPlanSyntax.sourceLeaf parts)) after⟩ from rfl) _ hp,evV_seq_ok hchoice]
    have hec := endpoint x afterAnchor.length ['?'] afterChoice he.1
    exact continuation_at x extra n rest afterChoice.length hec.2 hec.1
  | succ depth ih =>
    intro n x rest p hp hx
    let afterChoice := ending n++rest
    let afterChild := ')'::afterChoice
    let childInput := tree (2*n) depth++afterChild
    let afterAnchor := '('::childInput
    have hs : sfx x p=word n++'#'::afterAnchor := by simpa [tree,afterAnchor,childInput,afterChild,afterChoice,List.append_assoc] using hx
    have he := endpoint x p (word n++['#']) afterAnchor (by simpa only [List.append_assoc,List.singleton_append] using hs)
    have hopen := word_at x (tblV original x .callByValuePar (depth+extra+2)) [word n] (.lit ['(']) True.intro
      ['('] childInput rfl afterAnchor.length he.1
    have hec := endpoint x afterAnchor.length ['('] childInput he.1
    obtain ⟨c,tail,hstop,ht⟩ := first_word (2*n) depth afterChild
    have hc := fresh_doubled_capture x (tblV original x .callByValuePar (depth+extra+2)) n (c::tail)
      childInput.length hec.2 (hec.1.trans ht)
    have hcall : evV original x .callByValuePar (tblV original x .callByValuePar (depth+extra+2)) [word n]
        (.call 0 [doubled]) childInput.length=some (some afterChild.length) := by
      rw [evV_call_par (show ruleAtM original.rules 0=some ⟨1,.seq (mainPlan.exp (FieldPlanSyntax.sourceLeaf parts)) after⟩ from rfl)
        rfl (by decide),hc]
      exact ih (2*n) x afterChild childInput.length hec.2 hec.1
    have her := endpoint x childInput.length (tree (2*n) depth) afterChild hec.1
    have hclose := word_at x (tblV original x .callByValuePar (depth+extra+2)) [word n] (.lit [')']) True.intro
      [')'] afterChoice rfl afterChild.length her.1
    have hfirst : evV original x .callByValuePar (tblV original x .callByValuePar (depth+extra+2)) [word n]
        (FieldPlanSyntax.sourceLeaf parts 0) p=some (some afterChoice.length) := by
      change evV original x .callByValuePar _ _ (TupleFieldTransfer.sourceBody '#' [0] branch) p=_
      rw [TupleFieldTransfer.sourceBody,evV_seq_ok (anchor x _ n '#' afterAnchor p hp hs),branch,
        evV_alt_fail (show evV original x .callByValuePar _ [word n] (.lit ['!']) afterAnchor.length=some none by
          simp only [evV,he.1]; rfl),evV_seq_ok hopen,evV_seq_ok hcall]
      exact hclose
    have hchoice : evV original x .callByValuePar (tblV original x .callByValuePar (depth+extra+2)) [word n]
        (mainPlan.exp (FieldPlanSyntax.sourceLeaf parts)) p=some (some afterChoice.length) :=
      evV_alt_ok (b:=FieldPlanSyntax.sourceLeaf parts 1) hfirst
    rw [show depth+1+extra+2=(depth+extra+2)+1 by omega,valAt_tblV_succ (show ruleAtM original.rules 0=some
      ⟨1,.seq (mainPlan.exp (FieldPlanSyntax.sourceLeaf parts)) after⟩ from rfl) _ hp,evV_seq_ok hchoice]
    have hep := endpoint x afterChild.length [')'] afterChoice her.1
    exact continuation_at x (depth+extra+1) n rest afterChoice.length hep.2 hep.1

private theorem word_copies (n : Nat) : RepeatedWordArguments.copies ['a'] n=word n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [RepeatedWordArguments.copies,word,List.replicate_succ] using congrArg (List.cons 'a') ih

theorem producer_result (n depth extra : Nat) (x rest : List Char) (p : Nat)
    (hp : p≤x.length) (hx : sfx x p=tree n depth++rest) :
    evV original x .callByValuePar (tblV original x .callByValuePar (depth+extra+2)) [] producer p=some (some rest.length) := by
  obtain ⟨c,tail,hstop,ht⟩ := first_word n depth rest
  have hs := hx.trans ht
  have hscan : evV original x .callByValuePar (tblV original x .callByValuePar (depth+extra+2)) [] actual p=
      some (some (c::tail).length) := by
    apply RecapturedCopyBlock.literal_copies _ _ _ _ _ ['a'] (by decide) (c::tail) hstop n _ hp
    simpa only [word_copies] using hs
  have hpre : pre x p (c::tail).length=word n := by
    simpa only [length_sfx x hp] using pre_eq (sfx_is_suffix x p) hs
  rw [producer,evV_call_par (show ruleAtM original.rules 0=some ⟨1,.seq (mainPlan.exp (FieldPlanSyntax.sourceLeaf parts)) after⟩ from rfl)
    rfl (by decide),evPar_cons_ok hscan,evPar_nil,hpre]
  exact producer_rows depth extra n x rest p hp hx

theorem outer_capture (n depth : Nat) :
    evParArgs original (sample n depth) .callByValuePar
      (tblV original (sample n depth) .callByValuePar (depth+3)) [] [producer] (sample n depth).length=some (some [tree n depth]) := by
  have hx : sfx (sample n depth) (sample n depth).length=tree n depth++'$'::tree n depth := by rw [sfx_self]; rfl
  have hv := producer_result n depth 1 (sample n depth) ('$'::tree n depth) _ (Nat.le_refl _) hx
  have he : pre (sample n depth) (sample n depth).length ('$'::tree n depth).length=tree n depth :=
    pre_eq (x:=sample n depth) ⟨[],rfl⟩ rfl
  rw [show depth+1+2=depth+3 by omega] at hv
  rw [evPar_cons_ok hv,evPar_nil,he]

theorem source_and_generated_all_trees (n depth : Nat) :
    evV original (sample n depth) .callByValuePar (tblV original (sample n depth) .callByValuePar (depth+3)) []
      root (sample n depth).length=some (some 0) ∧
    evV generated (sample n depth) .callByValueSeq (tblV generated (sample n depth) .callByValueSeq (depth+3)) []
      generatedRoot (sample n depth).length=some (some 0) := by
  let x := sample n depth
  have hc : evV original x .callByValuePar (tblV original x .callByValuePar (depth+3)) [] (.call 2 [producer]) x.length=some (some 0) := by
    have hr : ruleAtM original.rules 2=some ⟨1,.seq (TupleFieldTransfer.sourceBody '$' [0] .eps) (.param 0)⟩ := rfl
    rw [evV_call_par hr rfl (by decide),outer_capture n depth]
    change valAt (tblV original x .callByValuePar (depth+3) 2 [tree n depth]) x.length=some (some 0)
    rw [show depth+3=(depth+2)+1 by omega,valAt_tblV_succ hr _ (Nat.le_refl _),TupleFieldTransfer.sourceBody,seq_assoc]
    have ha : evV original x .callByValuePar (tblV original x .callByValuePar (depth+2)) [tree n depth]
        (compile '$' (sourceParts '$' [0])) x.length=some (some (tree n depth).length) := by
      rw [compile_eval _ _ _ _ _ _ _ _ (Nat.le_refl _),RecapturedCopyBlock.source_run]
      · have he : encode '$' [tree n depth] [0]=tree n depth++['$'] := by simp [encode]
        rw [he,(CBVtoCBN.stripPrefix_exact _ _ _).mpr (show sfx x x.length=(tree n depth++['$'])++tree n depth by
          rw [sfx_self]; simp only [x,sample,List.append_assoc,List.singleton_append])]; rfl
      · intro i hi; simp only [List.mem_singleton] at hi; subst i; simp
    rw [evV_seq_ok ha,evV_seq_ok (show evV original x .callByValuePar _ [tree n depth] .eps (tree n depth).length=
      some (some (tree n depth).length) from rfl)]
    exact word_at x _ [tree n depth] (.param 0) True.intro (tree n depth) [] rfl (tree n depth).length
      (by simpa using (endpoint x x.length (tree n depth++['$']) (tree n depth)
        (by rw [sfx_self]; simp only [x,sample,List.append_assoc,List.singleton_append])).1)
  have hs : evV original x .callByValuePar (tblV original x .callByValuePar (depth+3)) [] root x.length=some (some 0) := by
    rw [root,evV_seq_ok hc]
    simp [evV,sfx]
  exact ⟨hs,(every_input_every_clock x (depth+3)).symm.trans hs⟩

theorem outer_capture_length_unbounded (depth n : Nat) : n≤(tree n depth).length := by
  cases depth <;> simp [tree,word,List.length_append,List.length_replicate] <;> omega

end Shallot.MacroPeg.CBV.RetainedContinuationProofs
