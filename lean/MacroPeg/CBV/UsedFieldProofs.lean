import MacroPeg.CBV.UsedFieldExamples

namespace Shallot.MacroPeg.CBV.UsedFieldProofs
open UsedFieldExamples
open DelimiterTemplate (compile compile_eval)
open DelimitedWordPattern (sourceParts encode)

private theorem endpoint (x : List Char) (p : Nat) (u v : List Char) (hx : sfx x p=u++v) :
    sfx x v.length=v ∧ v.length≤x.length := by
  have hs := suffix_trans (sfx_is_suffix x p) ⟨u,hx⟩
  refine ⟨sfx_suffix hs.choose_spec,?_⟩
  obtain ⟨front,hfront⟩ := hs
  have := congrArg List.length hfront
  simp only [List.length_append] at this
  omega

private theorem word_at (x : List Char) (T : Nat → List (List Char) → Val)
    (E : List (List Char)) (e : MExp) (he : WordArguments.Word e) (w rest : List Char)
    (hv : WordArguments.value E e=some w) (p : Nat) (hx : sfx x p=w++rest) :
    evV original x .callByValuePar T E e p=some (some rest.length) := by
  rw [WordArguments.word_eval original x .callByValuePar T E e he p,hv,WordArguments.literal]
  simp only [evV,(CBVtoCBN.stripPrefix_exact _ _ _).mpr hx]

private theorem anchorA (x : List Char) (T : Nat → List (List Char) → Val)
    (n : Nat) (u after : List Char) (p : Nat) (hp : p≤x.length) (hx : sfx x p=block n++after) :
    evV original x .callByValuePar T (wordsA n u) (compile '#' (sourceParts '#' [1])) p=some (some after.length) := by
  rw [compile_eval _ _ _ _ _ _ _ _ hp,RecapturedCopyBlock.source_run]
  · have he : encode '#' (wordsA n u) [1]=block n := by simp [encode,wordsA,block]
    rw [he,(CBVtoCBN.stripPrefix_exact _ _ _).mpr hx]; rfl
  · intro i hi; simp at hi; subst i; simp [wordsA]

private theorem anchorB (x : List Char) (T : Nat → List (List Char) → Val)
    (n : Nat) (after : List Char) (p : Nat) (hp : p≤x.length) (hx : sfx x p=block n++after) :
    evV original x .callByValuePar T (wordsB n) (compile '#' (sourceParts '#' [0])) p=some (some after.length) := by
  rw [compile_eval _ _ _ _ _ _ _ _ hp,RecapturedCopyBlock.source_run]
  · have he : encode '#' (wordsB n) [0]=block n := by simp [encode,wordsB,block]
    rw [he,(CBVtoCBN.stripPrefix_exact _ _ _).mpr hx]; rfl
  · intro i hi; simp at hi; subst i; simp [wordsB]

private theorem firstA (n depth : Nat) (rest : List Char) :
    ∃ tail, treeA n depth++rest=word n++'#'::tail := by
  cases depth with
  | zero => exact ⟨'!'::(word n++rest),by simp [treeA,block,List.append_assoc]⟩
  | succ depth => exact ⟨'('::(block (2*n)++(treeA (2*n) depth++(word (2*n)++')'::(word n++rest)))),by
      simp [treeA,block,List.append_assoc]⟩

private theorem firstB (n depth : Nat) (rest : List Char) :
    ∃ tail, treeB n depth++rest=word n++'#'::tail :=
  ⟨treeA n depth++(word n++rest),by simp [treeB,block,List.append_assoc]⟩

theorem fresh_b_captures (x : List Char) (T : Nat → List (List Char) → Val)
    (n : Nat) (u tail : List Char) (p : Nat) (hp : p≤x.length) (hx : sfx x p=word (2*n)++tail) :
    evParArgs original x .callByValuePar T (wordsA n u) argsB p=some (some (wordsB (2*n))) := by
  have hv : WordArguments.value (wordsA n u) doubled=some (word (2*n)) := by
    simp [WordArguments.value,wordsA,doubled,word,Nat.two_mul]
  have ha := word_at x T (wordsA n u) doubled ⟨True.intro,True.intro⟩ _ tail hv p hx
  have he : evV original x .callByValuePar T (wordsA n u) .eps p=some (some p) := rfl
  have hpre : pre x p tail.length=word (2*n) := by
    simpa only [length_sfx x hp] using pre_eq (sfx_is_suffix x p) hx
  rw [argsB,evPar_cons_ok ha,evPar_cons_ok he,evPar_nil,hpre]
  simp [wordsB,pre]

theorem fresh_a_captures (x : List Char) (T : Nat → List (List Char) → Val)
    (n : Nat) (tail : List Char) (p : Nat) (hp : p≤x.length) (hx : sfx x p=word n++tail) :
    evParArgs original x .callByValuePar T (wordsB n) argsA p=some (some (wordsA n [])) := by
  have ha := word_at x T (wordsB n) (.param 0) True.intro _ tail rfl p hx
  have he : evV original x .callByValuePar T (wordsB n) .eps p=some (some p) := rfl
  have hpre : pre x p tail.length=word n := by
    simpa only [length_sfx x hp] using pre_eq (sfx_is_suffix x p) hx
  rw [argsA,evPar_cons_ok he,evPar_cons_ok ha,evPar_cons_ok he,evPar_nil,hpre]
  simp [wordsA,pre]

private theorem b_row_of_a (depth : Nat)
    (ha : ∀ n u (x rest : List Char) p, p≤x.length → sfx x p=treeA n depth++rest →
      valAt (tblV original x .callByValuePar (2*depth+1) 0 (wordsA n u)) p=some (some rest.length))
    (n : Nat) (x rest : List Char) (p : Nat) (hp : p≤x.length) (hx : sfx x p=treeB n depth++rest) :
    valAt (tblV original x .callByValuePar (2*depth+2) 1 (wordsB n)) p=some (some rest.length) := by
  have hr : ruleAtM original.rules 1=some ⟨2,TupleFieldTransfer.sourceBody '#' [0] bodyB⟩ := rfl
  rw [show 2*depth+2=(2*depth+1)+1 by omega,valAt_tblV_succ hr _ hp,TupleFieldTransfer.sourceBody]
  let afterA := word n++rest
  let after := treeA n depth++afterA
  have hs : sfx x p=block n++after := by simpa [treeB,after,afterA,List.append_assoc] using hx
  have he := endpoint x p (block n) after hs
  rw [evV_seq_ok (anchorB x (tblV original x .callByValuePar (2*depth+1)) n after p hp hs)]
  obtain ⟨tail,ht⟩ := firstA n depth afterA
  have hc := fresh_a_captures x (tblV original x .callByValuePar (2*depth+1)) n ('#'::tail) after.length he.2 (he.1.trans ht)
  have har : ruleAtM original.rules 0=some ⟨3,TupleFieldTransfer.sourceBody '#' [1] bodyA⟩ := rfl
  have hcall : evV original x .callByValuePar (tblV original x .callByValuePar (2*depth+1)) (wordsB n)
      (.call 0 argsA) after.length=some (some afterA.length) := by
    rw [evV_call_par har rfl (by decide),hc]
    exact ha n [] x afterA after.length he.2 he.1
  have heA := endpoint x after.length (treeA n depth) afterA he.1
  rw [bodyB,evV_seq_ok hcall]
  exact word_at x _ (wordsB n) (.param 0) True.intro (word n) rest rfl afterA.length heA.1

/-- The first and third values are not in the anchor. An arbitrary first
payload has no effect on the continuation, while the recaptured second
word doubles at every round trip through the mutually recursive rules. -/
theorem a_rows_all_depths (depth : Nat) : ∀ n u (x rest : List Char) (p : Nat), p≤x.length →
    sfx x p=treeA n depth++rest →
    valAt (tblV original x .callByValuePar (2*depth+1) 0 (wordsA n u)) p=some (some rest.length) := by
  induction depth with
  | zero =>
    intro n u x rest p hp hx
    have hr : ruleAtM original.rules 0=some ⟨3,TupleFieldTransfer.sourceBody '#' [1] bodyA⟩ := rfl
    rw [valAt_tblV_succ hr _ hp,TupleFieldTransfer.sourceBody]
    let after := '!'::(word n++rest)
    have hs : sfx x p=block n++after := by simpa [treeA,after,List.append_assoc] using hx
    have he := endpoint x p (block n) after hs
    rw [evV_seq_ok (anchorA x (tblV original x .callByValuePar 0) n u after p hp hs)]
    have hbad : evV original x .callByValuePar (tblV original x .callByValuePar 0) (wordsA n u)
        (.lit ['(']) after.length=some none := by simp only [evV,he.1]; rfl
    rw [bodyA,evV_alt_fail (evV_seq_fail hbad)]
    exact word_at x _ (wordsA n u) (.seq (.lit ['!']) (.param 1)) ⟨True.intro,True.intro⟩
      ('!'::word n) rest rfl after.length (by simpa [after] using he.1)
  | succ depth ih =>
    intro n u x rest p hp hx
    have hr : ruleAtM original.rules 0=some ⟨3,TupleFieldTransfer.sourceBody '#' [1] bodyA⟩ := rfl
    rw [show 2*(depth+1)+1=(2*depth+2)+1 by omega,valAt_tblV_succ hr _ hp,TupleFieldTransfer.sourceBody]
    let back := word n++rest
    let afterB := ')'::back
    let childInput := treeB (2*n) depth++afterB
    let after := '('::childInput
    have hs : sfx x p=block n++after := by simpa [treeA,treeB,back,afterB,childInput,after,List.append_assoc] using hx
    have he := endpoint x p (block n) after hs
    rw [evV_seq_ok (anchorA x (tblV original x .callByValuePar (2*depth+2)) n u after p hp hs)]
    have hopen := word_at x (tblV original x .callByValuePar (2*depth+2)) (wordsA n u)
      (.lit ['(']) True.intro ['('] childInput rfl after.length he.1
    have hchildpos := endpoint x after.length ['('] childInput he.1
    obtain ⟨tail,ht⟩ := firstB (2*n) depth afterB
    have hc := fresh_b_captures x (tblV original x .callByValuePar (2*depth+2)) n u ('#'::tail)
      childInput.length hchildpos.2 (hchildpos.1.trans ht)
    have hbr : ruleAtM original.rules 1=some ⟨2,TupleFieldTransfer.sourceBody '#' [0] bodyB⟩ := rfl
    have hcall : evV original x .callByValuePar (tblV original x .callByValuePar (2*depth+2)) (wordsA n u)
        (.call 1 argsB) childInput.length=some (some afterB.length) := by
      rw [evV_call_par hbr rfl (by decide),hc]
      exact b_row_of_a depth ih (2*n) x afterB childInput.length hchildpos.2 hchildpos.1
    have heB := endpoint x childInput.length (treeB (2*n) depth) afterB hchildpos.1
    have hclose := word_at x (tblV original x .callByValuePar (2*depth+2)) (wordsA n u)
      (.lit [')']) True.intro [')'] back rfl afterB.length heB.1
    have hback := endpoint x afterB.length [')'] back heB.1
    have hreturn := word_at x (tblV original x .callByValuePar (2*depth+2)) (wordsA n u)
      (.param 1) True.intro (word n) rest rfl back.length hback.1
    rw [bodyA,evV_alt_ok (evV_seq_ok hopen |>.trans (evV_seq_ok hcall |>.trans (evV_seq_ok hclose |>.trans hreturn)))]

theorem b_rows_all_depths (n depth : Nat) (x rest : List Char) (p : Nat) (hp : p≤x.length)
    (hx : sfx x p=treeB n depth++rest) :
    valAt (tblV original x .callByValuePar (2*depth+2) 1 (wordsB n)) p=some (some rest.length) :=
  b_row_of_a depth (a_rows_all_depths depth) n x rest p hp hx

def initialUnused : Nat → List Char | 0 => [] | _+1 => ['a']

private theorem word_copies (n : Nat) : word n=RepeatedWordArguments.copies ['a'] n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [word,List.replicate_succ,RepeatedWordArguments.copies,List.singleton_append]
      using congrArg (List.cons 'a') ih

theorem initial_captures (x : List Char) (T : Nat → List (List Char) → Val) (n : Nat)
    (rest : List Char) (hx : x=word n++'#'::rest) :
    evParArgs original x .callByValuePar T [] actuals x.length=some (some (wordsA n (initialUnused n))) := by
  have hscan : evV original x .callByValuePar T [] (.star (.lit ['a'])) x.length=some (some ('#'::rest).length) := by
    apply RecapturedCopyBlock.literal_copies _ _ _ _ _ ['a'] (by decide) ('#'::rest)
      (by simp [Shallot.stripPrefix?,Shallot.beqChar]) n _ (Nat.le_refl _)
    simpa only [sfx_self,←word_copies] using hx
  have hpscan : pre x x.length ('#'::rest).length=word n := by
    simpa only [sfx_self] using pre_eq (x:=x) ⟨[],rfl⟩ hx
  have he : evV original x .callByValuePar T [] .eps x.length=some (some x.length) := rfl
  cases n with
  | zero =>
    have ho : evV original x .callByValuePar T [] (.alt (.lit ['a']) .eps) x.length=some (some x.length) := by
      have hf : evV original x .callByValuePar T [] (.lit ['a']) x.length=some none := by
        simp only [evV,sfx_self]
        rw [hx]
        rfl
      exact evV_alt_fail hf |>.trans he
    rw [actuals,evPar_cons_ok ho,evPar_cons_ok hscan,evPar_cons_ok he,evPar_nil,hpscan]
    simp [initialUnused,wordsA,pre]
  | succ n =>
    let tail := word n++'#'::rest
    have ht : x=['a']++tail := by simpa [word,tail,List.replicate_succ] using hx
    have hopt := word_at x T [] (.lit ['a']) True.intro ['a'] tail rfl x.length (by simpa [sfx_self] using ht)
    have hpopt : pre x x.length tail.length=['a'] := pre_eq (x:=x) ⟨[],rfl⟩ ht
    rw [actuals,evPar_cons_ok (evV_alt_ok hopt),evPar_cons_ok hscan,evPar_cons_ok he,evPar_nil,hpscan,hpopt]
    simp [initialUnused,wordsA,pre]

theorem source_and_target_all_trees (n depth : Nat) :
    evV original (treeA n depth) .callByValuePar (tblV original (treeA n depth) .callByValuePar (2*depth+1)) [] root
      (treeA n depth).length=some (some 0) ∧
    evV generated (treeA n depth) .callByValueSeq (tblV generated (treeA n depth) .callByValueSeq (2*depth+1)) []
      generatedRoot (treeA n depth).length=some (some 0) := by
  obtain ⟨tail,ht⟩ := firstA n depth []
  have hx : treeA n depth=word n++'#'::tail := by simpa using ht
  have hc := initial_captures (treeA n depth) (tblV original (treeA n depth) .callByValuePar (2*depth+1)) n tail hx
  have hr := a_rows_all_depths depth n (initialUnused n) (treeA n depth) [] (treeA n depth).length (Nat.le_refl _)
    (by simp only [sfx_self,List.append_nil])
  have hrow : ruleAtM original.rules 0=some ⟨3,TupleFieldTransfer.sourceBody '#' [1] bodyA⟩ := rfl
  have hcall : evV original (treeA n depth) .callByValuePar (tblV original (treeA n depth) .callByValuePar (2*depth+1)) []
      (.call 0 actuals) (treeA n depth).length=some (some 0) := by
    rw [evV_call_par hrow rfl (by decide),hc]
    exact hr
  have hs : evV original (treeA n depth) .callByValuePar (tblV original (treeA n depth) .callByValuePar (2*depth+1)) [] root
      (treeA n depth).length=some (some 0) := by
    rw [root,evV_seq_ok hcall]
    simp [evV,sfx]
  exact ⟨hs,(every_input_every_clock (treeA n depth) (2*depth+1)).symm.trans hs⟩

end Shallot.MacroPeg.CBV.UsedFieldProofs
