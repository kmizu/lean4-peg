import MacroPeg.CBV.MutualFieldExamples

namespace Shallot.MacroPeg.CBV.MutualFieldProofs
open MutualFieldExamples
open DelimiterTemplate (compile compile_eval)
open DelimitedWordPattern (sourceParts encode)
open RecursiveFieldExamples (word_at)

private theorem endpoint (x : List Char) (p : Nat) (u v : List Char) (hx : sfx x p=u++v) :
    sfx x v.length=v ∧ v.length≤x.length := by
  have hs := suffix_trans (sfx_is_suffix x p) ⟨u,hx⟩
  refine ⟨sfx_suffix hs.choose_spec,?_⟩
  obtain ⟨front,hfront⟩ := hs
  have := congrArg List.length hfront
  simp only [List.length_append] at this
  omega

private theorem anchorF (x : List Char) (T : Nat → List (List Char) → Val)
    (n : Nat) (after : List Char) (p : Nat) (hp : p≤x.length) (hx : sfx x p=block n++after) :
    evV original x .callByValuePar T (MutualFieldExamples.words n) (compile '#' (sourceParts '#' pattern)) p=some (some after.length) := by
  rw [compile_eval _ _ _ _ _ _ _ _ hp,RecapturedCopyBlock.source_run]
  · have hh : Shallot.stripPrefix? (encode '#' (MutualFieldExamples.words n) pattern) (sfx x p)=some after :=
      (CBVtoCBN.stripPrefix_exact _ _ _).mpr hx
    rw [hh]; rfl
  · intro i hi
    simp only [MutualFieldExamples.words,RecursiveFieldExamples.words,List.length_cons,List.length_nil]
    simp [pattern,RecursiveFieldExamples.pattern] at hi
    omega

private theorem anchorG (x : List Char) (T : Nat → List (List Char) → Val)
    (n : Nat) (after : List Char) (p : Nat) (hp : p≤x.length) (hx : sfx x p=gBlock n++after) :
    evV original x .callByValuePar T [short n] (compile '#' (sourceParts '#' [0])) p=some (some after.length) := by
  rw [compile_eval _ _ _ _ _ _ _ _ hp,RecapturedCopyBlock.source_run]
  · have he : encode '#' [short n] [0]=gBlock n := by simp [encode,gBlock]
    rw [he,(CBVtoCBN.stripPrefix_exact _ _ _).mpr hx]; rfl
  · intro i hi; simp at hi; subst i; simp

private theorem firstF (n depth : Nat) (rest : List Char) :
    ∃ tail, treeF n depth++rest=long n++tail := by
  cases depth with
  | zero =>
    refine ⟨['#']++short n++['#']++long n++['#']++short n++['!']++long n++rest,?_⟩
    simp [treeF,block,encode,RecursiveFieldExamples.block,
      RecursiveFieldExamples.pattern,RecursiveFieldExamples.words,List.append_assoc]
  | succ depth =>
    refine ⟨['#']++short n++['#']++long n++['#','(']++gBlock (2*n)++treeF (2*n) depth++
      short (2*n)++[')']++long n++['!']++short n++rest,?_⟩
    simp [treeF,block,encode,RecursiveFieldExamples.block,
      RecursiveFieldExamples.pattern,RecursiveFieldExamples.words,List.append_assoc]

private theorem firstG (n depth : Nat) (rest : List Char) :
    ∃ tail, treeG n depth++rest=short n++tail := by
  exact ⟨'#'::(treeF n depth++(short n++rest)),by simp [treeG,gBlock,List.append_assoc]⟩

theorem fresh_g_captures (x : List Char) (T : Nat → List (List Char) → Val)
    (n : Nat) (tail : List Char) (p : Nat) (hp : p≤x.length) (hx : sfx x p=short (2*n)++tail) :
    evParArgs original x .callByValuePar T (MutualFieldExamples.words n) MutualFieldExamples.gArgs p=some (some [short (2*n)]) := by
  have h := word_at original x .callByValuePar T (MutualFieldExamples.words n) doubled ⟨True.intro,True.intro⟩ _ tail
    (RecursiveFieldExamples.fresh_child_values n).1 p hx
  have hpre : pre x p tail.length=short (2*n) := by
    simpa only [length_sfx x hp] using pre_eq (sfx_is_suffix x p) hx
  rw [MutualFieldExamples.gArgs,evPar_cons_ok h,evPar_nil,hpre]

theorem fresh_f_captures (x : List Char) (T : Nat → List (List Char) → Val)
    (n : Nat) (tail : List Char) (p : Nat) (hp : p≤x.length) (hx : sfx x p=long n++tail) :
    evParArgs original x .callByValuePar T [short n] MutualFieldExamples.fArgs p=some (some (MutualFieldExamples.words n)) := by
  have hx0 : sfx x p=short n++'b'::tail := by simpa [long,RecursiveFieldExamples.long,List.append_assoc] using hx
  have h0 := word_at original x .callByValuePar T [short n] (.param 0) True.intro _ ('b'::tail) rfl p hx0
  have h1 := word_at original x .callByValuePar T [short n] (.seq (.param 0) (.lit ['b']))
    ⟨True.intro,True.intro⟩ _ tail rfl p hx
  have hpre0 : pre x p ('b'::tail).length=short n := by
    simpa only [length_sfx x hp] using pre_eq (sfx_is_suffix x p) hx0
  have hpre1 : pre x p tail.length=long n := by
    simpa only [length_sfx x hp] using pre_eq (sfx_is_suffix x p) hx
  rw [MutualFieldExamples.fArgs,evPar_cons_ok h0,evPar_cons_ok h1,evPar_nil,hpre0,hpre1]
  rfl

private theorem g_row_of_f (depth : Nat)
    (hf : ∀ n (x rest : List Char) p, p≤x.length → sfx x p=treeF n depth++rest →
      valAt (tblV original x .callByValuePar (2*depth+1) 0 (MutualFieldExamples.words n)) p=some (some rest.length))
    (n : Nat) (x rest : List Char) (p : Nat) (hp : p≤x.length) (hx : sfx x p=treeG n depth++rest) :
    valAt (tblV original x .callByValuePar (2*depth+2) 1 [short n]) p=some (some rest.length) := by
  have hr : ruleAtM original.rules 1=some ⟨1,TupleFieldTransfer.sourceBody '#' [0] bodyG⟩ := rfl
  rw [show 2*depth+2=(2*depth+1)+1 by omega,valAt_tblV_succ hr _ hp,TupleFieldTransfer.sourceBody]
  let afterF := short n++rest
  let after := treeF n depth++afterF
  have hs : sfx x p=gBlock n++after := by simpa [treeG,after,afterF,List.append_assoc] using hx
  have ha := anchorG x (tblV original x .callByValuePar (2*depth+1)) n after p hp hs
  have he := endpoint x p (gBlock n) after hs
  rw [evV_seq_ok ha]
  obtain ⟨tail,ht⟩ := firstF n depth afterF
  have hc := fresh_f_captures x (tblV original x .callByValuePar (2*depth+1)) n tail after.length he.2 (he.1.trans ht)
  have hfr : ruleAtM original.rules 0=some ⟨2,TupleFieldTransfer.sourceBody '#' pattern bodyF⟩ := rfl
  have hcall : evV original x .callByValuePar (tblV original x .callByValuePar (2*depth+1)) [short n]
      (.call 0 MutualFieldExamples.fArgs) after.length=some (some afterF.length) := by
    rw [evV_call_par hfr rfl (by decide),hc]
    exact hf n x afterF after.length he.2 he.1
  have heF := endpoint x after.length (treeF n depth) afterF he.1
  rw [bodyG,evV_seq_ok hcall]
  exact word_at original x .callByValuePar _ [short n] (.param 0) True.intro (short n) rest rfl afterF.length heF.1

/-- Every depth performs both real changes of tuple shape, then returns
through the unary and binary parents with their original retained values. -/
theorem f_rows_all_depths (depth : Nat) : ∀ n (x rest : List Char) (p : Nat), p≤x.length →
    sfx x p=treeF n depth++rest →
    valAt (tblV original x .callByValuePar (2*depth+1) 0 (MutualFieldExamples.words n)) p=some (some rest.length) := by
  induction depth with
  | zero =>
    intro n x rest p hp hx
    have hr : ruleAtM original.rules 0=some ⟨2,TupleFieldTransfer.sourceBody '#' pattern bodyF⟩ := rfl
    rw [valAt_tblV_succ hr _ hp,TupleFieldTransfer.sourceBody]
    let after := short n++'!'::(long n++rest)
    have hs : sfx x p=block n++after := by simpa [treeF,after,List.append_assoc] using hx
    have he := endpoint x p (block n) after hs
    rw [evV_seq_ok (anchorF x (tblV original x .callByValuePar 0) n after p hp hs)]
    have hbad : evV original x .callByValuePar (tblV original x .callByValuePar 0) (MutualFieldExamples.words n)
        (.lit ['(']) after.length=some none := by
      simp only [evV,he.1]
      cases n <;> simp [after,short,RecursiveFieldExamples.short,List.replicate_succ,Shallot.stripPrefix?,Shallot.beqChar]
    rw [bodyF,evV_alt_fail (evV_seq_fail hbad)]
    apply word_at _ _ _ _ _ base ⟨True.intro,True.intro,True.intro⟩ (short n++'!'::long n) rest
    · simp [base,RecursiveFieldExamples.base,WordArguments.value,MutualFieldExamples.words,RecursiveFieldExamples.words]
    · simpa [after,List.append_assoc] using he.1
  | succ depth ih =>
    intro n x rest p hp hx
    have hr : ruleAtM original.rules 0=some ⟨2,TupleFieldTransfer.sourceBody '#' pattern bodyF⟩ := rfl
    rw [show 2*(depth+1)+1=(2*depth+2)+1 by omega,valAt_tblV_succ hr _ hp,TupleFieldTransfer.sourceBody]
    let back := long n++'!'::(short n++rest)
    let afterG := ')'::back
    let childInput := treeG (2*n) depth++afterG
    let after := '('::childInput
    have hs : sfx x p=block n++after := by
      simpa [treeF,treeG,back,afterG,childInput,after,List.append_assoc] using hx
    have he := endpoint x p (block n) after hs
    rw [evV_seq_ok (anchorF x (tblV original x .callByValuePar (2*depth+2)) n after p hp hs)]
    have hopen := word_at original x .callByValuePar (tblV original x .callByValuePar (2*depth+2)) (MutualFieldExamples.words n)
      (.lit ['(']) True.intro ['('] childInput rfl after.length he.1
    have hchildpos := endpoint x after.length ['('] childInput he.1
    obtain ⟨tail,htail⟩ := firstG (2*n) depth afterG
    have hc := fresh_g_captures x (tblV original x .callByValuePar (2*depth+2)) n tail childInput.length hchildpos.2 (hchildpos.1.trans htail)
    have hgr : ruleAtM original.rules 1=some ⟨1,TupleFieldTransfer.sourceBody '#' [0] bodyG⟩ := rfl
    have hcall : evV original x .callByValuePar (tblV original x .callByValuePar (2*depth+2)) (MutualFieldExamples.words n)
        (.call 1 MutualFieldExamples.gArgs) childInput.length=some (some afterG.length) := by
      rw [evV_call_par hgr rfl (by decide),hc]
      exact g_row_of_f depth ih (2*n) x afterG childInput.length hchildpos.2 hchildpos.1
    have heG := endpoint x childInput.length (treeG (2*n) depth) afterG hchildpos.1
    have hclose := word_at original x .callByValuePar (tblV original x .callByValuePar (2*depth+2)) (MutualFieldExamples.words n)
      (.lit [')']) True.intro [')'] back rfl afterG.length heG.1
    have hback := endpoint x afterG.length [')'] back heG.1
    have hreturn := word_at original x .callByValuePar (tblV original x .callByValuePar (2*depth+2)) (MutualFieldExamples.words n)
      restore ⟨True.intro,True.intro,True.intro⟩ (long n++'!'::short n) rest
      (by simp [restore,RecursiveFieldExamples.restore,WordArguments.value,MutualFieldExamples.words,RecursiveFieldExamples.words]) back.length
      (by simpa [back,List.append_assoc] using hback.1)
    rw [bodyF,evV_alt_ok (evV_seq_ok hopen |>.trans (evV_seq_ok hcall |>.trans (evV_seq_ok hclose |>.trans hreturn)))]

theorem g_rows_all_depths (n depth : Nat) (x rest : List Char) (p : Nat) (hp : p≤x.length)
    (hx : sfx x p=treeG n depth++rest) :
    valAt (tblV original x .callByValuePar (2*depth+2) 1 [short n]) p=some (some rest.length) :=
  g_row_of_f depth (f_rows_all_depths depth) n x rest p hp hx

private theorem short_copies (n : Nat) : short n=RepeatedWordArguments.copies ['a'] n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [short,RecursiveFieldExamples.short,List.replicate_succ,RepeatedWordArguments.copies,List.singleton_append]
      using congrArg (List.cons 'a') ih

theorem initial_captures (x : List Char) (T : Nat → List (List Char) → Val)
    (n : Nat) (rest : List Char) (hx : x=long n++rest) :
    evParArgs original x .callByValuePar T [] MutualFieldExamples.actuals x.length=some (some (MutualFieldExamples.words n)) := by
  have hs : x=short n++'b'::rest := by simpa [long,RecursiveFieldExamples.long,List.append_assoc] using hx
  have hscan : evV original x .callByValuePar T [] (.star (.lit ['a'])) x.length=some (some ('b'::rest).length) := by
    apply RecapturedCopyBlock.literal_copies _ _ _ _ _ ['a'] (by decide) ('b'::rest)
      (by simp [Shallot.stripPrefix?,Shallot.beqChar]) n _ (Nat.le_refl _)
    simpa only [sfx_self,←short_copies] using hs
  have hb : evV original x .callByValuePar T [] (.lit ['b']) ('b'::rest).length=some (some rest.length) := by
    simp only [evV,sfx_suffix hs,Shallot.stripPrefix?,Shallot.beqChar]; rfl
  simp only [MutualFieldExamples.actuals,RecursiveFieldExamples.actuals]
  rw [evPar_cons_ok hscan,evPar_cons_ok (evV_seq_ok hscan |>.trans hb),evPar_nil]
  simp only [pre_eq (x:=x) ⟨[],rfl⟩ hs,pre_eq (x:=x) ⟨[],rfl⟩ hx,MutualFieldExamples.words,RecursiveFieldExamples.words]

theorem source_and_target_all_trees (n depth : Nat) :
    evV original (treeF n depth) .callByValuePar (tblV original (treeF n depth) .callByValuePar (2*depth+1)) [] root
      (treeF n depth).length=some (some 0) ∧
    evV generated (treeF n depth) .callByValueSeq (tblV generated (treeF n depth) .callByValueSeq (2*depth+1)) []
      generatedRoot (treeF n depth).length=some (some 0) := by
  obtain ⟨tail,htail⟩ := firstF n depth []
  have hx : treeF n depth=long n++tail := by simpa using htail
  have hc := initial_captures (treeF n depth) (tblV original (treeF n depth) .callByValuePar (2*depth+1)) n tail hx
  have hr := f_rows_all_depths depth n (treeF n depth) [] (treeF n depth).length (Nat.le_refl _)
    (by simp only [sfx_self,List.append_nil])
  have hrow : ruleAtM original.rules 0=some ⟨2,TupleFieldTransfer.sourceBody '#' pattern bodyF⟩ := rfl
  have hcall : evV original (treeF n depth) .callByValuePar (tblV original (treeF n depth) .callByValuePar (2*depth+1)) []
      (.call 0 MutualFieldExamples.actuals) (treeF n depth).length=some (some 0) := by
    rw [evV_call_par hrow rfl (by decide),hc]
    exact hr
  have hs : evV original (treeF n depth) .callByValuePar (tblV original (treeF n depth) .callByValuePar (2*depth+1)) [] root
      (treeF n depth).length=some (some 0) := by
    rw [root,evV_seq_ok hcall]
    simp [evV,sfx]
  exact ⟨hs,(every_input_every_clock (treeF n depth) (2*depth+1)).symm.trans hs⟩

end Shallot.MacroPeg.CBV.MutualFieldProofs
