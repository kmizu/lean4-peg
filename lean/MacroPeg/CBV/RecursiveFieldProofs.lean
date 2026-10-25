import MacroPeg.CBV.RecursiveFieldExamples

namespace Shallot.MacroPeg.CBV.RecursiveFieldProofs
open RecursiveFieldExamples DelimiterTemplate DelimitedWordPattern

private theorem endpoint (x : List Char) (p : Nat) (u v : List Char) (hx : sfx x p=u++v) :
    sfx x v.length=v ∧ v.length≤x.length := by
  have hs := suffix_trans (sfx_is_suffix x p) ⟨u,hx⟩
  refine ⟨sfx_suffix hs.choose_spec,?_⟩
  obtain ⟨front,hfront⟩ := hs
  have := congrArg List.length hfront
  simp only [List.length_append] at this
  omega

private theorem anchor (x : List Char) (T : Nat → List (List Char) → Val)
    (n : Nat) (after : List Char) (p : Nat) (hp : p≤x.length) (hx : sfx x p=block n++after) :
    evV original x .callByValuePar T (RecursiveFieldExamples.words n)
      (compile '#' (sourceParts '#' pattern)) p=some (some after.length) := by
  rw [compile_eval _ _ _ _ _ _ _ _ hp,RecapturedCopyBlock.source_run]
  · have hh : Shallot.stripPrefix? (encode '#' (RecursiveFieldExamples.words n) pattern) (sfx x p)=some after :=
      (CBVtoCBN.stripPrefix_exact _ _ _).mpr hx
    rw [hh]; rfl
  · intro i hi; simp only [RecursiveFieldExamples.words,List.length_cons,List.length_nil]; simp [pattern] at hi; omega

private theorem first_word (n : Nat) (depth : Nat) (rest : List Char) :
    ∃ tail, tree n depth++rest=long n++tail := by
  cases depth with
  | zero =>
    refine ⟨'#'::(short n++'#'::(long n++'#'::(short n++'!'::(long n++rest)))),?_⟩
    simp [tree,block,pattern,encode,RecursiveFieldExamples.words,List.append_assoc]
  | succ depth =>
    refine ⟨'#'::(short n++'#'::(long n++'#'::'('::(tree (2*n) depth++')'::(long n++'!'::(short n++rest))))),?_⟩
    simp [tree,block,pattern,encode,RecursiveFieldExamples.words,List.append_assoc]

/-- Every nesting depth executes real fresh binary captures. After the child
returns, both independently retained parent RecursiveFieldExamples.words are available again. -/
theorem row_all_trees (n depth : Nat) : ∀ (x rest : List Char) (p : Nat), p≤x.length →
    sfx x p=tree n depth++rest →
    valAt (tblV original x .callByValuePar (depth+1) 0 (RecursiveFieldExamples.words n)) p=some (some rest.length) := by
  induction depth generalizing n with
  | zero =>
    intro x rest p hp hx
    have hrow : ruleAtM original.rules 0=some ⟨2,TupleFieldTransfer.sourceBody '#' pattern body⟩ := rfl
    rw [valAt_tblV_succ hrow _ hp,TupleFieldTransfer.sourceBody]
    let after := short n++'!'::(long n++rest)
    have hs : sfx x p=block n++after := by simpa only [tree,List.append_assoc,List.cons_append,after] using hx
    have ha := anchor x (tblV original x .callByValuePar 0) n after p hp hs
    have hr := endpoint x p (block n) after hs
    rw [evV_seq_ok ha]
    have hbad : evV original x .callByValuePar (tblV original x .callByValuePar 0) (RecursiveFieldExamples.words n)
        (.lit ['(']) after.length=some none := by
      simp only [evV,hr.1]
      cases n <;> simp [after,short,List.replicate_succ,Shallot.stripPrefix?,Shallot.beqChar]
    rw [body,evV_alt_fail (evV_seq_fail hbad)]
    apply word_at _ _ _ _ _ base ⟨True.intro,True.intro,True.intro⟩ (short n++'!'::long n) rest
    · simp [base,WordArguments.value,RecursiveFieldExamples.words]
    · simpa only [after,List.append_assoc,List.cons_append] using hr.1
  | succ depth ih =>
    intro x rest p hp hx
    have hrow : ruleAtM original.rules 0=some ⟨2,TupleFieldTransfer.sourceBody '#' pattern body⟩ := rfl
    rw [valAt_tblV_succ hrow _ hp,TupleFieldTransfer.sourceBody]
    let back := long n++'!'::(short n++rest)
    let afterChild := ')'::back
    let childInput := tree (2*n) depth++afterChild
    let after := '('::childInput
    have hs : sfx x p=block n++after := by
      simpa only [tree,List.append_assoc,List.cons_append,after,childInput,afterChild,back] using hx
    have ha := anchor x (tblV original x .callByValuePar (depth+1)) n after p hp hs
    have hr := endpoint x p (block n) after hs
    rw [evV_seq_ok ha]
    have hopen := word_at original x .callByValuePar (tblV original x .callByValuePar (depth+1)) (RecursiveFieldExamples.words n)
      (.lit ['(']) True.intro ['('] childInput rfl after.length hr.1
    have hchildpos := endpoint x after.length ['('] childInput hr.1
    obtain ⟨tail,htail⟩ := first_word (2*n) depth afterChild
    have hargs := fresh_child_captures original x .callByValuePar (tblV original x .callByValuePar (depth+1)) n tail
      childInput.length hchildpos.2 (hchildpos.1.trans htail)
    have hchild : evV original x .callByValuePar (tblV original x .callByValuePar (depth+1)) (RecursiveFieldExamples.words n)
        (.call 0 childArgs) childInput.length=some (some afterChild.length) := by
      rw [evV_call_par hrow rfl (by decide),hargs]
      change valAt (tblV original x .callByValuePar (depth+1) 0 (RecursiveFieldExamples.words (2*n))) childInput.length=_
      exact ih (2*n) x afterChild childInput.length hchildpos.2 hchildpos.1
    have hbackpos := endpoint x childInput.length (tree (2*n) depth) afterChild hchildpos.1
    have hclose := word_at original x .callByValuePar (tblV original x .callByValuePar (depth+1)) (RecursiveFieldExamples.words n)
      (.lit [')']) True.intro [')'] back rfl afterChild.length hbackpos.1
    have hreturnpos := endpoint x afterChild.length [')'] back hbackpos.1
    have hreturn : evV original x .callByValuePar (tblV original x .callByValuePar (depth+1)) (RecursiveFieldExamples.words n)
        restore back.length=some (some rest.length) := by
      apply word_at _ _ _ _ _ restore ⟨True.intro,True.intro,True.intro⟩ (long n++'!'::short n) rest
      · simp [restore,WordArguments.value,RecursiveFieldExamples.words]
      · simpa only [back,List.append_assoc,List.cons_append] using hreturnpos.1
    rw [body,evV_alt_ok (evV_seq_ok hopen |>.trans (evV_seq_ok hchild |>.trans (evV_seq_ok hclose |>.trans hreturn)))]

private theorem short_copies (n : Nat) : short n=RepeatedWordArguments.copies ['a'] n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [short,List.replicate_succ,RepeatedWordArguments.copies,List.singleton_append] using congrArg (List.cons 'a') ih

theorem initial_captures (x : List Char) (T : Nat → List (List Char) → Val)
    (n : Nat) (rest : List Char) (hx : x=long n++rest) :
    evParArgs original x .callByValuePar T [] RecursiveFieldExamples.actuals x.length=some (some (RecursiveFieldExamples.words n)) := by
  have hs : x=short n++'b'::rest := by simpa [long,List.append_assoc] using hx
  have hscan : evV original x .callByValuePar T [] (.star (.lit ['a'])) x.length=some (some ('b'::rest).length) := by
    apply RecapturedCopyBlock.literal_copies _ _ _ _ _ ['a'] (by decide) ('b'::rest)
      (by simp [Shallot.stripPrefix?,Shallot.beqChar]) n _ (Nat.le_refl _)
    simpa only [sfx_self,←short_copies] using hs
  have hb : evV original x .callByValuePar T [] (.lit ['b']) ('b'::rest).length=some (some rest.length) := by
    simp only [evV,sfx_suffix hs,Shallot.stripPrefix?,Shallot.beqChar]
    rfl
  rw [RecursiveFieldExamples.actuals,evPar_cons_ok hscan,evPar_cons_ok (evV_seq_ok hscan |>.trans hb),evPar_nil]
  simp only [pre_eq (x:=x) ⟨[],rfl⟩ hs,pre_eq (x:=x) ⟨[],rfl⟩ hx,RecursiveFieldExamples.words]

theorem source_and_target_all_trees (n depth : Nat) :
    evV original (tree n depth) .callByValuePar (tblV original (tree n depth) .callByValuePar (depth+1)) [] root (tree n depth).length=some (some 0) ∧
    evV generated (tree n depth) .callByValueSeq (tblV generated (tree n depth) .callByValueSeq (depth+1)) [] generatedRoot (tree n depth).length=some (some 0) := by
  have hrow : ruleAtM original.rules 0=some ⟨2,TupleFieldTransfer.sourceBody '#' pattern body⟩ := rfl
  obtain ⟨rest,hrest⟩ := first_word n depth []
  have hx : tree n depth=long n++rest := by simpa using hrest
  have hcap := initial_captures (tree n depth) (tblV original (tree n depth) .callByValuePar (depth+1)) n rest hx
  have hr := row_all_trees n depth (tree n depth) [] (tree n depth).length (Nat.le_refl _) (by simp only [sfx_self,List.append_nil])
  have hcall : evV original (tree n depth) .callByValuePar (tblV original (tree n depth) .callByValuePar (depth+1)) []
      (.call 0 RecursiveFieldExamples.actuals) (tree n depth).length=some (some 0) := by
    rw [evV_call_par hrow rfl (by decide),hcap]
    exact hr
  have hsource : evV original (tree n depth) .callByValuePar (tblV original (tree n depth) .callByValuePar (depth+1)) [] root (tree n depth).length=some (some 0) := by
    rw [root,evV_seq_ok hcall]
    simp [evV,sfx]
  exact ⟨hsource,(every_input_every_clock _ _).symm.trans hsource⟩

end Shallot.MacroPeg.CBV.RecursiveFieldProofs
