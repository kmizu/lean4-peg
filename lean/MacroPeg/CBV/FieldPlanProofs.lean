import MacroPeg.CBV.FieldPlanExamples

namespace Shallot.MacroPeg.CBV.FieldPlanProofs
open FieldPlanExamples
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

private theorem word_at (x : List Char) (T : ClockFreezing.Table)
    (E : List (List Char)) (e : MExp) (he : WordArguments.Word e) (w rest : List Char)
    (hv : WordArguments.value E e=some w) (p : Nat) (hx : sfx x p=w++rest) :
    evV original x .callByValuePar T E e p=some (some rest.length) := by
  rw [WordArguments.word_eval original x .callByValuePar T E e he p,hv,WordArguments.literal]
  simp only [evV,(CBVtoCBN.stripPrefix_exact _ _ _).mpr hx]

private theorem encoded (n slot : Nat) (hs : slot<2) (d : Char) :
    encode d [word n,word n] [slot]=word n++[d] := by
  have : slot=0 ∨ slot=1 := by omega
  rcases this with rfl|rfl <;> simp [encode]

private theorem anchor (x : List Char) (T : ClockFreezing.Table) (n slot : Nat) (hs : slot<2)
    (d : Char) (after : List Char) (p : Nat) (hp : p≤x.length) (hx : sfx x p=word n++d::after) :
    evV original x .callByValuePar T [word n,word n] (compile d (sourceParts d [slot])) p=some (some after.length) := by
  rw [compile_eval _ _ _ _ _ _ _ _ hp,RecapturedCopyBlock.source_run]
  · rw [encoded n slot hs d,(CBVtoCBN.stripPrefix_exact _ _ _).mpr (by simpa only [List.append_assoc,List.singleton_append] using hx)]; rfl
  · intro i hi; simp only [List.mem_singleton] at hi; subst i; simpa using hs

private theorem marker_mismatch (w rest : List Char) (c d : Char) (hne : c≠d) :
    Shallot.stripPrefix? (w++[d]) (w++c::rest)=none := by
  cases h : Shallot.stripPrefix? (w++[d]) (w++c::rest) with
  | none => rfl
  | some tail =>
    have he := (CBVtoCBN.stripPrefix_exact _ _ _).mp h
    have hh : c::rest=d::tail := List.append_cancel_left (as:=w) (by simpa only [List.append_assoc,List.singleton_append] using he)
    exact False.elim (hne (List.cons.inj hh).1)

private theorem wrong_anchor (x : List Char) (T : ClockFreezing.Table) (n slot : Nat) (hs : slot<2)
    (c d : Char) (hne : c≠d) (after : List Char) (p : Nat) (hp : p≤x.length) (hx : sfx x p=word n++c::after) :
    evV original x .callByValuePar T [word n,word n] (compile d (sourceParts d [slot])) p=some none := by
  rw [compile_eval _ _ _ _ _ _ _ _ hp,RecapturedCopyBlock.source_run]
  · rw [encoded n slot hs d,hx,marker_mismatch _ _ c d hne]; rfl
  · intro i hi; simp only [List.mem_singleton] at hi; subst i; simpa using hs

theorem fresh_doubled_tuple (x : List Char) (T : ClockFreezing.Table) (n : Nat)
    (rest : List Char) (p : Nat) (hp : p≤x.length) (hx : sfx x p=word (2*n)++rest) :
    evParArgs original x .callByValuePar T [word n,word n] [doubled,doubled] p=some (some [word (2*n),word (2*n)]) := by
  have hv : WordArguments.value [word n,word n] doubled=some (word (2*n)) := by
    simp [WordArguments.value,doubled,word,Nat.two_mul]
  have ha := word_at x T [word n,word n] doubled ⟨True.intro,True.intro⟩ _ rest hv p hx
  have he : pre x p rest.length=word (2*n) := by
    simpa only [length_sfx x hp] using pre_eq (sfx_is_suffix x p) hx
  rw [evPar_cons_ok ha,evPar_cons_ok ha,evPar_nil,he]

/-- At the base, the first branch fails at '#'; the second branch reads
slot 1. Recursively, the first branch reads only slot 0, creates two fresh
doubled actuals and uses its parent's slot 0 again after return. -/
theorem producer_rows (depth extra : Nat) : ∀ n (x rest : List Char) p,
    p≤x.length → sfx x p=tree n depth++rest →
    valAt (tblV original x .callByValuePar (depth+extra+1) 0 [word n,word n]) p=some (some rest.length) := by
  induction depth with
  | zero =>
    intro n x rest p hp hx
    let after := '?'::(word n++rest)
    have hs : sfx x p=word n++'@'::after := by simpa [tree,after,List.append_assoc] using hx
    have he := endpoint x p (word n++['@']) after (by simpa only [List.append_assoc,List.singleton_append] using hs)
    have hfirst : evV original x .callByValuePar (tblV original x .callByValuePar extra) [word n,word n]
        (FieldPlanSyntax.sourceLeaf parts 0) p=some none :=
      evV_seq_fail (wrong_anchor x _ n 0 (by decide) '@' '#' (by decide) after p hp hs)
    have hmark := word_at x (tblV original x .callByValuePar extra) [word n,word n] (.lit ['?']) True.intro
      ['?'] (word n++rest) rfl after.length he.1
    have hew := endpoint x after.length ['?'] (word n++rest) he.1
    have hvalue := word_at x (tblV original x .callByValuePar extra) [word n,word n] (.param 1) True.intro
      (word n) rest rfl (word n++rest).length hew.1
    have hsecond : evV original x .callByValuePar (tblV original x .callByValuePar extra) [word n,word n]
        (FieldPlanSyntax.sourceLeaf parts 1) p=some (some rest.length) := by
      change evV original x .callByValuePar _ _ (TupleFieldTransfer.sourceBody '@' [1] secondTail) p=_
      rw [TupleFieldTransfer.sourceBody,evV_seq_ok (anchor x _ n 1 (by decide) '@' after p hp hs),
        secondTail,evV_seq_ok hmark]
      exact hvalue
    rw [show 0+extra+1=extra+1 by omega,valAt_tblV_succ (show ruleAtM original.rules 0=some
      ⟨2,mainPlan.exp (FieldPlanSyntax.sourceLeaf parts)⟩ from rfl) _ hp,ReplayControlFusion.Plan.exp_eval]
    simp only [mainPlan,ReplayControlFusion.Plan.eval,ReplayFallbackFusion.orElse,hfirst,hsecond]
  | succ depth ih =>
    intro n x rest p hp hx
    let afterReturn := word n++rest
    let afterChild := ')'::afterReturn
    let childInput := tree (2*n) depth++afterChild
    let after := '('::childInput
    have hs : sfx x p=word n++'#'::after := by simpa [tree,after,childInput,afterChild,afterReturn,List.append_assoc] using hx
    have he := endpoint x p (word n++['#']) after (by simpa only [List.append_assoc,List.singleton_append] using hs)
    have hopen := word_at x (tblV original x .callByValuePar (depth+extra+1)) [word n,word n] (.lit ['(']) True.intro
      ['('] childInput rfl after.length he.1
    have hec := endpoint x after.length ['('] childInput he.1
    have hstart : ∃ c tail, tree (2*n) depth++afterChild=word (2*n)++c::tail := by
      cases depth with
      | zero => exact ⟨'@','?'::(word (2*n)++afterChild),by simp [tree,List.append_assoc]⟩
      | succ d => exact ⟨'#','('::(tree (2*(2*n)) d++')'::(word (2*n)++afterChild)),by simp [tree,List.append_assoc]⟩
    obtain ⟨c,tail,ht⟩ := hstart
    have hc := fresh_doubled_tuple x (tblV original x .callByValuePar (depth+extra+1)) n (c::tail)
      childInput.length hec.2 (hec.1.trans ht)
    have hcall : evV original x .callByValuePar (tblV original x .callByValuePar (depth+extra+1)) [word n,word n]
        (.call 0 [doubled,doubled]) childInput.length=some (some afterChild.length) := by
      rw [evV_call_par (show ruleAtM original.rules 0=some ⟨2,mainPlan.exp (FieldPlanSyntax.sourceLeaf parts)⟩ from rfl)
        rfl (by decide),hc]
      exact ih (2*n) x afterChild childInput.length hec.2 hec.1
    have her := endpoint x childInput.length (tree (2*n) depth) afterChild hec.1
    have hclose := word_at x (tblV original x .callByValuePar (depth+extra+1)) [word n,word n] (.lit [')']) True.intro
      [')'] afterReturn rfl afterChild.length her.1
    have hep := endpoint x afterChild.length [')'] afterReturn her.1
    have hparent := word_at x (tblV original x .callByValuePar (depth+extra+1)) [word n,word n] (.param 0) True.intro
      (word n) rest rfl afterReturn.length hep.1
    have hfirst : evV original x .callByValuePar (tblV original x .callByValuePar (depth+extra+1)) [word n,word n]
        (FieldPlanSyntax.sourceLeaf parts 0) p=some (some rest.length) := by
      change evV original x .callByValuePar _ _ (TupleFieldTransfer.sourceBody '#' [0] firstTail) p=_
      rw [TupleFieldTransfer.sourceBody,evV_seq_ok (anchor x _ n 0 (by decide) '#' after p hp hs),firstTail,
        evV_alt_fail (evV_seq_fail (show evV original x .callByValuePar _ [word n,word n] (.lit ['!']) after.length=some none by
          simp only [evV,he.1]; rfl)),evV_seq_ok hopen,evV_seq_ok hcall,evV_seq_ok hclose]
      exact hparent
    rw [show depth+1+extra+1=(depth+extra+1)+1 by omega,valAt_tblV_succ (show ruleAtM original.rules 0=some
      ⟨2,mainPlan.exp (FieldPlanSyntax.sourceLeaf parts)⟩ from rfl) _ hp,ReplayControlFusion.Plan.exp_eval]
    simp only [mainPlan,ReplayControlFusion.Plan.eval,ReplayFallbackFusion.orElse,hfirst]

private theorem word_copies (n : Nat) : RepeatedWordArguments.copies ['a'] n=word n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [RepeatedWordArguments.copies,word,List.replicate_succ] using congrArg (List.cons 'a') ih

private theorem first_word (n depth : Nat) (rest : List Char) :
    ∃ c tail, Shallot.stripPrefix? ['a'] (c::tail)=none ∧ tree n depth++rest=word n++c::tail := by
  cases depth with
  | zero => exact ⟨'@','?'::(word n++rest),rfl,by simp [tree,List.append_assoc]⟩
  | succ d => exact ⟨'#','('::(tree (2*n) d++')'::(word n++rest)),rfl,by simp [tree,List.append_assoc]⟩

theorem initial_tuple (x : List Char) (T : ClockFreezing.Table) (n : Nat) (c : Char) (rest : List Char)
    (hstop : Shallot.stripPrefix? ['a'] (c::rest)=none) (p : Nat) (hp : p≤x.length)
    (hx : sfx x p=word n++c::rest) :
    evParArgs original x .callByValuePar T [] [actual,actual] p=some (some [word n,word n]) := by
  have hscan : evV original x .callByValuePar T [] actual p=some (some (c::rest).length) := by
    apply RecapturedCopyBlock.literal_copies _ _ _ _ _ ['a'] (by decide) (c::rest) hstop n _ hp
    simpa only [word_copies] using hx
  have he : pre x p (c::rest).length=word n := by
    simpa only [length_sfx x hp] using pre_eq (sfx_is_suffix x p) hx
  rw [evPar_cons_ok hscan,evPar_cons_ok hscan,evPar_nil,he]

theorem producer_result (n depth extra : Nat) (x rest : List Char) (p : Nat)
    (hp : p≤x.length) (hx : sfx x p=tree n depth++rest) :
    evV original x .callByValuePar (tblV original x .callByValuePar (depth+extra+1)) [] producer p=some (some rest.length) := by
  obtain ⟨c,tail,hstop,ht⟩ := first_word n depth rest
  have ha := initial_tuple x (tblV original x .callByValuePar (depth+extra+1)) n c tail hstop p hp (hx.trans ht)
  rw [producer,evV_call_par (show ruleAtM original.rules 0=some ⟨2,mainPlan.exp (FieldPlanSyntax.sourceLeaf parts)⟩ from rfl)
    rfl (by decide),ha]
  exact producer_rows depth extra n x rest p hp hx

theorem outer_capture (n depth : Nat) :
    evParArgs original (sample n depth) .callByValuePar
      (tblV original (sample n depth) .callByValuePar (depth+2)) [] [producer] (sample n depth).length=
        some (some [tree n depth]) := by
  have hx : sfx (sample n depth) (sample n depth).length=tree n depth++'$'::tree n depth := by rw [sfx_self]; rfl
  have hv := producer_result n depth 1 (sample n depth) ('$'::tree n depth) _ (Nat.le_refl _) hx
  have he : pre (sample n depth) (sample n depth).length ('$'::tree n depth).length=tree n depth :=
    pre_eq (x:=sample n depth) ⟨[],rfl⟩ rfl
  rw [show depth+1+1=depth+2 by omega] at hv
  rw [evPar_cons_ok hv,evPar_nil,he]

theorem source_and_generated_all_trees (n depth : Nat) :
    evV original (sample n depth) .callByValuePar (tblV original (sample n depth) .callByValuePar (depth+2)) []
      root (sample n depth).length=some (some 0) ∧
    evV generated (sample n depth) .callByValueSeq (tblV generated (sample n depth) .callByValueSeq (depth+2)) []
      generatedRoot (sample n depth).length=some (some 0) := by
  let x := sample n depth
  have hc : evV original x .callByValuePar (tblV original x .callByValuePar (depth+2)) [] (.call 1 [producer]) x.length=some (some 0) := by
    rw [evV_call_par (show ruleAtM original.rules 1=some ⟨1,TupleFieldTransfer.sourceBody '$' [0] (.param 0)⟩ from rfl)
      rfl (by decide),outer_capture n depth]
    change valAt (tblV original x .callByValuePar (depth+2) 1 [tree n depth]) x.length=some (some 0)
    rw [show depth+2=(depth+1)+1 by omega,valAt_tblV_succ (show ruleAtM original.rules 1=some
      ⟨1,TupleFieldTransfer.sourceBody '$' [0] (.param 0)⟩ from rfl) _ (Nat.le_refl _),TupleFieldTransfer.sourceBody]
    have ha : evV original x .callByValuePar (tblV original x .callByValuePar (depth+1)) [tree n depth]
        (compile '$' (sourceParts '$' [0])) x.length=some (some (tree n depth).length) := by
      rw [compile_eval _ _ _ _ _ _ _ _ (Nat.le_refl _),RecapturedCopyBlock.source_run]
      · have he : encode '$' [tree n depth] [0]=tree n depth++['$'] := by simp [encode]
        rw [he,(CBVtoCBN.stripPrefix_exact _ _ _).mpr (show sfx x x.length=(tree n depth++['$'])++tree n depth by
          rw [sfx_self]; simp only [x,sample,List.append_assoc,List.singleton_append])]; rfl
      · intro i hi; simp only [List.mem_singleton] at hi; subst i; simp
    rw [evV_seq_ok ha]
    exact word_at x _ [tree n depth] (.param 0) True.intro (tree n depth) [] rfl (tree n depth).length
      (by simpa using (endpoint x x.length (tree n depth++['$']) (tree n depth)
        (by rw [sfx_self]; simp only [x,sample,List.append_assoc,List.singleton_append])).1)
  have hs : evV original x .callByValuePar (tblV original x .callByValuePar (depth+2)) [] root x.length=some (some 0) := by
    rw [root,evV_seq_ok hc]
    simp [evV,sfx]
  exact ⟨hs,(every_input_every_clock x (depth+2)).symm.trans hs⟩

theorem outer_capture_length_unbounded (depth n : Nat) : n≤(tree n depth).length := by
  cases depth <;> simp [tree,word,List.length_append,List.length_replicate] <;> omega

end Shallot.MacroPeg.CBV.FieldPlanProofs
