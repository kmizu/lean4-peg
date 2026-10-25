import MacroPeg.CBV.NestedFieldProducer

namespace Shallot.MacroPeg.CBV.NestedFieldProducerProofs
open NestedFieldProducer
open DelimiterTemplate (compile compile_eval)
open DelimitedWordPattern (sourceParts encode)

def word (n : Nat) : List Char := List.replicate n 'a'
def block (n : Nat) : List Char := word n++['#']
def tree (n : Nat) : Nat → List Char
  | 0 => block n++'!'::word n
  | depth+1 => block n++(tree (2*n) depth++word n)
def sample (n depth : Nat) : List Char := tree n depth++'@'::tree n depth

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
    evV source x .callByValuePar T E e p=some (some rest.length) := by
  rw [WordArguments.word_eval source x .callByValuePar T E e he p,hv,WordArguments.literal]
  simp only [evV,(CBVtoCBN.stripPrefix_exact _ _ _).mpr hx]

private theorem anchor (x : List Char) (T : ClockFreezing.Table)
    (n : Nat) (after : List Char) (p : Nat) (hp : p≤x.length) (hx : sfx x p=block n++after) :
    evV source x .callByValuePar T [word n] (compile '#' (sourceParts '#' [0])) p=some (some after.length) := by
  rw [compile_eval _ _ _ _ _ _ _ _ hp,RecapturedCopyBlock.source_run]
  · have he : encode '#' [word n] [0]=block n := by simp [encode,block]
    rw [he,(CBVtoCBN.stripPrefix_exact _ _ _).mpr hx]; rfl
  · intro i hi; simp only [List.mem_singleton] at hi; subst i; simp

private theorem first_word (n depth : Nat) (rest : List Char) :
    ∃ tail, tree n depth++rest=word n++'#'::tail := by
  cases depth with
  | zero => exact ⟨'!'::(word n++rest),by simp [tree,block,List.append_assoc]⟩
  | succ depth => exact ⟨tree (2*n) depth++(word n++rest),by simp [tree,block,List.append_assoc]⟩

private theorem not_leaf (n depth : Nat) (rest : List Char) :
    Shallot.stripPrefix? ['!'] (tree n depth++rest)=none := by
  cases depth <;> cases n <;> rfl

theorem doubled_capture (x : List Char) (T : ClockFreezing.Table) (n : Nat)
    (rest : List Char) (p : Nat) (hp : p≤x.length) (hx : sfx x p=word (2*n)++rest) :
    evParArgs source x .callByValuePar T [word n] [doubled] p=some (some [word (2*n)]) := by
  have hv : WordArguments.value [word n] doubled=some (word (2*n)) := by
    simp [WordArguments.value,doubled,word,Nat.two_mul]
  have ha := word_at x T [word n] doubled ⟨True.intro,True.intro⟩ _ rest hv p hx
  have he : pre x p rest.length=word (2*n) := by
    simpa only [length_sfx x hp] using pre_eq (sfx_is_suffix x p) hx
  rw [evPar_cons_ok ha,evPar_nil,he]

/-- The actual recursive source rows, for every initial length, recursive
depth, extra clock, original input position and trailing string. Each child
gets a newly doubled word; after it returns the parent replays its own word. -/
theorem producer_rows (depth extra : Nat) : ∀ n (x rest : List Char) p,
    p≤x.length → sfx x p=tree n depth++rest →
    valAt (tblV source x .callByValuePar (depth+extra+1) 0 [word n]) p=some (some rest.length) := by
  induction depth with
  | zero =>
    intro n x rest p hp hx
    let after := '!'::(word n++rest)
    have hs : sfx x p=block n++after := by simpa [tree,after,List.append_assoc] using hx
    have he := endpoint x p (block n) after hs
    rw [show 0+extra+1=extra+1 by omega,valAt_tblV_succ (show ruleAtM source.rules 0=some
      ⟨1,TupleFieldTransfer.sourceBody '#' [0] producerBody⟩ from rfl) _ hp,
      TupleFieldTransfer.sourceBody,evV_seq_ok (anchor x _ n after p hp hs)]
    have hmark := word_at x (tblV source x .callByValuePar extra) [word n] (.lit ['!']) True.intro
      ['!'] (word n++rest) rfl after.length he.1
    have hew := endpoint x after.length ['!'] (word n++rest) he.1
    have hvalue := word_at x (tblV source x .callByValuePar extra) [word n] (.param 0) True.intro
      (word n) rest rfl (word n++rest).length hew.1
    rw [producerBody,evV_alt_ok (show evV source x .callByValuePar _ [word n] leaf after.length=
      some (some rest.length) from (evV_seq_ok hmark).trans hvalue)]
  | succ depth ih =>
    intro n x rest p hp hx
    let afterChild := word n++rest
    let after := tree (2*n) depth++afterChild
    have hs : sfx x p=block n++after := by simpa [tree,after,afterChild,List.append_assoc] using hx
    have he := endpoint x p (block n) after hs
    rw [show depth+1+extra+1=(depth+extra+1)+1 by omega,valAt_tblV_succ (show ruleAtM source.rules 0=some
      ⟨1,TupleFieldTransfer.sourceBody '#' [0] producerBody⟩ from rfl) _ hp,
      TupleFieldTransfer.sourceBody,evV_seq_ok (anchor x _ n after p hp hs)]
    have hleaf : evV source x .callByValuePar (tblV source x .callByValuePar (depth+extra+1))
        [word n] leaf after.length=some none := by
      apply evV_seq_fail
      simp only [evV,he.1,after,not_leaf]
    obtain ⟨tail,ht⟩ := first_word (2*n) depth afterChild
    have hc := doubled_capture x (tblV source x .callByValuePar (depth+extra+1)) n ('#'::tail)
      after.length he.2 (he.1.trans ht)
    have hcall : evV source x .callByValuePar (tblV source x .callByValuePar (depth+extra+1))
        [word n] (.call 0 [doubled]) after.length=some (some afterChild.length) := by
      rw [evV_call_par (show ruleAtM source.rules 0=some ⟨1,TupleFieldTransfer.sourceBody '#' [0] producerBody⟩ from rfl)
        rfl (by decide),hc]
      exact ih (2*n) x afterChild after.length he.2 he.1
    have hew := endpoint x after.length (tree (2*n) depth) afterChild he.1
    rw [producerBody,evV_alt_fail hleaf,evV_seq_ok hcall]
    exact word_at x _ [word n] (.param 0) True.intro (word n) rest rfl afterChild.length hew.1

private theorem word_copies (n : Nat) : RepeatedWordArguments.copies ['a'] n=word n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [RepeatedWordArguments.copies,word,List.replicate_succ] using congrArg (List.cons 'a') ih

theorem initial_captures (x : List Char) (T : ClockFreezing.Table) (n : Nat)
    (rest : List Char) (p : Nat) (hp : p≤x.length) (hx : sfx x p=word n++'#'::rest) :
    evParArgs source x .callByValuePar T [] [actual] p=some (some [word n]) := by
  have hscan : evV source x .callByValuePar T [] actual p=some (some ('#'::rest).length) := by
    apply RecapturedCopyBlock.literal_copies _ _ _ _ _ ['a'] (by decide) ('#'::rest)
      (by simp [Shallot.stripPrefix?,Shallot.beqChar]) n _ hp
    simpa only [word_copies] using hx
  have he : pre x p ('#'::rest).length=word n := by
    simpa only [length_sfx x hp] using pre_eq (sfx_is_suffix x p) hx
  rw [evPar_cons_ok hscan,evPar_nil,he]

theorem producer_result (n depth extra : Nat) (x rest : List Char) (p : Nat)
    (hp : p≤x.length) (hx : sfx x p=tree n depth++rest) :
    evV source x .callByValuePar (tblV source x .callByValuePar (depth+extra+1)) [] producer p=
      some (some rest.length) := by
  obtain ⟨tail,ht⟩ := first_word n depth rest
  have ha := initial_captures x (tblV source x .callByValuePar (depth+extra+1)) n tail p hp (hx.trans ht)
  rw [producer,evV_call_par (show ruleAtM source.rules 0=some ⟨1,TupleFieldTransfer.sourceBody '#' [0] producerBody⟩ from rfl)
    rfl (by decide),ha]
  exact producer_rows depth extra n x rest p hp hx

theorem outer_capture (n depth : Nat) :
    evParArgs source (sample n depth) .callByValuePar
      (tblV source (sample n depth) .callByValuePar (depth+2)) [] [producer] (sample n depth).length=
        some (some [tree n depth]) := by
  have hx : sfx (sample n depth) (sample n depth).length=tree n depth++'@'::tree n depth := by rw [sfx_self]; rfl
  have hv := producer_result n depth 1 (sample n depth) ('@'::tree n depth) _ (Nat.le_refl _) hx
  have he : pre (sample n depth) (sample n depth).length ('@'::tree n depth).length=tree n depth := by
    exact pre_eq (x:=sample n depth) ⟨[],rfl⟩ (show sample n depth=tree n depth++'@'::tree n depth from rfl)
  rw [show depth+1+1=depth+2 by omega] at hv
  rw [evPar_cons_ok hv,evPar_nil,he]

theorem source_and_target_all_trees (n depth : Nat) :
    evV source (sample n depth) .callByValuePar (tblV source (sample n depth) .callByValuePar (depth+2)) []
      root (sample n depth).length=some (some 0) ∧
    evV target (sample n depth) .callByValueSeq (tblV target (sample n depth) .callByValueSeq (depth+2)) []
      generatedRoot (sample n depth).length=some (some 0) := by
  let x := sample n depth
  have hc : evV source x .callByValuePar (tblV source x .callByValuePar (depth+2)) []
      (.call 1 [producer]) x.length=some (some 0) := by
    rw [evV_call_par (show ruleAtM source.rules 1=some ⟨1,TupleFieldTransfer.sourceBody '@' [0] (.param 0)⟩ from rfl)
      rfl (by decide),outer_capture n depth]
    change valAt (tblV source x .callByValuePar (depth+2) 1 [tree n depth]) x.length=some (some 0)
    rw [show depth+2=(depth+1)+1 by omega,
      valAt_tblV_succ (show ruleAtM source.rules 1=some ⟨1,TupleFieldTransfer.sourceBody '@' [0] (.param 0)⟩ from rfl)
      _ (Nat.le_refl _),TupleFieldTransfer.sourceBody]
    have hanchor : evV source x .callByValuePar (tblV source x .callByValuePar (depth+1)) [tree n depth]
        (compile '@' (sourceParts '@' [0])) x.length=some (some (tree n depth).length) := by
      rw [compile_eval _ _ _ _ _ _ _ _ (Nat.le_refl _),RecapturedCopyBlock.source_run]
      · have he : encode '@' [tree n depth] [0]=tree n depth++['@'] := by simp [encode]
        rw [he,(CBVtoCBN.stripPrefix_exact _ _ _).mpr (show sfx x x.length=(tree n depth++['@'])++tree n depth by
          rw [sfx_self]; simp only [x,sample,List.append_assoc,List.singleton_append])]; rfl
      · intro i hi; simp only [List.mem_singleton] at hi; subst i; simp
    rw [evV_seq_ok hanchor]
    exact word_at x _ [tree n depth] (.param 0) True.intro (tree n depth) [] rfl (tree n depth).length
      (by simpa using (endpoint x x.length (tree n depth++['@']) (tree n depth)
        (by rw [sfx_self]; simp only [x,sample,List.append_assoc,List.singleton_append])).1)
  have hs : evV source x .callByValuePar (tblV source x .callByValuePar (depth+2)) [] root x.length=some (some 0) := by
    rw [root,evV_seq_ok hc]
    simp [evV,sfx]
  exact ⟨hs,(physical x (depth+2)).symm.trans hs⟩

theorem capture_length_unbounded (depth n : Nat) : n≤(tree n depth).length := by
  cases depth <;> simp [tree,block,word,List.length_append,List.length_replicate] <;> omega

theorem direct_generated_runs :
    ([0,1,2].flatMap (fun n => [0,1,2].map (fun depth => (n,depth)))).all (fun (n,depth) =>
      evV target (sample n depth) .callByValueSeq (tblV target (sample n depth) .callByValueSeq (depth+2)) []
        generatedRoot (sample n depth).length==some (some 0))=true := by decide +kernel

theorem wrong_outer_word_rejected :
    evV target (tree 1 1++'@'::tree 2 1) .callByValueSeq
      (tblV target (tree 1 1++'@'::tree 2 1) .callByValueSeq 4) [] generatedRoot
      (tree 1 1++'@'::tree 2 1).length=some none := by decide +kernel

theorem fresh_child_does_not_replace_parent :
    evV target ['a','#','a','a','#','!','a','a','a','a','@','a','#','a','a','#','!','a','a','a','a']
      .callByValueSeq
      (tblV target ['a','#','a','a','#','!','a','a','a','a','@','a','#','a','a','#','!','a','a','a','a']
        .callByValueSeq 4) [] generatedRoot 21=some none := by decide +kernel

theorem undefined_actual_stays_undefined (x : List Char) (k : Nat) :
    evV source x .callByValuePar (tblV source x .callByValuePar k) [] (.call 0 [.star .eps]) x.length=none ∧
    evV target x .callByValueSeq (tblV target x .callByValueSeq k) []
      (TupleFieldTransfer.head 0 1 '#' [0] [.star .eps]) x.length=none := by
  have he : evV source x .callByValuePar (tblV source x .callByValuePar k) [] (.star .eps) x.length=none :=
    evStar_stuck rfl (Nat.lt_irrefl _)
  have hs : evV source x .callByValuePar (tblV source x .callByValuePar k) [] (.call 0 [.star .eps]) x.length=none := by
    rw [evV_call_par (show ruleAtM source.rules 0=some ⟨1,TupleFieldTransfer.sourceBody '#' [0] producerBody⟩ from rfl)
      rfl (by decide),evPar_cons_none he]
  have ht := producer_call x k [] (.star .eps) (.star .eps) (by repeat constructor) x.length (Nat.le_refl _) rfl
    (by intro q hq; rw [he] at hq; cases hq)
  exact ⟨hs,ht.symm.trans hs⟩

def tupleGrammar : MGrammar := ⟨[⟨2,.seq (.param 0) (.param 1)⟩]⟩
def tupleSignatures : List CaptureAlphabetEffects.Signature := [⟨[['a'],['b']],['a','b']⟩]
theorem parameter_alphabets_are_independent :
    CaptureAlphabetEffects.grammarCheck tupleGrammar tupleSignatures=true ∧
    CaptureAlphabetEffects.check tupleSignatures [] ['a','b'] (.call 0 [.lit ['a'],.lit ['b']])=true ∧
    CaptureAlphabetEffects.check tupleSignatures [] ['a','b'] (.call 0 [.lit ['b'],.lit ['a']])=false ∧
    CaptureAlphabetEffects.grammarCheck tupleGrammar [⟨[['a'],['b']],['a']⟩]=false := by decide +kernel

theorem producer_separators_cannot_be_erased_from_effects :
    CaptureAlphabetEffects.grammarCheck source [⟨[['a']],['a','!']⟩,⟨[['a','#','!']],['a','#','!','@']⟩]=false ∧
    CaptureAlphabetEffects.check signatures [] ['a','!'] producer=false ∧
    CaptureAlphabetEffects.check signatures [] [] (.notP (.star .eps))=true := by decide +kernel

def discarder : MGrammar := ⟨[⟨1,.eps⟩]⟩
/-- The certified effect is specifically the Par result. Reusing it for
Seq would wrongly forget the positive text consumed by actual evaluation. -/
theorem actual_output_is_not_the_par_call_output :
    CaptureAlphabetEffects.grammarCheck discarder [⟨[['a']],[]⟩]=true ∧
    CaptureAlphabetEffects.check [⟨[['a']],[]⟩] [] [] (.call 0 [.lit ['a']])=true ∧
    evV discarder ['a'] .callByValuePar (tblV discarder ['a'] .callByValuePar 1) [] (.call 0 [.lit ['a']]) 1=some (some 1) ∧
    evV discarder ['a'] .callByValueSeq (tblV discarder ['a'] .callByValueSeq 1) [] (.call 0 [.lit ['a']]) 1=some (some 0) := by decide +kernel

end Shallot.MacroPeg.CBV.NestedFieldProducerProofs
