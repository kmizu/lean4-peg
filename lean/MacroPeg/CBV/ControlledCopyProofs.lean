import MacroPeg.CBV.ControlledCopyExamples

namespace Shallot.MacroPeg.CBV.ControlledCopyProofs
open RetainedPatternSyntax
open ControlledCopySyntax
open ConsumingPatternExamples (producer tail copying)
open ControlledCopyExamples
open DelimiterTemplate (Part)
private abbrev pattern := ConsumingPatternExamples.pattern

private def baseBodies := [FiniteResidualControl.balancedBody,FiniteResidualControl.consumePrefix]
private theorem base_valid : RecursiveParserStability.Valid baseBodies := by
  intro e he
  exact DelimitedCopySyntax.lexical_checked 2 e (List.all_eq_true.mp (show baseBodies.all (DelimitedCopySyntax.lexicalCheck 2)=true from by decide +kernel) e he)

private theorem base_source : RecursiveParserStability.Installed baseBodies original := by
  intro i b hi
  cases i with
  | zero => have hb : b=FiniteResidualControl.balancedBody := by simpa [baseBodies] using hi.symm
            subst b; rfl
  | succ i => cases i with
    | zero => have hb : b=FiniteResidualControl.consumePrefix := by simpa [baseBodies] using hi.symm
              subst b; rfl
    | succ i => simp [baseBodies] at hi

private theorem base_old : RecursiveParserStability.Installed baseBodies DelimitedCopyExamples.original := by
  intro i b hi
  cases i with
  | zero => have hb : b=FiniteResidualControl.balancedBody := by simpa [baseBodies] using hi.symm
            subst b; rfl
  | succ i => cases i with
    | zero => have hb : b=FiniteResidualControl.consumePrefix := by simpa [baseBodies] using hi.symm
              subst b; rfl
    | succ i => simp [baseBodies] at hi

private theorem base_query (i : Nat) (hi : i<2) (x : List Char) (k p : Nat) (hp : p≤x.length) :
    evV original x .callByValuePar (tblV original x .callByValuePar k) [] (.call i []) p=
      evV DelimitedCopyExamples.original x .callByValuePar (tblV DelimitedCopyExamples.original x .callByValuePar k) [] (.call i []) p :=
  RecursiveParserStability.lexical_eval base_source base_old x _ _ _ _ (tblV_ok _ _ _ k)
    (fun j hj q hq => congrArg (fun row => valAt row q) (RecursiveParserStability.helper_rows_eq base_valid base_source base_old x _ _ k j hj [] [])) [] [] (.call i []) hi p hp

private theorem base_observations (i : Nat) (hi : i<2) (x : List Char) (rest : Option (List Char)) :
    SObs original .callByValuePar (.call i []) x rest ↔ SObs DelimitedCopyExamples.original .callByValuePar (.call i []) x rest := by
  have hold := DelimitedCopySyntax.source_firstOrder DelimitedCopyExamples.bodies DelimitedCopyExamples.d
    (DelimitedCopyCompiler.checked DelimitedCopyExamples.original DelimitedCopyExamples.originalRoot
      DelimitedCopyExamples.bodies DelimitedCopyExamples.alphabet DelimitedCopyExamples.d DelimitedCopyExamples.entry DelimitedCopyExamples.checked).1
  have hnew : original.FirstOrder := source_firstOrder bodies clients arity d body base_valid
  have hold : DelimitedCopyExamples.original.FirstOrder := hold
  rw [←decideObsV_iff hnew (by decide) (show (MExp.call i []).FirstOrder from True.intro),
    ←decideObsV_iff hold (by decide) (show (MExp.call i []).FirstOrder from True.intro)]
  unfold decideObsV
  rw [ScannerPairFusion.stable_result_eq _ _ x _ _ _ _ (fun k => base_query i hi x k x.length (Nat.le_refl _))]

private theorem observed (e : MExp) (he : e.FirstOrder) (x rest : List Char) (k : Nat)
    (hs : ∃ a, x=a++rest)
    (hv : evV original x .callByValuePar (tblV original x .callByValuePar k) [] e x.length=some (some rest.length)) :
    SObs original .callByValuePar e x (some rest) := by
  obtain ⟨o,hd,ho⟩ := evV_sound (by decide) (tblV_sound (source_firstOrder bodies clients arity d body base_valid) (by decide) k) e he _ (Nat.le_refl _) _ hv
  obtain ⟨t,actual,rfl,hlen⟩ := obsR_ok ho
  have hre : actual=rest := by
    have hh := rest_eq_sfx' hd
    rw [hlen] at hh
    exact hh.symm.trans (sfx_suffix hs.choose_spec)
  subst actual
  exact ⟨_,by simpa only [sfx_self,original] using hd,rfl⟩

private def bound (w : List Char) (e : RetainedPatternSyntax.Expr) :=
  MExp.subst [.lit w] (render bodies.length clients.length true e)

private theorem literal (w rest : List Char) : SObs original .callByValuePar (.lit w) (w++rest) (some rest) :=
  ⟨_,.litOk w (w++rest) rest ((CBVtoCBN.stripPrefix_exact _ _ _).mpr rfl),rfl⟩

private theorem enter_user (i : Nat) (e : RetainedPatternSyntax.Expr) (hi : clients[i]?=some e)
    (a : MExp) (w input middle rest : List Char) (hx : input=w++middle)
    (ha : SObs original .callByValuePar a input (some middle))
    (hb : SObs original .callByValuePar (bound w e) middle (some rest)) :
    SObs original .callByValuePar (.call (bodies.length+i) [a]) input (some rest) := by
  obtain ⟨oa,hda,hoa⟩ := ha
  obtain ⟨ta,rfl⟩ := restOf_eq_some hoa
  have hargs : DerivesArgsPar original .callByValuePar input [a] [.lit w] := .cons _ _ _ _ _ ta [] hda hx (.nil _)
  have hbody : SObs original .callByValuePar (MExp.subst [.lit w] (.seq (.param 0) (render bodies.length clients.length true e))) input (some rest) := by
    rw [hx]
    exact RootObservation.seq_ok (literal w middle) hb
  obtain ⟨o,hd,ho⟩ := hbody
  obtain ⟨t,rfl⟩ := restOf_eq_some ho
  exact ⟨_,.callParOk (bodies.length+i) [a] ⟨1,.seq (.param 0) (render bodies.length clients.length true e)⟩ input rest [.lit w] t
    rfl (source_user bodies clients arity d body i e hi) rfl hargs hd,rfl⟩

private theorem many_a (n : Nat) (c : Char) (hc : c≠'a') : ∀ rest, ∃ t,
    MDerives original .callByValuePar (.star (.chr 'a')) (List.replicate n 'a'++c::rest) (.ok t (c::rest)) := by
  induction n with
  | zero =>
    intro rest
    exact ⟨_,.starNil _ _ (.chrFail 'a' c rest (Bool.eq_false_iff.mpr (fun he => hc ((FiniteSuffixObservedAtoms.beq_char_iff _ _).mp he).symm)))⟩
  | succ n ih =>
    intro rest
    obtain ⟨t,ht⟩ := ih rest
    exact ⟨_,.starCons _ _ _ _ _ _ (.chrOk 'a' 'a' _ (by decide)) ht⟩

private theorem block_split (n : Nat) (rest : List Char) : ∃ tail, block n++rest=DelimitedCopyExamples.long (2*n)++tail := by
  refine ⟨d::((pattern.drop 1).flatMap (fun i => (ControlledCopyExamples.words n)[i]!++[d])++rest),?_⟩
  simp [block,ControlledCopyExamples.block,ConsumingPatternExamples.block,pattern,ConsumingPatternExamples.pattern,ControlledCopyExamples.words,ConsumingPatternExamples.words,d,List.append_assoc]

/-- Fresh actuals consume the real old parent and the real returned word
of a parameterized producer, not only parent-dependent zero-width tests. -/
theorem actual_captures (n : Nat) (rest : List Char) :
    DerivesArgsPar original .callByValuePar (block n++rest)
      (MExp.substArgs [.lit (List.replicate n 'a')] (renderArgs bodies.length clients.length true actuals))
      ((ControlledCopyExamples.words n).map MExp.lit) := by
  let w := List.replicate n 'a'
  let input := block n++rest
  obtain ⟨tail,hx⟩ := block_split n rest
  let afterPrefix := 'b'::(List.replicate (2*n) 'c'++tail)
  have hw : List.replicate (2*n) 'a'=w++w := by simp [w,Nat.two_mul]
  have hprefix : input=List.replicate (2*n) 'a'++afterPrefix := by
    simpa [afterPrefix,DelimitedCopyExamples.long,DelimitedCopyExamples.short,List.append_assoc] using hx
  have hx2 : input=w++(w++afterPrefix) := by rw [hprefix,hw,List.append_assoc]
  have ha : SObs original .callByValuePar (.call 0 []) input (some tail) := by
    rw [show input=DelimitedCopyExamples.long (2*n)++tail from hx]
    exact (base_observations 0 (by decide) _ _).mpr (DelimitedCopyExamples.balanced_capture (2*n) tail)
  have hb : SObs original .callByValuePar (.call 1 []) input (some (List.replicate (2*n) 'c'++tail)) := by
    rw [show input=DelimitedCopyExamples.long (2*n)++tail from hx]
    exact (base_observations 1 (by decide) _ _).mpr (DelimitedCopyExamples.short_capture (2*n) tail)
  have hparent : SObs original .callByValuePar (.lit w) input (some (w++afterPrefix)) := by
    rw [hx2]; exact literal w _
  have hproducer : SObs original .callByValuePar (bound w producer) (w++afterPrefix) (some afterPrefix) := by
    apply RootObservation.alt_left
    exact RootObservation.seq_ok (literal w afterPrefix) (RootObservation.not_fail ⟨_,.chrFail 'a' 'b' _ (by decide),rfl⟩)
  have hcall := enter_user 1 producer rfl (.lit w) w input (w++afterPrefix) afterPrefix hx2 hparent hproducer
  obtain ⟨oa,hda,hoa⟩ := ha
  obtain ⟨t0,rfl⟩ := restOf_eq_some hoa
  obtain ⟨ob,hdb,hob⟩ := hparent
  obtain ⟨t1,rfl⟩ := restOf_eq_some hob
  obtain ⟨oc,hdc,hoc⟩ := hcall
  obtain ⟨t2,rfl⟩ := restOf_eq_some hoc
  obtain ⟨od,hdd,hod⟩ := hb
  obtain ⟨t3,rfl⟩ := restOf_eq_some hod
  exact .cons _ _ _ _ _ t0 _ hda hx
    (.cons _ _ _ _ _ t1 _ hdb hx2
      (.cons _ _ _ _ _ t2 _ hdc hprefix
        (.cons _ _ _ _ _ t3 [] hdd (by rw [hx]; simp [DelimitedCopyExamples.long,List.append_assoc]) (.nil _))))

private theorem segment_at (d : Char) (W : List (List Char)) (i : Nat) (hi : i<W.length) (rest : List Char) :
    CopyBodyEvaluation.step d W i (W[i]++d::rest)=some rest := by
  have hh := DelimitedWordPattern.run_encode d W [i] (by intro j hj; simpa using (show j=i → j<W.length from fun he => he ▸ hi) (by simpa using hj)) rest
  simpa [CopyBodyEvaluation.step,CopyBodyEvaluation.partsRun,DelimitedWordPattern.encode,List.getElem?_eq_getElem hi,List.append_assoc] using hh

private theorem segment_compare (d : Char) (W : List (List Char)) (i : Nat) (hi : i<W.length) (w rest : List Char)
    (hwi : DelimitedCopyProjection.Free d W[i]) (hw : DelimitedCopyProjection.Free d w) :
    CopyBodyEvaluation.step d W i (w++d::rest)=if W[i]=w then some rest else none := by
  by_cases he : W[i]=w
  · rw [if_pos he,←he]; exact segment_at d W i hi rest
  · rw [if_neg he]
    cases hs : CopyBodyEvaluation.step d W i (w++d::rest) with
    | none => rfl
    | some tail =>
      obtain ⟨v,t,hv,hx,_⟩ := (DelimitedWordPattern.source_cons d W i [] _ tail).mp hs
      have hvw : v=W[i] := Option.some.inj (hv.symm.trans (List.getElem?_eq_getElem hi))
      subst v
      exact False.elim (he (DelimitedCopyProjection.split_unique d W[i] w t rest hwi hw hx.symm).1)

private theorem segments_run (d : Char) (W : List (List Char)) : ∀ hist x,
    CopyBodyEvaluation.run d W (segments hist) x=some (CopyBodyEvaluation.partsRun d W hist x)
  | [],_ => rfl
  | i::is,x => by
    have ha : CopyBodyEvaluation.partsRun d W (i::is) x=
        (CopyBodyEvaluation.partsRun d W [i] x).bind (CopyBodyEvaluation.partsRun d W is) := CopyBodyEvaluation.parts_append d W [i] is x
    change CopyBodyControl.chain (some (CopyBodyEvaluation.step d W i x))
      (CopyBodyControl.eval (CopyBodyEvaluation.step d W) (segments is))=some (CopyBodyEvaluation.partsRun d W (i::is) x)
    rw [ha]
    change _=some ((CopyBodyEvaluation.step d W i x).bind (CopyBodyEvaluation.partsRun d W is))
    cases hs : CopyBodyEvaluation.step d W i x with
    | none => simp only [CopyBodyControl.chain,hs,Option.bind_none]
    | some mid =>
      simpa only [CopyBodyControl.chain,hs,Option.bind_some,CopyBodyEvaluation.run] using segments_run d W is mid

private theorem select_second (d : Char) (W : List (List Char)) (h1 : 1<W.length) (h2 : 2<W.length)
    (hf1 : DelimitedCopyProjection.Free d W[1]) (hf2 : DelimitedCopyProjection.Free d W[2]) (rest : List Char) :
    CopyBodyControl.eval (CopyBodyEvaluation.step d W)
      (.alt (.seq (.notP (.segment 1)) (.segment 2)) (.segment 1)) (W[2]++d::rest)=some (some rest) := by
  have hs1 := segment_compare d W 1 h1 W[2] rest hf1 hf2
  have hs2 := segment_at d W 2 h2 rest
  by_cases he : W[1]=W[2] <;> simp only [he,if_true,if_false] at hs1 <;>
    simp only [CopyBodyControl.eval,CopyBodyControl.choice,CopyBodyControl.chain,CopyBodyControl.negative,hs1,hs2]

private theorem body_accepts (n : Nat) (rest : List Char) :
    CopyBodyEvaluation.run d (ControlledCopyExamples.words n) body (block n++rest)=some (some rest) := by
  let W := ControlledCopyExamples.words n
  let remaining := DelimitedWordPattern.encode d W [1,0,3,2,1]++rest
  let afterFirst := W[2]!++d::remaining
  have hW : W.length=4 := rfl
  have hinput : block n++rest=W[0]!++d::afterFirst := by
    simp [block,ConsumingPatternExamples.block,ConsumingPatternExamples.pattern,remaining,afterFirst,DelimitedWordPattern.encode,d,ConsumingPatternExamples.d,List.append_assoc,W]
  have h0 : CopyBodyEvaluation.step d W 0 (block n++rest)=some afterFirst := by
    rw [hinput,getElem!_pos W 0 (by omega)]
    exact segment_at d W 0 (by omega) afterFirst
  have hchoice : CopyBodyControl.eval (CopyBodyEvaluation.step d W)
      (.alt (.seq (.notP (.segment 1)) (.segment 2)) (.segment 1)) afterFirst=some (some remaining) := by
    have hf1 : DelimitedCopyProjection.Free d W[1] := by simp [W,ControlledCopyExamples.words,ConsumingPatternExamples.words,DelimitedCopyProjection.Free,d,ConsumingPatternExamples.d]
    have hf2 : DelimitedCopyProjection.Free d W[2] := by simp [W,ControlledCopyExamples.words,ConsumingPatternExamples.words,DelimitedCopyProjection.Free,d,ConsumingPatternExamples.d]
    simpa only [afterFirst,getElem!_pos W 2 (by omega)] using select_second d W (by omega) (by omega) hf1 hf2 remaining
  have hlast : CopyBodyControl.eval (CopyBodyEvaluation.step d W) (segments [1,0,3,2,1]) remaining=some (some rest) := by
    have hr := DelimitedWordPattern.run_encode d W [1,0,3,2,1] (by intro i hi; simp at hi; omega) rest
    rw [show CopyBodyControl.eval (CopyBodyEvaluation.step d W) (segments [1,0,3,2,1]) remaining=
      CopyBodyEvaluation.run d W (segments [1,0,3,2,1]) remaining from rfl,segments_run]
    exact congrArg some hr
  change CopyBodyControl.chain (some (CopyBodyEvaluation.step d W 0 (block n++rest)))
    (fun cur => CopyBodyControl.chain (CopyBodyControl.eval (CopyBodyEvaluation.step d W)
      (.alt (.seq (.notP (.segment 1)) (.segment 2)) (.segment 1)) cur)
      (CopyBodyControl.eval (CopyBodyEvaluation.step d W) (segments [1,0,3,2,1])))=some (some rest)
  rw [h0]
  change CopyBodyControl.chain (CopyBodyControl.eval (CopyBodyEvaluation.step d W)
    (.alt (.seq (.notP (.segment 1)) (.segment 2)) (.segment 1)) afterFirst)
    (CopyBodyControl.eval (CopyBodyEvaluation.step d W) (segments [1,0,3,2,1]))=some (some rest)
  rw [hchoice]
  exact hlast

private theorem copy_observed (n : Nat) (rest : List Char) :
    SObs original .callByValuePar (bound (List.replicate n 'a') copying) (block n++rest) (some rest) := by
  let input := block n++rest
  let W := ControlledCopyExamples.words n
  let sourceBody := CopyBodyControl.render d body
  have hfo : sourceBody.FirstOrder := CopyBodyControl.render_firstOrder _ _
  have hr : CopyBodyEvaluation.run d W body input=some (some rest) := body_accepts n rest
  have hev : evV original input .callByValuePar (tblV original input .callByValuePar 0) []
      (MExp.subst (W.map MExp.lit) sourceBody) input.length=some (some rest.length) := by
    have he := evV_subst (g := original) (x := input) (s := .callByValuePar)
      (T := tblV original input .callByValuePar 0) (E := []) W sourceBody hfo input.length
    have hh := CopyBodyEvaluation.physical original input .callByValuePar (tblV original input .callByValuePar 0)
      (tblV_ok _ _ _ 0) W d arity body (by decide +kernel) input.length (Nat.le_refl _)
    simpa only [sfx_self,hr,Option.map_some] using he.trans hh
  have ho := observed _ (firstOrder_subst (firstOrderArgs_lits W) sourceBody hfo) input rest 0 ⟨block n,rfl⟩ hev
  obtain ⟨o,hd,he⟩ := ho
  obtain ⟨t,rfl⟩ := restOf_eq_some he
  exact ⟨_,.callParOk (bodies.length+clients.length) _ ⟨arity,sourceBody⟩ input rest (W.map MExp.lit) t
    rfl (source_copy bodies clients arity d body) rfl (actual_captures n rest) hd,rfl⟩
private def afterHead (n depth : Nat) : List Char := match depth with
  | 0 => '|'::block n
  | depth+1 => '|'::(block n++'!'::(tree (2*n) depth++':'::List.replicate n 'a'))
private theorem tree_split (n depth : Nat) : tree n depth=List.replicate n 'a'++afterHead n depth := by cases depth <;> rfl

private def Stops (rest : List Char) : Prop := rest=[] ∨ ∃ c cs, rest=c::cs ∧ c≠'!'
private theorem bang_fails (rest : List Char) (h : Stops rest) : SObs original .callByValuePar (.chr '!') rest none := by
  rcases h with rfl|⟨c,cs,rfl,hc⟩
  · exact ⟨_,.chrEmpty _,rfl⟩
  · exact ⟨_,.chrFail '!' c cs (Bool.eq_false_iff.mpr (fun he => hc ((FiniteSuffixObservedAtoms.beq_char_iff _ _).mp he).symm)),rfl⟩

private theorem tail_observed : ∀ depth n rest, Stops rest →
    SObs original .callByValuePar (bound (List.replicate n 'a') ConsumingPatternExamples.tail) (afterHead n depth++rest) (some rest)
  | 0,n,rest,hs => by
    have h : SObs original .callByValuePar (bound (List.replicate n 'a') ConsumingPatternExamples.tail)
        ('|'::(block n++rest)) (some rest) := by
      apply RootObservation.seq_ok ⟨_,.chrOk '|' '|' _ (by decide),rfl⟩
      apply RootObservation.seq_ok (copy_observed n rest)
      apply RootObservation.alt_right
      · exact RootObservation.seq_fail (bang_fails rest hs)
      · exact ⟨_,.eps rest,rfl⟩
    simpa only [afterHead,List.cons_append] using h
  | depth+1,n,rest,hs => by
    let w := List.replicate n 'a'
    let childRest := ':'::(w++rest)
    have hc : Stops childRest := Or.inr ⟨':',w++rest,rfl,by decide⟩
    have hbody := tail_observed depth (2*n) childRest hc
    have hw : List.replicate (2*n) 'a'=w++w := by simp [w,Nat.two_mul,List.replicate_append_replicate]
    have hx : tree (2*n) depth++childRest=List.replicate (2*n) 'a'++(afterHead (2*n) depth++childRest) := by rw [tree_split]; simp [List.append_assoc]
    have ha : SObs original .callByValuePar (.seq (.lit w) (.lit w)) (tree (2*n) depth++childRest) (some (afterHead (2*n) depth++childRest)) := by
      rw [hx,hw,List.append_assoc]
      exact RootObservation.seq_ok (literal w _) (literal w _)
    have hchild := enter_user 0 ConsumingPatternExamples.tail rfl (.seq (.lit w) (.lit w)) (List.replicate (2*n) 'a') _ _ childRest hx ha hbody
    have hclose : SObs original .callByValuePar (.seq (.chr ':') (.lit w)) childRest (some rest) :=
      RootObservation.seq_ok ⟨_,.chrOk ':' ':' _ (by decide),rfl⟩ (literal w rest)
    have h : SObs original .callByValuePar (bound w ConsumingPatternExamples.tail)
        ('|'::(block n++'!'::(tree (2*n) depth++childRest))) (some rest) := by
      apply RootObservation.seq_ok ⟨_,.chrOk '|' '|' _ (by decide),rfl⟩
      apply RootObservation.seq_ok (copy_observed n ('!'::(tree (2*n) depth++childRest)))
      apply RootObservation.alt_left
      exact RootObservation.seq_ok ⟨_,.chrOk '!' '!' _ (by decide),rfl⟩ (RootObservation.seq_ok hchild hclose)
    simpa only [afterHead,childRest,w,List.append_assoc,List.cons_append] using h

/-- Every initial parent length and every nesting depth: child payloads
double, while continuations restore each actual parent's retained word. -/
theorem source_and_target_all_trees (n depth : Nat) :
    SObs original .callByValuePar originalRoot (tree n depth) (some []) ∧
      SObs generated .callByValueSeq generatedRoot (tree n depth) (some []) := by
  have ht := tail_observed depth n [] (Or.inl rfl)
  simp only [List.append_nil] at ht
  have hx := tree_split n depth
  obtain ⟨t,hd⟩ := many_a n '|' (by decide) (afterHead n depth).tail
  have ha : SObs original .callByValuePar (.star (.chr 'a')) (tree n depth) (some (afterHead n depth)) := by
    cases depth <;> exact ⟨_,by simpa [tree,ConsumingPatternExamples.tree,afterHead] using hd,rfl⟩
  have huser := enter_user 0 ConsumingPatternExamples.tail rfl (.star (.chr 'a')) (List.replicate n 'a') _ _ [] hx ha ht
  have hs : SObs original .callByValuePar originalRoot (tree n depth) (some []) :=
    RootObservation.seq_ok huser (RootObservation.not_fail ⟨_,.anyFail,rfl⟩)
  exact ⟨hs,(ControlledCopyCompiler.observations_iff original originalRoot bodies clients arity alphabet d body required entry checked (tree n depth) (some [])).mp hs⟩


theorem nullable_source_undefined (k : Nat) :
    evV (source [] [] arity d nullableBody) ['a','!'] .callByValuePar (tblV (source [] [] arity d nullableBody) ['a','!'] .callByValuePar k) []
      (render 0 0 true nullableEntry) 2=none := by
  have hr : ruleAtM (source [] [] arity d nullableBody).rules 0=some ⟨4,CopyBodyControl.render d nullableBody⟩ := rfl
  change evV _ _ _ _ [] (.call 0 [.lit ['a'],.eps,.eps,.eps]) 2=none
  rw [evV_call_par hr rfl (by decide),evPar_cons_ok rfl,evPar_cons_ok rfl,evPar_cons_ok rfl,evPar_cons_ok rfl,evPar_nil]
  change valAt (tblV (source [] [] arity d nullableBody) ['a','!'] .callByValuePar k 0 [['a'],[],[],[]]) 2=none
  cases k with
  | zero => rfl
  | succ k =>
    rw [valAt_tblV_succ hr [['a'],[],[],[]] (by decide)]
    change evV _ _ _ _ [['a'],[],[],[]] (.star (.notP (CopyBodyControl.render d (.segment 0)))) 2=none
    have hstep : evV (source [] [] arity d nullableBody) ['a','!'] .callByValuePar
        (tblV (source [] [] arity d nullableBody) ['a','!'] .callByValuePar k) [['a'],[],[],[]] (.notP (CopyBodyControl.render d (.segment 0))) 2=some (some 2) := rfl
    rw [evV_star,evStar_stuck hstep (Nat.lt_irrefl _)]

theorem nullable_target_undefined (k : Nat) :
    evV (target [] [] arity d nullableBody) ['a','!'] .callByValueSeq (tblV (target [] [] arity d nullableBody) ['a','!'] .callByValueSeq k) []
      (emit 0 0 arity nullableBody nullableEntry) 2=none := by
  exact (ControlledCopyCompiler.physical (source [] [] arity d nullableBody) _ [] [] arity alphabet d nullableBody [] nullableEntry nullable_checked ['a','!'] k).symm.trans (nullable_source_undefined k)

def cycleClients : List RetainedPatternSyntax.Expr := [.user 0 .parent]
def cycleRequired : List Bool := [true]
def cycleActuals : List RetainedPatternSyntax.Expr := [.eps,.eps,.eps,.user 0 .eps]
def cycleEntry : RetainedPatternSyntax.Expr := .copy cycleActuals

theorem cycle_checked (b : CopyBodyControl.Body) (hb : CopyBodyControl.check arity b=true) :
    ControlledCopySyntax.check [] cycleClients arity alphabet d b cycleRequired cycleEntry=true :=
  Bool.and_eq_true_iff.mpr ⟨hb,by decide +kernel⟩

theorem cycle_rows (b : CopyBodyControl.Body) (x : List Char) (p : Nat) (hp : p≤x.length) : ∀ k,
    valAt (tblV (source [] cycleClients arity d b) x .callByValuePar k 0 [[]]) p=none := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    have hr : ruleAtM (source [] cycleClients arity d b).rules 0=some ⟨1,.seq (.param 0) (.call 0 [.param 0])⟩ := rfl
    rw [valAt_tblV_succ hr [[]] hp]
    have hparent : evV (source [] cycleClients arity d b) x .callByValuePar
        (tblV (source [] cycleClients arity d b) x .callByValuePar k) [[]] (.param 0) p=some (some p) := by
      simp only [evV,List.getElem?_cons_zero,(CBVtoCBN.stripPrefix_exact [] (sfx x p) (sfx x p)).mpr rfl,length_sfx x hp]
    rw [evV_seq_ok hparent,evV_call_par hr rfl (by decide),evPar_cons_ok hparent,evPar_nil]
    simpa only [pre,Nat.sub_self,List.take_zero] using ih

theorem cycle_source (b : CopyBodyControl.Body) (x : List Char) (k : Nat) :
    evV (source [] cycleClients arity d b) x .callByValuePar (tblV (source [] cycleClients arity d b) x .callByValuePar k) []
      (render 0 1 true cycleEntry) x.length=none := by
  have hr : ruleAtM (source [] cycleClients arity d b).rules 0=some ⟨1,.seq (.param 0) (.call 0 [.param 0])⟩ := rfl
  have hcall : evV (source [] cycleClients arity d b) x .callByValuePar (tblV (source [] cycleClients arity d b) x .callByValuePar k) [] (.call 0 [.eps]) x.length=none := by
    rw [evV_call_par hr rfl (by decide),evPar_cons_ok rfl,evPar_nil]
    simpa only [pre,Nat.sub_self,List.take_zero] using cycle_rows b x x.length (Nat.le_refl _) k
  have hh : ruleAtM (source [] cycleClients arity d b).rules 1=some ⟨4,CopyBodyControl.render d b⟩ := rfl
  change evV _ _ _ _ [] (.call 1 [.eps,.eps,.eps,.call 0 [.eps]]) x.length=none
  rw [evV_call_par hh rfl (by decide),evPar_cons_ok rfl,evPar_cons_ok rfl,evPar_cons_ok rfl,evPar_cons_none hcall]

theorem cycle_target (b : CopyBodyControl.Body) (hb : CopyBodyControl.check arity b=true) (x : List Char) (k : Nat) :
    evV (target [] cycleClients arity d b) x .callByValueSeq (tblV (target [] cycleClients arity d b) x .callByValueSeq k) []
      (emit 0 1 arity b cycleEntry) x.length=none :=
  (ControlledCopyCorrespondence.physical [] cycleClients arity alphabet d b cycleRequired cycleEntry (cycle_checked b hb) x k x.length (Nat.le_refl _)).symm.trans (cycle_source b x k)

theorem preflight_required_for_empty_body :
    evV (target [] cycleClients arity d .eps) ['a'] .callByValueSeq (tblV (target [] cycleClients arity d .eps) ['a'] .callByValueSeq 4) []
      (.seq (.call 1 []) (CopyBodyEmission.emitPlan 1 arity .eps (emitArgs 0 1 arity .eps cycleActuals) (CopyBodyControl.normalized .eps))) 1=some (some 1) := by decide +kernel

theorem failure_before_initialization :
    evV (source [] [] arity d .eps) ['a'] .callByValuePar (tblV (source [] [] arity d .eps) ['a'] .callByValuePar 0) []
      (render 0 0 true (.copy [.lit ['b'],.eps,.eps,.eps])) 1=some none ∧
    evV (target [] [] arity d .eps) ['a'] .callByValueSeq (tblV (target [] [] arity d .eps) ['a'] .callByValueSeq 0) []
      (emit 0 0 arity .eps (.copy [.lit ['b'],.eps,.eps,.eps])) 1=some none := by decide +kernel

end Shallot.MacroPeg.CBV.ControlledCopyProofs
