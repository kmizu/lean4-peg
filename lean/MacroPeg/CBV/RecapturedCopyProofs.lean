import MacroPeg.CBV.RecapturedCopyExamples

namespace Shallot.MacroPeg.CBV.RecapturedCopyProofs
open RetainedPatternSyntax RecapturedCopySyntax RecapturedCopyExamples
open ConsumingPatternExamples (producer copying)
open DelimiterTemplate (Part)

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
  have hnew : original.FirstOrder := RecapturedCopySyntax.source_firstOrder bodies clients arity d pattern base_valid
  have hold : DelimitedCopyExamples.original.FirstOrder := hold
  rw [←decideObsV_iff hnew (by decide) (show (MExp.call i []).FirstOrder from True.intro),
    ←decideObsV_iff hold (by decide) (show (MExp.call i []).FirstOrder from True.intro)]
  unfold decideObsV
  rw [ScannerPairFusion.stable_result_eq _ _ x _ _ _ _ (fun k => base_query i hi x k x.length (Nat.le_refl _))]

private theorem observed (e : MExp) (he : e.FirstOrder) (x rest : List Char) (k : Nat)
    (hs : ∃ a, x=a++rest)
    (hv : evV original x .callByValuePar (tblV original x .callByValuePar k) [] e x.length=some (some rest.length)) :
    SObs original .callByValuePar e x (some rest) := by
  obtain ⟨o,hd,ho⟩ := evV_sound (by decide) (tblV_sound (RecapturedCopySyntax.source_firstOrder bodies clients arity d pattern base_valid) (by decide) k) e he _ (Nat.le_refl _) _ hv
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
    rfl (RecapturedCopySyntax.source_user bodies clients arity d pattern i e hi) rfl hargs hd,rfl⟩

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
  refine ⟨d::((pattern.drop 1).flatMap (fun i => (ConsumingPatternExamples.words n)[i]!++[d])++rest),?_⟩
  simp [block,ConsumingPatternExamples.block,pattern,ConsumingPatternExamples.pattern,ConsumingPatternExamples.words,d,List.append_assoc]

/-- Fresh actuals consume the real old parent and the real returned word
of a parameterized producer, not only parent-dependent zero-width tests. -/
theorem actual_captures (n : Nat) (rest : List Char) :
    DerivesArgsPar original .callByValuePar (block n++rest)
      (MExp.substArgs [.lit (List.replicate n 'a')] (renderArgs bodies.length clients.length true actuals))
      ((ConsumingPatternExamples.words n).map MExp.lit) := by
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

theorem blocks_copies (n : Nat) : ∀ r, blocks n r=RepeatedWordArguments.copies (block n) r
  | 0 => rfl
  | r+1 => by simp only [blocks,RepeatedWordArguments.copies,blocks_copies n r]

private def BStops (rest : List Char) : Prop := rest=[] ∨ ∃ c cs, rest=c::cs ∧ c≠'a' ∧ c≠'b'

private theorem ab_prefix_fails (n : Nat) (tail rest : List Char) (hs : BStops rest) :
    Shallot.stripPrefix? (List.replicate n 'a'++'b'::tail) rest=none := by
  rcases hs with rfl|⟨c,cs,rfl,ha,hb⟩
  · cases n <;> rfl
  · have hca : Shallot.beqChar 'a' c=false := Bool.eq_false_iff.mpr (fun h => ha ((FiniteSuffixObservedAtoms.beq_char_iff _ _).mp h).symm)
    have hcb : Shallot.beqChar 'b' c=false := Bool.eq_false_iff.mpr (fun h => hb ((FiniteSuffixObservedAtoms.beq_char_iff _ _).mp h).symm)
    cases n <;> simp [List.replicate_succ,Shallot.stripPrefix?,hca,hcb]

private theorem block_stops (n : Nat) (rest : List Char) (hs : BStops rest) :
    Shallot.stripPrefix? (block n) rest=none := by
  obtain ⟨tail,hx⟩ := block_split n []
  simp only [List.append_nil] at hx
  rw [hx,RepeatedWordArguments.strip_concat]
  have hh : Shallot.stripPrefix? (DelimitedCopyExamples.long (2*n)) rest=none := by
    simpa [DelimitedCopyExamples.long,DelimitedCopyExamples.short,List.append_assoc] using ab_prefix_fails (2*n) (List.replicate (2*n) 'c') rest hs
  rw [hh]
  rfl

private theorem copy_observed (n count : Nat) (rest : List Char) (hs : BStops rest) :
    SObs original .callByValuePar (bound (List.replicate n 'a') copying) (blocks n (count+1)++rest) (some rest) := by
  let input := blocks n (count+1)++rest
  let W := RecapturedCopyExamples.words n
  let sourceBody := MExp.star (DelimiterTemplate.compile d (DelimitedWordPattern.sourceParts d pattern))
  have hfo : sourceBody.FirstOrder := DelimiterTemplate.compile_firstOrder _ _
  have hscope : ∀ i∈pattern, i<W.length := by
    intro i hi; simp [pattern,ConsumingPatternExamples.pattern,W,RecapturedCopyExamples.words,ConsumingPatternExamples.words] at hi ⊢; omega
  have hencode : DelimitedWordPattern.encode d W pattern=block n := rfl
  have hb : block n≠[] := by
    rw [←hencode]
    exact RecapturedCopyBlock.block_nonempty d W 0 [2,1,0,3,2,1]
  have hev : evV original input .callByValuePar (tblV original input .callByValuePar 0) []
      (MExp.subst (W.map MExp.lit) sourceBody) input.length=some (some rest.length) := by
    have he := evV_subst (g := original) (x := input) (s := .callByValuePar)
      (T := tblV original input .callByValuePar 0) (E := []) W sourceBody hfo input.length
    have hh : evV original input .callByValuePar (tblV original input .callByValuePar 0) W sourceBody input.length=some (some rest.length) := by
      rw [RecapturedCopyBlock.star_literal original input .callByValuePar _ W d pattern hscope _ (Nat.le_refl _),hencode]
      exact RecapturedCopyBlock.literal_copies original input .callByValuePar _ [] (block n) hb rest (block_stops n rest hs)
        (count+1) input.length (Nat.le_refl _) (by simp only [sfx_self,input,blocks_copies])
    exact he.trans hh
  have ho := observed _ (firstOrder_subst (firstOrderArgs_lits W) sourceBody hfo) input rest 0 ⟨blocks n (count+1),rfl⟩ hev
  obtain ⟨o,hd,he⟩ := ho
  obtain ⟨t,rfl⟩ := restOf_eq_some he
  refine ⟨_,.callParOk (bodies.length+clients.length) _ ⟨arity,sourceBody⟩ input rest (W.map MExp.lit) t
    rfl (RecapturedCopySyntax.source_copy bodies clients arity d pattern) rfl ?_ hd,rfl⟩
  simpa only [input,blocks,List.append_assoc] using actual_captures n (blocks n count++rest)

private def afterHead (n count depth : Nat) : List Char := match depth with
  | 0 => '|'::blocks n (count+1)
  | depth+1 => '|'::(blocks n (count+1)++'!'::(tree (2*n) count depth++':'::List.replicate n 'a'))
private theorem tree_split (n count depth : Nat) : tree n count depth=List.replicate n 'a'++afterHead n count depth := by cases depth <;> rfl

private def Stops (rest : List Char) : Prop := rest=[] ∨ ∃ c cs, rest=c::cs ∧ c≠'!'
private theorem bang_fails (rest : List Char) (h : Stops rest) : SObs original .callByValuePar (.chr '!') rest none := by
  rcases h with rfl|⟨c,cs,rfl,hc⟩
  · exact ⟨_,.chrEmpty _,rfl⟩
  · exact ⟨_,.chrFail '!' c cs (Bool.eq_false_iff.mpr (fun he => hc ((FiniteSuffixObservedAtoms.beq_char_iff _ _).mp he).symm)),rfl⟩

private theorem tail_observed : ∀ depth n count rest, BStops rest → Stops rest →
    SObs original .callByValuePar (bound (List.replicate n 'a') ConsumingPatternExamples.tail) (afterHead n count depth++rest) (some rest)
  | 0,n,count,rest,hbs,hs => by
    have h : SObs original .callByValuePar (bound (List.replicate n 'a') ConsumingPatternExamples.tail)
        ('|'::(blocks n (count+1)++rest)) (some rest) := by
      apply RootObservation.seq_ok ⟨_,.chrOk '|' '|' _ (by decide),rfl⟩
      apply RootObservation.seq_ok (copy_observed n count rest hbs)
      apply RootObservation.alt_right
      · exact RootObservation.seq_fail (bang_fails rest hs)
      · exact ⟨_,.eps rest,rfl⟩
    simpa only [afterHead,List.cons_append] using h
  | depth+1,n,count,rest,hbs,hs => by
    let w := List.replicate n 'a'
    let childRest := ':'::(w++rest)
    have hc : Stops childRest := Or.inr ⟨':',w++rest,rfl,by decide⟩
    have hbody := tail_observed depth (2*n) count childRest (Or.inr ⟨':',w++rest,rfl,by decide,by decide⟩) hc
    have hw : List.replicate (2*n) 'a'=w++w := by simp [w,Nat.two_mul,List.replicate_append_replicate]
    have hx : tree (2*n) count depth++childRest=List.replicate (2*n) 'a'++(afterHead (2*n) count depth++childRest) := by rw [tree_split]; simp [List.append_assoc]
    have ha : SObs original .callByValuePar (.seq (.lit w) (.lit w)) (tree (2*n) count depth++childRest) (some (afterHead (2*n) count depth++childRest)) := by
      rw [hx,hw,List.append_assoc]
      exact RootObservation.seq_ok (literal w _) (literal w _)
    have hchild := enter_user 0 ConsumingPatternExamples.tail rfl (.seq (.lit w) (.lit w)) (List.replicate (2*n) 'a') _ _ childRest hx ha hbody
    have hclose : SObs original .callByValuePar (.seq (.chr ':') (.lit w)) childRest (some rest) :=
      RootObservation.seq_ok ⟨_,.chrOk ':' ':' _ (by decide),rfl⟩ (literal w rest)
    have h : SObs original .callByValuePar (bound w ConsumingPatternExamples.tail)
        ('|'::(blocks n (count+1)++'!'::(tree (2*n) count depth++childRest))) (some rest) := by
      apply RootObservation.seq_ok ⟨_,.chrOk '|' '|' _ (by decide),rfl⟩
      apply RootObservation.seq_ok (copy_observed n count ('!'::(tree (2*n) count depth++childRest)) (Or.inr ⟨'!',_,rfl,by decide,by decide⟩))
      apply RootObservation.alt_left
      exact RootObservation.seq_ok ⟨_,.chrOk '!' '!' _ (by decide),rfl⟩ (RootObservation.seq_ok hchild hclose)
    simpa only [afterHead,childRest,w,List.append_assoc,List.cons_append] using h

/-- Every initial parent length and every nesting depth: child payloads
double, while continuations restore each actual parent's retained word. -/
theorem source_and_target_all_trees (n count depth : Nat) :
    SObs original .callByValuePar originalRoot (tree n count depth) (some []) ∧
      SObs generated .callByValueSeq generatedRoot (tree n count depth) (some []) := by
  have ht := tail_observed depth n count [] (Or.inl rfl) (Or.inl rfl)
  simp only [List.append_nil] at ht
  have hx := tree_split n count depth
  obtain ⟨t,hd⟩ := many_a n '|' (by decide) (afterHead n count depth).tail
  have ha : SObs original .callByValuePar (.star (.chr 'a')) (tree n count depth) (some (afterHead n count depth)) := by
    cases depth <;> exact ⟨_,by simpa [tree,afterHead] using hd,rfl⟩
  have huser := enter_user 0 ConsumingPatternExamples.tail rfl (.star (.chr 'a')) (List.replicate n 'a') _ _ [] hx ha ht
  have hs : SObs original .callByValuePar originalRoot (tree n count depth) (some []) :=
    RootObservation.seq_ok huser (RootObservation.not_fail ⟨_,.anyFail,rfl⟩)
  exact ⟨hs,(RecapturedCopyCompiler.observations_iff original originalRoot bodies clients arity alphabet d pattern required entry checked (tree n count depth) (some [])).mp hs⟩


def cycleClients : List RetainedPatternSyntax.Expr := [.user 0 .parent]
def cycleRequired : List Bool := [true]
def cycleActuals : List RetainedPatternSyntax.Expr := [.eps,.eps,.eps,.user 0 .eps]
def cycleEntry : RetainedPatternSyntax.Expr := .copy cycleActuals

theorem cycle_checked (b : List Nat) (hb : RecapturedCopySyntax.patternCheck arity b=true) :
    RecapturedCopySyntax.check [] cycleClients arity alphabet d b cycleRequired cycleEntry=true :=
  Bool.and_eq_true_iff.mpr ⟨hb,by decide +kernel⟩

theorem cycle_rows (b : List Nat) (x : List Char) (p : Nat) (hp : p≤x.length) : ∀ k,
    valAt (tblV (RecapturedCopySyntax.source [] cycleClients arity d b) x .callByValuePar k 0 [[]]) p=none := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    have hr : ruleAtM (RecapturedCopySyntax.source [] cycleClients arity d b).rules 0=some ⟨1,.seq (.param 0) (.call 0 [.param 0])⟩ := rfl
    rw [valAt_tblV_succ hr [[]] hp]
    have hparent : evV (RecapturedCopySyntax.source [] cycleClients arity d b) x .callByValuePar
        (tblV (RecapturedCopySyntax.source [] cycleClients arity d b) x .callByValuePar k) [[]] (.param 0) p=some (some p) := by
      simp only [evV,List.getElem?_cons_zero,(CBVtoCBN.stripPrefix_exact [] (sfx x p) (sfx x p)).mpr rfl,length_sfx x hp]
    rw [evV_seq_ok hparent,evV_call_par hr rfl (by decide),evPar_cons_ok hparent,evPar_nil]
    simpa only [pre,Nat.sub_self,List.take_zero] using ih

theorem cycle_source (b : List Nat) (x : List Char) (k : Nat) :
    evV (RecapturedCopySyntax.source [] cycleClients arity d b) x .callByValuePar (tblV (RecapturedCopySyntax.source [] cycleClients arity d b) x .callByValuePar k) []
      (render 0 1 true cycleEntry) x.length=none := by
  have hr : ruleAtM (RecapturedCopySyntax.source [] cycleClients arity d b).rules 0=some ⟨1,.seq (.param 0) (.call 0 [.param 0])⟩ := rfl
  have hcall : evV (RecapturedCopySyntax.source [] cycleClients arity d b) x .callByValuePar (tblV (RecapturedCopySyntax.source [] cycleClients arity d b) x .callByValuePar k) [] (.call 0 [.eps]) x.length=none := by
    rw [evV_call_par hr rfl (by decide),evPar_cons_ok rfl,evPar_nil]
    simpa only [pre,Nat.sub_self,List.take_zero] using cycle_rows b x x.length (Nat.le_refl _) k
  have hh : ruleAtM (RecapturedCopySyntax.source [] cycleClients arity d b).rules 1=some ⟨4,(.star (DelimiterTemplate.compile d (DelimitedWordPattern.sourceParts d b)))⟩ := rfl
  change evV _ _ _ _ [] (.call 1 [.eps,.eps,.eps,.call 0 [.eps]]) x.length=none
  rw [evV_call_par hh rfl (by decide),evPar_cons_ok rfl,evPar_cons_ok rfl,evPar_cons_ok rfl,evPar_cons_none hcall]

theorem cycle_target (b : List Nat) (hb : RecapturedCopySyntax.patternCheck arity b=true) (x : List Char) (k : Nat) :
    evV (RecapturedCopySyntax.target [] cycleClients arity d b) x .callByValueSeq (tblV (RecapturedCopySyntax.target [] cycleClients arity d b) x .callByValueSeq k) []
      (emit 0 1 arity d b cycleEntry) x.length=none :=
  (RecapturedCopyCorrespondence.physical [] cycleClients arity alphabet d b cycleRequired cycleEntry (cycle_checked b hb) x k x.length (Nat.le_refl _)).symm.trans (cycle_source b x k)



end Shallot.MacroPeg.CBV.RecapturedCopyProofs
