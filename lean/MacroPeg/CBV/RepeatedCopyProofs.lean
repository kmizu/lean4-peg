import MacroPeg.CBV.RepeatedCopyExamples

namespace Shallot.MacroPeg.CBV.RepeatedCopyProofs
open RetainedPatternSyntax
open RepeatedCopySyntax
open ConsumingPatternExamples (producer copying)
open RepeatedCopyExamples
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
  have hnew : original.FirstOrder := RepeatedCopySyntax.source_firstOrder bodies clients arity d body base_valid
  have hold : DelimitedCopyExamples.original.FirstOrder := hold
  rw [←decideObsV_iff hnew (by decide) (show (MExp.call i []).FirstOrder from True.intro),
    ←decideObsV_iff hold (by decide) (show (MExp.call i []).FirstOrder from True.intro)]
  unfold decideObsV
  rw [ScannerPairFusion.stable_result_eq _ _ x _ _ _ _ (fun k => base_query i hi x k x.length (Nat.le_refl _))]

private theorem observed (e : MExp) (he : e.FirstOrder) (x rest : List Char) (k : Nat)
    (hs : ∃ a, x=a++rest)
    (hv : evV original x .callByValuePar (tblV original x .callByValuePar k) [] e x.length=some (some rest.length)) :
    SObs original .callByValuePar e x (some rest) := by
  obtain ⟨o,hd,ho⟩ := evV_sound (by decide) (tblV_sound (RepeatedCopySyntax.source_firstOrder bodies clients arity d body base_valid) (by decide) k) e he _ (Nat.le_refl _) _ hv
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
    rfl (RepeatedCopySyntax.source_user bodies clients arity d body i e hi) rfl hargs hd,rfl⟩

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
  refine ⟨d::((pattern.drop 1).flatMap (fun i => (RepeatedCopyExamples.words n)[i]!++[d])++rest),?_⟩
  simp [block,RepeatedCopyExamples.block,ConsumingPatternExamples.block,pattern,ConsumingPatternExamples.pattern,RepeatedCopyExamples.words,ConsumingPatternExamples.words,d,List.append_assoc]

/-- Fresh actuals consume the real old parent and the real returned word
of a parameterized producer, not only parent-dependent zero-width tests. -/
theorem actual_captures (n : Nat) (rest : List Char) :
    DerivesArgsPar original .callByValuePar (block n++rest)
      (MExp.substArgs [.lit (List.replicate n 'a')] (renderArgs bodies.length clients.length true actuals))
      ((RepeatedCopyExamples.words n).map MExp.lit) := by
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

theorem encode_copies (n : Nat) : ∀ r,
    DelimitedWordPattern.encode d (RepeatedCopyExamples.words n) (RepeatedWordPattern.copies body r)=blocks n r
  | 0 => rfl
  | r+1 => by
    simp only [RepeatedWordPattern.copies,DelimitedWordPattern.encode,List.flatMap_append,
      blocks,←encode_copies n r]
    rfl

theorem body_all_repetitions (n r : Nat) :
    RepeatedWordPattern.SourceAccept d (RepeatedCopyExamples.words n) body (blocks n r) := by
  refine ⟨r,?_⟩
  have hs : ∀ i∈RepeatedWordPattern.copies body r, i<(RepeatedCopyExamples.words n).length :=
    RepeatedWordPattern.copies_scope body (RepeatedCopyExamples.words n).length (by
      intro i hi
      have hh : i<4 := (show ∀ i∈body, i<4 from by decide +kernel) i hi
      simpa [RepeatedCopyExamples.words,ConsumingPatternExamples.words] using hh) r
  simpa only [encode_copies,List.append_nil] using
    DelimitedWordPattern.run_encode d (RepeatedCopyExamples.words n) (RepeatedWordPattern.copies body r) hs []

private theorem copy_observed (n r : Nat) :
    SObs original .callByValuePar (bound (List.replicate n 'a') copying) (blocks n (r+1)) (some []) := by
  classical
  let input := blocks n (r+1)
  let W := RepeatedCopyExamples.words n
  let sourceBody := RepeatedWordEvaluation.sourceBody d body
  have hfo : sourceBody.FirstOrder := RepeatedWordTransfer.source_firstOrder _ _
  have hev : evV original input .callByValuePar (tblV original input .callByValuePar 0) []
      (MExp.subst (W.map MExp.lit) sourceBody) input.length=some (some 0) := by
    have he := evV_subst (g := original) (x := input) (s := .callByValuePar)
      (T := tblV original input .callByValuePar 0) (E := []) W sourceBody hfo input.length
    have hh := RepeatedWordEvaluation.source_physical original input .callByValuePar
      (tblV original input .callByValuePar 0) (tblV_ok _ _ _ 0) W d 0 [2,1,0,3,2,1] input.length (Nat.le_refl _)
    have hr : RepeatedWordPattern.SourceAccept d W body input := body_all_repetitions n (r+1)
    rw [show sfx input input.length=input from by simp [sfx]] at hh
    change _=some (if RepeatedWordPattern.SourceAccept d W body input then some 0 else none) at hh
    rw [if_pos hr] at hh
    exact he.trans hh
  have ho := observed _ (firstOrder_subst (firstOrderArgs_lits W) sourceBody hfo) input [] 0 ⟨input,by simp⟩ hev
  obtain ⟨o,hd,he⟩ := ho
  obtain ⟨t,rfl⟩ := restOf_eq_some he
  exact ⟨_,.callParOk (bodies.length+clients.length) _ ⟨arity,sourceBody⟩ input [] (W.map MExp.lit) t
    rfl (RepeatedCopySyntax.source_copy bodies clients arity d body) rfl (actual_captures n (blocks n r)) hd,rfl⟩

/-- Both capture length and the consuming repetition count are unbounded. -/
theorem source_and_target_all_repetitions (n r : Nat) :
    SObs original .callByValuePar originalRoot (input n (r+1)) (some []) ∧
      SObs generated .callByValueSeq generatedRoot (input n (r+1)) (some []) := by
  have htail : SObs original .callByValuePar (bound (List.replicate n 'a') tail)
      ('|'::blocks n (r+1)) (some []) :=
    RootObservation.seq_ok ⟨_,.chrOk '|' '|' _ (by decide),rfl⟩ (copy_observed n r)
  obtain ⟨t,ht⟩ := many_a n '|' (by decide) (blocks n (r+1))
  have hu := enter_user 0 tail rfl (.star (.chr 'a')) (List.replicate n 'a')
    (input n (r+1)) ('|'::blocks n (r+1)) [] rfl ⟨_,ht,rfl⟩ htail
  have ho : SObs original .callByValuePar originalRoot (input n (r+1)) (some []) :=
    RootObservation.seq_ok hu (RootObservation.not_fail ⟨_,.anyFail,rfl⟩)
  refine ⟨ho,?_⟩
  exact (RepeatedCopyCompiler.observations_iff original originalRoot bodies clients arity alphabet d body required entry checked _ (some [])).mp ho

def cycleClients : List RetainedPatternSyntax.Expr := [.user 0 .parent]
def cycleRequired : List Bool := [true]
def cycleActuals : List RetainedPatternSyntax.Expr := [.eps,.eps,.eps,.user 0 .eps]
def cycleEntry : RetainedPatternSyntax.Expr := .copy cycleActuals

theorem cycle_checked (b : List Nat) (hb : RepeatedCopySyntax.patternCheck arity b=true) :
    RepeatedCopySyntax.check [] cycleClients arity alphabet d b cycleRequired cycleEntry=true :=
  Bool.and_eq_true_iff.mpr ⟨hb,by decide +kernel⟩

theorem cycle_rows (b : List Nat) (x : List Char) (p : Nat) (hp : p≤x.length) : ∀ k,
    valAt (tblV (RepeatedCopySyntax.source [] cycleClients arity d b) x .callByValuePar k 0 [[]]) p=none := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    have hr : ruleAtM (RepeatedCopySyntax.source [] cycleClients arity d b).rules 0=some ⟨1,.seq (.param 0) (.call 0 [.param 0])⟩ := rfl
    rw [valAt_tblV_succ hr [[]] hp]
    have hparent : evV (RepeatedCopySyntax.source [] cycleClients arity d b) x .callByValuePar
        (tblV (RepeatedCopySyntax.source [] cycleClients arity d b) x .callByValuePar k) [[]] (.param 0) p=some (some p) := by
      simp only [evV,List.getElem?_cons_zero,(CBVtoCBN.stripPrefix_exact [] (sfx x p) (sfx x p)).mpr rfl,length_sfx x hp]
    rw [evV_seq_ok hparent,evV_call_par hr rfl (by decide),evPar_cons_ok hparent,evPar_nil]
    simpa only [pre,Nat.sub_self,List.take_zero] using ih

theorem cycle_source (b : List Nat) (x : List Char) (k : Nat) :
    evV (RepeatedCopySyntax.source [] cycleClients arity d b) x .callByValuePar (tblV (RepeatedCopySyntax.source [] cycleClients arity d b) x .callByValuePar k) []
      (render 0 1 true cycleEntry) x.length=none := by
  have hr : ruleAtM (RepeatedCopySyntax.source [] cycleClients arity d b).rules 0=some ⟨1,.seq (.param 0) (.call 0 [.param 0])⟩ := rfl
  have hcall : evV (RepeatedCopySyntax.source [] cycleClients arity d b) x .callByValuePar (tblV (RepeatedCopySyntax.source [] cycleClients arity d b) x .callByValuePar k) [] (.call 0 [.eps]) x.length=none := by
    rw [evV_call_par hr rfl (by decide),evPar_cons_ok rfl,evPar_nil]
    simpa only [pre,Nat.sub_self,List.take_zero] using cycle_rows b x x.length (Nat.le_refl _) k
  have hh : ruleAtM (RepeatedCopySyntax.source [] cycleClients arity d b).rules 1=some ⟨4,RepeatedWordEvaluation.sourceBody d b⟩ := rfl
  change evV _ _ _ _ [] (.call 1 [.eps,.eps,.eps,.call 0 [.eps]]) x.length=none
  rw [evV_call_par hh rfl (by decide),evPar_cons_ok rfl,evPar_cons_ok rfl,evPar_cons_ok rfl,evPar_cons_none hcall]

theorem cycle_target (b : List Nat) (hb : RepeatedCopySyntax.patternCheck arity b=true) (x : List Char) (k : Nat) :
    evV (RepeatedCopySyntax.target [] cycleClients arity d b) x .callByValueSeq (tblV (RepeatedCopySyntax.target [] cycleClients arity d b) x .callByValueSeq k) []
      (emit 0 1 arity b cycleEntry) x.length=none :=
  (RepeatedCopyCorrespondence.physical [] cycleClients arity alphabet d b cycleRequired cycleEntry (cycle_checked b hb) x k x.length (Nat.le_refl _)).symm.trans (cycle_source b x k)


theorem preflight_cannot_be_omitted :
    evV (RepeatedCopySyntax.target [] cycleClients arity d body) [] .callByValueSeq
      (tblV (RepeatedCopySyntax.target [] cycleClients arity d body) [] .callByValueSeq 1) []
      (.seq (.call 1 []) (.alt (.notP .any)
        (DelimitedPatternEvaluation.passes 2 (emitArgs 0 1 arity body cycleActuals) (List.range arity)))) 0=some (some 0) := by decide +kernel

end Shallot.MacroPeg.CBV.RepeatedCopyProofs
