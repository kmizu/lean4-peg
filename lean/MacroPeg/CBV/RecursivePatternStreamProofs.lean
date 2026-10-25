import MacroPeg.CBV.RecursivePatternExamples

namespace Shallot.MacroPeg.CBV.RecursivePatternStreamProofs
open RecursivePatternSyntax RecursivePatternExamples
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
  have hnew : original.FirstOrder := source_firstOrder clients arity d pattern
  have hold : DelimitedCopyExamples.original.FirstOrder := hold
  rw [←decideObsV_iff hnew (by decide) (show (MExp.call i []).FirstOrder from True.intro),
    ←decideObsV_iff hold (by decide) (show (MExp.call i []).FirstOrder from True.intro)]
  unfold decideObsV
  rw [ScannerPairFusion.stable_result_eq _ _ x _ _ _ _ (fun k => base_query i hi x k x.length (Nat.le_refl _))]

private theorem observed (e : MExp) (he : e.FirstOrder) (x rest : List Char) (k : Nat)
    (hs : ∃ a, x=a++rest)
    (hv : evV original x .callByValuePar (tblV original x .callByValuePar k) [] e x.length=some (some rest.length)) :
    SObs original .callByValuePar e x (some rest) := by
  obtain ⟨o,hd,ho⟩ := evV_sound (by decide) (tblV_sound (source_firstOrder clients arity d pattern) (by decide) k) e he _ (Nat.le_refl _) _ hv
  obtain ⟨t,actual,rfl,hlen⟩ := obsR_ok ho
  have hre : actual=rest := by
    have hh := rest_eq_sfx' hd
    rw [hlen] at hh
    exact hh.symm.trans (sfx_suffix hs.choose_spec)
  subst actual
  exact ⟨_,by simpa only [sfx_self,original] using hd,rfl⟩

private theorem user_observed (i : Nat) (e : RecursivePatternSyntax.Expr) (hi : clients[i]?=some e)
    (x rest : List Char) (he : SObs original .callByValuePar (render clients.length true e) x (some rest)) :
    SObs original .callByValuePar (.call i []) x (some rest) := by
  obtain ⟨o,hd,ho⟩ := he
  have hh : MDerives original .callByValuePar (MExp.subst [] (render clients.length true e)) x o := by
    rw [ReplayFallbackFusion.subst_closed [] _ (source_closed _ _)]
    exact hd
  simpa only [ho,original] using call0_obs (source_user clients arity d pattern i e hi) rfl hh

private def skipParts : Nat → List Part
  | 0 => []
  | n+1 => .gap::.lit [d]::skipParts n

private theorem skip_render (n : Nat) : render clients.length true (skipSegments n)=DelimiterTemplate.compile d (skipParts n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change MExp.seq (DelimiterTemplate.gap d) (.seq (.lit [d]) (render clients.length true (skipSegments n)))=
      .seq (DelimiterTemplate.gap d) (.seq (.lit [d]) (DelimiterTemplate.compile d (skipParts n)))
    rw [ih]

private theorem run_skips : ∀ segs : List (List Char), (∀ w∈segs, DelimitedCopyProjection.Free d w) → ∀ rest,
    DelimiterTemplate.run d [] (skipParts segs.length) (segs.flatMap (fun w => w++[d])++rest)=some rest
  | [],_,rest => rfl
  | w::ws,hw,rest => by
    apply (DelimitedCopyTemplates.run_gap_sep_iff d [] _ _ rest).mpr
    refine ⟨w,ws.flatMap (fun w => w++[d])++rest,hw w (by simp),?_,?_⟩
    · simp [List.append_assoc]
    · exact run_skips ws (fun v hv => hw v (by simp [hv])) rest

private theorem skip_observed (n : Nat) (rest : List Char) :
    SObs original .callByValuePar (render clients.length true (skipSegments pattern.length)) (block n++rest) (some rest) := by
  let segs := pattern.map (fun i => (RecursivePatternExamples.words n)[i]!)
  have hfree : ∀ w∈segs, DelimitedCopyProjection.Free d w := by
    intro w hw
    simp only [segs,pattern,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp [RecursivePatternExamples.words,DelimitedPatternExamples.words,DelimitedCopyExamples.long,DelimitedCopyExamples.short,DelimitedCopyProjection.Free,d]
  have hb : segs.flatMap (fun w => w++[d])=block n := by
    simp [segs,block,DelimitedPatternExamples.block,List.flatMap_map,pattern,d,DelimitedPatternExamples.d,DelimitedPatternExamples.pattern]
  have hl : segs.length=pattern.length := by simp [segs]
  have hr : DelimiterTemplate.run d [] (skipParts pattern.length) (block n++rest)=some rest := by
    simpa only [hl,hb] using run_skips segs hfree rest
  apply observed _ (render_firstOrder _ _ _) _ rest 0 ⟨block n,rfl⟩
  rw [skip_render,DelimiterTemplate.compile_eval _ _ _ _ _ d _ _ (Nat.le_refl _),sfx_self,hr]
  rfl

private theorem query_observed (n : Nat) (rest after : List Char)
    (h : SObs original .callByValuePar (render clients.length true (.alt (.notP .any) (.user 2))) rest (some after)) :
    SObs original .callByValuePar (render clients.length true queryNext) (block n++rest) (some (block n++rest)) :=
  RootObservation.not_fail (RootObservation.not_ok (RootObservation.seq_ok (skip_observed n rest) h))

private theorem a_star (n : Nat) : ∀ tail, ∃ t, MDerives original .callByValuePar (.star (.chr 'a'))
    (List.replicate n 'a'++'b'::tail) (.ok t ('b'::tail)) := by
  induction n with
  | zero => intro tail; exact ⟨_,.starNil _ _ (.chrFail 'a' 'b' tail (by decide))⟩
  | succ n ih =>
    intro tail
    obtain ⟨t,ht⟩ := ih tail
    exact ⟨_,.starCons _ _ _ _ _ _ (.chrOk 'a' 'a' _ (by decide)) ht⟩

private theorem block_split (n : Nat) (rest : List Char) : ∃ tail, block n++rest=DelimitedCopyExamples.long n++tail := by
  refine ⟨d::((pattern.drop 1).flatMap (fun i => (RecursivePatternExamples.words n)[i]!++[d])++rest),?_⟩
  simp [block,DelimitedPatternExamples.block,pattern,DelimitedPatternExamples.pattern,RecursivePatternExamples.words,DelimitedPatternExamples.words,d,DelimitedPatternExamples.d,List.append_assoc]

private theorem finish_block (n : Nat) (rest : List Char)
    (hq : SObs original .callByValuePar (render clients.length true queryNext) (block n++rest) (some (block n++rest))) :
    SObs original .callByValuePar (.call 2 []) (block n++rest) (some rest) ∧
      DerivesArgsPar original .callByValuePar (block n++rest) (renderArgs clients.length true actuals)
        ((RecursivePatternExamples.words n).map MExp.lit) := by
  let input := block n++rest
  obtain ⟨tail,hx⟩ := block_split n rest
  have ha : SObs original .callByValuePar (.call 0 []) input (some tail) := by
    rw [show input=DelimitedCopyExamples.long n++tail from hx]
    exact (base_observations 0 (by decide) _ _).mpr (DelimitedCopyExamples.balanced_capture n tail)
  have hb : SObs original .callByValuePar (.call 1 []) input (some (List.replicate n 'c'++tail)) := by
    rw [show input=DelimitedCopyExamples.long n++tail from hx]
    exact (base_observations 1 (by decide) _ _).mpr (DelimitedCopyExamples.short_capture n tail)
  obtain ⟨ta,hta⟩ := a_star n (List.replicate n 'c'++tail)
  have hc : SObs original .callByValuePar (.star (.chr 'a')) input (some ('b'::(List.replicate n 'c'++tail))) :=
    ⟨_,by simpa [input,hx,DelimitedCopyExamples.long,DelimitedCopyExamples.short,List.append_assoc] using hta,rfl⟩
  have h3 := user_observed 3 longActual rfl input _ (RootObservation.seq_ok hq ha)
  have h4 := user_observed 4 shortActual rfl input _ (RootObservation.seq_ok hq hb)
  have h5 := user_observed 5 starActual rfl input _ (RootObservation.seq_ok hq hc)
  have h6 := user_observed 6 emptyActual rfl input input (RootObservation.seq_ok hq ⟨_,.eps input,rfl⟩)
  obtain ⟨o3,hd3,he3⟩ := h3
  obtain ⟨t3,rfl⟩ := restOf_eq_some he3
  obtain ⟨o4,hd4,he4⟩ := h4
  obtain ⟨t4,rfl⟩ := restOf_eq_some he4
  obtain ⟨o5,hd5,he5⟩ := h5
  obtain ⟨t5,rfl⟩ := restOf_eq_some he5
  obtain ⟨o6,hd6,he6⟩ := h6
  obtain ⟨t6,rfl⟩ := restOf_eq_some he6
  have hargs : DerivesArgsPar original .callByValuePar input (renderArgs clients.length true actuals)
      ((RecursivePatternExamples.words n).map MExp.lit) :=
    .cons _ _ _ _ _ t3 _ hd3 hx
      (.cons _ _ _ _ _ t4 _ hd4 (by rw [show input=DelimitedCopyExamples.long n++tail from hx]; simp [DelimitedCopyExamples.long,List.append_assoc])
        (.cons _ _ _ _ _ t5 _ hd5 (by rw [show input=DelimitedCopyExamples.long n++tail from hx]; simp [DelimitedCopyExamples.long,DelimitedCopyExamples.short,List.append_assoc])
          (.cons _ _ _ _ _ t6 [] hd6 rfl (.nil _))))
  let parts := DelimitedWordPattern.sourceParts d pattern
  let body := DelimiterTemplate.compile d parts
  have hscope : ∀ i∈pattern, i<(RecursivePatternExamples.words n).length := by
    intro i hi; simp [pattern,RecursivePatternExamples.words,DelimitedPatternExamples.words] at hi ⊢; omega
  have hr : DelimiterTemplate.run d (RecursivePatternExamples.words n) parts input=some rest := by
    simpa only [input,parts,DelimitedWordPattern.encode,block,DelimitedPatternExamples.block,RecursivePatternExamples.words,pattern,DelimitedPatternExamples.pattern,d,DelimitedPatternExamples.d] using
      DelimitedWordPattern.run_encode d (RecursivePatternExamples.words n) pattern hscope rest
  have hfo : body.FirstOrder := DelimiterTemplate.compile_firstOrder _ _
  have hev : evV original input .callByValuePar (tblV original input .callByValuePar 0) []
      (MExp.subst ((RecursivePatternExamples.words n).map MExp.lit) body) input.length=some (some rest.length) := by
    have he := evV_subst (g := original) (x := input) (s := .callByValuePar)
      (T := tblV original input .callByValuePar 0) (E := []) (RecursivePatternExamples.words n) body hfo input.length
    have hh := DelimiterTemplate.compile_eval original input .callByValuePar
      (tblV original input .callByValuePar 0) (RecursivePatternExamples.words n) d parts input.length (Nat.le_refl _)
    simpa only [sfx_self,hr,Option.map_some] using he.trans hh
  have ho := observed _ (firstOrder_subst (firstOrderArgs_lits (RecursivePatternExamples.words n)) body hfo) input rest 0 ⟨block n,rfl⟩ hev
  obtain ⟨o,hd,he⟩ := ho
  obtain ⟨t,rfl⟩ := restOf_eq_some he
  have hcopy : SObs original .callByValuePar (render clients.length true RecursivePatternExamples.copyBody) input (some rest) :=
    ⟨_,MDerives.callParOk clients.length (renderArgs clients.length true actuals) ⟨arity,body⟩ input rest
      ((RecursivePatternExamples.words n).map MExp.lit) t rfl (source_copy clients arity d pattern) rfl hargs hd,rfl⟩
  exact ⟨user_observed 2 RecursivePatternExamples.copyBody rfl input rest hcopy,hargs⟩

def stream : List Nat → List Char
  | [] => []
  | n::ns => block n++stream ns

private theorem stream_nonempty (n : Nat) (ns : List Nat) : stream (n::ns)≠[] := by
  have hl : 0<(block n).length := by
    obtain ⟨tail,hx⟩ := block_split n []
    simp only [List.append_nil] at hx
    rw [hx,List.length_append]
    have hh : 0<(DelimitedCopyExamples.long n).length := by simp [DelimitedCopyExamples.long,DelimitedCopyExamples.short]; omega
    omega
  intro he
  have he := congrArg List.length he
  simp only [stream,List.length_append,List.length_nil] at he
  omega

/-- Recursive validation of every later block closes for arbitrary numbers
of blocks and arbitrary unbounded producer lengths, not only native samples. -/
theorem source_block_and_actuals (n : Nat) (ns : List Nat) :
    SObs original .callByValuePar (.call 2 []) (block n++stream ns) (some (stream ns)) ∧
      DerivesArgsPar original .callByValuePar (block n++stream ns) (renderArgs clients.length true actuals)
        ((RecursivePatternExamples.words n).map MExp.lit) := by
  induction ns generalizing n with
  | nil =>
    have heof : SObs original .callByValuePar (.notP .any) [] (some []) := RootObservation.not_fail ⟨_,.anyFail,rfl⟩
    exact finish_block n [] (query_observed n [] [] (RootObservation.alt_left heof))
  | cons m ms ih =>
    have hf : SObs original .callByValuePar (.notP .any) (stream (m::ms)) none := by
      cases hx : stream (m::ms) with
      | nil => exact False.elim (stream_nonempty m ms hx)
      | cons c rest => exact RootObservation.not_ok ⟨_,.anyOk c rest,rfl⟩
    exact finish_block n (stream (m::ms))
      (query_observed n (stream (m::ms)) (stream ms) (RootObservation.alt_right hf (ih m).1))

private theorem empty_copy_fails : SObs original .callByValuePar (.call 2 []) [] none := by
  have hv : evV original [] .callByValuePar (tblV original [] .callByValuePar 2) [] (.call 2 []) 0=some none := by decide +kernel
  obtain ⟨o,hd,ho⟩ := evV_sound (by decide) (tblV_sound (source_firstOrder clients arity d pattern) (by decide) 2)
    (.call 2 []) True.intro 0 (by decide) none hv
  cases o with
  | fail => exact ⟨_,by simpa [sfx,original] using hd,rfl⟩
  | ok t rest => simp [obsR] at ho

private theorem star_observed : ∀ ns : List Nat,
    SObs original .callByValuePar (.star (.call 2 [])) (stream ns) (some [])
  | [] => by
    obtain ⟨o,hd,ho⟩ := empty_copy_fails
    rw [restOf_eq_none ho] at hd
    exact ⟨_,.starNil _ _ hd,rfl⟩
  | n::ns => by
    obtain ⟨oh,hh,he⟩ := (source_block_and_actuals n ns).1
    obtain ⟨th,rfl⟩ := restOf_eq_some he
    obtain ⟨ot,ht,he'⟩ := star_observed ns
    obtain ⟨tt,rfl⟩ := restOf_eq_some he'
    exact ⟨_,.starCons _ _ _ _ _ _ hh ht,rfl⟩

theorem source_and_target_all_streams (ns : List Nat) :
    SObs original .callByValuePar originalRoot (stream ns) (some []) ∧
      SObs generated .callByValueSeq generatedRoot (stream ns) (some []) := by
  have hs : SObs original .callByValuePar originalRoot (stream ns) (some []) :=
    RootObservation.seq_ok (star_observed ns) (RootObservation.not_fail ⟨_,.anyFail,rfl⟩)
  exact ⟨hs,(RecursivePatternCompiler.observations_iff original originalRoot clients arity alphabet d pattern entry checked (stream ns) (some [])).mp hs⟩

end Shallot.MacroPeg.CBV.RecursivePatternStreamProofs
