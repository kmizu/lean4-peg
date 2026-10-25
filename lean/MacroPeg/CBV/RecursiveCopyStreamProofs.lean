import MacroPeg.CBV.RecursiveCopyExamples

namespace Shallot.MacroPeg.CBV.RecursiveCopyStreamProofs
open RecursiveCopySyntax RecursiveCopyExamples
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
  rw [←decideObsV_iff (source_firstOrder clients d) (by decide) (show (MExp.call i []).FirstOrder from True.intro),
    ←decideObsV_iff hold (by decide) (show (MExp.call i []).FirstOrder from True.intro)]
  unfold decideObsV
  rw [ScannerPairFusion.stable_result_eq _ _ x _ _ _ _ (fun k => base_query i hi x k x.length (Nat.le_refl _))]

private theorem observed (e : MExp) (he : e.FirstOrder) (x rest : List Char) (k : Nat)
    (hs : ∃ a, x=a++rest)
    (hv : evV original x .callByValuePar (tblV original x .callByValuePar k) [] e x.length=some (some rest.length)) :
    SObs original .callByValuePar e x (some rest) := by
  obtain ⟨o,hd,ho⟩ := evV_sound (by decide) (tblV_sound (source_firstOrder clients d) (by decide) k) e he _ (Nat.le_refl _) _ hv
  obtain ⟨t,actual,rfl,hlen⟩ := obsR_ok ho
  have hre : actual=rest := by
    have hh := rest_eq_sfx' hd
    rw [hlen] at hh
    exact hh.symm.trans (sfx_suffix hs.choose_spec)
  subst actual
  exact ⟨_,by simpa only [sfx_self] using hd,rfl⟩

private theorem user_observed (i : Nat) (e : RecursiveCopySyntax.Expr) (hi : clients[i]?=some e)
    (x rest : List Char) (he : SObs original .callByValuePar (render clients.length true e) x (some rest)) :
    SObs original .callByValuePar (.call i []) x (some rest) := by
  obtain ⟨o,hd,ho⟩ := he
  have hh : MDerives original .callByValuePar (MExp.subst [] (render clients.length true e)) x o := by
    rw [ReplayFallbackFusion.subst_closed [] _ (render_closed _ _ _)]
    exact hd
  simpa only [ho] using call0_obs (source_user clients d i e hi) rfl hh

private theorem short_free (n : Nat) : DelimitedCopyProjection.Free d (short n) := by
  simp [DelimitedCopyProjection.Free,short,DelimitedCopyExamples.short,d]
private theorem long_free (n : Nat) : DelimitedCopyProjection.Free d (long n) := by
  simp [DelimitedCopyProjection.Free,long,short,DelimitedCopyExamples.long,DelimitedCopyExamples.short,d]

private theorem skip_observed (n : Nat) (rest : List Char) :
    SObs original .callByValuePar (render clients.length true skipBlock) (block n++rest) (some rest) := by
  let parts : List Part := [.gap,.lit [d],.gap,.lit [d],.gap,.lit [d]]
  have hr : DelimiterTemplate.run d [] parts (block n++rest)=some rest := by
    apply (DelimitedCopyTemplates.run_gap_sep_iff d [] _ _ rest).mpr
    refine ⟨long n,short n++d::(long n++d::rest),long_free n,?_,?_⟩
    · simp [block,DelimitedCopyExamples.block,DelimitedCopyExamples.d,d,List.append_assoc]
    · apply (DelimitedCopyTemplates.run_gap_sep_iff d [] _ _ rest).mpr
      refine ⟨short n,long n++d::rest,short_free n,rfl,?_⟩
      exact (DelimitedCopyTemplates.run_gap_sep_iff d [] [] _ rest).mpr ⟨long n,rest,long_free n,rfl,rfl⟩
  apply observed _ (render_firstOrder _ _ _) _ rest 0 ⟨block n,rfl⟩
  change evV original (block n++rest) .callByValuePar (tblV original (block n++rest) .callByValuePar 0) []
    (DelimiterTemplate.compile d parts) (block n++rest).length=some (some rest.length)
  rw [DelimiterTemplate.compile_eval _ _ _ _ _ d parts _ (Nat.le_refl _),sfx_self,hr]
  rfl


private theorem query_observed (n : Nat) (rest after : List Char)
    (h : SObs original .callByValuePar (render clients.length true (.alt (.notP .any) (.user 2))) rest (some after)) :
    SObs original .callByValuePar (render clients.length true queryNext) (block n++rest) (some (block n++rest)) :=
  RootObservation.not_fail (RootObservation.not_ok (RootObservation.seq_ok (skip_observed n rest) h))

private theorem finish_block (n : Nat) (rest : List Char)
    (hq : SObs original .callByValuePar (render clients.length true queryNext) (block n++rest) (some (block n++rest))) :
    SObs original .callByValuePar (.call 2 []) (block n++rest) (some rest) ∧
      DerivesArgsPar original .callByValuePar (block n++rest) [.call 3 [],.call 4 []] [.lit (short n),.lit (long n)] := by
  let input := block n++rest
  let tail := d::(short n++d::(long n++d::rest))
  have hx : input=long n++tail := by simp [input,tail,block,DelimitedCopyExamples.block,DelimitedCopyExamples.d,d,List.append_assoc]
  have ha : SObs original .callByValuePar (.call 1 []) input (some (List.replicate n 'c'++tail)) := by
    rw [hx]
    exact (base_observations 1 (by decide) _ _).mpr (DelimitedCopyExamples.short_capture n tail)
  have hb : SObs original .callByValuePar (.call 0 []) input (some tail) := by
    rw [hx]
    exact (base_observations 0 (by decide) _ _).mpr (DelimitedCopyExamples.balanced_capture n tail)
  have h3 := user_observed 3 shortActual rfl input _ (RootObservation.seq_ok hq ha)
  have h4 := user_observed 4 longActual rfl input _ (RootObservation.seq_ok hq hb)
  obtain ⟨o3,hd3,he3⟩ := h3
  obtain ⟨t3,rfl⟩ := restOf_eq_some he3
  obtain ⟨o4,hd4,he4⟩ := h4
  obtain ⟨t4,rfl⟩ := restOf_eq_some he4
  have hargs : DerivesArgsPar original .callByValuePar input [.call 3 [],.call 4 []] [.lit (short n),.lit (long n)] :=
    .cons _ _ _ _ _ t3 _ hd3 (by rw [hx]; simp [long,DelimitedCopyExamples.long,List.append_assoc])
      (.cons _ _ _ _ _ t4 [] hd4 hx (.nil _))
  let parts := DelimitedCopyTemplates.sourceBlockParts d
  let body := DelimiterTemplate.compile d parts
  have hr : DelimiterTemplate.run d [short n,long n] parts input=some rest :=
    (DelimitedCopyTemplates.source_block d (short n) (long n) input rest).mpr (by rw [hx])
  have heFO : body.FirstOrder := DelimiterTemplate.compile_firstOrder d parts
  have hev : evV original input .callByValuePar (tblV original input .callByValuePar 0) []
      (MExp.subst [.lit (short n),.lit (long n)] body) input.length=some (some rest.length) := by
    have he := evV_subst (g := original) (x := input) (s := .callByValuePar)
      (T := tblV original input .callByValuePar 0) (E := []) [short n,long n] body heFO input.length
    have hh := DelimiterTemplate.compile_eval original input .callByValuePar
      (tblV original input .callByValuePar 0) [short n,long n] d parts input.length (Nat.le_refl _)
    simpa only [sfx_self,hr,Option.map_some,List.map_cons,List.map_nil] using he.trans hh
  have ho := observed _ (firstOrder_subst (firstOrderArgs_lits [short n,long n]) body heFO) input rest 0 ⟨block n,rfl⟩ hev
  obtain ⟨o,hd,he⟩ := ho
  obtain ⟨t,rfl⟩ := restOf_eq_some he
  have hcopy : SObs original .callByValuePar (render clients.length true RecursiveCopyExamples.copyBody) input (some rest) :=
    ⟨_,MDerives.callParOk clients.length [.call 3 [],.call 4 []] ⟨2,body⟩ input rest [.lit (short n),.lit (long n)] t
      rfl (source_copy clients d) rfl hargs hd,rfl⟩
  exact ⟨user_observed 2 RecursiveCopyExamples.copyBody rfl input rest hcopy,hargs⟩

def stream : List Nat → List Char
  | [] => []
  | n::ns => block n++stream ns

private theorem stream_nonempty (n : Nat) (ns : List Nat) : stream (n::ns)≠[] := by
  have hl : 0<(block n).length := by simp [block,DelimitedCopyExamples.block,DelimitedCopyExamples.long,DelimitedCopyExamples.short]; omega
  intro he
  have he := congrArg List.length he
  simp only [stream,List.length_append,List.length_nil] at he
  omega

/-- Recursive validation of every later block closes for arbitrary numbers
of blocks and arbitrary unbounded producer lengths, not only native samples. -/
theorem source_block_and_actuals (n : Nat) (ns : List Nat) :
    SObs original .callByValuePar (.call 2 []) (block n++stream ns) (some (stream ns)) ∧
      DerivesArgsPar original .callByValuePar (block n++stream ns) [.call 3 [],.call 4 []] [.lit (short n),.lit (long n)] := by
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
  obtain ⟨o,hd,ho⟩ := evV_sound (by decide) (tblV_sound (source_firstOrder clients d) (by decide) 2)
    (.call 2 []) True.intro 0 (by decide) none hv
  cases o with
  | fail => exact ⟨_,by simpa [sfx] using hd,rfl⟩
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
  exact ⟨hs,(RecursiveCopyCompiler.observations_iff original originalRoot clients alphabet d entry checked (stream ns) (some [])).mp hs⟩

end Shallot.MacroPeg.CBV.RecursiveCopyStreamProofs
