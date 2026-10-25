import MacroPeg.CBV.DelimitedPatternExamples

namespace Shallot.MacroPeg.CBV.DelimitedPatternCaptureProofs
open DelimitedPatternExamples DelimitedPatternCompiler DelimitedWordPattern DelimiterTemplate

private theorem library_valid : RecursiveParserStability.Valid bodies :=
  (checked original originalRoot bodies args alphabet d pattern DelimitedPatternExamples.checked).1.library
private theorem library_old : RecursiveParserStability.Installed bodies DelimitedCopyExamples.original := by
  intro i b hi
  cases i with
  | zero => have he : b=FiniteResidualControl.balancedBody := by simpa [bodies] using hi.symm
            subst b; rfl
  | succ i => cases i with
    | zero => have he : b=FiniteResidualControl.consumePrefix := by simpa [bodies] using hi.symm
              subst b; rfl
    | succ i => simp [bodies] at hi

private theorem helper_observations (i : Nat) (hi : i<bodies.length) (x : List Char) (rest : Option (List Char)) :
    SObs original .callByValuePar (.call i []) x rest ↔ SObs DelimitedCopyExamples.original .callByValuePar (.call i []) x rest := by
  have hold := DelimitedCopySyntax.source_firstOrder DelimitedCopyExamples.bodies DelimitedCopyExamples.d
    (DelimitedCopyCompiler.checked DelimitedCopyExamples.original DelimitedCopyExamples.originalRoot
      DelimitedCopyExamples.bodies DelimitedCopyExamples.alphabet DelimitedCopyExamples.d DelimitedCopyExamples.entry DelimitedCopyExamples.checked).1
  have hnew : original.FirstOrder := source_firstOrder bodies args.length d pattern library_valid
  have hold : DelimitedCopyExamples.original.FirstOrder := hold
  rw [←decideObsV_iff hnew (by decide) (show (MExp.call i []).FirstOrder from True.intro),
    ←decideObsV_iff hold (by decide) (show (MExp.call i []).FirstOrder from True.intro)]
  unfold decideObsV
  have hphysical (k : Nat) :
      evV original x .callByValuePar (tblV original x .callByValuePar k) [] (.call i []) x.length=
        evV DelimitedCopyExamples.original x .callByValuePar (tblV DelimitedCopyExamples.original x .callByValuePar k) [] (.call i []) x.length :=
    RecursiveParserStability.lexical_eval (source_installed bodies args.length d pattern) library_old x _ _ _ _ (tblV_ok _ _ _ k)
      (fun j hj q hq => congrArg (fun row => valAt row q) (RecursiveParserStability.helper_rows_eq library_valid (source_installed bodies args.length d pattern) library_old x _ _ k j hj [] [])) [] [] (.call i []) hi x.length (Nat.le_refl _)
  rw [ScannerPairFusion.stable_result_eq _ _ x _ _ _ _ hphysical]

private theorem a_star (n : Nat) : ∀ tail, ∃ t, MDerives original .callByValuePar (.star (.chr 'a'))
    (List.replicate n 'a'++'b'::tail) (.ok t ('b'::tail)) := by
  induction n with
  | zero => intro tail; exact ⟨_,.starNil _ _ (.chrFail 'a' 'b' tail (by decide))⟩
  | succ n ih =>
    intro tail
    obtain ⟨t,ht⟩ := ih tail
    exact ⟨_,.starCons _ _ _ _ _ _ (.chrOk 'a' 'a' _ (by decide)) ht⟩

/-- All four actual DelimitedPatternExamples.words are captured in the real source derivation,
including three unbounded prefixes with different endpoints and an empty one. -/
theorem actual_captures (n : Nat) (rest : List Char) :
    DerivesArgsPar original .callByValuePar (DelimitedCopyExamples.long n++rest) args ((DelimitedPatternExamples.words n).map MExp.lit) := by
  obtain ⟨o,hd,ho⟩ := (helper_observations 0 (by decide) _ _).mpr (DelimitedCopyExamples.balanced_capture n rest)
  obtain ⟨t,rfl⟩ := restOf_eq_some ho
  obtain ⟨o',hd',ho'⟩ := (helper_observations 1 (by decide) _ _).mpr (DelimitedCopyExamples.short_capture n rest)
  obtain ⟨t',rfl⟩ := restOf_eq_some ho'
  obtain ⟨ta,ha⟩ := a_star n (List.replicate n 'c'++rest)
  have ha : MDerives original .callByValuePar (.star (.chr 'a'))
      (DelimitedCopyExamples.long n++rest) (.ok ta ('b'::(List.replicate n 'c'++rest))) := by
    simpa [DelimitedCopyExamples.long,DelimitedCopyExamples.short,List.append_assoc] using ha
  refine .cons _ _ _ _ _ t _ hd rfl (.cons _ _ _ _ _ t' _ hd' ?_ (.cons _ _ _ _ _ ta _ ha ?_ (.cons _ _ _ _ _ _ [] (.eps _) rfl (.nil _))))
  · simp [DelimitedCopyExamples.long,List.append_assoc]
  · simp [DelimitedCopyExamples.long,DelimitedCopyExamples.short,List.append_assoc]

private theorem block_split (n : Nat) : ∃ tail, block n=DelimitedCopyExamples.long n++tail := by
  exact ⟨d::(pattern.drop 1).flatMap (fun i => (DelimitedPatternExamples.words n)[i]!++[d]),by simp [block,pattern,DelimitedPatternExamples.words,List.append_assoc]⟩

/-- No finite sample bound: every length n is accepted by the real source
and its fixed generated Seq grammar. -/
theorem all_lengths (n : Nat) :
    SObs original .callByValuePar originalRoot (block n) (some []) ∧
      SObs generated .callByValueSeq generatedRoot (block n) (some []) := by
  obtain ⟨tail,hx⟩ := block_split n
  have hargs : DerivesArgsPar original .callByValuePar (block n) args ((DelimitedPatternExamples.words n).map MExp.lit) := by rw [hx]; exact actual_captures n tail
  have hscope : ∀ i∈pattern, i<(DelimitedPatternExamples.words n).length := by intro i hi; simp [pattern,DelimitedPatternExamples.words] at hi ⊢; omega
  have hr : run d (DelimitedPatternExamples.words n) (sourceParts d pattern) (block n)=some [] := by
    simpa only [List.append_nil,encode,block] using run_encode d (DelimitedPatternExamples.words n) pattern hscope []
  let body := compile d (sourceParts d pattern)
  have hfo : body.FirstOrder := compile_firstOrder _ _
  have hev : evV original (block n) .callByValuePar (tblV original (block n) .callByValuePar 0) []
      (MExp.subst ((DelimitedPatternExamples.words n).map MExp.lit) body) (block n).length=some (some 0) := by
    have he := evV_subst (g := original) (x := block n) (s := .callByValuePar)
      (T := tblV original (block n) .callByValuePar 0) (E := []) (DelimitedPatternExamples.words n) body hfo (block n).length
    have hh := compile_eval original (block n) .callByValuePar (tblV original (block n) .callByValuePar 0)
      (DelimitedPatternExamples.words n) d (sourceParts d pattern) (block n).length (Nat.le_refl _)
    simpa only [sfx_self,hr,Option.map_some,List.length_nil] using he.trans hh
  obtain ⟨o,hd,ho⟩ := evV_sound (by decide) (tblV_sound (source_firstOrder bodies args.length d pattern library_valid) (by decide) 0)
    _ (firstOrder_subst (firstOrderArgs_lits (DelimitedPatternExamples.words n)) body hfo) _ (Nat.le_refl _) _ hev
  obtain ⟨t,actual,rfl,hlen⟩ := obsR_ok ho
  have he : actual=[] := List.eq_nil_of_length_eq_zero hlen
  subst actual
  have hs : SObs original .callByValuePar originalRoot (block n) (some []) :=
    ⟨_,.callParOk bodies.length args ⟨args.length,body⟩ (block n) [] ((DelimitedPatternExamples.words n).map MExp.lit) t
      rfl (source_rule bodies args.length d pattern) rfl hargs (by simpa only [sfx_self,original] using hd),rfl⟩
  exact ⟨hs,(observations_iff original originalRoot bodies args alphabet d pattern DelimitedPatternExamples.checked (block n) (some [])).mp hs⟩

theorem three_unbounded (bound : Nat) : ∃ n,
    bound<((DelimitedPatternExamples.words n)[0]!).length ∧
    bound<((DelimitedPatternExamples.words n)[1]!).length ∧
    bound<((DelimitedPatternExamples.words n)[2]!).length := by
  refine ⟨bound+1,?_⟩
  simp [DelimitedPatternExamples.words,DelimitedCopyExamples.long,DelimitedCopyExamples.short]
  omega

end Shallot.MacroPeg.CBV.DelimitedPatternCaptureProofs
