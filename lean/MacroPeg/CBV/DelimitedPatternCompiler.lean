import MacroPeg.CBV.DelimitedPatternEvaluation

namespace Shallot.MacroPeg.CBV.DelimitedPatternCompiler
open DelimiterTemplate DelimitedWordPattern
open RecursiveParserStability (Lexical Installed)

def source (bodies : List MExp) (arity : Nat) (d : Char) (js : List Nat) : MGrammar :=
  ⟨bodies.map (fun b => ⟨0,b⟩)++[⟨arity,compile d (sourceParts d js)⟩]⟩
def target (bodies : List MExp) (arity : Nat) (d : Char) (js : List Nat) : MGrammar :=
  ⟨bodies.map (fun b => ⟨0,b⟩)++(List.range arity).map (fun i => ⟨1,compile d (afterParts d i js)⟩)⟩
def root (bodies : List MExp) (args : List MExp) : MExp := .call bodies.length args
def targetRoot (bodies : List MExp) (args : List MExp) : MExp := DelimitedPatternEvaluation.targetHead bodies.length args

def checkCore (bodies args : List MExp) (alphabet : List Char) (d : Char) (js : List Nat) : Bool :=
  decide (0<args.length ∧ js≠[]) && bodies.all (DelimitedCopySyntax.lexicalCheck bodies.length) &&
    args.all (DelimitedCopySyntax.lexicalCheck bodies.length) && decide (d∉alphabet) &&
    args.all (MaskedScannerAbsorption.check bodies alphabet) && js.all (fun i => decide (i<args.length))

def check (g : MGrammar) (start : MExp) (bodies args : List MExp) (alphabet : List Char) (d : Char) (js : List Nat) : Bool :=
  checkCore bodies args alphabet d js && FiniteSuffixCallCompiler.sameRules g.rules (source bodies args.length d js).rules && MExp.beqE start (root bodies args)

structure Checked (bodies args : List MExp) (alphabet : List Char) (d : Char) (js : List Nat) : Prop where
  nonempty : 0<args.length
  pattern : js≠[]
  library : RecursiveParserStability.Valid bodies
  actuals : ∀ a∈args, Lexical bodies.length a
  separator : d∉alphabet
  safe : ∀ a∈args, MaskedScannerAbsorption.Valid bodies (MaskedScannerAbsorption.mask bodies alphabet) alphabet ∧
    MaskedScannerAbsorption.Safe (MaskedScannerAbsorption.mask bodies alphabet) alphabet a
  scope : ∀ i∈js, i<args.length

theorem checkedCore (bodies args : List MExp) (alphabet : List Char) (d : Char) (js : List Nat)
    (hc : checkCore bodies args alphabet d js=true) : Checked bodies args alphabet d js := by
  simp only [checkCore,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨hn,hl⟩,ha⟩,hd⟩,hs⟩,hj⟩ := hc
  have hn := of_decide_eq_true hn
  exact ⟨hn.1,hn.2,fun b hb => DelimitedCopySyntax.lexical_checked _ b (List.all_eq_true.mp hl b hb),
    fun a hm => DelimitedCopySyntax.lexical_checked _ a (List.all_eq_true.mp ha a hm),
    of_decide_eq_true hd,fun a hm => MaskedScannerAbsorption.checked _ _ a (List.all_eq_true.mp hs a hm),
    fun i hi => of_decide_eq_true (List.all_eq_true.mp hj i hi)⟩

theorem checked (g : MGrammar) (start : MExp) (bodies args : List MExp) (alphabet : List Char) (d : Char) (js : List Nat)
    (hc : check g start bodies args alphabet d js=true) :
    Checked bodies args alphabet d js ∧ g=source bodies args.length d js ∧ start=root bodies args := by
  obtain ⟨h,hs⟩ := Bool.and_eq_true_iff.mp hc
  obtain ⟨hc,hg⟩ := Bool.and_eq_true_iff.mp h
  have hg := FiniteSuffixCallCompiler.sameRules_checked _ _ hg
  refine ⟨checkedCore _ _ _ _ _ hc,?_,(MExp.beqE_iff _ _).mp hs⟩
  cases g; simp_all

theorem source_installed (bodies : List MExp) (arity : Nat) (d : Char) (js : List Nat) :
    Installed bodies (source bodies arity d js) := DelimitedCopySyntax.installed_append _ _
theorem target_installed (bodies : List MExp) (arity : Nat) (d : Char) (js : List Nat) :
    Installed bodies (target bodies arity d js) := DelimitedCopySyntax.installed_append _ _

theorem source_rule (bodies : List MExp) (arity : Nat) (d : Char) (js : List Nat) :
    ruleAtM (source bodies arity d js).rules bodies.length=some ⟨arity,compile d (sourceParts d js)⟩ := by
  simp [source,ruleAtM_eq_getElem?,List.getElem?_append_right,List.length_map]
theorem target_rule (bodies : List MExp) (arity : Nat) (d : Char) (js : List Nat) (i : Nat) (hi : i<arity) :
    ruleAtM (target bodies arity d js).rules (bodies.length+i)=some ⟨1,compile d (afterParts d i js)⟩ := by
  simp [target,ruleAtM_eq_getElem?,List.getElem?_append_right,List.length_map,List.getElem?_map,List.getElem?_range hi]

theorem source_firstOrder (bodies : List MExp) (arity : Nat) (d : Char) (js : List Nat)
    (hb : RecursiveParserStability.Valid bodies) : (source bodies arity d js).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with h|h
  · obtain ⟨b,hm,rfl⟩ := List.mem_map.mp h
    exact RecursiveParserStability.lexical_firstOrder _ b (hb b hm)
  · have he : r=⟨arity,compile d (sourceParts d js)⟩ := by simpa using h
    subst r; exact compile_firstOrder _ _
theorem target_firstOrder (bodies : List MExp) (arity : Nat) (d : Char) (js : List Nat)
    (hb : RecursiveParserStability.Valid bodies) : (target bodies arity d js).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with h|h
  · obtain ⟨b,hm,rfl⟩ := List.mem_map.mp h
    exact RecursiveParserStability.lexical_firstOrder _ b (hb b hm)
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp h
    exact compile_firstOrder _ _

theorem args_firstOrder : ∀ (args : List MExp) (n : Nat), (∀ a∈args, Lexical n a) → MExp.FirstOrderArgs args
  | [],_,_ => True.intro
  | a::args,n,h => ⟨RecursiveParserStability.lexical_firstOrder _ a (h a (by simp)),args_firstOrder args n (fun b hb => h b (by simp [hb]))⟩
theorem preflight_firstOrder : ∀ (args : List MExp), MExp.FirstOrderArgs args → (DelimitedPatternEvaluation.preflight args).FirstOrder
  | [],_ => True.intro
  | a::args,h => ⟨h.1,preflight_firstOrder args h.2⟩
theorem passes_firstOrder (n : Nat) (args : List MExp) (ha : MExp.FirstOrderArgs args) :
    ∀ is, (∀ i∈is, i<args.length) → (DelimitedPatternEvaluation.passes n args is).FirstOrder
  | [],_ => True.intro
  | [i],h => by
    rw [DelimitedPatternEvaluation.passes,DelimitedPatternEvaluation.argument_eq args i (h i (by simp))]
    exact ⟨DelimitedPatternEvaluation.firstOrder_get args ha i (h i (by simp)),True.intro⟩
  | i::j::is,h => by
    rw [DelimitedPatternEvaluation.passes,DelimitedPatternEvaluation.argument_eq args i (h i (by simp))]
    exact ⟨⟨DelimitedPatternEvaluation.firstOrder_get args ha i (h i (by simp)),True.intro⟩,
      passes_firstOrder n args ha (j::is) (fun k hk => h k (by simp [hk]))⟩

theorem firstOrder (bodies args : List MExp) (alphabet : List Char) (d : Char) (js : List Nat)
    (hc : Checked bodies args alphabet d js) :
    (source bodies args.length d js).FirstOrder ∧ (root bodies args).FirstOrder ∧
      (target bodies args.length d js).FirstOrder ∧ (targetRoot bodies args).FirstOrder := by
  have ha := args_firstOrder args bodies.length hc.actuals
  exact ⟨source_firstOrder _ _ _ _ hc.library,ha,target_firstOrder _ _ _ _ hc.library,
    preflight_firstOrder args ha,passes_firstOrder _ args ha _ (fun i hi => List.mem_range.mp hi)⟩

theorem core_physical (bodies args : List MExp) (alphabet : List Char) (d : Char) (js : List Nat)
    (hc : Checked bodies args alphabet d js) (x : List Char) (k p : Nat) (hp : p≤x.length) :
    evV (source bodies args.length d js) x .callByValuePar (tblV (source bodies args.length d js) x .callByValuePar k) [] (root bodies args) p=
      evV (target bodies args.length d js) x .callByValueSeq (tblV (target bodies args.length d js) x .callByValueSeq k) [] (targetRoot bodies args) p := by
  cases js with
  | nil => exact False.elim (hc.pattern rfl)
  | cons j js =>
    apply DelimitedPatternEvaluation.physical _ _ bodies.length d j js args hc.nonempty hc.scope
      (source_rule _ _ _ _) (target_rule _ _ _ _) (source_firstOrder _ _ _ _ hc.library)
      (args_firstOrder args bodies.length hc.actuals) x k p hp
    · intro a ha
      exact RecursiveParserStability.lexical_eval (source_installed bodies args.length d (j::js)) (target_installed bodies args.length d (j::js)) x _ _ _ _ (tblV_ok _ _ _ k)
        (fun i hi q hq => congrArg (fun row => valAt row q) (RecursiveParserStability.helper_rows_eq hc.library (source_installed bodies args.length d (j::js)) (target_installed bodies args.length d (j::js)) x _ _ k i hi [] [])) [] [] a (hc.actuals a ha) p hp
    · intro i hi q hv
      have ha := hc.safe args[i] (List.getElem_mem hi)
      exact CaptureDelimiterSafety.captured_free (source_installed bodies args.length d (j::js))
        (source_firstOrder _ _ _ _ hc.library) _ alphabet ha.1 d hc.separator args[i] ha.2
        (RecursiveParserStability.lexical_firstOrder _ _ (hc.actuals args[i] (List.getElem_mem hi))) x .callByValuePar (by decide) k p q hp hv

theorem physical (g : MGrammar) (start : MExp) (bodies args : List MExp) (alphabet : List Char) (d : Char) (js : List Nat)
    (hc : check g start bodies args alphabet d js=true) (x : List Char) (k : Nat) :
    evV g x .callByValuePar (tblV g x .callByValuePar k) [] start x.length=
      evV (target bodies args.length d js) x .callByValueSeq (tblV (target bodies args.length d js) x .callByValueSeq k) [] (targetRoot bodies args) x.length := by
  obtain ⟨he,rfl,rfl⟩ := checked g start bodies args alphabet d js hc
  exact core_physical _ _ _ _ _ he x k _ (Nat.le_refl _)

theorem observations_iff (g : MGrammar) (start : MExp) (bodies args : List MExp) (alphabet : List Char) (d : Char) (js : List Nat)
    (hc : check g start bodies args alphabet d js=true) (x : List Char) (rest : Option (List Char)) :
    SObs g .callByValuePar start x rest ↔ SObs (target bodies args.length d js) .callByValueSeq (targetRoot bodies args) x rest := by
  obtain ⟨he,rfl,rfl⟩ := checked g start bodies args alphabet d js hc
  have hf := firstOrder _ _ _ _ _ he
  rw [←decideObsV_iff hf.1 (by decide) hf.2.1,←decideObsV_iff hf.2.2.1 (by decide) hf.2.2.2]
  unfold decideObsV
  rw [ScannerPairFusion.stable_result_eq _ _ x _ _ _ _ (fun k => core_physical _ _ _ _ _ he x k _ (Nat.le_refl _))]

theorem language_translation (g : MGrammar) (start : MExp) (bodies args : List MExp) (alphabet : List Char) (d : Char) (js : List Nat)
    (hc : check g start bodies args alphabet d js=true) :
    (fun x => SObs g .callByValuePar start x (some []))=
      (fun x => SObs (target bodies args.length d js) .callByValueSeq (targetRoot bodies args) x (some [])) := by
  funext x; exact propext (observations_iff g start bodies args alphabet d js hc x (some []))

theorem defined_iff (g : MGrammar) (start : MExp) (bodies args : List MExp) (alphabet : List Char) (d : Char) (js : List Nat)
    (hc : check g start bodies args alphabet d js=true) (x : List Char) (v : Option Nat) :
    (∃ k, evV g x .callByValuePar (tblV g x .callByValuePar k) [] start x.length=some v) ↔
      ∃ k, evV (target bodies args.length d js) x .callByValueSeq (tblV (target bodies args.length d js) x .callByValueSeq k) [] (targetRoot bodies args) x.length=some v := by
  constructor
  · rintro ⟨k,hk⟩; exact ⟨k,(physical g start bodies args alphabet d js hc x k).symm.trans hk⟩
  · rintro ⟨k,hk⟩; exact ⟨k,(physical g start bodies args alphabet d js hc x k).trans hk⟩

theorem undefined_iff (g : MGrammar) (start : MExp) (bodies args : List MExp) (alphabet : List Char) (d : Char) (js : List Nat)
    (hc : check g start bodies args alphabet d js=true) (x : List Char) :
    (∀ k, evV g x .callByValuePar (tblV g x .callByValuePar k) [] start x.length=none) ↔
      ∀ k, evV (target bodies args.length d js) x .callByValueSeq (tblV (target bodies args.length d js) x .callByValueSeq k) [] (targetRoot bodies args) x.length=none := by
  constructor
  · intro h k; rw [←physical g start bodies args alphabet d js hc x k]; exact h k
  · intro h k; rw [physical g start bodies args alphabet d js hc x k]; exact h k

end Shallot.MacroPeg.CBV.DelimitedPatternCompiler
