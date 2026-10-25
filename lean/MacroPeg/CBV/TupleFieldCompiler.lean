import MacroPeg.CBV.TupleFieldTransfer
import MacroPeg.CBV.CaptureDelimiterSafety

namespace Shallot.MacroPeg.CBV.TupleFieldCompiler
open DelimiterTemplate DelimitedWordPattern

def source (bodies : List MExp) (arity : Nat) (d : Char) (js : List Nat) (e : MExp) : MGrammar :=
  ⟨bodies.map (fun b => ⟨0,b⟩)++[⟨arity,TupleFieldTransfer.sourceBody d js e⟩]⟩

def target (bodies : List MExp) (arity : Nat) (d : Char) (js : List Nat) (e : MExp) : MGrammar :=
  ⟨bodies.map (fun b => ⟨0,b⟩)++TupleFieldTransfer.rules arity d js e⟩

def check (bodies args : List MExp) (A : List Char) (d : Char) (js : List Nat) (e : MExp) : Bool :=
  decide (0<args.length ∧ js≠[] ∧ d∉A) &&
    js.all (fun i => decide (i<args.length)) &&
    (List.range args.length).all (fun i => decide (i∈js)) &&
    bodies.all (DelimitedCopySyntax.lexicalCheck bodies.length) &&
    TupleFieldControl.check bodies.length args.length e &&
    MaskedScannerAbsorption.check bodies A .eps &&
    args.all (fun a => TupleFieldControl.check bodies.length 0 a &&
      MaskedScannerAbsorption.safeCheck (MaskedScannerAbsorption.mask bodies A) A a)

structure Checked (bodies args : List MExp) (A : List Char) (d : Char) (js : List Nat) (e : MExp) : Prop where
  positive : 0<args.length
  nonempty : js≠[]
  separator : d∉A
  scope : ∀ i∈js, i<args.length
  cover : ∀ i, i<args.length → i∈js
  library : RecursiveParserStability.Valid bodies
  body : TupleFieldControl.check bodies.length args.length e=true
  mask : MaskedScannerAbsorption.Valid bodies (MaskedScannerAbsorption.mask bodies A) A
  actuals : ∀ a∈args, TupleFieldControl.check bodies.length 0 a=true ∧
    MaskedScannerAbsorption.Safe (MaskedScannerAbsorption.mask bodies A) A a

theorem checked (bodies args : List MExp) (A : List Char) (d : Char) (js : List Nat) (e : MExp)
    (hc : check bodies args A d js e=true) : Checked bodies args A d js e := by
  simp only [check,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨hn,hs⟩,hv⟩,hb⟩,he⟩,hm⟩,ha⟩ := hc
  have hn := of_decide_eq_true hn
  refine ⟨hn.1,hn.2.1,hn.2.2,?_,?_,?_,he,(MaskedScannerAbsorption.checked bodies A .eps hm).1,?_⟩
  · intro i hi; exact of_decide_eq_true (List.all_eq_true.mp hs i hi)
  · intro i hi; exact of_decide_eq_true (List.all_eq_true.mp hv i (List.mem_range.mpr hi))
  · intro b hb'; exact DelimitedCopySyntax.lexical_checked _ b (List.all_eq_true.mp hb b hb')
  · intro a ha'
    obtain ⟨h,h'⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp ha a ha')
    exact ⟨h,MaskedScannerAbsorption.safe_checked _ _ _ h'⟩

theorem source_installed (bodies : List MExp) (arity : Nat) (d : Char) (js : List Nat) (e : MExp) :
    RecursiveParserStability.Installed bodies (source bodies arity d js e) := DelimitedCopySyntax.installed_append _ _

theorem target_installed (bodies : List MExp) (arity : Nat) (d : Char) (js : List Nat) (e : MExp) :
    RecursiveParserStability.Installed bodies (target bodies arity d js e) := DelimitedCopySyntax.installed_append _ _

theorem source_row (bodies : List MExp) (arity : Nat) (d : Char) (js : List Nat) (e : MExp) :
    ruleAtM (source bodies arity d js e).rules bodies.length=
      some ⟨arity,TupleFieldTransfer.sourceBody d js e⟩ := by
  simp [source,ruleAtM_eq_getElem?]

theorem target_rows (bodies : List MExp) (arity : Nat) (d : Char) (js : List Nat) (e : MExp) :
    TupleFieldTransfer.Installed (target bodies arity d js e) bodies.length arity d js e := by
  have hext (i : Nat) : ruleAtM (target bodies arity d js e).rules (bodies.length+i)=
      ruleAtM (TupleFieldTransfer.rules arity d js e) i := by
    simp [target,ruleAtM_eq_getElem?,List.getElem?_append_right]
  exact ⟨fun i hi => (hext i).trans (TupleFieldTransfer.rules_projection arity d js e i hi),
    (hext arity).trans (TupleFieldTransfer.rules_entry arity d js e)⟩

theorem source_firstOrder (bodies : List MExp) (arity : Nat) (d : Char) (js : List Nat) (e : MExp)
    (hb : RecursiveParserStability.Valid bodies) (he : e.FirstOrder) :
    (source bodies arity d js e).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr|hr
  · obtain ⟨b,hm,rfl⟩ := List.mem_map.mp hr
    exact RecursiveParserStability.lexical_firstOrder _ b (hb b hm)
  · have hr : r=⟨arity,TupleFieldTransfer.sourceBody d js e⟩ := by simpa using hr
    subst r; exact ⟨compile_firstOrder _ _,he⟩

theorem target_firstOrder (bodies : List MExp) (arity : Nat) (d : Char) (js : List Nat) (e : MExp)
    (hb : RecursiveParserStability.Valid bodies) (he : e.FirstOrder) :
    (target bodies arity d js e).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr|hr
  · obtain ⟨b,hm,rfl⟩ := List.mem_map.mp hr
    exact RecursiveParserStability.lexical_firstOrder _ b (hb b hm)
  · exact TupleFieldTransfer.rules_firstOrder arity d js e he r hr

theorem args_firstOrder (bodies args : List MExp) (A : List Char) (d : Char) (js : List Nat) (e : MExp)
    (hc : Checked bodies args A d js e) : MExp.FirstOrderArgs args := by
  have h : ∀ as : List MExp, (∀ a∈as, a.FirstOrder) → MExp.FirstOrderArgs as := by
    intro as
    induction as with
    | nil => intro _; trivial
    | cons a as ih => intro h; exact ⟨h a (by simp),ih (fun b hb => h b (by simp [hb]))⟩
  exact h args (fun a ha => TupleFieldControl.firstOrder _ _ a (hc.actuals a ha).1)

/-- A finite syntax/alphabet/coverage check produces an actual Seq grammar
over exactly the original strings, preserving every physical clock. -/
theorem physical (bodies args : List MExp) (A : List Char) (d : Char) (js : List Nat) (e : MExp)
    (hc : check bodies args A d js e=true) (x : List Char) (k p : Nat) (hp : p≤x.length) :
    evV (source bodies args.length d js e) x .callByValuePar
      (tblV (source bodies args.length d js e) x .callByValuePar k) [] (.call bodies.length args) p=
    evV (target bodies args.length d js e) x .callByValueSeq
      (tblV (target bodies args.length d js e) x .callByValueSeq k) []
      (TupleFieldTransfer.head bodies.length args.length d js args) p := by
  have hc := checked bodies args A d js e hc
  cases js with
  | nil => exact False.elim (hc.nonempty rfl)
  | cons j js =>
    have hs := source_installed bodies args.length d (j::js) e
    have ht := target_installed bodies args.length d (j::js) e
    have hfo := source_firstOrder bodies args.length d (j::js) e hc.library (TupleFieldControl.firstOrder _ _ e hc.body)
    apply TupleFieldTransfer.physical bodies _ _ bodies.length d j js e hc.library hs ht
      args args rfl hc.positive hc.body hc.scope hc.cover (source_row _ _ _ _ _)
      (target_rows _ _ _ _ _) hfo (args_firstOrder _ _ _ _ _ _ hc) x [] k p hp
    · intro i hi
      exact TupleFieldControl.physical bodies _ _ hc.library hs ht x k [] 0 args[i]
        (hc.actuals _ (List.getElem_mem hi)).1 p hp
    · intro i hi q hv
      exact CaptureDelimiterSafety.captured_free hs hfo _ A hc.mask d hc.separator args[i]
        (hc.actuals _ (List.getElem_mem hi)).2
        (TupleFieldControl.firstOrder _ _ _ (hc.actuals _ (List.getElem_mem hi)).1)
        x .callByValuePar (by decide) k p q hp hv

theorem observations_iff (bodies args : List MExp) (A : List Char) (d : Char) (js : List Nat) (e : MExp)
    (hc : check bodies args A d js e=true) (x : List Char) (rest : Option (List Char)) :
    SObs (source bodies args.length d js e) .callByValuePar (.call bodies.length args) x rest ↔
      SObs (target bodies args.length d js e) .callByValueSeq
        (TupleFieldTransfer.head bodies.length args.length d js args) x rest := by
  have h := checked bodies args A d js e hc
  have he := TupleFieldControl.firstOrder _ _ e h.body
  have ha := args_firstOrder _ _ _ _ _ _ h
  have hroot : (MExp.call bodies.length args).FirstOrder := ha
  rw [←decideObsV_iff (source_firstOrder _ _ _ _ _ h.library he) (by decide) hroot,
    ←decideObsV_iff (target_firstOrder _ _ _ _ _ h.library he) (by decide)
      (TupleFieldTransfer.head_firstOrder _ _ _ _ _ ha)]
  unfold decideObsV
  rw [ScannerPairFusion.stable_result_eq _ _ x _ _ _ _ (fun k => physical bodies args A d js e hc x k _ (Nat.le_refl _))]

theorem language_translation (bodies args : List MExp) (A : List Char) (d : Char) (js : List Nat) (e : MExp)
    (hc : check bodies args A d js e=true) :
    (fun x => SObs (source bodies args.length d js e) .callByValuePar (.call bodies.length args) x (some []))=
      (fun x => SObs (target bodies args.length d js e) .callByValueSeq
        (TupleFieldTransfer.head bodies.length args.length d js args) x (some [])) := by
  funext x
  exact propext (observations_iff bodies args A d js e hc x (some []))

theorem undefined_iff (bodies args : List MExp) (A : List Char) (d : Char) (js : List Nat) (e : MExp)
    (hc : check bodies args A d js e=true) (x : List Char) :
    (∀ k, evV (source bodies args.length d js e) x .callByValuePar
      (tblV (source bodies args.length d js e) x .callByValuePar k) [] (.call bodies.length args) x.length=none) ↔
    (∀ k, evV (target bodies args.length d js e) x .callByValueSeq
      (tblV (target bodies args.length d js e) x .callByValueSeq k) []
      (TupleFieldTransfer.head bodies.length args.length d js args) x.length=none) := by
  constructor
  · intro h k; rw [←physical bodies args A d js e hc x k _ (Nat.le_refl _)]; exact h k
  · intro h k; rw [physical bodies args A d js e hc x k _ (Nat.le_refl _)]; exact h k

end Shallot.MacroPeg.CBV.TupleFieldCompiler
