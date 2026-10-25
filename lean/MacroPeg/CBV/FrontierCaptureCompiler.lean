import MacroPeg.CBV.FrontierArgumentCompiler
import MacroPeg.CBV.ProducedScannerCompiler
import MacroPeg.CBV.NestedScannerFusion

namespace Shallot.MacroPeg.CBV.FrontierCaptureCompiler
open FrontierArgumentCompiler (Selection)

def choiceAlphabet : MExp → Option (List Char)
  | .notP .eps => some []
  | .alt (.chr c) e => (choiceAlphabet e).map (c::·)
  | _ => none

theorem choiceAlphabet_sound : ∀ e A, choiceAlphabet e=some A → e=NestedScannerArguments.choice A
  | .notP .eps,_,h => by cases h; rfl
  | .alt (.chr c) e,_,h => by
    cases hh : choiceAlphabet e with
    | none => simp [choiceAlphabet,hh] at h
    | some B =>
      have he := choiceAlphabet_sound e B hh
      simp only [choiceAlphabet,hh,Option.map_some,Option.some.injEq] at h
      subst_vars
      rfl
  | .notP (.notP _),_,h | .notP (.alt _ _),_,h | .notP (.chr _),_,h
  | .notP (.seq _ _),_,h | .notP (.star _),_,h | .notP (.lit _),_,h
  | .notP .any,_,h | .notP (.range _ _),_,h | .notP (.param _),_,h
  | .notP (.call _ _),_,h | .notP (.dbg _),_,h | .notP (.lam _ _),_,h
  | .notP (.invoke _ _ _),_,h | .notP (.callParam _ _),_,h => by cases h
  | .alt .eps _,_,h | .alt .any _,_,h | .alt (.range _ _) _,_,h
  | .alt (.lit _) _,_,h | .alt (.param _) _,_,h | .alt (.call _ _) _,_,h
  | .alt (.seq _ _) _,_,h | .alt (.alt _ _) _,_,h | .alt (.notP _) _,_,h
  | .alt (.star _) _,_,h | .alt (.dbg _) _,_,h | .alt (.lam _ _) _,_,h
  | .alt (.invoke _ _ _) _,_,h | .alt (.callParam _ _) _,_,h => by cases h
  | .eps,_,h | .any,_,h | .chr _,_,h | .range _ _,_,h | .lit _,_,h | .param _,_,h
  | .seq _ _,_,h | .star _,_,h | .call _ _,_,h | .dbg _,_,h | .lam _ _,_,h
  | .invoke _ _ _,_,h | .callParam _ _,_,h => by cases h

def alphabets : List MExp → Option (List (List Char))
  | [] => some []
  | .star e::args => do
    let A ← choiceAlphabet e
    let As ← alphabets args
    pure (A::As)
  | _ => none

theorem alphabets_sound : ∀ args As, alphabets args=some As → args=As.map NestedScannerArguments.scan
  | [],_,h => by cases h; rfl
  | .star e::args,_,h => by
    cases he : choiceAlphabet e with
    | none => simp [alphabets,he] at h
    | some A =>
      cases ha : alphabets args with
      | none => simp [alphabets,he,ha] at h
      | some As =>
        have hh := choiceAlphabet_sound e A he
        have ht := alphabets_sound args As ha
        simp [alphabets,he,ha] at h
        subst_vars
        rfl
  | .eps::_,_,h | .any::_,_,h | .chr _::_,_,h | .range _ _::_,_,h | .lit _::_,_,h
  | .param _::_,_,h | .seq _ _::_,_,h | .alt _ _::_,_,h | .notP _::_,_,h
  | .call _ _::_,_,h | .dbg _::_,_,h | .lam _ _::_,_,h | .invoke _ _ _::_,_,h
  | .callParam _ _::_,_,h => by cases h

def nestedCheck : List (List Char) → Bool
  | [] => true
  | A::As => As.all (NestedScannerArguments.covers A) && nestedCheck As

theorem nested_checked : ∀ As, nestedCheck As=true → As.Pairwise NestedScannerArguments.Included
  | [],_ => .nil
  | A::As,h => by
    obtain ⟨hh,ht⟩ := Bool.and_eq_true_iff.mp h
    exact List.pairwise_cons.mpr ⟨fun B hb => (NestedScannerArguments.covers_iff A B).mp
      (List.all_eq_true.mp hh B hb),nested_checked As ht⟩

def supportedCheck : MExp → Bool
  | .call _ args => match alphabets args with
    | none => false
    | some As => nestedCheck As
  | .seq a b | .alt a b => supportedCheck a && supportedCheck b
  | .star a | .notP a => supportedCheck a
  | .eps | .any | .chr _ | .range _ _ | .lit _ | .param _ => true
  | _ => false

theorem supported_checked : ∀ e, supportedCheck e=true → NestedScannerFusion.Supported e
  | .call i args,h => by
    cases hh : alphabets args with
    | none => simp [supportedCheck,hh] at h
    | some As =>
      exact ⟨As,nested_checked As (by simpa only [supportedCheck,hh] using h),alphabets_sound args As hh⟩
  | .seq a b,h | .alt a b,h => ⟨supported_checked a (Bool.and_eq_true_iff.mp h).1,
      supported_checked b (Bool.and_eq_true_iff.mp h).2⟩
  | .star a,h | .notP a,h => supported_checked a h
  | .eps,_ | .any,_ | .chr _,_ | .range _ _,_ | .lit _,_ | .param _,_ => True.intro
  | .dbg _,h | .lam _ _,h | .callParam _ _,h | .invoke _ _ _,h => by cases h

abbrev prepared (g : MGrammar) (ps : Selection) := FrontierArgumentCompiler.target g ps
abbrev normalized (g : MGrammar) (ps : Selection) (producers : SelectedProducerNormalization.Selection) :=
  SelectedProducerNormalization.target (prepared g ps) producers

def check (g : MGrammar) (ps : Selection) (producers : SelectedProducerNormalization.Selection)
    (rules : List MRule) : Bool :=
  ((FrontierArgumentCompiler.check g ps && SelectedProducerNormalization.check (prepared g ps) producers) &&
    ProducedScannerCompiler.sameGrammar (normalized g ps producers) (NestedScannerFusion.parGrammar rules)) &&
    rules.all (fun r => supportedCheck r.body)

def rootCheck (ps : Selection) (producers : SelectedProducerNormalization.Selection) (e template : MExp) : Bool :=
  ((MixedGrowthChecks.firstOrderCheck e && SelectedProducerNormalization.conforms producers (FrontierArgumentCompiler.render ps e)) &&
    MExp.beqE (FrontierArgumentCompiler.render ps e) (NestedScannerFusion.source 0 template)) && supportedCheck template

theorem observations_iff (g : MGrammar) (ps : Selection) (producers : SelectedProducerNormalization.Selection)
    (rules : List MRule) (hc : check g ps producers rules=true)
    (e template : MExp) (he : rootCheck ps producers e template=true) (x : List Char) (rest : Option (List Char)) :
    SObs g .callByValuePar e x rest ↔ SObs (PrefixFamilyFusion.seqGrammar rules) .callByValueSeq
      (PrefixFamilyFusion.render false 0 template) x rest := by
  obtain ⟨hc,hs⟩ := Bool.and_eq_true_iff.mp hc
  obtain ⟨hc,hg⟩ := Bool.and_eq_true_iff.mp hc
  obtain ⟨ha,hp⟩ := Bool.and_eq_true_iff.mp hc
  obtain ⟨he,ht⟩ := Bool.and_eq_true_iff.mp he
  obtain ⟨he,hr⟩ := Bool.and_eq_true_iff.mp he
  obtain ⟨hf,hcon⟩ := Bool.and_eq_true_iff.mp he
  have hf := MixedGrowthChecks.firstOrder_checked e hf
  have hroot := (MExp.beqE_iff _ _).mp hr
  have hgram := ProducedScannerCompiler.sameGrammar_eq _ _ hg
  have hobs := (FrontierArgumentCompiler.observations_iff g ps ha e hf x rest).trans
    (SelectedProducerCorrespondence.observations_iff (prepared g ps) producers hp _
      (FrontierArgumentCompiler.render_firstOrder ps e hf) hcon x rest)
  dsimp only [normalized] at hgram
  rw [hgram,hroot] at hobs
  exact hobs.trans (NestedScannerFusion.observations_iff
    (fun r hm => supported_checked r.body (List.all_eq_true.mp hs r hm)) (supported_checked template ht) x rest)

theorem undefined_iff (g : MGrammar) (ps : Selection) (producers : SelectedProducerNormalization.Selection)
    (rules : List MRule) (hc : check g ps producers rules=true)
    (e template : MExp) (he : rootCheck ps producers e template=true) (x : List Char) :
    (∀ k, evV g x .callByValuePar (tblV g x .callByValuePar k) [] e x.length=none) ↔
      ∀ k, evV (PrefixFamilyFusion.seqGrammar rules) x .callByValueSeq
        (tblV (PrefixFamilyFusion.seqGrammar rules) x .callByValueSeq k) []
        (PrefixFamilyFusion.render false 0 template) x.length=none := by
  have ha := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hc).1).1).1
  have hf := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp he).1).1).1
  exact BoundedBodyRewrite.undefined_of_observations _ _ (FrontierArgumentCompiler.source_firstOrder g ps ha)
    (PrefixFamilyFusion.seq_firstOrder rules) _ _ (by decide) (by decide) _ _
    (MixedGrowthChecks.firstOrder_checked e hf) (PrefixFamilyFusion.render_firstOrder _ _ _) x
    (fun rest => observations_iff g ps producers rules hc e template he x rest)

theorem language_translation (g : MGrammar) (ps : Selection) (producers : SelectedProducerNormalization.Selection)
    (rules : List MRule) (hc : check g ps producers rules=true)
    (e template : MExp) (he : rootCheck ps producers e template=true) :
    ∃ (out : MGrammar) (root : MExp), out.FirstOrder ∧ root.FirstOrder ∧ ∀ x,
      SObs g .callByValuePar e x (some []) ↔ SObs out .callByValueSeq root x (some []) :=
  ⟨PrefixFamilyFusion.seqGrammar rules,PrefixFamilyFusion.render false 0 template,
    PrefixFamilyFusion.seq_firstOrder _,PrefixFamilyFusion.render_firstOrder _ _ _,
    fun x => observations_iff g ps producers rules hc e template he x (some [])⟩

end Shallot.MacroPeg.CBV.FrontierCaptureCompiler
