import MacroPeg.CBV.SelectedProducerCorrespondence
import MacroPeg.CBV.ProfileCheckedScannerCorrespondence

namespace Shallot.MacroPeg.CBV.ProducedScannerCompiler
open RecursiveScannerProductCompiler (Entries Arg source sourceExpr target plain)
open RecursiveCaptureProfiles (ScannerSummary Summary)
open ProfileCheckedScannerCorrespondence (Inputs)
open SelectedProducerNormalization (Selection)

/-- This compares finite syntax and arities, not semantic rows. -/
def sameGrammar (g h : MGrammar) : Bool :=
  decide (g.rules.map (fun r => (r.arity,r.body))=h.rules.map (fun r => (r.arity,r.body)))

theorem sameGrammar_eq (g h : MGrammar) (hc : sameGrammar g h=true) : g=h := by
  have he := of_decide_eq_true hc
  have hr := congrArg (List.map (fun p : Nat×MExp => ({ arity := p.1,body := p.2 } : MRule))) he
  simp only [List.map_map] at hr
  change g.rules.map id=h.rules.map id at hr
  simp only [List.map_id] at hr
  cases g; cases h; cases hr; rfl

/-- The producer stage keeps every scanner/helper declaration at its actual
arity. Its emitted ordinary grammar must equal the checked profile backend's
source grammar; that connection is validated as finite syntax. -/
def check {n : Nat} (g : MGrammar) (ps : Selection) (M : StatefulScanner.Machine n)
    (entries : Entries n) (bodies : List Arg) (H : ScannerSummary n) (C : Summary) (A : Inputs) : Bool :=
  ((SelectedProducerNormalization.check g ps && sameGrammar (SelectedProducerNormalization.target g ps) (source M entries bodies)) &&
    RecursiveCaptureProfiles.scannerCheck M H) &&
    (RecursiveCaptureProfiles.grammarCheck M entries bodies H C && ProfileCheckedScannerCorrespondence.bodiesCheck M entries bodies C A)

theorem checked {n : Nat} (g : MGrammar) (ps : Selection) (M : StatefulScanner.Machine n)
    (entries : Entries n) (bodies : List Arg) (H : ScannerSummary n) (C : Summary) (A : Inputs)
    (hc : check g ps M entries bodies H C A=true) :
    SelectedProducerNormalization.check g ps=true ∧
    SelectedProducerNormalization.target g ps=source M entries bodies ∧
    RecursiveCaptureProfiles.scannerCheck M H=true ∧
    RecursiveCaptureProfiles.grammarCheck M entries bodies H C=true ∧
    ProfileCheckedScannerCorrespondence.bodiesCheck M entries bodies C A=true := by
  obtain ⟨hl,hr⟩ := Bool.and_eq_true_iff.mp hc
  obtain ⟨hl,hH⟩ := Bool.and_eq_true_iff.mp hl
  obtain ⟨hs,hshape⟩ := Bool.and_eq_true_iff.mp hl
  obtain ⟨hC,hB⟩ := Bool.and_eq_true_iff.mp hr
  exact ⟨hs,sameGrammar_eq _ _ hshape,hH,hC,hB⟩

def rootCheck {n : Nat} (ps : Selection) (M : StatefulScanner.Machine n) (entries : Entries n) (bodies : List Arg)
    (C : Summary) (A : Inputs) (e : Arg) : Bool :=
  SelectedProducerNormalization.conforms ps (sourceExpr M e) && ProfileCheckedScannerCorrespondence.check M entries bodies C A [] e

theorem observations_iff {n : Nat} (g : MGrammar) (ps : Selection) (M : StatefulScanner.Machine n)
    (entries : Entries n) (bodies : List Arg) (H : ScannerSummary n) (C : Summary) (A : Inputs)
    (hc : check g ps M entries bodies H C A=true) (e : Arg) (he : rootCheck ps M entries bodies C A e=true)
    (x : List Char) (rest : Option (List Char)) :
    SObs g .callByValuePar (sourceExpr M e) x rest ↔ SObs (target M entries bodies) .callByValueSeq (plain M bodies [] e) x rest := by
  have h := checked g ps M entries bodies H C A hc
  have hr := Bool.and_eq_true_iff.mp he
  have hs := SelectedProducerCorrespondence.observations_iff g ps h.1 (sourceExpr M e) (RecursiveScannerProductCompiler.sourceExpr_firstOrder M e) hr.1 x rest
  rw [h.2.1] at hs
  exact hs.trans (ProfileCheckedScannerCorrespondence.observations_iff M entries bodies H C A h.2.2.1 h.2.2.2.1 h.2.2.2.2 e hr.2 x rest)

theorem defined_iff {n : Nat} (g : MGrammar) (ps : Selection) (M : StatefulScanner.Machine n)
    (entries : Entries n) (bodies : List Arg) (H : ScannerSummary n) (C : Summary) (A : Inputs)
    (hc : check g ps M entries bodies H C A=true) (e : Arg) (he : rootCheck ps M entries bodies C A e=true)
    (x : List Char) (v : Option Nat) :
    (∃ k, evV g x .callByValuePar (tblV g x .callByValuePar k) [] (sourceExpr M e) x.length=some v) ↔
      ∃ k, evV (target M entries bodies) x .callByValueSeq (tblV (target M entries bodies) x .callByValueSeq k) [] (plain M bodies [] e) x.length=some v := by
  have h := checked g ps M entries bodies H C A hc
  have hr := Bool.and_eq_true_iff.mp he
  have hs := SelectedProducerCorrespondence.defined_iff g ps h.1 x [] (sourceExpr M e)
    (RecursiveScannerProductCompiler.sourceExpr_firstOrder M e) hr.1 x.length (Nat.le_refl _) v
  dsimp only [SelectedProducerCorrespondence.sourceTable,SelectedProducerCorrespondence.targetTable] at hs
  rw [h.2.1] at hs
  exact hs.trans (ProfileCheckedScannerCorrespondence.defined_iff M entries bodies H C A h.2.2.1 h.2.2.2.1 h.2.2.2.2 e hr.2 x v)

theorem undefined_iff {n : Nat} (g : MGrammar) (ps : Selection) (M : StatefulScanner.Machine n)
    (entries : Entries n) (bodies : List Arg) (H : ScannerSummary n) (C : Summary) (A : Inputs)
    (hc : check g ps M entries bodies H C A=true) (e : Arg) (he : rootCheck ps M entries bodies C A e=true) (x : List Char) :
    (∀ k, evV g x .callByValuePar (tblV g x .callByValuePar k) [] (sourceExpr M e) x.length=none) ↔
      (∀ k, evV (target M entries bodies) x .callByValueSeq (tblV (target M entries bodies) x .callByValueSeq k) [] (plain M bodies [] e) x.length=none) :=
  BoundedBodyRewrite.undefined_of_observations _ _
    (SelectedProducerNormalization.source_firstOrder g ps (checked g ps M entries bodies H C A hc).1)
    (RecursiveScannerProductCompiler.target_firstOrder M entries bodies) .callByValuePar .callByValueSeq (by decide) (by decide)
    _ _ (RecursiveScannerProductCompiler.sourceExpr_firstOrder M e) (RecursiveScannerProductCompiler.plain_firstOrder M bodies [] e)
    x (fun rest => observations_iff g ps M entries bodies H C A hc e he x rest)

theorem language_translation {n : Nat} (g : MGrammar) (ps : Selection) (M : StatefulScanner.Machine n)
    (entries : Entries n) (bodies : List Arg) (H : ScannerSummary n) (C : Summary) (A : Inputs)
    (hc : check g ps M entries bodies H C A=true) (e : Arg) (he : rootCheck ps M entries bodies C A e=true) :
    ∃ (out : MGrammar) (root : MExp), out.FirstOrder ∧ root.FirstOrder ∧
      ∀ x, SObs g .callByValuePar (sourceExpr M e) x (some []) ↔ SObs out .callByValueSeq root x (some []) :=
  ⟨target M entries bodies,plain M bodies [] e,RecursiveScannerProductCompiler.target_firstOrder M entries bodies,
    RecursiveScannerProductCompiler.plain_firstOrder M bodies [] e,fun x => observations_iff g ps M entries bodies H C A hc e he x (some [])⟩

end Shallot.MacroPeg.CBV.ProducedScannerCompiler
