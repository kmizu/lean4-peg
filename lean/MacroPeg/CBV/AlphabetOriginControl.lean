import MacroPeg.CBV.AlphabetCaptureProfiles
import MacroPeg.CBV.AutomaticOriginControl

namespace Shallot.MacroPeg.CBV.AlphabetOriginControl
open ScannerOriginControl (Part coreEntries coreBodies normalize expand callArg)
open RecursiveScannerProductCompiler (Arg sourceExpr)
open ReplayControlFusion (Plan)
open StatefulScanner (Machine)

private theorem callArg_literal {n : Nat} (parts : List (Part n)) (alphabet : List Char)
    (j : Nat) (a : Arg) (ha : AlphabetCaptureProfiles.literalCheck alphabet a=true) :
    AlphabetCaptureProfiles.literalCheck alphabet (callArg parts j a)=true := by
  cases hr : parts[j]? with
  | none => simpa [callArg,hr] using ha
  | some r =>
    cases hc : r.closed <;> simp [callArg,hr,hc,ha,AlphabetCaptureProfiles.literalCheck]

theorem expand_literal {n : Nat} (parts : List (Part n)) (alphabet : List Char)
    (a : Arg) (ha : AlphabetCaptureProfiles.literalCheck alphabet a=true) :
    ∀ p, AlphabetCaptureProfiles.literalCheck alphabet (expand parts a p)=true
  | .leaf j => callArg_literal parts alphabet j a ha
  | .alt p q | .guard p q => Bool.and_eq_true_iff.mpr
      ⟨expand_literal parts alphabet a ha p,expand_literal parts alphabet a ha q⟩
  | .notP p => expand_literal parts alphabet a ha p

theorem normalize_literal {n : Nat} (parts : List (Part n)) (plans : List Plan) (alphabet : List Char) :
    ∀ e, AlphabetCaptureProfiles.literalCheck alphabet e=true →
    AlphabetCaptureProfiles.literalCheck alphabet (normalize parts plans e)=true
  | .lit _,h | .param _,h => h
  | .seq a b,h | .alt a b,h => Bool.and_eq_true_iff.mpr
      ⟨normalize_literal parts plans alphabet a (Bool.and_eq_true_iff.mp h).1,
       normalize_literal parts plans alphabet b (Bool.and_eq_true_iff.mp h).2⟩
  | .notP a,h | .star a,h => normalize_literal parts plans alphabet a h
  | .user i a,h => by
    have ha := normalize_literal parts plans alphabet a h
    cases hp : plans[i]? with
    | none => simp [normalize,hp,AlphabetCaptureProfiles.literalCheck]
    | some p =>
      simpa only [normalize,hp,AlphabetCaptureProfiles.literalCheck] using
        Bool.and_eq_true_iff.mpr ⟨ha,expand_literal parts alphabet _ ha p⟩

def entryCheck {n : Nat} (M : Machine n) (alphabet : List Char) (e : RecursiveScannerProductCompiler.Entry n) : Bool :=
  (RecursiveScannerProductCompiler.headerCheck M e && AlphabetCaptureProfiles.headerLiteralCheck alphabet e) &&
    (AlphabetCaptureProfiles.domain (DynamicScannerCapture.observer M) alphabet).all
      (RecursiveScannerProductHeader.entryCheck M e)

/-- Actual source literals and the configured frontier are checked;
no all-state readability or successful-capture annotation is required. -/
def check {n : Nat} (M : Machine n) (parts : List (Part n)) (plans : List Plan) (alphabet : List Char) : Bool :=
  ScannerOriginControl.readyCheck parts plans && (AlphabetCaptureProfiles.machineCheck M alphabet &&
    parts.all (fun r => AlphabetCaptureProfiles.literalCheck alphabet r.body && (r.closed || entryCheck M alphabet r.entry)))

theorem core_checked {n : Nat} (M : Machine n) (parts : List (Part n)) (plans : List Plan) (alphabet : List Char)
    (h : check M parts plans alphabet=true) :
    AlphabetCaptureProfiles.check M (coreEntries parts) (coreBodies parts plans) alphabet=true := by
  obtain ⟨hr,hm⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨hm,he⟩ := Bool.and_eq_true_iff.mp hm
  refine Bool.and_eq_true_iff.mpr ⟨hm,?_⟩
  unfold coreBodies
  rw [List.zipIdx_map]
  apply List.all_eq_true.mpr
  intro bi hbi
  obtain ⟨r,hrm,rfl⟩ := List.mem_map.mp hbi
  have hz := List.mem_zipIdx hrm
  have hb : r.2<parts.length := by simpa using hz.2.1
  have hh : parts[r.2]?=some r.1 := by
    rw [List.getElem?_eq_getElem hb]
    simpa using congrArg some hz.2.2.symm
  have hpart := (Bool.and_eq_true_iff.mp ((List.all_eq_true.mp he) r.1 (List.mem_of_getElem? hh)))
  have hscope := (Bool.and_eq_true_iff.mp ((List.all_eq_true.mp (Bool.and_eq_true_iff.mp hr).2)
    r.1 (List.mem_of_getElem? hh))).1
  refine Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
    ⟨AutomaticOriginControl.normalize_scope parts plans hr _ hscope,normalize_literal parts plans alphabet _ hpart.1⟩,?_⟩
  change entryCheck M alphabet (coreEntries parts r.2)=true
  simp only [coreEntries,hh]
  cases hc : r.1.closed with
  | false => simpa [hc] using hpart.2
  | true => simp [entryCheck,RecursiveScannerProductCompiler.headerCheck,
      AlphabetCaptureProfiles.headerLiteralCheck,RecursiveScannerProductHeader.entryCheck]

theorem certificates {n : Nat} (M : Machine n) (parts : List (Part n)) (plans : List Plan) (alphabet : List Char)
    (h : check M parts plans alphabet=true) (e : Arg) (he : ScannerOriginControl.scopeCheck plans e=true)
    (ha : AlphabetCaptureProfiles.literalCheck alphabet e=true) :
    RecursiveCaptureProfiles.scannerCheck M (AlphabetCaptureProfiles.scannerSummary M alphabet)=true ∧
    RecursiveCaptureProfiles.grammarCheck M (coreEntries parts) (coreBodies parts plans)
      (AlphabetCaptureProfiles.scannerSummary M alphabet) (AlphabetCaptureProfiles.summary M alphabet)=true ∧
    ProfileCheckedScannerCorrespondence.bodiesCheck M (coreEntries parts) (coreBodies parts plans)
      (AlphabetCaptureProfiles.summary M alphabet) (AlphabetCaptureProfiles.inputs M alphabet)=true ∧
    ProfileCheckedScannerCorrespondence.check M (coreEntries parts) (coreBodies parts plans)
      (AlphabetCaptureProfiles.summary M alphabet) (AlphabetCaptureProfiles.inputs M alphabet) [] (normalize parts plans e)=true := by
  have hc := core_checked M parts plans alphabet h
  refine ⟨AlphabetCaptureProfiles.scanner_checked M alphabet (Bool.and_eq_true_iff.mp hc).1,
    AlphabetCaptureProfiles.grammar_checked M _ _ alphabet hc,
    AlphabetCaptureProfiles.bodies_checked M _ _ alphabet hc,?_⟩
  exact AlphabetCaptureProfiles.expression_checked M _ _ alphabet hc [] (by intro P hP; cases hP) _
    (AutomaticOriginControl.normalize_scope parts plans (Bool.and_eq_true_iff.mp h).1 e he)
    (normalize_literal parts plans alphabet e ha)

theorem observations_iff {n : Nat} (M : Machine n) (parts : List (Part n)) (plans : List Plan) (alphabet : List Char)
    (h : check M parts plans alphabet=true) (e : Arg) (he : ScannerOriginControl.scopeCheck plans e=true)
    (ha : AlphabetCaptureProfiles.literalCheck alphabet e=true) (x : List Char) (rest : Option (List Char)) :
    SObs (ScannerOriginControl.original M parts plans) .callByValuePar (sourceExpr M e) x rest ↔
      SObs (ScannerOriginControl.target M parts plans) .callByValueSeq
        (ScannerOriginControl.targetExpr M parts plans e) x rest := by
  obtain ⟨hH,hC,hB,hRoot⟩ := certificates M parts plans alphabet h e he ha
  exact ScannerOriginControl.observations_iff M parts plans (Bool.and_eq_true_iff.mp h).1 e he _ _ _ hH hC hB hRoot x rest

theorem language_translation {n : Nat} (M : Machine n) (parts : List (Part n)) (plans : List Plan) (alphabet : List Char)
    (h : check M parts plans alphabet=true) (e : Arg) (he : ScannerOriginControl.scopeCheck plans e=true)
    (ha : AlphabetCaptureProfiles.literalCheck alphabet e=true) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
      SObs (ScannerOriginControl.original M parts plans) .callByValuePar (sourceExpr M e) x (some []) ↔
        SObs g .callByValueSeq start x (some []) :=
  ⟨_,_,RecursiveScannerProductCompiler.target_firstOrder M _ _,
    RecursiveScannerProductCompiler.plain_firstOrder M _ [] _,
    fun x => observations_iff M parts plans alphabet h e he ha x (some [])⟩

theorem defined_iff {n : Nat} (M : Machine n) (parts : List (Part n)) (plans : List Plan) (alphabet : List Char)
    (h : check M parts plans alphabet=true) (e : Arg) (he : ScannerOriginControl.scopeCheck plans e=true)
    (ha : AlphabetCaptureProfiles.literalCheck alphabet e=true) (x : List Char) (v : Option Nat) :
    (∃ k, evV (ScannerOriginControl.original M parts plans) x .callByValuePar
      (tblV (ScannerOriginControl.original M parts plans) x .callByValuePar k) [] (sourceExpr M e) x.length=some v) ↔
    (∃ k, evV (ScannerOriginControl.target M parts plans) x .callByValueSeq
      (tblV (ScannerOriginControl.target M parts plans) x .callByValueSeq k) []
      (ScannerOriginControl.targetExpr M parts plans e) x.length=some v) := by
  obtain ⟨hH,hC,hB,hRoot⟩ := certificates M parts plans alphabet h e he ha
  exact ScannerOriginControl.defined_iff M parts plans (Bool.and_eq_true_iff.mp h).1 e he _ _ _ hH hC hB hRoot x v

theorem undefined_iff {n : Nat} (M : Machine n) (parts : List (Part n)) (plans : List Plan) (alphabet : List Char)
    (h : check M parts plans alphabet=true) (e : Arg) (he : ScannerOriginControl.scopeCheck plans e=true)
    (ha : AlphabetCaptureProfiles.literalCheck alphabet e=true) (x : List Char) :
    (∀ k, evV (ScannerOriginControl.original M parts plans) x .callByValuePar
      (tblV (ScannerOriginControl.original M parts plans) x .callByValuePar k) [] (sourceExpr M e) x.length=none) ↔
    (∀ k, evV (ScannerOriginControl.target M parts plans) x .callByValueSeq
      (tblV (ScannerOriginControl.target M parts plans) x .callByValueSeq k) []
      (ScannerOriginControl.targetExpr M parts plans e) x.length=none) := by
  obtain ⟨hH,hC,hB,hRoot⟩ := certificates M parts plans alphabet h e he ha
  exact ScannerOriginControl.undefined_iff M parts plans (Bool.and_eq_true_iff.mp h).1 e he _ _ _ hH hC hB hRoot x

end Shallot.MacroPeg.CBV.AlphabetOriginControl
