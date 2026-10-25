import MacroPeg.CBV.ReadableScannerProfiles

namespace Shallot.MacroPeg.CBV.ScannerLoopCompiler
open RecursiveScannerProductCompiler (Arg Entry Entries sourceExpr sourceHeader)
open RecursiveCaptureProfiles (Summary ScannerSummary effects headerEffects scopeCheck product)
open DynamicScannerCapture (observer)
open CaptureTransitionProfile (profile profiles)
open StatefulScanner (Machine)

/-- User 0 iterates the actual scanner while retaining its original value;
user 1 captures a complete scanner result for a fresh recursive argument. -/
def entries {n : Nat} (q : Fin n) : Entries n := fun i => if i=0 then .scannerIterate q else .scan q
def bodies (tail : Arg) : List Arg := [tail,.lit []]
abbrev alphabet {n : Nat} (M : Machine n) := ReadableScannerProfiles.alphabet M
abbrev H {n : Nat} (M : Machine n) := ReadableScannerProfiles.summary M (alphabet M)
def C {n : Nat} (M : Machine n) (q : Fin n) : Summary := fun i _ => if i=1 then H M q else profiles (observer M)
def A {n : Nat} (M : Machine n) (q : Fin n) : ProfileCheckedScannerCorrespondence.Inputs := fun _ => H M q

def check {n : Nat} (M : Machine n) (q : Fin n) (tail : Arg) : Bool :=
  ReadableScannerProfiles.arcsCheck M && (scopeCheck (bodies tail) tail &&
    (H M q).all (fun P => ProfileCheckedScannerCorrespondence.check M (entries q) (bodies tail) (C M q) (A M q) [P] tail))

def root : Arg := .user 0 (.user 1 (.lit []))
abbrev source {n : Nat} (M : Machine n) (q : Fin n) (tail : Arg) :=
  RecursiveScannerProductCompiler.source M (entries q) (bodies tail)
abbrev target {n : Nat} (M : Machine n) (q : Fin n) (tail : Arg) :=
  RecursiveScannerProductCompiler.target M (entries q) (bodies tail)
abbrev targetExpr {n : Nat} (M : Machine n) (tail : Arg) := RecursiveScannerProductCompiler.plain M (bodies tail) [] root

theorem summary_valid {n : Nat} (M : Machine n) (q : Fin n) (i : Nat) (P : List Nat) :
    UniversalCaptureProfiles.AllIn (observer M) (C M q i P) := by
  unfold C
  split
  · exact ReadableScannerProfiles.valid M (alphabet M) q
  · exact fun _ h => h

theorem grammar_checked {n : Nat} (M : Machine n) (q : Fin n) (tail : Arg)
    (h : check M q tail=true) : RecursiveCaptureProfiles.grammarCheck M (entries q) (bodies tail) (H M) (C M q)=true := by
  have hs := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).2).1
  apply List.all_eq_true.mpr
  intro bi hbi
  have hc : bi=(tail,0) ∨ bi=(.lit [],1) := by simpa [bodies,List.zipIdx] using hbi
  rcases hc with rfl | rfl
  · refine Bool.and_eq_true_iff.mpr ⟨hs,?_⟩
    apply List.all_eq_true.mpr
    intro P hP
    apply List.all_eq_true.mpr
    intro Q hQ
    apply List.contains_iff_mem.mpr
    change Q∈profiles (observer M)
    apply UniversalCaptureProfiles.product_all _ _ _ _ _ Q hQ
    · apply UniversalCaptureProfiles.product_all
      · exact UniversalCaptureProfiles.closure_all _ (DynamicScannerCapture.observer_valid M) _
          (ReadableScannerProfiles.valid M (alphabet M) q)
      · intro Q hQ
        obtain rfl := List.mem_singleton.mp hQ
        exact hP
    · exact AlphabetCaptureProfiles.effects_valid M (C M q) (summary_valid M q) [P]
        (by intro Q hQ; have he : Q=P := List.mem_singleton.mp hQ; subst Q; exact hP) tail
  · refine Bool.and_eq_true_iff.mpr ⟨rfl,?_⟩
    apply List.all_eq_true.mpr
    intro P _
    apply List.all_eq_true.mpr
    intro Q hQ
    apply List.contains_iff_mem.mpr
    obtain ⟨R,hR,hQ⟩ := List.mem_flatMap.mp hQ
    obtain ⟨S,hS,rfl⟩ := List.mem_map.mp hQ
    have hS : S=profile (observer M) [] := List.mem_singleton.mp hS
    subst S
    obtain ⟨w,_,_,rfl⟩ := ReadableScannerProfiles.generated M (alphabet M) q R hR
    simpa [CaptureTransitionProfile.compose_correct _ (DynamicScannerCapture.observer_valid M),entries,headerEffects,C]
      using hR

theorem bodies_checked {n : Nat} (M : Machine n) (q : Fin n) (tail : Arg)
    (h : check M q tail=true) :
    ProfileCheckedScannerCorrespondence.bodiesCheck M (entries q) (bodies tail) (C M q) (A M q)=true := by
  refine Bool.and_eq_true_iff.mpr ⟨by simp [RecursiveScannerProductCompiler.entriesCheck,entries,bodies,RecursiveScannerProductCompiler.headerCheck,List.zipIdx],?_⟩
  apply List.all_eq_true.mpr
  intro bi hbi
  have hc : bi=(tail,0) ∨ bi=(.lit [],1) := by simpa [bodies,List.zipIdx] using hbi
  rcases hc with rfl | rfl
  · apply List.all_eq_true.mpr
    intro P _
    by_cases hi : ProfileCheckedScannerCorrespondence.inputCheck M (entries q) (A M q) 0 P=true
    · have hP : P∈H M q := List.contains_iff_mem.mp (Bool.and_eq_true_iff.mp hi).1
      have hh := (List.all_eq_true.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).2).2) P hP
      simp [hi,hh]
    · simp [hi]
  · simp [ProfileCheckedScannerCorrespondence.check]

theorem root_checked {n : Nat} (M : Machine n) (q : Fin n) (tail : Arg) :
    ProfileCheckedScannerCorrespondence.check M (entries q) (bodies tail) (C M q) (A M q) [] root=true := by
  have hnil := ReadableScannerProfiles.nil_mem M (alphabet M) q
  simp only [root,ProfileCheckedScannerCorrespondence.check,bodies,List.length_cons,List.length_nil]
  refine Bool.and_eq_true_iff.mpr ⟨rfl,Bool.and_eq_true_iff.mpr ⟨?_,?_⟩⟩
  · apply List.all_eq_true.mpr
    intro P hP
    have hPH : P∈H M q := by simpa [effects,C] using hP
    exact Bool.and_eq_true_iff.mpr ⟨List.contains_iff_mem.mpr hPH,ReadableScannerProfiles.frontier M (alphabet M) q P hPH⟩
  · refine Bool.and_eq_true_iff.mpr ⟨rfl,Bool.and_eq_true_iff.mpr ⟨?_,rfl⟩⟩
    apply List.all_eq_true.mpr
    intro P hP
    have he : P=profile (observer M) [] := List.mem_singleton.mp hP
    subst P
    exact Bool.and_eq_true_iff.mpr ⟨List.contains_iff_mem.mpr hnil,ReadableScannerProfiles.frontier M (alphabet M) q _ hnil⟩

theorem language_translation {n : Nat} (M : Machine n) (q : Fin n) (tail : Arg)
    (h : check M q tail=true) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
      SObs (source M q tail) .callByValuePar (sourceExpr M root) x (some []) ↔
        SObs g .callByValueSeq start x (some []) :=
  ProfileCheckedScannerCorrespondence.language_translation M (entries q) (bodies tail) (H M) (C M q) (A M q)
    (ReadableScannerProfiles.checked M (alphabet M) (Bool.and_eq_true_iff.mp h).1 (ReadableScannerProfiles.machine_checked M))
    (grammar_checked M q tail h) (bodies_checked M q tail h) root (root_checked M q tail)

theorem defined_iff {n : Nat} (M : Machine n) (q : Fin n) (tail : Arg)
    (h : check M q tail=true) (x : List Char) (v : Option Nat) :
    (∃ k, evV (source M q tail) x .callByValuePar (tblV (source M q tail) x .callByValuePar k) [] (sourceExpr M root) x.length=some v) ↔
    (∃ k, evV (target M q tail) x .callByValueSeq (tblV (target M q tail) x .callByValueSeq k) [] (targetExpr M tail) x.length=some v) :=
  ProfileCheckedScannerCorrespondence.defined_iff M (entries q) (bodies tail) (H M) (C M q) (A M q)
    (ReadableScannerProfiles.checked M (alphabet M) (Bool.and_eq_true_iff.mp h).1 (ReadableScannerProfiles.machine_checked M))
    (grammar_checked M q tail h) (bodies_checked M q tail h) root (root_checked M q tail) x v

theorem undefined_iff {n : Nat} (M : Machine n) (q : Fin n) (tail : Arg)
    (h : check M q tail=true) (x : List Char) :
    (∀ k, evV (source M q tail) x .callByValuePar (tblV (source M q tail) x .callByValuePar k) [] (sourceExpr M root) x.length=none) ↔
    (∀ k, evV (target M q tail) x .callByValueSeq (tblV (target M q tail) x .callByValueSeq k) [] (targetExpr M tail) x.length=none) :=
  ProfileCheckedScannerCorrespondence.undefined_iff M (entries q) (bodies tail) (H M) (C M q) (A M q)
    (ReadableScannerProfiles.checked M (alphabet M) (Bool.and_eq_true_iff.mp h).1 (ReadableScannerProfiles.machine_checked M))
    (grammar_checked M q tail h) (bodies_checked M q tail h) root (root_checked M q tail) x

end Shallot.MacroPeg.CBV.ScannerLoopCompiler
