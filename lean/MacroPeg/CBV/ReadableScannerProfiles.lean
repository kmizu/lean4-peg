import MacroPeg.CBV.AlphabetCaptureProfiles

namespace Shallot.MacroPeg.CBV.ReadableScannerProfiles
open StatefulScanner (Machine advance next)
open DynamicScannerCapture (observer)
open CaptureTransitionProfile (profile compose)

/-- Every listed arc is effective under the scanner's priority lookup.
This is a finite source-table check, including duplicated equal arcs. -/
def arcsCheck {n : Nat} (M : Machine n) : Bool :=
  (List.finRange n).all (fun q => (M.arcs q).all (fun cr => decide (next (M.arcs q) cr.1=some cr.2)))

def alphabet {n : Nat} (M : Machine n) : List Char :=
  ((List.finRange n).flatMap (fun q => (M.arcs q).map Prod.fst)).eraseDups

theorem machine_checked {n : Nat} (M : Machine n) :
    AlphabetCaptureProfiles.machineCheck M (alphabet M)=true := by
  apply List.all_eq_true.mpr
  intro q _
  apply List.all_eq_true.mpr
  intro cr hcr
  apply List.contains_iff_mem.mpr
  exact List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨q,List.mem_finRange q,List.mem_map.mpr ⟨cr,hcr,rfl⟩⟩)

def summary {n : Nat} (M : Machine n) (alphabet : List Char) : RecursiveCaptureProfiles.ScannerSummary n :=
  fun q => (AlphabetCaptureProfiles.domain (observer M) alphabet).filter
    (fun P => ScannerFrontierCertificate.check P q)

theorem generated {n : Nat} (M : Machine n) (alphabet : List Char) (q : Fin n)
    (P : List Nat) (hP : P∈summary M alphabet q) :
    ∃ w, AlphabetCaptureProfiles.Word alphabet w ∧ advance M q w≠none ∧ P=profile (observer M) w := by
  obtain ⟨hP,hq⟩ := List.mem_filter.mp hP
  obtain ⟨w,hw,rfl⟩ := AlphabetCaptureProfiles.generated _ (DynamicScannerCapture.observer_valid M) alphabet P hP
  exact ⟨w,hw,(ScannerFrontierCertificate.check_actual M w q).mp hq,rfl⟩

theorem nil_mem {n : Nat} (M : Machine n) (alphabet : List Char) (q : Fin n) :
    profile (observer M) []∈summary M alphabet q := by
  apply List.mem_filter.mpr
  exact ⟨AlphabetCaptureProfiles.nil_mem _ (DynamicScannerCapture.observer_valid M) alphabet,
    (ScannerFrontierCertificate.check_actual M [] q).mpr (by simp [advance])⟩

theorem frontier {n : Nat} (M : Machine n) (alphabet : List Char) (q : Fin n)
    (P : List Nat) (hP : P∈summary M alphabet q) : ScannerFrontierCertificate.check P q=true :=
  (List.mem_filter.mp hP).2

theorem valid {n : Nat} (M : Machine n) (alphabet : List Char) (q : Fin n) :
    UniversalCaptureProfiles.AllIn (observer M) (summary M alphabet q) :=
  fun _ hP => AlphabetCaptureProfiles.valid _ (DynamicScannerCapture.observer_valid M) alphabet _ (List.mem_filter.mp hP).1

/-- The exact readable subset of the generated alphabet domain satisfies
the scanner's recursive output check. Captured-word shapes are inferred
from actual scanner transitions rather than supplied as an oracle. -/
theorem checked {n : Nat} (M : Machine n) (alphabet : List Char)
    (hArcs : arcsCheck M=true) (hAlphabet : AlphabetCaptureProfiles.machineCheck M alphabet=true) :
    RecursiveCaptureProfiles.scannerCheck M (summary M alphabet)=true := by
  apply List.all_eq_true.mpr
  intro q _
  refine Bool.and_eq_true_iff.mpr ⟨List.contains_iff_mem.mpr (nil_mem M alphabet q),?_⟩
  apply List.all_eq_true.mpr
  intro cr hcr
  obtain ⟨c,r⟩ := cr
  have hs := of_decide_eq_true ((List.all_eq_true.mp ((List.all_eq_true.mp hArcs) q (List.mem_finRange q))) (c,r) hcr)
  have hc := List.contains_iff_mem.mp ((List.all_eq_true.mp ((List.all_eq_true.mp hAlphabet) q (List.mem_finRange q))) (c,r) hcr)
  apply List.all_eq_true.mpr
  intro P hP
  obtain ⟨w,hw,hr,rfl⟩ := generated M alphabet r P hP
  apply List.contains_iff_mem.mpr
  rw [CaptureTransitionProfile.compose_correct _ (DynamicScannerCapture.observer_valid M)]
  apply List.mem_filter.mpr
  refine ⟨AlphabetCaptureProfiles.word_mem _ (DynamicScannerCapture.observer_valid M) alphabet (c::w) ?_,?_⟩
  · intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact hc
    · exact hw d hd
  · apply (ScannerFrontierCertificate.check_actual M (c::w) q).mpr
    simpa only [advance,hs,Option.bind_some] using hr

end Shallot.MacroPeg.CBV.ReadableScannerProfiles
