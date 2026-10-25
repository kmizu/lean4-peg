import MacroPeg.CBV.ScannerLanguageSafety
import MacroPeg.CBV.DynamicScannerBinding

namespace Shallot.MacroPeg.CBV.ScannerFrontierCertificate
open StatefulScanner (Machine advance run)
open DynamicScannerCapture (observer)
open CaptureTransitionProfile (profile)

/-- The exact frontier condition: the scan reaches the end of a proposed
capture iff that word is readable from its actual initial state. No other
initial state, later continuation, or successful parser run is assumed. -/
theorem readable_iff_endpoint {n : Nat} (M : Machine n) (w suffix : List Char) (q : Fin n) :
    advance M q w≠none ↔ (run M q (w++suffix)).2.length≤suffix.length := by
  induction w generalizing q with
  | nil =>
    simp only [advance,List.nil_append,ne_eq,Option.some_ne_none,not_false_eq_true,true_iff]
    exact StatefulScanner.run_length M q suffix
  | cons c w ih =>
    cases hs : StatefulScanner.next (M.arcs q) c with
    | none =>
      simp only [advance,run,List.cons_append,hs,Option.bind_none,ne_eq,not_true_eq_false,
        List.length_cons,List.length_append,false_iff]
      omega
    | some r => simpa only [advance,run,List.cons_append,hs,Option.bind_some] using ih r

/-- This finite test reads the already selected whole-capture profile.
It does not test a bounded prefix or require all-state totality. -/
def check {n : Nat} (P : List Nat) (q : Fin n) : Bool :=
  (DynamicScannerBinding.resume P q).isSome

theorem check_actual {n : Nat} (M : Machine n) (w : List Char) (q : Fin n) :
    check (profile (observer M) w) q=true ↔ advance M q w≠none := by
  rw [check,DynamicScannerBinding.resume_actual]
  cases advance M q w <;> simp

theorem check_endpoint {n : Nat} (M : Machine n) (w suffix : List Char) (q : Fin n) :
    check (profile (observer M) w) q=true ↔ (run M q (w++suffix)).2.length≤suffix.length :=
  (check_actual M w q).trans (readable_iff_endpoint M w suffix q)

/-- An actual capture endpoint can be compared with the original scanner
endpoint using only its finite selected profile. -/
theorem check_position {n : Nat} (M : Machine n) (x w : List Char)
    (p j : Nat) (hj : j≤x.length) (hcap : sfx x p=w++sfx x j) (q : Fin n) :
    check (profile (observer M) w) q=true ↔ (run M q (sfx x p)).2.length≤j := by
  rw [hcap]
  simpa only [length_sfx x hj] using check_endpoint M w (sfx x j) q

/-- A finite simulation certificate covers just the actual target entry,
without requiring coverage of every state of M. -/
def covers {n : Nat} (M : Machine n) (start target : Fin n) : Bool :=
  ScannerLanguageSafety.simulationCheck M (ScannerLanguageSafety.certificate M) &&
    ScannerLanguageSafety.certificate M start target

theorem covers_sound {n : Nat} (M : Machine n) (start target : Fin n)
    (h : covers M start target=true) (w : List Char) (r : Fin n)
    (hw : advance M start w=some r) : advance M target w≠none := by
  have hh := Bool.and_eq_true_iff.mp h
  obtain ⟨u,hu,_⟩ := ScannerLanguageSafety.advance_simulation M _ hh.1 w start target r hh.2 hw
  rw [hu]
  simp

/-- Whole words of an actual source scanner inherit entry-specific safety,
including words whose individual characters fail all-state safety. -/
theorem covers_consumed {n : Nat} (M : Machine n) (start target : Fin n)
    (h : covers M start target=true) (x : List Char) :
    check (profile (observer M) (ObservedScanner.consumed M start x)) target=true :=
  (check_actual M _ target).mpr
    (covers_sound M start target h _ _ (ScannerLanguageSafety.advance_consumed M start x))

/-- The exact same captured profile can pass one entry and fail another.
In particular, this certificate is strictly weaker than all-state safety. -/
def partialM : Machine 2 := ⟨fun q => if q.val=0 then [] else [('b',1)]⟩

theorem state_specific :
    check (profile (observer partialM) ['b']) (1 : Fin 2)=true ∧
    check (profile (observer partialM) ['b']) (0 : Fin 2)=false ∧
    ¬ TotalCaptureSafety.Total partialM ['b'] := by
  refine ⟨by decide +kernel,by decide +kernel,?_⟩
  intro h
  exact h 0 (by decide +kernel)

/-- This scanner language is safe for entry 1 but not entry 0; the previous
all-state scanner-language certificate rejects it. -/
theorem coverage_specific :
    covers partialM 1 1=true ∧ covers partialM 1 0=false ∧
    ScannerLanguageSafety.safe partialM 1=false := by decide +kernel

end Shallot.MacroPeg.CBV.ScannerFrontierCertificate
