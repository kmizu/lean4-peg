import MacroPeg.CBV.ScannerFrontierCertificate
import MacroPeg.CBV.RecursiveScannerProductHelpers

namespace Shallot.MacroPeg.CBV.RecursiveScannerProductCapture
open RecursiveScannerProductCompiler
open RecursiveScannerProductHelpers (grammar)
open StatefulScanner (Machine)

/-- Entry-specific safety for an actual installed scanner row, at every
physical clock and arbitrary retained environment. A small-clock success
is lifted to the exact run; no semantic row premise is supplied. -/
theorem scanner_frontier_physical {n : Nat} (M : Machine n) (extra : List MRule)
    (start target : Fin n) (hc : ScannerFrontierCertificate.covers M start target=true)
    (x : List Char) (s : Strategy) (clock : Nat) (E : List (List Char))
    (p j : Nat) (hp : p≤x.length)
    (h : valAt (tblV (grammar M extra) x s clock start.val E) p=some (some j)) :
    ScannerFrontierCertificate.check
      (CaptureTransitionProfile.profile (DynamicScannerCapture.observer M) (pre x p j)) target=true := by
  have hH : start.val<(helperBodies M).length := by
    rw [RecursiveScannerProductHelpers.helperBodies_length]
    exact Nat.lt_of_lt_of_le start.isLt (by omega)
  have henv := RecursiveParserStability.helper_rows_eq (RecursiveScannerProductHelpers.lexical M)
    (RecursiveScannerProductHelpers.installed M extra) (RecursiveScannerProductHelpers.installed M extra)
    x s s clock start.val hH E []
  rw [henv] at h
  have hlift := ((tblV_le (grammar M extra) x s (show clock≤clock+p+1 by omega)) start.val [] p).eq_of_some h
  have hrun := StatefulScanner.query_eval M (fun _ => true) (grammar M extra) 0
    (fun r => by simpa only [Nat.zero_add,StatefulScanner.terminal,if_true] using RecursiveScannerProductHelpers.scanner_rule M extra r)
    x s p hp (clock+p+1) (by omega) start
  have hj : (StatefulScanner.run M start (sfx x p)).2.length=j := by
    have hh := (by simpa only [Nat.zero_add,if_true] using hrun :
      valAt (tblV (grammar M extra) x s (clock+p+1) start.val []) p=
        some (some (StatefulScanner.run M start (sfx x p)).2.length)).symm.trans hlift
    simpa only [Option.some.injEq] using hh
  rw [←hj,ObservedScanner.consumed_pre M start x p hp]
  exact ScannerFrontierCertificate.covers_consumed M start target hc (sfx x p)

/-- A primitive's successful physical row is the real scanner run, even
at small clocks: monotonicity lifts that success to a sufficient clock. -/
theorem primitive_physical_rows {n : Nat} (M : Machine n) (extra : List MRule)
    (x : List Char) (s : Strategy) (clock : Nat) :
    SelectedCaptureSafety.Rows M (primitive M) x (tblV (grammar M extra) x s clock) := by
  intro i hi E _ p j hp h
  have hn : i<n := by
    by_cases hn : i<n
    · exact hn
    · simp [primitive,hn] at hi
  let q : Fin n := ⟨i,hn⟩
  have hq : ScannerLanguageSafety.safe M q=true := by simpa [primitive,hn,q] using hi
  have hH : i<(helperBodies M).length := by
    rw [RecursiveScannerProductHelpers.helperBodies_length]
    omega
  have henv := RecursiveParserStability.helper_rows_eq (RecursiveScannerProductHelpers.lexical M)
    (RecursiveScannerProductHelpers.installed M extra) (RecursiveScannerProductHelpers.installed M extra)
    x s s clock i hH E []
  rw [henv] at h
  have hlift := ((tblV_le (grammar M extra) x s (show clock≤clock+p+1 by omega)) i [] p).eq_of_some h
  have hrun := StatefulScanner.query_eval M (fun _ => true) (grammar M extra) 0
    (fun r => by simpa only [Nat.zero_add,StatefulScanner.terminal,if_true] using RecursiveScannerProductHelpers.scanner_rule M extra r)
    x s p hp (clock+p+1) (by omega) q
  have hj : (StatefulScanner.run M q (sfx x p)).2.length=j := by
    have hh := (by simpa only [Nat.zero_add,q,if_true] using hrun :
      valAt (tblV (grammar M extra) x s (clock+p+1) i []) p=
        some (some (StatefulScanner.run M q (sfx x p)).2.length)).symm.trans hlift
    simpa only [q,Nat.zero_add,if_true,Option.some.injEq] using hh
  have hlen := StatefulScanner.run_length M q (sfx x p)
  rw [length_sfx x hp] at hlen
  refine ⟨by omega,ObservedScanner.consumed M q (sfx x p),
    ScannerLanguageSafety.consumed_total M q hq _,?_⟩
  have split := ObservedScanner.consumed_split M q (sfx x p)
  have hrest : sfx x (StatefulScanner.run M q (sfx x p)).2.length=
      (StatefulScanner.run M q (sfx x p)).2 :=
    sfx_suffix (suffix_trans (sfx_is_suffix x p) ⟨_,split⟩).choose_spec
  rw [←hj,hrest]
  exact split

theorem primitive_frozen {n : Nat} (M : Machine n) (i : Nat) (hi : primitive M i=true) :
    RecursiveParserStability.pick (helperBodies M) i=true := by
  have hn : i<n := by
    by_cases hn : i<n
    · exact hn
    · simp [primitive,hn] at hi
  simp only [RecursiveParserStability.pick,decide_eq_true_eq,
    RecursiveScannerProductHelpers.helperBodies_length]
  omega

/-- Actual selected recursive users inherit capture safety from the
structural check plus concrete primitive scanner rows. -/
theorem frozen_rows {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg)
    (safeUsers : Nat) (hSafe : sourceSafe M entries bodies safeUsers=true)
    (x : List Char) (k : Nat) :
    SelectedCaptureSafety.Rows M (selected M safeUsers) x (sourceTable M entries bodies x k) :=
  SelectedCaptureSafety.certified_frozen_rows M (source M entries bodies)
    (selected M safeUsers) (primitive M) (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hSafe).2).1 x .callByValuePar
    (RecursiveParserStability.pick (helperBodies M)) (RecursiveParserStability.floor (helperBodies M) x)
    (primitive_physical_rows M (sourceRules M entries bodies) x .callByValuePar)
    (primitive_frozen M) k

end Shallot.MacroPeg.CBV.RecursiveScannerProductCapture
