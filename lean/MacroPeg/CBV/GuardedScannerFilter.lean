import MacroPeg.CBV.RecursiveScannerProductHelpers
import MacroPeg.CBV.IndependentCaptureControl
import MacroPeg.CBV.ControlFilter

namespace Shallot.MacroPeg.CBV.GuardedScannerFilter
open StatefulScanner (Machine)
open DynamicScannerCapture (observer)
open RecursiveScannerProductCompiler (helperBodies valid)
open GuardedScannerIteration

abbrev grammar := @RecursiveScannerProductHelpers.grammar
abbrev table {n : Nat} (M : Machine n) (extra : List MRule) (x : List Char) (k : Nat) :=
  RecursiveParserStability.frozen (helperBodies M) (grammar M extra) x .callByValueSeq k

theorem scanner_correct {n : Nat} (M : Machine n) (extra : List MRule) (r : Fin n) (x : List Char)
    (k p : Nat) (E : List (List Char)) (hp : p≤x.length) (a z : Nat)
    (ha : a<(observer M).width) :
    evV (grammar M extra) x .callByValueSeq (table M extra x k) E (scanFilter M r a z) p=
      RegularCaptureProduct.filtered (observer M) x a z p
        (evV (grammar M extra) x .callByValueSeq (table M extra x k) E (.call r.val []) p) := by
  let K := fun v : Fin (n*(observer M).width) =>
    if (StatefulScannerProduct.right (valid M).1 v).val=z then MExp.eps else MExp.failAlways
  simp only [scanFilter,dif_pos ha]
  rw [RecursiveScannerProductHelpers.dispatch_eval M extra r ⟨a,ha⟩ K x .callByValueSeq k p E hp,
    RecursiveScannerProductHelpers.scanner_eval M extra r x .callByValueSeq k p E hp]
  simp only [K,StatefulScannerProduct.right_pack,ObservedScanner.finish,
    RegularCaptureProduct.filtered,ObservedScanner.consumed_pre M r x p hp]
  split <;> simp [MExp.failAlways,evV]

theorem step_correct {n : Nat} (M : Machine n) (extra : List MRule) (hFO : (grammar M extra).FirstOrder)
    (r : Fin n) (x w : List Char) (k p : Nat) (hp : p≤x.length) (a z : Nat)
    (ha : a<(observer M).width) (hz : z<(observer M).width) :
    evV (grammar M extra) x .callByValueSeq (table M extra x k) [w]
      (stepFilter M r (CaptureTransitionProfile.profile (observer M) w) a z) p=
      RegularCaptureProduct.filtered (observer M) x a z p
        (evV (grammar M extra) x .callByValueSeq (table M extra x k) [w] (residualStep r) p) := by
  have hT : SoundTV (grammar M extra) x .callByValueSeq (table M extra x k) :=
    ClockFreezing.frozen_sound hFO x .callByValueSeq (by decide) _ _ k
  refine ControlFilter.seq_correct (observer M) (valid M) (grammar M extra) x .callByValueSeq
    (by decide) (table M extra x k) hT [w] (.call r.val []) (.param 0) True.intro True.intro
    (scanFilter M r) (paramFilter M (CaptureTransitionProfile.profile (observer M) w)) p hp ?_ ?_ a z ha hz
  · intro a z ha hz
    exact scanner_correct M extra r x k p [w] hp a z ha
  · intro j hj a z ha hz
    exact IndependentCaptureControl.filter_correct (observer M) (valid M) (grammar M extra) (grammar M extra) x
      (table M extra x k) (table M extra x k) (ClockFreezing.frozen_ok _ _ _ _ _ _) (ClockFreezing.frozen_ok _ _ _ _ _ _)
      _ [w] (DependentCaptureFilter.environment_accurate _ [w]) (.param 0) True.intro j hj a z ha hz

theorem star_correct {n : Nat} (M : Machine n) (extra : List MRule) (hFO : (grammar M extra).FirstOrder)
    (r : Fin n) (x w : List Char) (k p : Nat) (hp : p≤x.length) (a z : Nat)
    (ha : a<(observer M).width) :
    evV (grammar M extra) x .callByValueSeq (table M extra x k) [w]
      (GeneralStarFilter.filter (observer M).width (residualStep r)
        (stepFilter M r (CaptureTransitionProfile.profile (observer M) w)) a z) p=
      RegularCaptureProduct.filtered (observer M) x a z p
        (evV (grammar M extra) x .callByValueSeq (table M extra x k) [w] (.star (residualStep r)) p) :=
  GeneralStarFilter.correct (observer M) (valid M) (grammar M extra) x .callByValueSeq (by decide)
    (table M extra x k) (ClockFreezing.frozen_sound hFO x .callByValueSeq (by decide) _ _ k) [w]
    (residualStep r) ⟨True.intro,True.intro⟩ _
    (fun a z j ha hz hj => step_correct M extra hFO r x w k j hj a z ha hz) a z p ha hp

end Shallot.MacroPeg.CBV.GuardedScannerFilter
