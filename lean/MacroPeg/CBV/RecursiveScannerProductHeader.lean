import MacroPeg.CBV.RecursiveScannerProductCapture

namespace Shallot.MacroPeg.CBV.RecursiveScannerProductHeader
open RecursiveScannerProductCompiler
open StatefulScanner (Machine)
open DynamicScannerCapture (observer)
open CaptureTransitionProfile (profile)

/-- A positive parameterized call inside an actual source argument obtains
its capture safety from the finite certified prefix, with arbitrary other
user bodies outside that prefix. -/
theorem argument_capture {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg)
    (safeUsers : Nat) (hSafe : sourceSafe M entries bodies safeUsers=true)
    (a : Arg) (trusted : Bool) (ha : argumentCheck M safeUsers trusted a=true) (x : List Char) (k : Nat)
    (E : List (List Char)) (hE : CaptureInputSafety.EnvironmentFor M trusted E) (p j : Nat) (hp : p≤x.length)
    (hv : evV (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) E (sourceExpr M a) p=some (some j)) :
    TotalCaptureSafety.Total M (pre x p j) ∧ sfx x p=pre x p j++sfx x j :=
  ParameterizedCaptureSafety.capture_of_shape M x p j hp
    (CaptureInputSafety.suffix_shape M (source M entries bodies) x .callByValuePar _ E trusted hE
      (selected M safeUsers) (RecursiveScannerProductCapture.frozen_rows M entries bodies safeUsers hSafe x k)
      (sourceExpr M a) ha p j hp hv)

theorem source_scan {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg) (q : Fin n)
    (x : List Char) (k p : Nat) (E : List (List Char)) (hp : p≤x.length) :
    evV (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) E (.call q.val []) p=
      some (some (StatefulScanner.run M q (sfx x p)).2.length) :=
  RecursiveScannerProductHelpers.scanner_eval M (sourceRules M entries bodies) q x .callByValuePar k p E hp

theorem target_scan {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg) (r : Fin n)
    (x : List Char) (k p : Nat) (E : List (List Char)) (hp : p≤x.length) :
    evV (target M entries bodies) x .callByValueSeq (targetTable M entries bodies x k) E (.call r.val []) p=
      some (some (StatefulScanner.run M r (sfx x p)).2.length) :=
  RecursiveScannerProductHelpers.scanner_eval M (targetRules M entries bodies) r x .callByValueSeq k p E hp

theorem source_scan_prefix {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg) (q : Fin n)
    (x : List Char) (k p : Nat) (E : List (List Char)) (hp : p≤x.length) :
    let z := (StatefulScanner.run M q (sfx x p)).2.length
    z≤x.length ∧ sfx x p=pre x p z++sfx x z :=
  DependentCaptureFilter.success_prefix (by decide)
    (ClockFreezing.frozen_sound (source_firstOrder M entries bodies) x .callByValuePar (by decide) _ _ k)
    E (.call q.val []) True.intro p _ hp (source_scan M entries bodies q x k p E hp)

/-- The plain generated header starts after the actual argument but
reaches the exact endpoint of the source's original-position header. -/
theorem plain_body {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg) (q : Fin n)
    (b : Arg) (w x : List Char) (p j k l : Nat) (hp : p≤x.length) (hj : j≤x.length)
    (hcap : sfx x p=w++sfx x j) (hw : TotalCaptureSafety.Total M w)
    (hBody : ∀ z, z≤x.length →
      evV (target M entries bodies) x .callByValueSeq (targetTable M entries bodies x l) [w]
        (plain M bodies [profile (observer M) w] b) z=
      evV (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) [w] (sourceExpr M b) z) :
    evV (target M entries bodies) x .callByValueSeq (targetTable M entries bodies x l) [w]
      (scannerBody M q bodies (profile (observer M) w) none b) j=
    evV (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) [w]
      (.seq (.call q.val []) (sourceExpr M b)) p := by
  cases ht : StatefulScanner.advance M q w with
  | none => exact False.elim (hw q ht)
  | some r =>
    have hs := source_scan M entries bodies q x k p [w] hp
    have hscan := target_scan M entries bodies r x l j [w] hj
    have he := StatefulScanner.run_after_prefix M w (sfx x j) q r ht
    rw [←hcap] at he
    rw [←he] at hscan
    rw [scannerBody,DynamicScannerBinding.resume_actual,ht]
    rw [evV_seq_ok hscan,evV_seq_ok hs]
    exact hBody _ (source_scan_prefix M entries bodies q x k p [w] hp).1

/-- A product header starts its observer after the argument, yet describes
the source's complete consumed prefix from the original position. The
continuation relation is the structural induction hypothesis at the real
shared scanner endpoint, including finite failure and undefinedness. -/
theorem product_body {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg) (q : Fin n)
    (b : Arg) (w x : List Char) (p j k l : Nat) (hp : p≤x.length) (hj : j≤x.length)
    (hcap : sfx x p=w++sfx x j) (hw : TotalCaptureSafety.Total M w)
    (a : Fin (observer M).width) (t : Nat) (ht : t<(observer M).width)
    (hBody : ∀ z, z≤x.length → ∀ u, u<(observer M).width →
      evV (target M entries bodies) x .callByValueSeq (targetTable M entries bodies x l) [w]
        (filter M bodies [profile (observer M) w] b u t) z=
      RegularCaptureProduct.filtered (observer M) x u t z
        (evV (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) [w] (sourceExpr M b) z)) :
    evV (target M entries bodies) x .callByValueSeq (targetTable M entries bodies x l) [w]
      (scannerBody M q bodies (profile (observer M) w) (some (a.val,t)) b) j=
    RegularCaptureProduct.filtered (observer M) x a.val t p
      (evV (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) [w]
        (.seq (.call q.val []) (sourceExpr M b)) p) := by
  cases hstep : StatefulScanner.advance M q w with
  | none => exact False.elim (hw q hstep)
  | some r =>
    have hs := source_scan M entries bodies q x k p [w] hp
    have hz := source_scan_prefix M entries bodies q x k p [w] hp
    let K := fun v : Fin (n*(observer M).width) =>
      filter M bodies [profile (observer M) w] b (StatefulScannerProduct.right (valid M).1 v).val t
    rw [scannerBody,DynamicScannerBinding.resume_actual,hstep]
    simp only [dif_pos a.isLt]
    rw [SequentialRecursiveScanner.state_actual]
    change evV (target M entries bodies) x .callByValueSeq (targetTable M entries bodies x l) [w]
      (ObservedScannerDispatch.dispatch n r (ObservedScanner.finish (observer M) (valid M) a w) K) j=_
    refine (RecursiveScannerProductHelpers.dispatch_handoff M (targetRules M entries bodies) q r a w x p j l hp hj hcap hstep .callByValueSeq [w] K).symm.trans ?_
    rw [RecursiveScannerProductHelpers.dispatch_eval M (targetRules M entries bodies) q a K x .callByValueSeq l p [w] hp]
    simp only [K,StatefulScannerProduct.right_pack]
    change evV (target M entries bodies) x .callByValueSeq (targetTable M entries bodies x l) [w]
      (filter M bodies [profile (observer M) w] b
        (ObservedScanner.finish (observer M) (valid M) a (ObservedScanner.consumed M q (sfx x p))).val t)
        (StatefulScanner.run M q (sfx x p)).2.length=_
    rw [hBody _ hz.1 _ (ObservedScanner.finish (observer M) (valid M) a _).isLt]
    rw [evV_seq_ok hs]
    have hfinish : (ObservedScanner.finish (observer M) (valid M) a
        (ObservedScanner.consumed M q (sfx x p))).val=
        RegularCaptureProduct.run (observer M) a.val (pre x p (StatefulScanner.run M q (sfx x p)).2.length) := by
      simp only [ObservedScanner.finish,ObservedScanner.consumed_pre M q x p hp]
    rw [hfinish]
    exact (CapturePrefixRows.filter_prefix (observer M) x
      (pre x p (StatefulScanner.run M q (sfx x p)).2.length) p _ a.val t hp hz.1 hz.2
      (evV (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) [w] (sourceExpr M b) _)
      (fun z h => DependentCaptureFilter.success_prefix (by decide)
        (ClockFreezing.frozen_sound (source_firstOrder M entries bodies) x .callByValuePar (by decide) _ _ k)
        [w] (sourceExpr M b) (sourceExpr_firstOrder M b) _ z hz.1 h)).symm

/-- Replaying the retained value consumes exactly the actual argument
prefix, with no scanner or termination premise. -/
theorem replay_prefix (g : MGrammar) (x w : List Char) (s : Strategy) (T : ClockFreezing.Table)
    (p j : Nat) (hj : j≤x.length) (hcap : sfx x p=w++sfx x j) :
    evV g x s T [w] (.param 0) p=some (some j) := by
  have hs := (CBVtoCBN.stripPrefix_exact w (sfx x p) (sfx x j)).mpr hcap
  simp only [evV,List.getElem?_cons_zero,hs,length_sfx x hj]

theorem entry_plain_body {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg)
    (entry : Entry n) (b : Arg) (w x : List Char) (p j k l : Nat)
    (hp : p≤x.length) (hj : j≤x.length) (hcap : sfx x p=w++sfx x j)
    (hw : entry.inputSafe=true → TotalCaptureSafety.Total M w)
    (hBody : ∀ z, z≤x.length →
      evV (target M entries bodies) x .callByValueSeq (targetTable M entries bodies x l) [w]
        (plain M bodies [profile (observer M) w] b) z=
      evV (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) [w] (sourceExpr M b) z) :
    evV (target M entries bodies) x .callByValueSeq (targetTable M entries bodies x l) [w]
      (targetBody M entry bodies (profile (observer M) w) none b) j=
    evV (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) [w]
      (.seq (sourceHeader entry) (sourceExpr M b)) p := by
  cases entry with
  | scan q => exact plain_body M entries bodies q b w x p j k l hp hj hcap (hw rfl) hBody
  | replay | safeReplay =>
    simp only [sourceHeader]
    rw [evV_seq_ok (replay_prefix _ x w .callByValuePar _ p j hj hcap)]
    exact hBody j hj

theorem entry_product_body {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg)
    (entry : Entry n) (b : Arg) (w x : List Char) (p j k l : Nat)
    (hp : p≤x.length) (hj : j≤x.length) (hcap : sfx x p=w++sfx x j)
    (hw : entry.inputSafe=true → TotalCaptureSafety.Total M w)
    (a : Fin (observer M).width) (t : Nat) (ht : t<(observer M).width)
    (hBody : ∀ z, z≤x.length → ∀ u, u<(observer M).width →
      evV (target M entries bodies) x .callByValueSeq (targetTable M entries bodies x l) [w]
        (filter M bodies [profile (observer M) w] b u t) z=
      RegularCaptureProduct.filtered (observer M) x u t z
        (evV (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) [w] (sourceExpr M b) z)) :
    evV (target M entries bodies) x .callByValueSeq (targetTable M entries bodies x l) [w]
      (targetBody M entry bodies (profile (observer M) w) (some (a.val,t)) b) j=
    RegularCaptureProduct.filtered (observer M) x a.val t p
      (evV (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) [w]
        (.seq (sourceHeader entry) (sourceExpr M b)) p) := by
  cases entry with
  | scan q => exact product_body M entries bodies q b w x p j k l hp hj hcap (hw rfl) a t ht hBody
  | replay | safeReplay =>
    rw [targetBody]
    simp only [dif_pos a.isLt]
    rw [SequentialRecursiveScanner.state_actual]
    rw [hBody j hj _ (ObservedScanner.finish (observer M) (valid M) a w).isLt]
    simp only [sourceHeader]
    rw [evV_seq_ok (replay_prefix _ x w .callByValuePar _ p j hj hcap)]
    exact (CapturePrefixRows.filter_prefix (observer M) x w p j a.val t hp hj hcap
      (evV (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) [w] (sourceExpr M b) j)
      (fun z h => DependentCaptureFilter.success_prefix (by decide)
        (ClockFreezing.frozen_sound (source_firstOrder M entries bodies) x .callByValuePar (by decide) _ _ k)
        [w] (sourceExpr M b) (sourceExpr_firstOrder M b) j z hj h)).symm

end Shallot.MacroPeg.CBV.RecursiveScannerProductHeader
