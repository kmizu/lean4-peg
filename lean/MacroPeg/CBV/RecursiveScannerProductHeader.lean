import MacroPeg.CBV.ScannerFrontierCertificate
import MacroPeg.CBV.RecursiveScannerProductCapture

namespace Shallot.MacroPeg.CBV.RecursiveScannerProductHeader
open RecursiveScannerProductCompiler
open StatefulScanner (Machine)
open DynamicScannerCapture (observer)
open CaptureTransitionProfile (profile)

/-- Entry resumption depends only on the configured scanner state and
whole-capture profile. Replay entries impose no scanner frontier. -/
def entryCheck {n : Nat} (entry : Entry n) (P : List Nat) : Bool :=
  match entry with
  | .scan q | .shift q _ => ScannerFrontierCertificate.check P q
  | .replay | .safeReplay => true

theorem entryCheck_of_safe {n : Nat} (M : Machine n) (entry : Entry n) (w : List Char)
    (h : entry.inputSafe=true → TotalCaptureSafety.Total M w) :
    entryCheck entry (profile (observer M) w)=true := by
  cases entry with
  | scan q | shift q _ => exact (ScannerFrontierCertificate.check_actual M w q).mpr (h rfl q)
  | replay | safeReplay => rfl

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

/-- For an actual source argument, the selected finite profile certifies
exactly that the original scanner reaches the capture endpoint. This lemma
requires neither a capture safety check nor a safe retained environment. -/
theorem argument_frontier {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg)
    (a : Arg) (x : List Char) (k : Nat) (E : List (List Char))
    (p j : Nat) (hp : p≤x.length)
    (hv : evV (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) E
      (sourceExpr M a) p=some (some j)) (q : Fin n) :
    ScannerFrontierCertificate.check (profile (observer M) (pre x p j)) q=true ↔
      (StatefulScanner.run M q (sfx x p)).2.length≤j := by
  have hh := DependentCaptureFilter.success_prefix (by decide)
    (ClockFreezing.frozen_sound (source_firstOrder M entries bodies) x .callByValuePar (by decide) _ _ k)
    E (sourceExpr M a) (sourceExpr_firstOrder M a) p j hp hv
  exact ScannerFrontierCertificate.check_position M x (pre x p j) p j hh.1 hh.2 q

/-- The plain generated header starts after the actual argument but
reaches the exact endpoint of the source's original-position header. -/
theorem plain_body {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg) (q : Fin n)
    (b : Arg) (w x : List Char) (p j k l : Nat) (hp : p≤x.length) (hj : j≤x.length)
    (hcap : sfx x p=w++sfx x j) (hw : StatefulScanner.advance M q w≠none)
    (hBody : ∀ z, z≤x.length →
      evV (target M entries bodies) x .callByValueSeq (targetTable M entries bodies x l) [w]
        (plain M bodies [profile (observer M) w] b) z=
      evV (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) [w] (sourceExpr M b) z) :
    evV (target M entries bodies) x .callByValueSeq (targetTable M entries bodies x l) [w]
      (scannerBody M q bodies (profile (observer M) w) none b) j=
    evV (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) [w]
      (.seq (.call q.val []) (sourceExpr M b)) p := by
  cases ht : StatefulScanner.advance M q w with
  | none => exact False.elim (hw ht)
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
    (hcap : sfx x p=w++sfx x j) (hw : StatefulScanner.advance M q w≠none)
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
  | none => exact False.elim (hw hstep)
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
    (entry : Entry n) (hEntry : headerCheck M entry=true) (b : Arg) (w x : List Char) (p j k l : Nat)
    (hp : p≤x.length) (hj : j≤x.length) (hcap : sfx x p=w++sfx x j)
    (hw : entryCheck entry (profile (observer M) w)=true)
    (hBody : ∀ z, z≤x.length →
      evV (target M entries bodies) x .callByValueSeq (targetTable M entries bodies x l) [w]
        (plain M bodies [profile (observer M) w] b) z=
      evV (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) [w] (sourceExpr M b) z) :
    evV (target M entries bodies) x .callByValueSeq (targetTable M entries bodies x l) [w]
      (targetBody M entry bodies (profile (observer M) w) none b) j=
    evV (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) [w]
      (.seq (sourceHeader entry) (sourceExpr M b)) p := by
  cases entry with
  | scan q => exact plain_body M entries bodies q b w x p j k l hp hj hcap ((ScannerFrontierCertificate.check_actual M w q).mp hw) hBody
  | shift q R =>
    have hr := (ScannerFrontierCertificate.check_actual M w q).mp hw
    cases hs : StatefulScanner.advance M q w with
    | none => exact False.elim (hr hs)
    | some r =>
      have he := ScannerReplayResidual.replay_eq M R q hEntry w r hs
        (source M entries bodies) (target M entries bodies) x
        (sourceTable M entries bodies x k) (targetTable M entries bodies x l) p j hj hcap
      simp only [targetBody,shiftedBody,DynamicScannerBinding.resume_actual,hs]
      simp only [sourceHeader]
      cases hv : evV (target M entries bodies) x .callByValueSeq (targetTable M entries bodies x l) [w]
          (.lit ((R r).getD [])) j with
      | none => rw [evV_seq_none hv,evV_seq_none (he.trans hv)]
      | some result => cases result with
        | none => rw [evV_seq_fail hv,evV_seq_fail (he.trans hv)]
        | some z =>
          rw [evV_seq_ok hv,evV_seq_ok (he.trans hv)]
          exact hBody z (DependentCaptureFilter.success_prefix (by decide)
            (ClockFreezing.frozen_sound (target_firstOrder M entries bodies) x .callByValueSeq (by decide) _ _ l)
            [w] (.lit ((R r).getD [])) True.intro j z hj hv).1
  | replay | safeReplay =>
    simp only [sourceHeader]
    rw [evV_seq_ok (replay_prefix _ x w .callByValuePar _ p j hj hcap)]
    exact hBody j hj

theorem entry_product_body {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg)
    (entry : Entry n) (hEntry : headerCheck M entry=true) (b : Arg) (w x : List Char) (p j k l : Nat)
    (hp : p≤x.length) (hj : j≤x.length) (hcap : sfx x p=w++sfx x j)
    (hw : entryCheck entry (profile (observer M) w)=true)
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
  | scan q => exact product_body M entries bodies q b w x p j k l hp hj hcap ((ScannerFrontierCertificate.check_actual M w q).mp hw) a t ht hBody
  | shift q R =>
    have hr := (ScannerFrontierCertificate.check_actual M w q).mp hw
    cases hs : StatefulScanner.advance M q w with
    | none => exact False.elim (hr hs)
    | some r =>
      let u := (R r).getD []
      let g := source M entries bodies
      let T := sourceTable M entries bodies x k
      let h := target M entries bodies
      let U := targetTable M entries bodies x l
      have he := ScannerReplayResidual.replay_eq M R q hEntry w r hs g g x T T p j hj hcap
      have header_eq : evV g x .callByValuePar T [w]
          (.seq (sourceHeader (.shift q R)) (sourceExpr M b)) p =
          evV g x .callByValuePar T [w] (.seq (.lit u) (sourceExpr M b)) j := by
        simp only [sourceHeader]
        cases hv : evV g x .callByValueSeq T [w] (.lit u) j with
        | none => rw [evV_seq_none (he.trans hv),evV_seq_none (show evV g x .callByValuePar T [w] (.lit u) j=none from hv)]
        | some result => cases result with
          | none => rw [evV_seq_fail (he.trans hv),evV_seq_fail (show evV g x .callByValuePar T [w] (.lit u) j=some none from hv)]
          | some z => rw [evV_seq_ok (he.trans hv),evV_seq_ok (show evV g x .callByValuePar T [w] (.lit u) j=some (some z) from hv)]
      rw [header_eq]
      rw [CapturePrefixRows.filter_prefix (observer M) x w p j a.val t hp hj hcap _
        (fun z hz => DependentCaptureFilter.success_prefix (by decide)
          (ClockFreezing.frozen_sound (source_firstOrder M entries bodies) x .callByValuePar (by decide) _ _ k)
          [w] (.seq (.lit u) (sourceExpr M b)) ⟨True.intro,sourceExpr_firstOrder M b⟩ j z hj hz)]
      simp only [targetBody,shiftedBody,DynamicScannerBinding.resume_actual,hs,dif_pos a.isLt]
      rw [SequentialRecursiveScanner.state_actual]
      change evV h x .callByValueSeq U [w]
        (.seq (.lit u) (filter M bodies [profile (observer M) w] b
          (RegularCaptureProduct.run (observer M) (RegularCaptureProduct.run (observer M) a.val w) u) t)) j=_
      cases hv : evV g x .callByValuePar T [w] (.lit u) j with
      | none => rw [evV_seq_none hv,evV_seq_none (show evV h x .callByValueSeq U [w] (.lit u) j=none from hv)]; rfl
      | some result => cases result with
        | none => rw [evV_seq_fail hv,evV_seq_fail (show evV h x .callByValueSeq U [w] (.lit u) j=some none from hv)]; rfl
        | some z =>
          have hz := DependentCaptureFilter.success_prefix (by decide)
            (ClockFreezing.frozen_sound (source_firstOrder M entries bodies) x .callByValuePar (by decide) _ _ k)
            [w] (.lit u) True.intro j z hj hv
          have hword : sfx x j=u++sfx x z := by
            cases hvv : Shallot.stripPrefix? u (sfx x j) with
            | none => simp [evV,hvv] at hv
            | some rest =>
              have hvz : rest.length=z := by simpa only [evV,hvv,Option.some.injEq] using hv
              have hh := (CBVtoCBN.stripPrefix_exact u (sfx x j) rest).mp hvv
              have hr : sfx x rest.length=rest :=
                sfx_suffix (suffix_trans (sfx_is_suffix x j) ⟨u,hh⟩).choose_spec
              rw [←hvz,hr]; exact hh
          rw [evV_seq_ok hv,evV_seq_ok (show evV h x .callByValueSeq U [w] (.lit u) j=some (some z) from hv)]
          rw [hBody z hz.1 _ (RegularCaptureProduct.run_bound (valid M) _
            (RegularCaptureProduct.run_bound (valid M) _ a.isLt w) u)]
          exact (CapturePrefixRows.filter_prefix (observer M) x u j z
            (RegularCaptureProduct.run (observer M) a.val w) t hj hz.1 hword _
            (fun v hv => DependentCaptureFilter.success_prefix (by decide)
              (ClockFreezing.frozen_sound (source_firstOrder M entries bodies) x .callByValuePar (by decide) _ _ k)
              [w] (sourceExpr M b) (sourceExpr_firstOrder M b) z v hz.1 hv)).symm
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
