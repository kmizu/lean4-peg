import MacroPeg.CBV.GuardedScannerFilter
import MacroPeg.CBV.IndependentCaptureControl
import MacroPeg.CBV.ControlFilter
import MacroPeg.CBV.ScannerFrontierCertificate
import MacroPeg.CBV.RecursiveScannerProductCapture

namespace Shallot.MacroPeg.CBV.RecursiveScannerProductHeader
open RecursiveScannerProductCompiler
open StatefulScanner (Machine)
open DynamicScannerCapture (observer)
open CaptureTransitionProfile (profile)

/-- Entry resumption depends only on the configured scanner state and
whole-capture profile. Replay entries impose no scanner frontier. -/
def entryCheck {n : Nat} (M : Machine n) (entry : Entry n) (P : List Nat) : Bool :=
  match entry with
  | .scan q | .scannerIterate q => ScannerFrontierCertificate.check P q
  | .shift q R => ScannerReplayResidual.completeCheck M R || ScannerFrontierCertificate.check P q
  | .replay | .safeReplay | .iterate _ _ => true
  | .aligned c => GuardedReplayControl.captureCheck P c
  | .alt a b | .guard _ a b => entryCheck M a P && entryCheck M b P

theorem entryCheck_of_safe {n : Nat} (M : Machine n) (entry : Entry n) (w : List Char)
    (h : entry.inputSafe=true → TotalCaptureSafety.Total M w) :
    entryCheck M entry (profile (observer M) w)=true := by
  induction entry with
  | scan q | scannerIterate q => exact (ScannerFrontierCertificate.check_actual M w q).mpr (h rfl q)
  | shift q R => exact Bool.or_eq_true_iff.mpr (Or.inr ((ScannerFrontierCertificate.check_actual M w q).mpr (h rfl q)))
  | replay | safeReplay | iterate _ _ => rfl
  | aligned c => exact GuardedReplayControl.capture_safe M w c h
  | alt a b ha hb | guard _ a b ha hb =>
    exact Bool.and_eq_true_iff.mpr ⟨ha (fun hx => h (Bool.or_eq_true_iff.mpr (Or.inl hx))),
      hb (fun hx => h (Bool.or_eq_true_iff.mpr (Or.inr hx)))⟩

/-- The weaker shift certificate either reads this particular capture,
or certifies that every unreadable capture makes the actual source fail. -/
theorem shift_complete_of_unreadable {n : Nat} (M : Machine n)
    (q : Fin n) (R : ScannerReplayResidual.Labels n) (w : List Char)
    (hw : entryCheck M (.shift q R) (profile (observer M) w)=true)
    (hs : StatefulScanner.advance M q w=none) :
    ScannerReplayResidual.completeCheck M R=true := by
  rcases Bool.or_eq_true_iff.mp hw with hc | hr
  · exact hc
  · exact False.elim ((ScannerFrontierCertificate.check_actual M w q).mp hr hs)

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


theorem scanner_iteration_residual {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg)
    (q : Fin n) (w x : List Char) (k l p : Nat) (hp : p≤x.length) :
    evV (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) [w]
      (GuardedScannerIteration.residual (profile (observer M) w) q) p=
    evV (target M entries bodies) x .callByValueSeq (targetTable M entries bodies x l) [w]
      (GuardedScannerIteration.residual (profile (observer M) w) q) p := by
  cases hs : StatefulScanner.advance M q w with
  | none => simp [GuardedScannerIteration.residual,DynamicScannerBinding.resume_actual,hs,MExp.failAlways,evV]
  | some r =>
    simp only [GuardedScannerIteration.residual,DynamicScannerBinding.resume_actual,hs]
    exact GuardedScannerIteration.residual_transfer M r w _ _ x .callByValuePar .callByValueSeq _ _
      (fun r p hp => source_scan M entries bodies r x k p [w] hp)
      (fun r p hp => target_scan M entries bodies r x l p [w] hp) p hp

theorem scanner_iteration_source {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg)
    (q : Fin n) (w x : List Char) (k p j : Nat) (hp : p≤x.length) (hj : j≤x.length)
    (hcap : sfx x p=w++sfx x j) (hw : StatefulScanner.advance M q w≠none) :
    evV (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) [w]
      (sourceHeader (.scannerIterate q)) p=
    evV (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) [w]
      (GuardedScannerIteration.residual (profile (observer M) w) q) j := by
  cases hs : StatefulScanner.advance M q w with
  | none => exact False.elim (hw hs)
  | some r =>
    simp only [sourceHeader,GuardedScannerIteration.residual,DynamicScannerBinding.resume_actual,hs]
    exact GuardedScannerIteration.header_eq M q r w hs _ _ x .callByValuePar .callByValuePar _ _
      (fun r p hp => source_scan M entries bodies r x k p [w] hp)
      (fun r p hp => source_scan M entries bodies r x k p [w] hp) p j ⟨hp,hj,hcap⟩

theorem scanner_iteration_filter {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg)
    (q : Fin n) (w x : List Char) (k l p : Nat) (hp : p≤x.length)
    (hw : StatefulScanner.advance M q w≠none) (a z : Nat) (ha : a<(observer M).width) :
    evV (target M entries bodies) x .callByValueSeq (targetTable M entries bodies x l) [w]
      (GuardedScannerIteration.residualFilter M (profile (observer M) w) q a z) p=
    RegularCaptureProduct.filtered (observer M) x a z p
      (evV (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) [w]
        (GuardedScannerIteration.residual (profile (observer M) w) q) p) := by
  have ht := scanner_iteration_residual M entries bodies q w x k l p hp
  cases hs : StatefulScanner.advance M q w with
  | none => exact False.elim (hw hs)
  | some r =>
    simp only [GuardedScannerIteration.residualFilter,GuardedScannerIteration.residual,
      DynamicScannerBinding.resume_actual,hs] at ht ⊢
    exact (GuardedScannerFilter.star_correct M (targetRules M entries bodies)
      (target_firstOrder M entries bodies) r x w l p hp a z ha).trans
      (congrArg (RegularCaptureProduct.filtered (observer M) x a z p) ht.symm)

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

/-- The actual capture selects a rotated word or zero iterations. -/
theorem iteration_header {n : Nat} (M : Machine n) (P : List Nat) (q : Fin n)
    (R : ScannerReplayResidual.Labels n) (hc : headerCheck M (.iterate q R)=true)
    (w : List Char) (hP : P=profile (observer M) w)
    (g h : MGrammar) (x : List Char) (s t : Strategy) (T U : ClockFreezing.Table)
    (p j : Nat) (hp : p≤x.length) (hj : j≤x.length) (hcap : sfx x p=w++sfx x j) :
    evV g x s T [w] (sourceHeader (.iterate q R)) p=
      evV h x t U [w] (sourceExpr M (iterationArg P q R)) j := by
  subst P
  have ha := replay_prefix g x w s T p j hj hcap
  obtain ⟨he,hc⟩ := Bool.and_eq_true_iff.mp hc
  cases hs : StatefulScanner.advance M q w with
  | some r =>
    have hr := GuardedReplayIteration.rotate g x s T w _ _
      (ScannerReplayResidual.actual_rotation M R q he w r hs) p j hp ha
    simpa only [sourceHeader,iterationArg,DynamicScannerBinding.resume_actual,hs,sourceExpr]
      using hr.trans (ParserPrefixFusion.pure_eval g h x s t T U [w] [w] (.star (.lit ((R r).getD []))) True.intro j)
  | none =>
    have hf := ScannerReplayResidual.replay_unreadable M R q he hc w hs g x s T p j hcap
    have hg : evV g x s T [w] (GuardedReplayIteration.step ((R q).getD [])) p=some none := by
      simp only [GuardedReplayIteration.step,evV] at hf ⊢
      split at hf <;> simp_all [MExp.andP,evV]
    simp only [sourceHeader,GuardedReplayIteration.header,iterationArg,
      DynamicScannerBinding.resume_actual,hs,sourceExpr]
    rw [evV_seq_ok (show evV g x s T [w] (.star (GuardedReplayIteration.step ((R q).getD []))) p=some (some p) from evStar_fail hg),ha]
    simp [evV,Shallot.stripPrefix?,length_sfx x hj]

theorem iteration_filter {n : Nat} (M : Machine n) (bodies : List Arg)
    (P : List Nat) (q : Fin n) (R : ScannerReplayResidual.Labels n)
    (g h : MGrammar) (x : List Char) (T U : ClockFreezing.Table)
    (hT : OkTV x.length T) (hU : OkTV x.length U) (w : List Char)
    (hP : P=profile (observer M) w) (p : Nat) (hp : p≤x.length)
    (a z : Nat) (ha : a<(observer M).width) (hz : z<(observer M).width) :
    evV h x .callByValueSeq U [w] (filter M bodies [P] (iterationArg P q R) a z) p=
      RegularCaptureProduct.filtered (observer M) x a z p
        (evV g x .callByValuePar T [w] (sourceExpr M (iterationArg P q R)) p) := by
  have hS : DependentCaptureFilter.Accurate (observer M) [P] [w] := by
    subst P
    exact DependentCaptureFilter.environment_accurate (observer M) [w]
  cases hs : DynamicScannerBinding.resume P q with
  | none =>
    simp only [iterationArg,hs]
    exact IndependentCaptureControl.filter_correct (observer M) (valid M) g h x T U hT hU
      [P] [w] hS (.lit []) True.intro p hp a z ha hz
  | some r =>
    simp only [iterationArg,hs]
    exact IndependentCaptureControl.filter_correct (observer M) (valid M) g h x T U hT hU
      [P] [w] hS (.star (.lit ((R r).getD []))) True.intro p hp a z ha hz

theorem aligned_header {n : Nat} (M : Machine n) (P : List Nat) (c : GuardedReplayControl.Expr n)
    (hc : headerCheck M (.aligned c)=true) (w : List Char) (hP : P=profile (observer M) w)
    (hCap : GuardedReplayControl.captureCheck P c=true)
    (g h : MGrammar) (x : List Char) (s t : Strategy) (T U : ClockFreezing.Table)
    (p j : Nat) (hp : p≤x.length) (hj : j≤x.length) (hcap : sfx x p=w++sfx x j) :
    evV g x s T [w] (sourceHeader (.aligned c)) p=
      evV h x t U [w] (sourceExpr M (controlArg P c)) j := by
  subst P
  rw [controlArg_source]
  exact GuardedReplayControl.header_eq M c hc g h x w s t T U p j ⟨hp,hj,hcap⟩ hCap

theorem aligned_filter {n : Nat} (M : Machine n) (bodies : List Arg) (P : List Nat)
    (c : GuardedReplayControl.Expr n) (g h : MGrammar) (x : List Char) (T U : ClockFreezing.Table)
    (hT : OkTV x.length T) (hU : OkTV x.length U) (w : List Char)
    (hP : P=profile (observer M) w) (p : Nat) (hp : p≤x.length)
    (a z : Nat) (ha : a<(observer M).width) (hz : z<(observer M).width) :
    evV h x .callByValueSeq U [w] (filter M bodies [P] (controlArg P c) a z) p=
      RegularCaptureProduct.filtered (observer M) x a z p
        (evV g x .callByValuePar T [w] (sourceExpr M (controlArg P c)) p) := by
  have hS : DependentCaptureFilter.Accurate (observer M) [P] [w] := by
    subst P
    exact DependentCaptureFilter.environment_accurate (observer M) [w]
  rw [controlArg_filter,controlArg_source]
  exact IndependentCaptureControl.filter_correct (observer M) (valid M) g h x T U hT hU
    [P] [w] hS (GuardedReplayControl.residual P c) (GuardedReplayControl.residual_noHelpers P c) p hp a z ha hz

/-- Headers transfer their full partial result to the real capture endpoint. -/
theorem target_header {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg)
    (entry : Entry n) (hEntry : headerCheck M entry=true) (w x : List Char) (p j k l : Nat)
    (hp : p≤x.length) (hj : j≤x.length) (hcap : sfx x p=w++sfx x j)
    (hw : entryCheck M entry (profile (observer M) w)=true) :
    evV (target M entries bodies) x .callByValueSeq (targetTable M entries bodies x l) [w]
      (targetHeader M (profile (observer M) w) entry) j=
    evV (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) [w]
      (sourceHeader entry) p := by
  induction entry with
  | replay | safeReplay => exact (replay_prefix _ x w .callByValuePar _ p j hj hcap).symm
  | scan q =>
    have hr := (ScannerFrontierCertificate.check_actual M w q).mp hw
    cases hs : StatefulScanner.advance M q w with
    | none => exact False.elim (hr hs)
    | some r =>
      simp only [targetHeader,DynamicScannerBinding.resume_actual,hs,sourceHeader]
      rw [target_scan M entries bodies r x l j [w] hj,source_scan M entries bodies q x k p [w] hp,
        hcap,StatefulScanner.run_after_prefix M w (sfx x j) q r hs]
  | scannerIterate q =>
    have hr := (ScannerFrontierCertificate.check_actual M w q).mp hw
    exact ((scanner_iteration_source M entries bodies q w x k p j hp hj hcap hr).trans
      (scanner_iteration_residual M entries bodies q w x k l j hj)).symm
  | aligned c =>
    exact (aligned_header M _ c hEntry w rfl hw _ _ x _ _ _ _ p j hp hj hcap).symm
  | iterate q R =>
    exact (iteration_header M _ q R hEntry w rfl _ _ x _ _ _ _ p j hp hj hcap).symm
  | shift q R =>
    cases hs : StatefulScanner.advance M q w with
    | none =>
      have he := ScannerReplayResidual.replay_unreadable M R q hEntry
        (shift_complete_of_unreadable M q R w hw hs) w hs
        (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) p j hcap
      simp only [targetHeader,DynamicScannerBinding.resume_actual,hs]
      change some none=_
      exact he.symm
    | some r =>
      simp only [targetHeader,DynamicScannerBinding.resume_actual,hs]
      exact (ScannerReplayResidual.replay_eq M R q hEntry w r hs _ _ x _ _ p j hj hcap).symm
  | alt a b ha hb =>
    have heA := ha (Bool.and_eq_true_iff.mp hEntry).1 (Bool.and_eq_true_iff.mp hw).1
    have heB := hb (Bool.and_eq_true_iff.mp hEntry).2 (Bool.and_eq_true_iff.mp hw).2
    simp only [targetHeader,sourceHeader,evV,heA,heB]
  | guard positive a b ha hb =>
    have heA := ha (Bool.and_eq_true_iff.mp hEntry).1 (Bool.and_eq_true_iff.mp hw).1
    have heB := hb (Bool.and_eq_true_iff.mp hEntry).2 (Bool.and_eq_true_iff.mp hw).2
    cases positive <;>
      cases hv : evV (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) [w] (sourceHeader a) p with
      | none => simp only [targetHeader,sourceHeader,Bool.false_eq_true,if_false,if_true,MExp.andP,evV,heA,hv]
      | some result => cases result <;> simp only [targetHeader,sourceHeader,Bool.false_eq_true,if_false,if_true,MExp.andP,evV,heA,hv,heB]

theorem entry_plain_body {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg)
    (entry : Entry n) (hEntry : headerCheck M entry=true) (b : Arg) (w x : List Char) (p j k l : Nat)
    (hp : p≤x.length) (hj : j≤x.length) (hcap : sfx x p=w++sfx x j)
    (hw : entryCheck M entry (profile (observer M) w)=true)
    (hBody : ∀ z, z≤x.length →
      evV (target M entries bodies) x .callByValueSeq (targetTable M entries bodies x l) [w]
        (plain M bodies [profile (observer M) w] b) z=
      evV (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) [w] (sourceExpr M b) z) :
    evV (target M entries bodies) x .callByValueSeq (targetTable M entries bodies x l) [w]
      (targetBody M entry bodies (profile (observer M) w) none b) j=
    evV (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) [w]
      (.seq (sourceHeader entry) (sourceExpr M b)) p := by
  induction entry with
  | scannerIterate q =>
    have hr := (ScannerFrontierCertificate.check_actual M w q).mp hw
    have he := (scanner_iteration_source M entries bodies q w x k p j hp hj hcap hr).trans
      (scanner_iteration_residual M entries bodies q w x k l j hj)
    simp only [targetBody,scannerIteratedBody]
    cases hv : evV (target M entries bodies) x .callByValueSeq (targetTable M entries bodies x l) [w]
        (GuardedScannerIteration.residual (profile (observer M) w) q) j with
    | none => rw [evV_seq_none hv,evV_seq_none (he.trans hv)]
    | some v => cases v with
      | none => rw [evV_seq_fail hv,evV_seq_fail (he.trans hv)]
      | some z =>
        rw [evV_seq_ok hv,evV_seq_ok (he.trans hv)]
        exact hBody z (DependentCaptureFilter.success_prefix (by decide)
          (ClockFreezing.frozen_sound (target_firstOrder M entries bodies) x .callByValueSeq (by decide) _ _ l)
          [w] _ (GuardedScannerIteration.residual_firstOrder _ q) j z hj hv).1
  | scan q => exact plain_body M entries bodies q b w x p j k l hp hj hcap ((ScannerFrontierCertificate.check_actual M w q).mp hw) hBody
  | iterate q R =>
    have he := iteration_header M _ q R hEntry w rfl
      (source M entries bodies) (target M entries bodies) x .callByValuePar .callByValueSeq
      (sourceTable M entries bodies x k) (targetTable M entries bodies x l) p j hp hj hcap
    have hplain : plain M bodies [profile (observer M) w] (iterationArg (profile (observer M) w) q R)=
        sourceExpr M (iterationArg (profile (observer M) w) q R) := by
      simp only [iterationArg]; split <;> rfl
    simp only [targetBody,iteratedBody,plain,hplain]
    cases hv : evV (target M entries bodies) x .callByValueSeq (targetTable M entries bodies x l) [w]
        (sourceExpr M (iterationArg (profile (observer M) w) q R)) j with
    | none => rw [evV_seq_none hv,evV_seq_none (he.trans hv)]
    | some result => cases result with
      | none => rw [evV_seq_fail hv,evV_seq_fail (he.trans hv)]
      | some z =>
        rw [evV_seq_ok hv,evV_seq_ok (he.trans hv)]
        exact hBody z (DependentCaptureFilter.success_prefix (by decide)
          (ClockFreezing.frozen_sound (target_firstOrder M entries bodies) x .callByValueSeq (by decide) _ _ l)
          [w] _ (sourceExpr_firstOrder M _) j z hj hv).1
  | aligned c =>
    have he := aligned_header M _ c hEntry w rfl hw
      (source M entries bodies) (target M entries bodies) x .callByValuePar .callByValueSeq
      (sourceTable M entries bodies x k) (targetTable M entries bodies x l) p j hp hj hcap
    have hplain := (controlArg_plain M bodies (profile (observer M) w) c).trans
      (controlArg_source M (profile (observer M) w) c).symm
    simp only [targetBody,controlledBody,plain,hplain]
    cases hv : evV (target M entries bodies) x .callByValueSeq (targetTable M entries bodies x l) [w]
        (sourceExpr M (controlArg (profile (observer M) w) c)) j with
    | none => rw [evV_seq_none hv,evV_seq_none (he.trans hv)]
    | some result => cases result with
      | none => rw [evV_seq_fail hv,evV_seq_fail (he.trans hv)]
      | some z =>
        rw [evV_seq_ok hv,evV_seq_ok (he.trans hv)]
        exact hBody z (DependentCaptureFilter.success_prefix (by decide)
          (ClockFreezing.frozen_sound (target_firstOrder M entries bodies) x .callByValueSeq (by decide) _ _ l)
          [w] _ (sourceExpr_firstOrder M _) j z hj hv).1
  | shift q R =>
    cases hs : StatefulScanner.advance M q w with
    | none =>
      have he := ScannerReplayResidual.replay_unreadable M R q hEntry
        (shift_complete_of_unreadable M q R w hw hs) w hs
        (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) p j hcap
      simp only [sourceHeader]
      rw [evV_seq_fail he]
      simp [targetBody,shiftedBody,DynamicScannerBinding.resume_actual,hs,MExp.failAlways,evV]
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
  | alt a c ha hc =>
    have he := target_header M entries bodies a (Bool.and_eq_true_iff.mp hEntry).1 w x p j k l hp hj hcap (Bool.and_eq_true_iff.mp hw).1
    simp only [targetBody,ChoiceArguments.branch_eval,he]
    have hA := ha (Bool.and_eq_true_iff.mp hEntry).1 (Bool.and_eq_true_iff.mp hw).1
    have hC := hc (Bool.and_eq_true_iff.mp hEntry).2 (Bool.and_eq_true_iff.mp hw).2
    cases hv : evV (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) [w] (sourceHeader a) p with
    | none => simp only [sourceHeader,evV,hv] <;> rfl
    | some result => cases result with
      | none => simpa only [sourceHeader,evV,hv] using hC
      | some z => simpa only [sourceHeader,evV,hv] using hA
  | guard positive a c ha hc =>
    have he := target_header M entries bodies a (Bool.and_eq_true_iff.mp hEntry).1 w x p j k l hp hj hcap (Bool.and_eq_true_iff.mp hw).1
    have hC := hc (Bool.and_eq_true_iff.mp hEntry).2 (Bool.and_eq_true_iff.mp hw).2
    cases positive <;>
      cases hv : evV (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) [w] (sourceHeader a) p with
      | none => simp only [targetBody,sourceHeader,Bool.false_eq_true,if_false,if_true,MExp.andP,evV,he,hv] <;> rfl
      | some result => cases result <;>
          simp only [targetBody,sourceHeader,Bool.false_eq_true,if_false,if_true,MExp.andP,evV,he,hv] <;>
          first | exact hC | rfl

theorem entry_product_body {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg)
    (entry : Entry n) (hEntry : headerCheck M entry=true) (b : Arg) (w x : List Char) (p j k l : Nat)
    (hp : p≤x.length) (hj : j≤x.length) (hcap : sfx x p=w++sfx x j)
    (hw : entryCheck M entry (profile (observer M) w)=true)
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
  induction entry with
  | scannerIterate q =>
    have hr := (ScannerFrontierCertificate.check_actual M w q).mp hw
    let e := GuardedScannerIteration.residual (profile (observer M) w) q
    let g := source M entries bodies
    let h := target M entries bodies
    let T := sourceTable M entries bodies x k
    let U := targetTable M entries bodies x l
    have hT : SoundTV g x .callByValuePar T :=
      ClockFreezing.frozen_sound (source_firstOrder M entries bodies) x .callByValuePar (by decide) _ _ k
    have he := scanner_iteration_source M entries bodies q w x k p j hp hj hcap hr
    have hseq : evV g x .callByValuePar T [w] (.seq (sourceHeader (.scannerIterate q)) (sourceExpr M b)) p=
        evV g x .callByValuePar T [w] (.seq e (sourceExpr M b)) j := by
      change (match evV g x .callByValuePar T [w] (sourceHeader (.scannerIterate q)) p with
        | some (some z) => evV g x .callByValuePar T [w] (sourceExpr M b) z | other => other)=_
      rw [he]
      rfl
    rw [hseq]
    rw [CapturePrefixRows.filter_prefix (observer M) x w p j a.val t hp hj hcap _
      (fun z hz => DependentCaptureFilter.success_prefix (by decide) hT [w]
        (.seq e (sourceExpr M b)) ⟨GuardedScannerIteration.residual_firstOrder _ q,sourceExpr_firstOrder M b⟩ j z hj hz)]
    simp only [targetBody,scannerIteratedBody,dif_pos a.isLt,SequentialRecursiveScanner.state_actual]
    apply ControlFilter.seq_transfer (observer M) (valid M) g h x .callByValuePar .callByValueSeq
      (by decide) T U hT [w] e (sourceExpr M b) (GuardedScannerIteration.residual_firstOrder _ q)
      (sourceExpr_firstOrder M b)
      (GuardedScannerIteration.residualFilter M (profile (observer M) w) q)
      (fun a z => filter M bodies [profile (observer M) w] b a z) j hj
      (RegularCaptureProduct.run (observer M) a.val w) t
      (RegularCaptureProduct.run_bound (valid M) _ a.isLt w) ht
    · intro a z ha hz
      exact scanner_iteration_filter M entries bodies q w x k l j hj hr a z ha
    · intro z hz a ha
      exact hBody z hz a ha
  | scan q => exact product_body M entries bodies q b w x p j k l hp hj hcap ((ScannerFrontierCertificate.check_actual M w q).mp hw) a t ht hBody
  | iterate q R =>
    let e := iterationArg (profile (observer M) w) q R
    let g := source M entries bodies
    let h := target M entries bodies
    let T := sourceTable M entries bodies x k
    let U := targetTable M entries bodies x l
    have hT : SoundTV g x .callByValuePar T :=
      ClockFreezing.frozen_sound (source_firstOrder M entries bodies) x .callByValuePar (by decide) _ _ k
    have he := iteration_header M _ q R hEntry w rfl g g x .callByValuePar .callByValuePar T T p j hp hj hcap
    have hseq : evV g x .callByValuePar T [w] (.seq (sourceHeader (.iterate q R)) (sourceExpr M b)) p=
        evV g x .callByValuePar T [w] (.seq (sourceExpr M e) (sourceExpr M b)) j := by
      change (match evV g x .callByValuePar T [w] (sourceHeader (.iterate q R)) p with
        | some (some z) => evV g x .callByValuePar T [w] (sourceExpr M b) z | other => other)=_
      rw [he]
      rfl
    rw [hseq]
    rw [CapturePrefixRows.filter_prefix (observer M) x w p j a.val t hp hj hcap _
      (fun z hz => DependentCaptureFilter.success_prefix (by decide) hT [w]
        (.seq (sourceExpr M e) (sourceExpr M b)) ⟨sourceExpr_firstOrder M e,sourceExpr_firstOrder M b⟩ j z hj hz)]
    simp only [targetBody,iteratedBody,dif_pos a.isLt,SequentialRecursiveScanner.state_actual]
    apply ControlFilter.seq_transfer (observer M) (valid M) g h x .callByValuePar .callByValueSeq
      (by decide) T U hT [w] (sourceExpr M e) (sourceExpr M b)
      (sourceExpr_firstOrder M e) (sourceExpr_firstOrder M b)
      (fun a z => filter M bodies [profile (observer M) w] e a z)
      (fun a z => filter M bodies [profile (observer M) w] b a z) j hj
      (RegularCaptureProduct.run (observer M) a.val w) t
      (RegularCaptureProduct.run_bound (valid M) _ a.isLt w) ht
    · intro a z ha hz
      exact iteration_filter M bodies _ q R g h x T U
        (ClockFreezing.frozen_ok _ _ _ _ _ _) (ClockFreezing.frozen_ok _ _ _ _ _ _) w rfl j hj a z ha hz
    · intro z hz a ha
      exact hBody z hz a ha
  | aligned c =>
    let e := controlArg (profile (observer M) w) c
    let g := source M entries bodies
    let h := target M entries bodies
    let T := sourceTable M entries bodies x k
    let U := targetTable M entries bodies x l
    have hT : SoundTV g x .callByValuePar T :=
      ClockFreezing.frozen_sound (source_firstOrder M entries bodies) x .callByValuePar (by decide) _ _ k
    have he := aligned_header M _ c hEntry w rfl hw g g x .callByValuePar .callByValuePar T T p j hp hj hcap
    have hseq : evV g x .callByValuePar T [w] (.seq (sourceHeader (.aligned c)) (sourceExpr M b)) p=
        evV g x .callByValuePar T [w] (.seq (sourceExpr M e) (sourceExpr M b)) j := by
      change (match evV g x .callByValuePar T [w] (sourceHeader (.aligned c)) p with
        | some (some z) => evV g x .callByValuePar T [w] (sourceExpr M b) z | other => other)=_
      rw [he]
      rfl
    rw [hseq]
    rw [CapturePrefixRows.filter_prefix (observer M) x w p j a.val t hp hj hcap _
      (fun z hz => DependentCaptureFilter.success_prefix (by decide) hT [w]
        (.seq (sourceExpr M e) (sourceExpr M b)) ⟨sourceExpr_firstOrder M e,sourceExpr_firstOrder M b⟩ j z hj hz)]
    simp only [targetBody,controlledBody,dif_pos a.isLt,SequentialRecursiveScanner.state_actual]
    apply ControlFilter.seq_transfer (observer M) (valid M) g h x .callByValuePar .callByValueSeq
      (by decide) T U hT [w] (sourceExpr M e) (sourceExpr M b)
      (sourceExpr_firstOrder M e) (sourceExpr_firstOrder M b)
      (fun a z => filter M bodies [profile (observer M) w] e a z)
      (fun a z => filter M bodies [profile (observer M) w] b a z) j hj
      (RegularCaptureProduct.run (observer M) a.val w) t
      (RegularCaptureProduct.run_bound (valid M) _ a.isLt w) ht
    · intro a z ha hz
      exact aligned_filter M bodies _ c g h x T U
        (ClockFreezing.frozen_ok _ _ _ _ _ _) (ClockFreezing.frozen_ok _ _ _ _ _ _) w rfl j hj a z ha hz
    · intro z hz a ha
      exact hBody z hz a ha
  | shift q R =>
    cases hs : StatefulScanner.advance M q w with
    | none =>
      have he := ScannerReplayResidual.replay_unreadable M R q hEntry
        (shift_complete_of_unreadable M q R w hw hs) w hs
        (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) p j hcap
      simp only [sourceHeader]
      rw [evV_seq_fail he]
      simp [targetBody,shiftedBody,DynamicScannerBinding.resume_actual,hs,MExp.failAlways,evV,RegularCaptureProduct.filtered]
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
  | alt a c ha hc =>
    have he := target_header M entries bodies a (Bool.and_eq_true_iff.mp hEntry).1 w x p j k l hp hj hcap (Bool.and_eq_true_iff.mp hw).1
    simp only [targetBody,ChoiceArguments.branch_eval,he]
    have hA := ha (Bool.and_eq_true_iff.mp hEntry).1 (Bool.and_eq_true_iff.mp hw).1
    have hC := hc (Bool.and_eq_true_iff.mp hEntry).2 (Bool.and_eq_true_iff.mp hw).2
    cases hv : evV (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) [w] (sourceHeader a) p with
    | none => simp only [sourceHeader,evV,hv] <;> rfl
    | some result => cases result with
      | none => simpa only [sourceHeader,evV,hv] using hC
      | some z => simpa only [sourceHeader,evV,hv] using hA
  | guard positive a c ha hc =>
    have he := target_header M entries bodies a (Bool.and_eq_true_iff.mp hEntry).1 w x p j k l hp hj hcap (Bool.and_eq_true_iff.mp hw).1
    have hC := hc (Bool.and_eq_true_iff.mp hEntry).2 (Bool.and_eq_true_iff.mp hw).2
    cases positive <;>
      cases hv : evV (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) [w] (sourceHeader a) p with
      | none => simp only [targetBody,sourceHeader,Bool.false_eq_true,if_false,if_true,MExp.andP,evV,he,hv] <;> rfl
      | some result => cases result <;>
          simp only [targetBody,sourceHeader,Bool.false_eq_true,if_false,if_true,MExp.andP,evV,he,hv] <;>
          first | exact hC | rfl

end Shallot.MacroPeg.CBV.RecursiveScannerProductHeader
