import MacroPeg.CBV.DynamicScannerCompiler

namespace Shallot.MacroPeg.CBV.DynamicScannerCorrespondence
open DynamicScannerCompiler
open DynamicScannerCapture (observer)
open CaptureTransitionProfile (profile profiles)
open ClockFreezing (Table)
abbrev Form := DynamicScannerCompiler.Expr

def Rows {n : Nat} (M : StatefulScanner.Machine n) (_state : Fin n) (bodies : List Form)
    (x : List Char) (T U : Table) : Prop :=
  ∀ i b, bodies[i]?=some b → ∀ w p j, TotalCaptureSafety.Total M w →
    p≤x.length → j≤x.length → sfx x p=w++sfx x j →
    valAt (T (n+i) [w]) p=valAt (U (address M bodies i (profile (observer M) w)) [w]) j

theorem evaluator_of_rows {n : Nat} (M : StatefulScanner.Machine n) (state : Fin n)
    (bodies : List Form) (x : List Char) (T U : Table)
    (hT : OkTV x.length T) (hU : OkTV x.length U) (hRows : Rows M state bodies x T U) :
    ∀ e, Valid M bodies e → ∀ S E,
      DependentCaptureFilter.Accurate (observer M) S E → TotalCaptureSafety.Environment M E →
      ∀ p, p≤x.length →
      evV (source M state bodies) x .callByValuePar T E (sourceExpr M bodies e) p=
        evV (target M state bodies) x .callByValueSeq U E (targetExpr M bodies S e) p
  | .user i a, he, S, E, hS, hE, p, hp => by
    let b := bodies[i]'he.1
    have hb : bodies[i]?=some b := List.getElem?_eq_getElem he.1
    have ha : evV (source M state bodies) x .callByValuePar T E (DependentCaptureFilter.render a) p=
        evV (target M state bodies) x .callByValueSeq U E (DependentCaptureFilter.render a) p :=
      IndependentCaptureControl.eval_eq _ _ x _ _ T U hT E _
        (IndependentCaptureControl.render_safe (observer M) a he.2.1) p hp
    have hF (q r : Nat) (hq : q<(observer M).width) (hr : r<(observer M).width) :
        evV (target M state bodies) x .callByValueSeq U E
          (DependentCaptureFilter.filter [] (observer M) S a q r) p=
        RegularCaptureProduct.filtered (observer M) x q r p
          (evV (target M state bodies) x .callByValueSeq U E (DependentCaptureFilter.render a) p) := by
      rw [←ha]
      exact IndependentCaptureControl.filter_correct (observer M) (DynamicScannerCapture.observer_valid M)
        _ _ x T U hT hU S E hS a he.2.1 p hp q r hq hr
    simp only [sourceExpr,targetExpr]
    rw [ProfileControl.select_correct (observer M) (DynamicScannerCapture.observer_valid M)
      (target M state bodies) x .callByValueSeq U E (DependentCaptureFilter.render a) _ p hF,←ha,
      evV_call_par (source_rule M state bodies i b hb) rfl (by decide)]
    simp only [evParArgs]
    cases hv : evV (source M state bodies) x .callByValuePar T E (DependentCaptureFilter.render a) p with
    | none => rfl
    | some v => cases v with
      | none => rfl
      | some j =>
        dsimp only []
        rw [evV_call_seq (target_rule M state bodies i b hb _
          (CaptureTransitionProfile.profile_mem _ (DynamicScannerCapture.observer_valid M) _)) rfl]
        simp only [evSeqArgs,←ha,hv]
        have hj := evV_ok hT _ p hp j hv
        obtain ⟨ht,hcap⟩ := TotalCaptureSafety.capture_total M _ x .callByValuePar T E hE _ he.2.2 p j hp hv
        exact hRows i b hb _ p j ht hp hj hcap
  | .seq a b, he, S, E, hS, hE, p, hp => by
    have ha := evaluator_of_rows M state bodies x T U hT hU hRows a he.1 S E hS hE p hp
    cases hv : evV (source M state bodies) x .callByValuePar T E (sourceExpr M bodies a) p with
    | none => rw [sourceExpr,targetExpr,evV_seq_none hv,evV_seq_none (ha.symm.trans hv)]
    | some v => cases v with
      | none => rw [sourceExpr,targetExpr,evV_seq_fail hv,evV_seq_fail (ha.symm.trans hv)]
      | some j =>
        rw [sourceExpr,targetExpr,evV_seq_ok hv,evV_seq_ok (ha.symm.trans hv)]
        exact evaluator_of_rows M state bodies x T U hT hU hRows b he.2 S E hS hE j (evV_ok hT _ p hp j hv)
  | .alt a b, he, S, E, hS, hE, p, hp => by
    have ha := evaluator_of_rows M state bodies x T U hT hU hRows a he.1 S E hS hE p hp
    cases hv : evV (source M state bodies) x .callByValuePar T E (sourceExpr M bodies a) p with
    | none => rw [sourceExpr,targetExpr,evV_alt_none hv,evV_alt_none (ha.symm.trans hv)]
    | some v => cases v with
      | none =>
        rw [sourceExpr,targetExpr,evV_alt_fail hv,evV_alt_fail (ha.symm.trans hv)]
        exact evaluator_of_rows M state bodies x T U hT hU hRows b he.2 S E hS hE p hp
      | some j => rw [sourceExpr,targetExpr,evV_alt_ok hv,evV_alt_ok (ha.symm.trans hv)]
  | .star a, he, S, E, hS, hE, p, hp =>
    evStar_congr p (fun j hj => evaluator_of_rows M state bodies x T U hT hU hRows a he S E hS hE j (by omega))
  | .notP a, he, S, E, hS, hE, p, hp => by
    simp only [sourceExpr,targetExpr,evV]
    rw [evaluator_of_rows M state bodies x T U hT hU hRows a he S E hS hE p hp]
  | .eps, _, _, _, _, _, _, _ | .lit _, _, _, _, _, _, _, _ | .param _, _, _, _, _, _, _, _
  | .any, _, _, _, _, _, _, _ | .chr _, _, _, _, _, _, _, _ | .range _ _, _, _, _, _, _, _, _ => rfl

theorem tables_rows {n : Nat} (M : StatefulScanner.Machine n) (state : Fin n)
    (bodies : List Form) (hBodies : ∀ b∈bodies, Valid M bodies b) (x : List Char) :
    ∀ k, Rows M state bodies x
      (frozen (source M state bodies) n x .callByValuePar k)
      (frozen (target M state bodies) n x .callByValueSeq k)
  | 0 => by
    intro i b hb w p j hw hp hj hcap
    simp [frozen,ClockFreezing.frozen,helpers,address,show ∀ t, ¬ n+t<n from by intro t; omega]
    rfl
  | k+1 => by
    intro i b hb w p j hw hp hj hcap
    have hs := source_rule M state bodies i b hb
    have ht := target_rule M state bodies i b hb (profile (observer M) w)
      (CaptureTransitionProfile.profile_mem _ (DynamicScannerCapture.observer_valid M) w)
    rw [ClockFreezing.frozen_user_step _ _ _ _ _ k _ (by simp [helpers]) _ hs [w] p hp,
      ClockFreezing.frozen_user_step _ _ _ _ _ k _ (by simp [helpers,address]) _ ht [w] j hj]
    cases hadv : StatefulScanner.advance M state w with
    | none => exact False.elim (hw state hadv)
    | some r =>
      simp only [DynamicScannerBinding.resume_actual,hadv,DynamicScannerBinding.scanner,Nat.zero_add]
      have hscanS : evV (source M state bodies) x .callByValuePar
          (frozen (source M state bodies) n x .callByValuePar k) [w] (.call state.val []) p=
          some (some (StatefulScanner.run M state (sfx x p)).2.length) :=
        scanner_eval M _ state x .callByValuePar k p [w] hp
      have hscanT : evV (target M state bodies) x .callByValueSeq
          (frozen (target M state bodies) n x .callByValueSeq k) [w] (.call r.val []) j=
          some (some (StatefulScanner.run M r (sfx x j)).2.length) :=
        scanner_eval M _ r x .callByValueSeq k j [w] hj
      have hrun : StatefulScanner.run M state (sfx x p)=StatefulScanner.run M r (sfx x j) := by
        rw [hcap,StatefulScanner.run_after_prefix M w (sfx x j) state r hadv]
      rw [evV_seq_ok hscanS,evV_seq_ok hscanT,hrun]
      have hz : (StatefulScanner.run M r (sfx x j)).2.length≤x.length :=
        Nat.le_trans (StatefulScanner.run_length M r _) (by rw [length_sfx x hj]; exact hj)
      exact evaluator_of_rows M state bodies x _ _ (ClockFreezing.frozen_ok _ _ _ _ _ k)
        (ClockFreezing.frozen_ok _ _ _ _ _ k) (tables_rows M state bodies hBodies x k)
        b (hBodies b (List.mem_of_getElem? hb)) [profile (observer M) w] [w]
        (DependentCaptureFilter.environment_accurate (observer M) [w])
        (by intro v hv; simp only [List.mem_singleton] at hv; subst v; exact hw) _ hz

theorem evaluator_eq {n : Nat} (M : StatefulScanner.Machine n) (state : Fin n)
    (bodies : List Form) (hBodies : ∀ b∈bodies, Valid M bodies b)
    (e : Form) (he : Valid M bodies e) (x : List Char) (k : Nat) :
    evV (source M state bodies) x .callByValuePar
      (frozen (source M state bodies) n x .callByValuePar k) [] (sourceExpr M bodies e) x.length=
    evV (target M state bodies) x .callByValueSeq
      (frozen (target M state bodies) n x .callByValueSeq k) [] (targetExpr M bodies [] e) x.length :=
  evaluator_of_rows M state bodies x _ _ (ClockFreezing.frozen_ok _ _ _ _ _ k)
    (ClockFreezing.frozen_ok _ _ _ _ _ k) (tables_rows M state bodies hBodies x k) e he [] []
    (by intro i w h; cases i <;> cases h) (by intro w h; cases h) x.length (Nat.le_refl _)

theorem observations_iff {n : Nat} (M : StatefulScanner.Machine n) (state : Fin n)
    (bodies : List Form) (hBodies : ∀ b∈bodies, Valid M bodies b)
    (e : Form) (he : Valid M bodies e) (x : List Char) (rest : Option (List Char)) :
    SObs (source M state bodies) .callByValuePar (sourceExpr M bodies e) x rest ↔
      SObs (target M state bodies) .callByValueSeq (targetExpr M bodies [] e) x rest := by
  rw [ClockFreezing.observations_iff (source_firstOrder M state bodies) x .callByValuePar (by decide)
      (helpers n) (x.length+1) (helpers_stable M _ x .callByValuePar) _ (sourceExpr_firstOrder M bodies e),
    ClockFreezing.observations_iff (target_firstOrder M state bodies) x .callByValueSeq (by decide)
      (helpers n) (x.length+1) (helpers_stable M _ x .callByValueSeq) _ (targetExpr_firstOrder M bodies [] e)]
  exact exists_congr (fun k => exists_congr (fun v => by rw [evaluator_eq M state bodies hBodies e he x k]))

theorem defined_iff {n : Nat} (M : StatefulScanner.Machine n) (state : Fin n)
    (bodies : List Form) (hBodies : ∀ b∈bodies, Valid M bodies b)
    (e : Form) (he : Valid M bodies e) (x : List Char) (v : Option Nat) :
    (∃ k, evV (source M state bodies) x .callByValuePar
      (tblV (source M state bodies) x .callByValuePar k) [] (sourceExpr M bodies e) x.length=some v) ↔
    (∃ k, evV (target M state bodies) x .callByValueSeq
      (tblV (target M state bodies) x .callByValueSeq k) [] (targetExpr M bodies [] e) x.length=some v) := by
  rw [←ClockFreezing.defined_iff (source M state bodies) x .callByValuePar (helpers n) (x.length+1)
      (helpers_stable M _ x .callByValuePar) [] (sourceExpr M bodies e) x.length v,
    ←ClockFreezing.defined_iff (target M state bodies) x .callByValueSeq (helpers n) (x.length+1)
      (helpers_stable M _ x .callByValueSeq) [] (targetExpr M bodies [] e) x.length v]
  exact exists_congr (fun k => by rw [evaluator_eq M state bodies hBodies e he x k])

theorem undefined_iff {n : Nat} (M : StatefulScanner.Machine n) (state : Fin n)
    (bodies : List Form) (hBodies : ∀ b∈bodies, Valid M bodies b)
    (e : Form) (he : Valid M bodies e) (x : List Char) :
    (∀ k, evV (source M state bodies) x .callByValuePar
      (tblV (source M state bodies) x .callByValuePar k) [] (sourceExpr M bodies e) x.length=none) ↔
    (∀ k, evV (target M state bodies) x .callByValueSeq
      (tblV (target M state bodies) x .callByValueSeq k) [] (targetExpr M bodies [] e) x.length=none) := by
  constructor
  · intro h k
    cases hv : evV (target M state bodies) x .callByValueSeq
      (tblV (target M state bodies) x .callByValueSeq k) [] (targetExpr M bodies [] e) x.length with
    | none => rfl
    | some v =>
      obtain ⟨l,hl⟩ := (defined_iff M state bodies hBodies e he x v).mpr ⟨k,hv⟩
      rw [h l] at hl; cases hl
  · intro h k
    cases hv : evV (source M state bodies) x .callByValuePar
      (tblV (source M state bodies) x .callByValuePar k) [] (sourceExpr M bodies e) x.length with
    | none => rfl
    | some v =>
      obtain ⟨l,hl⟩ := (defined_iff M state bodies hBodies e he x v).mp ⟨k,hv⟩
      rw [h l] at hl; cases hl

theorem language_translation {n : Nat} (M : StatefulScanner.Machine n) (state : Fin n)
    (bodies : List Form) (hBodies : ∀ b∈bodies, Valid M bodies b)
    (e : Form) (he : Valid M bodies e) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
      SObs (source M state bodies) .callByValuePar (sourceExpr M bodies e) x (some []) ↔
        SObs g .callByValueSeq start x (some []) :=
  ⟨target M state bodies,targetExpr M bodies [] e,target_firstOrder M state bodies,
    targetExpr_firstOrder M bodies [] e,fun x => observations_iff M state bodies hBodies e he x (some [])⟩

/-- The public entrypoint needs only finite syntax checks on the actual
arguments and bodies. Capture, frontier and recursive-row facts are derived. -/
theorem checked_observations_iff {n : Nat} (M : StatefulScanner.Machine n) (state : Fin n)
    (bodies : List Form) (hBodies : bodies.all (check M bodies)=true)
    (e : Form) (he : check M bodies e=true) (x : List Char) (rest : Option (List Char)) :
    SObs (source M state bodies) .callByValuePar (sourceExpr M bodies e) x rest ↔
      SObs (target M state bodies) .callByValueSeq (targetExpr M bodies [] e) x rest :=
  observations_iff M state bodies (bodies_check_sound M bodies hBodies) e (check_sound M bodies e he) x rest

theorem checked_language_translation {n : Nat} (M : StatefulScanner.Machine n) (state : Fin n)
    (bodies : List Form) (hBodies : bodies.all (check M bodies)=true)
    (e : Form) (he : check M bodies e=true) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
      SObs (source M state bodies) .callByValuePar (sourceExpr M bodies e) x (some []) ↔
        SObs g .callByValueSeq start x (some []) :=
  language_translation M state bodies (bodies_check_sound M bodies hBodies) e (check_sound M bodies e he)

end Shallot.MacroPeg.CBV.DynamicScannerCorrespondence
