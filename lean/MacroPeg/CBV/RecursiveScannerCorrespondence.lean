import MacroPeg.CBV.RecursiveScannerCompiler

namespace Shallot.MacroPeg.CBV.RecursiveScannerCorrespondence
open RecursiveScannerCompiler
open DynamicScannerCapture (observer)
open CaptureTransitionProfile (profile profiles)
open ClockFreezing (Table)
open RegularCaptureProduct (Node)
open RecursiveScannerHelpers (base)
abbrev Form := RecursiveScannerCompiler.Expr

def Rows {n : Nat} (M : StatefulScanner.Machine n) (nodes : List Node) (_state : Fin n) (bodies : List Form)
    (x : List Char) (T U : Table) : Prop :=
  ∀ i b, bodies[i]?=some b → ∀ w p j, TotalCaptureSafety.Total M w →
    p≤x.length → j≤x.length → sfx x p=w++sfx x j →
    valAt (T (offset M nodes+i) [w]) p=valAt (U (address M nodes bodies i (profile (observer M) w)) [w]) j

theorem evaluator_of_rows {n : Nat} (M : StatefulScanner.Machine n) (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes)
    (hSafe : (nodes.map RegularCaptureProduct.body).all
      (RecursiveCaptureSafety.check M nodes.length)=true) (state : Fin n)
    (bodies : List Form) (x : List Char) (k l : Nat)
    (hRows : Rows M nodes state bodies x
      (frozen (source M nodes state bodies) M nodes x .callByValuePar k)
      (frozen (target M nodes state bodies) M nodes x .callByValueSeq l)) :
    ∀ e, Valid M nodes bodies e → ∀ S E,
      DependentCaptureFilter.Accurate (observer M) S E → TotalCaptureSafety.Environment M E →
      ∀ p, p≤x.length →
      evV (source M nodes state bodies) x .callByValuePar (frozen (source M nodes state bodies) M nodes x .callByValuePar k) E (sourceExpr M nodes bodies e) p=
        evV (target M nodes state bodies) x .callByValueSeq (frozen (target M nodes state bodies) M nodes x .callByValueSeq l) E (targetExpr M nodes bodies S e) p
  | .user i a, he, S, E, hS, hE, p, hp => by
    let b := bodies[i]'he.1
    have hb : bodies[i]?=some b := List.getElem?_eq_getElem he.1
    have ha : evV (source M nodes state bodies) x .callByValuePar (frozen (source M nodes state bodies) M nodes x .callByValuePar k) E (DependentCaptureFilter.render a) p=
        evV (target M nodes state bodies) x .callByValueSeq (frozen (target M nodes state bodies) M nodes x .callByValueSeq l) E (DependentCaptureFilter.render a) p :=
      RecursiveScannerArguments.argument_eq M nodes hNodes _ _ x k l E a he.2.1 p hp
    have hF (q r : Nat) (hq : q<(observer M).width) (hr : r<(observer M).width) :
        evV (target M nodes state bodies) x .callByValueSeq (frozen (target M nodes state bodies) M nodes x .callByValueSeq l) E
          (DependentCaptureFilter.filter nodes (observer M) S a q r) p=
        RegularCaptureProduct.filtered (observer M) x q r p
          (evV (target M nodes state bodies) x .callByValueSeq (frozen (target M nodes state bodies) M nodes x .callByValueSeq l) E (DependentCaptureFilter.render a) p) := by
      rw [←ha]
      exact RecursiveScannerArguments.filter_correct M nodes hNodes _ _ x k l S E hS a he.2.1 p q r hp hq hr
    simp only [sourceExpr,targetExpr]
    rw [ProfileControl.select_correct (observer M) (DynamicScannerCapture.observer_valid M)
      (target M nodes state bodies) x .callByValueSeq (frozen (target M nodes state bodies) M nodes x .callByValueSeq l) E (DependentCaptureFilter.render a) _ p hF,←ha,
      evV_call_par (source_rule M nodes state bodies i b hb) rfl (by decide)]
    simp only [evParArgs]
    cases hv : evV (source M nodes state bodies) x .callByValuePar (frozen (source M nodes state bodies) M nodes x .callByValuePar k) E (DependentCaptureFilter.render a) p with
    | none => rfl
    | some v => cases v with
      | none => rfl
      | some j =>
        dsimp only []
        rw [evV_call_seq (target_rule M nodes state bodies i b hb _
          (CaptureTransitionProfile.profile_mem _ (DynamicScannerCapture.observer_valid M) _)) rfl]
        simp only [evSeqArgs,←ha,hv]
        have hj := evV_ok (ClockFreezing.frozen_ok _ _ _ _ _ _) _ p hp j hv
        obtain ⟨ht,hcap⟩ := RecursiveScannerArguments.capture M nodes hSafe _ x .callByValuePar k E hE a he.2.2 p j hp hv
        exact hRows i b hb _ p j ht hp hj hcap
  | .seq a b, he, S, E, hS, hE, p, hp => by
    have ha := evaluator_of_rows M nodes hNodes hSafe state bodies x k l hRows a he.1 S E hS hE p hp
    cases hv : evV (source M nodes state bodies) x .callByValuePar (frozen (source M nodes state bodies) M nodes x .callByValuePar k) E (sourceExpr M nodes bodies a) p with
    | none => rw [sourceExpr,targetExpr,evV_seq_none hv,evV_seq_none (ha.symm.trans hv)]
    | some v => cases v with
      | none => rw [sourceExpr,targetExpr,evV_seq_fail hv,evV_seq_fail (ha.symm.trans hv)]
      | some j =>
        rw [sourceExpr,targetExpr,evV_seq_ok hv,evV_seq_ok (ha.symm.trans hv)]
        exact evaluator_of_rows M nodes hNodes hSafe state bodies x k l hRows b he.2 S E hS hE j (evV_ok (ClockFreezing.frozen_ok _ _ _ _ _ _) _ p hp j hv)
  | .alt a b, he, S, E, hS, hE, p, hp => by
    have ha := evaluator_of_rows M nodes hNodes hSafe state bodies x k l hRows a he.1 S E hS hE p hp
    cases hv : evV (source M nodes state bodies) x .callByValuePar (frozen (source M nodes state bodies) M nodes x .callByValuePar k) E (sourceExpr M nodes bodies a) p with
    | none => rw [sourceExpr,targetExpr,evV_alt_none hv,evV_alt_none (ha.symm.trans hv)]
    | some v => cases v with
      | none =>
        rw [sourceExpr,targetExpr,evV_alt_fail hv,evV_alt_fail (ha.symm.trans hv)]
        exact evaluator_of_rows M nodes hNodes hSafe state bodies x k l hRows b he.2 S E hS hE p hp
      | some j => rw [sourceExpr,targetExpr,evV_alt_ok hv,evV_alt_ok (ha.symm.trans hv)]
  | .star a, he, S, E, hS, hE, p, hp =>
    evStar_congr p (fun j hj => evaluator_of_rows M nodes hNodes hSafe state bodies x k l hRows a he S E hS hE j (by omega))
  | .notP a, he, S, E, hS, hE, p, hp => by
    simp only [sourceExpr,targetExpr,evV]
    rw [evaluator_of_rows M nodes hNodes hSafe state bodies x k l hRows a he S E hS hE p hp]
  | .eps, _, _, _, _, _, _, _ | .lit _, _, _, _, _, _, _, _ | .param _, _, _, _, _, _, _, _
  | .any, _, _, _, _, _, _, _ | .chr _, _, _, _, _, _, _, _ | .range _ _, _, _, _, _, _, _, _ => rfl

theorem tables_rows {n : Nat} (M : StatefulScanner.Machine n) (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes)
    (hSafe : (nodes.map RegularCaptureProduct.body).all
      (RecursiveCaptureSafety.check M nodes.length)=true) (state : Fin n)
    (bodies : List Form) (hBodies : ∀ b∈bodies, Valid M nodes bodies b) (x : List Char) :
    ∀ k, Rows M nodes state bodies x
      (frozen (source M nodes state bodies) M nodes x .callByValuePar k)
      (frozen (target M nodes state bodies) M nodes x .callByValueSeq k)
  | 0 => by
    intro i b hb w p j hw hp hj hcap
    simp [frozen,RecursiveParserStability.frozen,ClockFreezing.frozen,RecursiveParserStability.pick,
      RecursiveScannerHelpers.length,offset,address,show ∀ t, ¬ base M nodes+n+t<base M nodes+n from by intro t; omega]
    rfl
  | k+1 => by
    intro i b hb w p j hw hp hj hcap
    have hs := source_rule M nodes state bodies i b hb
    have ht := target_rule M nodes state bodies i b hb (profile (observer M) w)
      (CaptureTransitionProfile.profile_mem _ (DynamicScannerCapture.observer_valid M) w)
    rw [ClockFreezing.frozen_user_step _ _ _ _ _ k _ (by simp [RecursiveParserStability.pick,RecursiveScannerHelpers.length,offset]) _ hs [w] p hp,
      ClockFreezing.frozen_user_step _ _ _ _ _ k _ (by simp [RecursiveParserStability.pick,RecursiveScannerHelpers.length,offset,address]) _ ht [w] j hj]
    cases hadv : StatefulScanner.advance M state w with
    | none => exact False.elim (hw state hadv)
    | some r =>
      simp only [DynamicScannerBinding.resume_actual,hadv,DynamicScannerBinding.scanner]
      have hscanS : evV (source M nodes state bodies) x .callByValuePar
          (frozen (source M nodes state bodies) M nodes x .callByValuePar k) [w] (.call (base M nodes+state.val) []) p=
          some (some (StatefulScanner.run M state (sfx x p)).2.length) :=
        RecursiveScannerHelpers.scanner_eval M nodes _ state x .callByValuePar k p [w] hp
      have hscanT : evV (target M nodes state bodies) x .callByValueSeq
          (frozen (target M nodes state bodies) M nodes x .callByValueSeq k) [w] (.call (base M nodes+r.val) []) j=
          some (some (StatefulScanner.run M r (sfx x j)).2.length) :=
        RecursiveScannerHelpers.scanner_eval M nodes _ r x .callByValueSeq k j [w] hj
      have hrun : StatefulScanner.run M state (sfx x p)=StatefulScanner.run M r (sfx x j) := by
        rw [hcap,StatefulScanner.run_after_prefix M w (sfx x j) state r hadv]
      rw [evV_seq_ok hscanS,evV_seq_ok hscanT,hrun]
      have hz : (StatefulScanner.run M r (sfx x j)).2.length≤x.length :=
        Nat.le_trans (StatefulScanner.run_length M r _) (by rw [length_sfx x hj]; exact hj)
      exact evaluator_of_rows M nodes hNodes hSafe state bodies x k k (tables_rows M nodes hNodes hSafe state bodies hBodies x k)
        b (hBodies b (List.mem_of_getElem? hb)) [profile (observer M) w] [w]
        (DependentCaptureFilter.environment_accurate (observer M) [w])
        (by intro v hv; simp only [List.mem_singleton] at hv; subst v; exact hw) _ hz

theorem evaluator_eq {n : Nat} (M : StatefulScanner.Machine n) (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes)
    (hSafe : (nodes.map RegularCaptureProduct.body).all
      (RecursiveCaptureSafety.check M nodes.length)=true) (state : Fin n)
    (bodies : List Form) (hBodies : ∀ b∈bodies, Valid M nodes bodies b)
    (e : Form) (he : Valid M nodes bodies e) (x : List Char) (k : Nat) :
    evV (source M nodes state bodies) x .callByValuePar
      (frozen (source M nodes state bodies) M nodes x .callByValuePar k) [] (sourceExpr M nodes bodies e) x.length=
    evV (target M nodes state bodies) x .callByValueSeq
      (frozen (target M nodes state bodies) M nodes x .callByValueSeq k) [] (targetExpr M nodes bodies [] e) x.length :=
  evaluator_of_rows M nodes hNodes hSafe state bodies x k k (tables_rows M nodes hNodes hSafe state bodies hBodies x k) e he [] []
    (by intro i w h; cases i <;> cases h) (by intro w h; cases h) x.length (Nat.le_refl _)

theorem observations_iff {n : Nat} (M : StatefulScanner.Machine n) (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes)
    (hSafe : (nodes.map RegularCaptureProduct.body).all
      (RecursiveCaptureSafety.check M nodes.length)=true) (state : Fin n)
    (bodies : List Form) (hBodies : ∀ b∈bodies, Valid M nodes bodies b)
    (e : Form) (he : Valid M nodes bodies e) (x : List Char) (rest : Option (List Char)) :
    SObs (source M nodes state bodies) .callByValuePar (sourceExpr M nodes bodies e) x rest ↔
      SObs (target M nodes state bodies) .callByValueSeq (targetExpr M nodes bodies [] e) x rest := by
  rw [ClockFreezing.observations_iff (source_firstOrder M nodes state bodies) x .callByValuePar (by decide)
      (helpers M nodes) (RecursiveParserStability.floor (helperBodies M nodes) x) (helpers_stable M nodes hNodes _ x .callByValuePar) _ (sourceExpr_firstOrder M nodes bodies e),
    ClockFreezing.observations_iff (target_firstOrder M nodes state bodies) x .callByValueSeq (by decide)
      (helpers M nodes) (RecursiveParserStability.floor (helperBodies M nodes) x) (helpers_stable M nodes hNodes _ x .callByValueSeq) _ (targetExpr_firstOrder M nodes bodies [] e)]
  exact exists_congr (fun k => exists_congr (fun v => by rw [evaluator_eq M nodes hNodes hSafe state bodies hBodies e he x k]))

theorem defined_iff {n : Nat} (M : StatefulScanner.Machine n) (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes)
    (hSafe : (nodes.map RegularCaptureProduct.body).all
      (RecursiveCaptureSafety.check M nodes.length)=true) (state : Fin n)
    (bodies : List Form) (hBodies : ∀ b∈bodies, Valid M nodes bodies b)
    (e : Form) (he : Valid M nodes bodies e) (x : List Char) (v : Option Nat) :
    (∃ k, evV (source M nodes state bodies) x .callByValuePar
      (tblV (source M nodes state bodies) x .callByValuePar k) [] (sourceExpr M nodes bodies e) x.length=some v) ↔
    (∃ k, evV (target M nodes state bodies) x .callByValueSeq
      (tblV (target M nodes state bodies) x .callByValueSeq k) [] (targetExpr M nodes bodies [] e) x.length=some v) := by
  rw [←ClockFreezing.defined_iff (source M nodes state bodies) x .callByValuePar (helpers M nodes) (RecursiveParserStability.floor (helperBodies M nodes) x)
      (helpers_stable M nodes hNodes _ x .callByValuePar) [] (sourceExpr M nodes bodies e) x.length v,
    ←ClockFreezing.defined_iff (target M nodes state bodies) x .callByValueSeq (helpers M nodes) (RecursiveParserStability.floor (helperBodies M nodes) x)
      (helpers_stable M nodes hNodes _ x .callByValueSeq) [] (targetExpr M nodes bodies [] e) x.length v]
  exact exists_congr (fun k => by rw [evaluator_eq M nodes hNodes hSafe state bodies hBodies e he x k])

theorem undefined_iff {n : Nat} (M : StatefulScanner.Machine n) (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes)
    (hSafe : (nodes.map RegularCaptureProduct.body).all
      (RecursiveCaptureSafety.check M nodes.length)=true) (state : Fin n)
    (bodies : List Form) (hBodies : ∀ b∈bodies, Valid M nodes bodies b)
    (e : Form) (he : Valid M nodes bodies e) (x : List Char) :
    (∀ k, evV (source M nodes state bodies) x .callByValuePar
      (tblV (source M nodes state bodies) x .callByValuePar k) [] (sourceExpr M nodes bodies e) x.length=none) ↔
    (∀ k, evV (target M nodes state bodies) x .callByValueSeq
      (tblV (target M nodes state bodies) x .callByValueSeq k) [] (targetExpr M nodes bodies [] e) x.length=none) := by
  constructor
  · intro h k
    cases hv : evV (target M nodes state bodies) x .callByValueSeq
      (tblV (target M nodes state bodies) x .callByValueSeq k) [] (targetExpr M nodes bodies [] e) x.length with
    | none => rfl
    | some v =>
      obtain ⟨l,hl⟩ := (defined_iff M nodes hNodes hSafe state bodies hBodies e he x v).mpr ⟨k,hv⟩
      rw [h l] at hl; cases hl
  · intro h k
    cases hv : evV (source M nodes state bodies) x .callByValuePar
      (tblV (source M nodes state bodies) x .callByValuePar k) [] (sourceExpr M nodes bodies e) x.length with
    | none => rfl
    | some v =>
      obtain ⟨l,hl⟩ := (defined_iff M nodes hNodes hSafe state bodies hBodies e he x v).mp ⟨k,hv⟩
      rw [h l] at hl; cases hl

theorem language_translation {n : Nat} (M : StatefulScanner.Machine n) (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes)
    (hSafe : (nodes.map RegularCaptureProduct.body).all
      (RecursiveCaptureSafety.check M nodes.length)=true) (state : Fin n)
    (bodies : List Form) (hBodies : ∀ b∈bodies, Valid M nodes bodies b)
    (e : Form) (he : Valid M nodes bodies e) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
      SObs (source M nodes state bodies) .callByValuePar (sourceExpr M nodes bodies e) x (some []) ↔
        SObs g .callByValueSeq start x (some []) :=
  ⟨target M nodes state bodies,targetExpr M nodes bodies [] e,target_firstOrder M nodes state bodies,
    targetExpr_firstOrder M nodes bodies [] e,fun x => observations_iff M nodes hNodes hSafe state bodies hBodies e he x (some [])⟩

/-- The public entrypoint needs only finite syntax checks on the actual
arguments and bodies. Capture, frontier and recursive-row facts are derived. -/
theorem checked_observations_iff {n : Nat} (M : StatefulScanner.Machine n) (nodes : List Node) (hNodes : nodesCheck nodes=true)
    (hSafe : (nodes.map RegularCaptureProduct.body).all
      (RecursiveCaptureSafety.check M nodes.length)=true) (state : Fin n)
    (bodies : List Form) (hBodies : bodies.all (check M nodes bodies)=true)
    (e : Form) (he : check M nodes bodies e=true) (x : List Char) (rest : Option (List Char)) :
    SObs (source M nodes state bodies) .callByValuePar (sourceExpr M nodes bodies e) x rest ↔
      SObs (target M nodes state bodies) .callByValueSeq (targetExpr M nodes bodies [] e) x rest :=
  observations_iff M nodes (nodesCheck_sound nodes hNodes) hSafe state bodies (bodies_check_sound M nodes bodies hBodies) e (check_sound M nodes bodies e he) x rest

theorem checked_language_translation {n : Nat} (M : StatefulScanner.Machine n) (nodes : List Node) (hNodes : nodesCheck nodes=true)
    (hSafe : (nodes.map RegularCaptureProduct.body).all
      (RecursiveCaptureSafety.check M nodes.length)=true) (state : Fin n)
    (bodies : List Form) (hBodies : bodies.all (check M nodes bodies)=true)
    (e : Form) (he : check M nodes bodies e=true) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
      SObs (source M nodes state bodies) .callByValuePar (sourceExpr M nodes bodies e) x (some []) ↔
        SObs g .callByValueSeq start x (some []) :=
  language_translation M nodes (nodesCheck_sound nodes hNodes) hSafe state bodies (bodies_check_sound M nodes bodies hBodies) e (check_sound M nodes bodies e he)

end Shallot.MacroPeg.CBV.RecursiveScannerCorrespondence
