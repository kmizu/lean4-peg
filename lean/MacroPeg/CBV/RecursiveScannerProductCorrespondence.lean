import MacroPeg.CBV.RecursiveScannerProductHeader
import MacroPeg.CBV.IndependentCaptureControl
import MacroPeg.CBV.ControlFilter

namespace Shallot.MacroPeg.CBV.RecursiveScannerProductCorrespondence
open RecursiveScannerProductCompiler
open StatefulScanner (Machine)
open DynamicScannerCapture (observer)
open CaptureTransitionProfile (profile profiles)
open RegularCaptureProduct (filtered run)

theorem source_sound {n : Nat} (M : Machine n) (start : Fin n) (bodies : List Arg) (x : List Char) (k : Nat) :
    SoundTV (source M start bodies) x .callByValuePar (sourceTable M start bodies x k) :=
  ClockFreezing.frozen_sound (source_firstOrder M start bodies) x .callByValuePar (by decide) _ _ k

theorem target_sound {n : Nat} (M : Machine n) (start : Fin n) (bodies : List Arg) (x : List Char) (k : Nat) :
    SoundTV (target M start bodies) x .callByValueSeq (targetTable M start bodies x k) :=
  ClockFreezing.frozen_sound (target_firstOrder M start bodies) x .callByValueSeq (by decide) _ _ k

theorem source_ok {n : Nat} (M : Machine n) (start : Fin n) (bodies : List Arg) (x : List Char) (k : Nat) :
    OkTV x.length (sourceTable M start bodies x k) := ClockFreezing.frozen_ok _ _ _ _ _ _

theorem target_ok {n : Nat} (M : Machine n) (start : Fin n) (bodies : List Arg) (x : List Char) (k : Nat) :
    OkTV x.length (targetTable M start bodies x k) := ClockFreezing.frozen_ok _ _ _ _ _ _

def Rows {n : Nat} (M : Machine n) (start : Fin n) (bodies : List Arg) (x : List Char) (k : Nat) : Prop :=
  ∀ i b, bodies[i]?=some b → ∀ w p j, p≤x.length → j≤x.length → sfx x p=w++sfx x j →
    TotalCaptureSafety.Total M w →
    (valAt (sourceTable M start bodies x k (offset M+i) [w]) p=
      valAt (targetTable M start bodies x k (address M bodies i (profile (observer M) w) none) [w]) j) ∧
    (∀ q t, q<(observer M).width → t<(observer M).width →
      valAt (targetTable M start bodies x k (address M bodies i (profile (observer M) w) (some (q,t))) [w]) j=
        filtered (observer M) x q t p (valAt (sourceTable M start bodies x k (offset M+i) [w]) p))

theorem selected_call {n : Nat} (M : Machine n) (start : Fin n) (bodies : List Arg)
    (x : List Char) (k : Nat) (i : Nat) (b : Arg) (hi : bodies[i]?=some b)
    (a : Arg) (S : List (List Nat)) (E : List (List Char)) (p : Nat) (mode : Mode) (hm : mode∈modes M)
    (hplain : evV (target M start bodies) x .callByValueSeq (targetTable M start bodies x k) E (plain M bodies S a) p=
      evV (source M start bodies) x .callByValuePar (sourceTable M start bodies x k) E (sourceExpr M a) p)
    (hfilter : ∀ q r, q<(observer M).width → r<(observer M).width →
      evV (target M start bodies) x .callByValueSeq (targetTable M start bodies x k) E (filter M bodies S a q r) p=
        filtered (observer M) x q r p (evV (target M start bodies) x .callByValueSeq (targetTable M start bodies x k) E (plain M bodies S a) p)) :
    evV (target M start bodies) x .callByValueSeq (targetTable M start bodies x k) E
      (ProfileControl.select (observer M) (plain M bodies S a) (fun q r => filter M bodies S a q r)
        (fun P => .call (address M bodies i P mode) [plain M bodies S a])) p=
      match evV (source M start bodies) x .callByValuePar (sourceTable M start bodies x k) E (sourceExpr M a) p with
      | some (some j) => valAt (targetTable M start bodies x k (address M bodies i (profile (observer M) (pre x p j)) mode) [pre x p j]) j
      | other => other := by
  rw [ProfileControl.select_correct (observer M) (valid M) _ x .callByValueSeq _ E _ _ p hfilter,hplain]
  cases hv : evV (source M start bodies) x .callByValuePar (sourceTable M start bodies x k) E (sourceExpr M a) p with
  | none => rfl
  | some result => cases result with
    | none => rfl
    | some j =>
      dsimp only []
      rw [evV_call_seq (target_rule M start bodies i b hi _ (CaptureTransitionProfile.profile_mem (observer M) (valid M) _) mode hm) rfl]
      simp only [evSeqArgs,hplain,hv]

theorem user_correct {n : Nat} (M : Machine n) (start : Fin n) (bodies : List Arg)
    (safeUsers : Nat) (hSafe : sourceSafe M start bodies safeUsers=true)
    (x : List Char) (k : Nat) (hRows : Rows M start bodies x k) (i : Nat) (b : Arg) (hi : bodies[i]?=some b)
    (a : Arg) (ha : argumentCheck M safeUsers a=true) (S : List (List Nat)) (E : List (List Char))
    (hE : TotalCaptureSafety.Environment M E) (p : Nat) (hp : p≤x.length)
    (hplain : evV (target M start bodies) x .callByValueSeq (targetTable M start bodies x k) E (plain M bodies S a) p=
      evV (source M start bodies) x .callByValuePar (sourceTable M start bodies x k) E (sourceExpr M a) p)
    (hfilter : ∀ q r, q<(observer M).width → r<(observer M).width →
      evV (target M start bodies) x .callByValueSeq (targetTable M start bodies x k) E (filter M bodies S a q r) p=
        filtered (observer M) x q r p (evV (target M start bodies) x .callByValueSeq (targetTable M start bodies x k) E (plain M bodies S a) p)) :
    (evV (target M start bodies) x .callByValueSeq (targetTable M start bodies x k) E (plain M bodies S (.user i a)) p=
      evV (source M start bodies) x .callByValuePar (sourceTable M start bodies x k) E (sourceExpr M (.user i a)) p) ∧
    (∀ q r, q<(observer M).width → r<(observer M).width →
      evV (target M start bodies) x .callByValueSeq (targetTable M start bodies x k) E (filter M bodies S (.user i a) q r) p=
        filtered (observer M) x q r p (evV (source M start bodies) x .callByValuePar (sourceTable M start bodies x k) E (sourceExpr M (.user i a)) p)) := by
  have harg := DependentCaptureFilter.success_prefix (g := source M start bodies) (x := x)
    (by decide) (source_sound M start bodies x k) E (sourceExpr M a) (sourceExpr_firstOrder M a) p
  constructor
  · simp only [plain,sourceExpr]
    rw [selected_call M start bodies x k i b hi a S E p none (mode_plain_mem M) hplain hfilter,
      evV_call_par (source_rule M start bodies i b hi) rfl (by decide)]
    simp only [evParArgs]
    cases hv : evV (source M start bodies) x .callByValuePar (sourceTable M start bodies x k) E (sourceExpr M a) p with
    | none => rfl
    | some result => cases result with
      | none => rfl
      | some j =>
        obtain ⟨hj,hcap⟩ := harg j hp hv
        have hw := (RecursiveScannerProductHeader.argument_capture M start bodies safeUsers hSafe a ha x k E hE p j hp hv).1
        exact (hRows i b hi _ p j hp hj hcap hw).1.symm
  · intro q r hq hr
    simp only [filter,sourceExpr]
    rw [selected_call M start bodies x k i b hi a S E p (some (q,r)) (mode_filter_mem M q r hq hr) hplain hfilter,
      evV_call_par (source_rule M start bodies i b hi) rfl (by decide)]
    simp only [evParArgs]
    cases hv : evV (source M start bodies) x .callByValuePar (sourceTable M start bodies x k) E (sourceExpr M a) p with
    | none => rfl
    | some result => cases result with
      | none => rfl
      | some j =>
        obtain ⟨hj,hcap⟩ := harg j hp hv
        have hw := (RecursiveScannerProductHeader.argument_capture M start bodies safeUsers hSafe a ha x k E hE p j hp hv).1
        exact (hRows i b hi _ p j hp hj hcap hw).2 q r hq hr

/-- The source argument syntax and recursive user rows are separate
inductions. Captures are certified from the actual source component. -/
theorem evaluator_of_rows {n : Nat} (M : Machine n) (start : Fin n) (bodies : List Arg)
    (safeUsers : Nat) (hSafe : sourceSafe M start bodies safeUsers=true)
    (x : List Char) (k : Nat) (hRows : Rows M start bodies x k) :
    ∀ e, Valid M bodies safeUsers e → ∀ S E, DependentCaptureFilter.Accurate (observer M) S E →
      TotalCaptureSafety.Environment M E → ∀ p, p≤x.length →
    (evV (target M start bodies) x .callByValueSeq (targetTable M start bodies x k) E (plain M bodies S e) p=
      evV (source M start bodies) x .callByValuePar (sourceTable M start bodies x k) E (sourceExpr M e) p) ∧
    (∀ q r, q<(observer M).width → r<(observer M).width →
      evV (target M start bodies) x .callByValueSeq (targetTable M start bodies x k) E (filter M bodies S e q r) p=
        filtered (observer M) x q r p
          (evV (source M start bodies) x .callByValuePar (sourceTable M start bodies x k) E (sourceExpr M e) p))
  | .lit w, _, S, E, hS, _, p, hp => by
    refine ⟨rfl,?_⟩
    intro q r hq hr
    exact IndependentCaptureControl.filter_correct (observer M) (valid M) _ _ x _ _
      (source_ok M start bodies x k) (target_ok M start bodies x k) S E hS (.lit w) True.intro p hp q r hq hr
  | .param i, _, S, E, hS, _, p, hp => by
    refine ⟨rfl,?_⟩
    intro q r hq hr
    exact IndependentCaptureControl.filter_correct (observer M) (valid M) _ _ x _ _
      (source_ok M start bodies x k) (target_ok M start bodies x k) S E hS (.param i) True.intro p hp q r hq hr
  | .user i a, ha, S, E, hS, hE, p, hp => by
    have hib : i<bodies.length := ha.1
    have hr : bodies[i]?=some bodies[i] := List.getElem?_eq_getElem hib
    have ih := evaluator_of_rows M start bodies safeUsers hSafe x k hRows a ha.2.2 S E hS hE p hp
    apply user_correct M start bodies safeUsers hSafe x k hRows i bodies[i] hr a ha.2.1 S E hE p hp ih.1
    intro q t hq ht
    rw [ih.1]
    exact ih.2 q t hq ht
  | .seq a b, ha, S, E, hS, hE, p, hp => by
    have hA := evaluator_of_rows M start bodies safeUsers hSafe x k hRows a ha.1 S E hS hE p hp
    have he : evV (target M start bodies) x .callByValueSeq (targetTable M start bodies x k) E (plain M bodies S (.seq a b)) p =
        evV (source M start bodies) x .callByValuePar (sourceTable M start bodies x k) E (sourceExpr M (.seq a b)) p := by
      change (match evV _ _ _ _ E (plain M bodies S a) p with
        | some (some z) => evV _ _ _ _ E (plain M bodies S b) z | other => other)=
        (match evV _ _ _ _ E (sourceExpr M a) p with
        | some (some z) => evV _ _ _ _ E (sourceExpr M b) z | other => other)
      rw [hA.1]
      cases hv : evV (source M start bodies) x .callByValuePar (sourceTable M start bodies x k) E (sourceExpr M a) p with
      | none => rfl
      | some result => cases result with
        | none => rfl
        | some z =>
          exact (evaluator_of_rows M start bodies safeUsers hSafe x k hRows b ha.2 S E hS hE z
            (evV_ok (source_ok M start bodies x k) _ p hp z hv)).1
    refine ⟨he,?_⟩
    intro q t hq ht
    rw [←he]
    exact ControlFilter.seq_correct (observer M) (valid M) _ x .callByValueSeq (by decide) _
      (target_sound M start bodies x k)
      E (plain M bodies S a) (plain M bodies S b) (plain_firstOrder M bodies S a) (plain_firstOrder M bodies S b)
      _ _ p hp (by intro q t hq ht; rw [hA.1]; exact hA.2 q t hq ht)
      (by
        intro z hz q t hq ht
        have hB := evaluator_of_rows M start bodies safeUsers hSafe x k hRows b ha.2 S E hS hE z hz
        rw [hB.1]
        exact hB.2 q t hq ht) q t hq ht
  | .alt a b, ha, S, E, hS, hE, p, hp => by
    have hA := evaluator_of_rows M start bodies safeUsers hSafe x k hRows a ha.1 S E hS hE p hp
    have hB := evaluator_of_rows M start bodies safeUsers hSafe x k hRows b ha.2 S E hS hE p hp
    have he : evV (target M start bodies) x .callByValueSeq (targetTable M start bodies x k) E (plain M bodies S (.alt a b)) p =
        evV (source M start bodies) x .callByValuePar (sourceTable M start bodies x k) E (sourceExpr M (.alt a b)) p := by
      change (match evV _ _ _ _ E (plain M bodies S a) p with
        | some none => evV _ _ _ _ E (plain M bodies S b) p | other => other)=
        (match evV _ _ _ _ E (sourceExpr M a) p with
        | some none => evV _ _ _ _ E (sourceExpr M b) p | other => other)
      rw [hA.1]
      cases hv : evV (source M start bodies) x .callByValuePar (sourceTable M start bodies x k) E (sourceExpr M a) p with
      | none => rfl
      | some result => cases result with
        | none => exact hB.1
        | some z => rfl
    refine ⟨he,?_⟩
    intro q t hq ht
    change evV _ _ _ _ E (RootObservation.branch (.andP (plain M bodies S a)) _ _) p=_
    rw [ChoiceArguments.branch_eval]
    cases hv : evV (target M start bodies) x .callByValueSeq (targetTable M start bodies x k) E (plain M bodies S a) p with
    | none =>
      have hs := hA.1.symm.trans hv
      rw [show sourceExpr M (.alt a b)=.alt (sourceExpr M a) (sourceExpr M b) from rfl,
        evV_alt_none hs]
      rfl
    | some result => cases result with
      | none =>
        have hs := hA.1.symm.trans hv
        rw [show sourceExpr M (.alt a b)=.alt (sourceExpr M a) (sourceExpr M b) from rfl,
          evV_alt_fail hs]
        exact hB.2 q t hq ht
      | some z =>
        have hs := hA.1.symm.trans hv
        rw [show sourceExpr M (.alt a b)=.alt (sourceExpr M a) (sourceExpr M b) from rfl,
          evV_alt_ok hs]
        simpa only [hs] using hA.2 q t hq ht
  | .star a, ha, S, E, hS, hE, p, hp => by
    have he : evV (target M start bodies) x .callByValueSeq (targetTable M start bodies x k) E (plain M bodies S (.star a)) p =
        evV (source M start bodies) x .callByValuePar (sourceTable M start bodies x k) E (sourceExpr M (.star a)) p :=
      evStar_congr p (fun z hz => (evaluator_of_rows M start bodies safeUsers hSafe x k hRows a ha S E hS hE z (by omega)).1)
    refine ⟨he,?_⟩
    intro q t hq ht
    rw [←he]
    exact GeneralStarFilter.correct (observer M) (valid M) _ x .callByValueSeq (by decide) _
      (target_sound M start bodies x k)
      E _ (plain_firstOrder M bodies S a) _
      (by
        intro q t z hq ht hz
        have hA := evaluator_of_rows M start bodies safeUsers hSafe x k hRows a ha S E hS hE z hz
        rw [hA.1]
        exact hA.2 q t hq ht) q t p hq hp
  | .notP a, ha, S, E, hS, hE, p, hp => by
    have hA := evaluator_of_rows M start bodies safeUsers hSafe x k hRows a ha S E hS hE p hp
    have he : evV (target M start bodies) x .callByValueSeq (targetTable M start bodies x k) E (plain M bodies S (.notP a)) p =
        evV (source M start bodies) x .callByValuePar (sourceTable M start bodies x k) E (sourceExpr M (.notP a)) p := by
      simp only [plain,sourceExpr,evV,hA.1]
    refine ⟨he,?_⟩
    intro q t hq ht
    rw [←he]
    apply DependentCaptureFilter.atom_correct (state := some q)
    intro j hv
    cases hz : evV (target M start bodies) x .callByValueSeq (targetTable M start bodies x k) E (plain M bodies S a) p with
    | none => simp [evV,hz] at hv
    | some result => cases result with
      | some z => simp [evV,hz] at hv
      | none =>
        have hj : p=j := by simpa only [plain,evV,hz,Option.some.injEq] using hv
        subst j
        simp [pre,run]

private theorem source_unfrozen {n : Nat} (M : Machine n) (i : Nat) :
    RecursiveParserStability.pick (helperBodies M) (offset M+i)=false := by
  simp [RecursiveParserStability.pick,helperBodies,offset]

private theorem target_unfrozen {n : Nat} (M : Machine n) (bodies : List Arg)
    (i : Nat) (P : List Nat) (mode : Mode) :
    RecursiveParserStability.pick (helperBodies M) (address M bodies i P mode)=false := by
  simp [RecursiveParserStability.pick,helperBodies,offset,address]

theorem source_zero {n : Nat} (M : Machine n) (start : Fin n) (bodies : List Arg)
    (x : List Char) (i : Nat) (E : List (List Char)) (p : Nat) :
    valAt (sourceTable M start bodies x 0 (offset M+i) E) p=none := by
  simp only [sourceTable,RecursiveParserStability.frozen,ClockFreezing.frozen,source_unfrozen,
    Bool.false_eq_true,if_false,valAt_nil]

theorem target_zero {n : Nat} (M : Machine n) (start : Fin n) (bodies : List Arg)
    (x : List Char) (i : Nat) (P : List Nat) (mode : Mode) (E : List (List Char)) (p : Nat) :
    valAt (targetTable M start bodies x 0 (address M bodies i P mode) E) p=none := by
  simp only [targetTable,RecursiveParserStability.frozen,ClockFreezing.frozen,target_unfrozen,
    Bool.false_eq_true,if_false,valAt_nil]

theorem source_step {n : Nat} (M : Machine n) (start : Fin n) (bodies : List Arg)
    (x : List Char) (k i : Nat) (b : Arg) (hi : bodies[i]?=some b) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    valAt (sourceTable M start bodies x (k+1) (offset M+i) E) p=
      evV (source M start bodies) x .callByValuePar (sourceTable M start bodies x k) E
        (.seq (.call start.val []) (sourceExpr M b)) p :=
  ClockFreezing.frozen_user_step _ _ _ _ _ k _ (source_unfrozen M i) _ (source_rule M start bodies i b hi) E p hp

theorem target_step {n : Nat} (M : Machine n) (start : Fin n) (bodies : List Arg)
    (x : List Char) (k i : Nat) (b : Arg) (hi : bodies[i]?=some b) (P : List Nat)
    (hP : P∈profiles (observer M)) (mode : Mode) (hm : mode∈modes M)
    (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    valAt (targetTable M start bodies x (k+1) (address M bodies i P mode) E) p=
      evV (target M start bodies) x .callByValueSeq (targetTable M start bodies x k) E
        (targetBody M start bodies P mode b) p :=
  ClockFreezing.frozen_user_step _ _ _ _ _ k _ (target_unfrozen M bodies i P mode) _
    (target_rule M start bodies i b hi P hP mode hm) E p hp

/-- Simultaneous recursion closes both actual target row modes. Only
finite syntax checks and the finite certified source prefix remain. -/
theorem tables_rows {n : Nat} (M : Machine n) (start : Fin n) (bodies : List Arg)
    (safeUsers : Nat) (hSafe : sourceSafe M start bodies safeUsers=true)
    (hB : bodies.all (check M bodies safeUsers)=true) (x : List Char) (k : Nat) :
    Rows M start bodies x k := by
  induction k with
  | zero =>
    intro i b hi w p j hp hj hcap hw
    constructor
    · rw [source_zero,target_zero]
    · intro q t hq ht
      rw [target_zero,source_zero]
      rfl
  | succ k ih =>
    intro i b hi w p j hp hj hcap hw
    have hvalid := check_sound M bodies safeUsers b ((List.all_eq_true.mp hB) b (List.mem_of_getElem? hi))
    have hE : TotalCaptureSafety.Environment M [w] := by
      intro v hv
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
      subst v; exact hw
    have hBody := fun z hz => evaluator_of_rows M start bodies safeUsers hSafe x k ih b hvalid
      [profile (observer M) w] [w] (DependentCaptureFilter.environment_accurate (observer M) [w]) hE z hz
    constructor
    · rw [source_step M start bodies x k i b hi [w] p hp,
        target_step M start bodies x k i b hi _ (CaptureTransitionProfile.profile_mem (observer M) (valid M) w)
          none (mode_plain_mem M) [w] j hj]
      exact (RecursiveScannerProductHeader.plain_body M start bodies b w x p j k k hp hj hcap hw
        (fun z hz => (hBody z hz).1)).symm
    · intro q t hq ht
      rw [target_step M start bodies x k i b hi _ (CaptureTransitionProfile.profile_mem (observer M) (valid M) w)
          (some (q,t)) (mode_filter_mem M q t hq ht) [w] j hj,
        source_step M start bodies x k i b hi [w] p hp]
      exact RecursiveScannerProductHeader.product_body M start bodies b w x p j k k hp hj hcap hw ⟨q,hq⟩ t ht
        (fun z hz u hu => (hBody z hz).2 u t hu ht)

theorem evaluator_eq {n : Nat} (M : Machine n) (start : Fin n) (bodies : List Arg)
    (safeUsers : Nat) (hSafe : sourceSafe M start bodies safeUsers=true)
    (hB : bodies.all (check M bodies safeUsers)=true) (x : List Char) (k : Nat)
    (e : Arg) (he : check M bodies safeUsers e=true) (S : List (List Nat)) (E : List (List Char))
    (hS : DependentCaptureFilter.Accurate (observer M) S E) (hE : TotalCaptureSafety.Environment M E)
    (p : Nat) (hp : p≤x.length) :
    evV (target M start bodies) x .callByValueSeq (targetTable M start bodies x k) E (plain M bodies S e) p=
      evV (source M start bodies) x .callByValuePar (sourceTable M start bodies x k) E (sourceExpr M e) p :=
  (evaluator_of_rows M start bodies safeUsers hSafe x k (tables_rows M start bodies safeUsers hSafe hB x k)
    e (check_sound M bodies safeUsers e he) S E hS hE p hp).1

theorem filter_eq {n : Nat} (M : Machine n) (start : Fin n) (bodies : List Arg)
    (safeUsers : Nat) (hSafe : sourceSafe M start bodies safeUsers=true)
    (hB : bodies.all (check M bodies safeUsers)=true) (x : List Char) (k : Nat)
    (e : Arg) (he : check M bodies safeUsers e=true) (S : List (List Nat)) (E : List (List Char))
    (hS : DependentCaptureFilter.Accurate (observer M) S E) (hE : TotalCaptureSafety.Environment M E)
    (p : Nat) (hp : p≤x.length) (q t : Nat) (hq : q<(observer M).width) (ht : t<(observer M).width) :
    evV (target M start bodies) x .callByValueSeq (targetTable M start bodies x k) E (filter M bodies S e q t) p=
      filtered (observer M) x q t p
        (evV (source M start bodies) x .callByValuePar (sourceTable M start bodies x k) E (sourceExpr M e) p) :=
  (evaluator_of_rows M start bodies safeUsers hSafe x k (tables_rows M start bodies safeUsers hSafe hB x k)
    e (check_sound M bodies safeUsers e he) S E hS hE p hp).2 q t hq ht

/-- The fixed generated Seq grammar preserves all finite observations on
the same unchanged original strings. Actual helper stabilization removes
the frozen analysis clock; no recursive row oracle is an input. -/
theorem observations_iff {n : Nat} (M : Machine n) (start : Fin n) (bodies : List Arg)
    (safeUsers : Nat) (hSafe : sourceSafe M start bodies safeUsers=true)
    (hB : bodies.all (check M bodies safeUsers)=true) (e : Arg) (he : check M bodies safeUsers e=true)
    (x : List Char) (rest : Option (List Char)) :
    SObs (source M start bodies) .callByValuePar (sourceExpr M e) x rest ↔
      SObs (target M start bodies) .callByValueSeq (plain M bodies [] e) x rest := by
  have hs := RecursiveParserStability.helpers_stable (RecursiveScannerProductHelpers.lexical M)
    (RecursiveScannerProductHelpers.installed M (sourceRules M start bodies)) x .callByValuePar
  have ht := RecursiveParserStability.helpers_stable (RecursiveScannerProductHelpers.lexical M)
    (RecursiveScannerProductHelpers.installed M (targetRules M start bodies)) x .callByValueSeq
  rw [ClockFreezing.observations_iff (source_firstOrder M start bodies) x .callByValuePar (by decide)
      (RecursiveParserStability.pick (helperBodies M)) (RecursiveParserStability.floor (helperBodies M) x) hs
      (sourceExpr M e) (sourceExpr_firstOrder M e) rest,
    ClockFreezing.observations_iff (target_firstOrder M start bodies) x .callByValueSeq (by decide)
      (RecursiveParserStability.pick (helperBodies M)) (RecursiveParserStability.floor (helperBodies M) x) ht
      (plain M bodies [] e) (plain_firstOrder M bodies [] e) rest]
  have hE : TotalCaptureSafety.Environment M [] := by intro w hw; cases hw
  have hEq := fun k => evaluator_eq M start bodies safeUsers hSafe hB x k e he [] []
    (DependentCaptureFilter.environment_accurate (observer M) []) hE x.length (Nat.le_refl _)
  constructor
  · rintro ⟨k,v,hv,hr⟩
    exact ⟨k,v,(hEq k).trans hv,hr⟩
  · rintro ⟨k,v,hv,hr⟩
    exact ⟨k,v,(hEq k).symm.trans hv,hr⟩

theorem language_translation {n : Nat} (M : Machine n) (start : Fin n) (bodies : List Arg)
    (safeUsers : Nat) (hSafe : sourceSafe M start bodies safeUsers=true)
    (hB : bodies.all (check M bodies safeUsers)=true) (e : Arg) (he : check M bodies safeUsers e=true) :
    ∃ (g : MGrammar) (root : MExp), g.FirstOrder ∧ root.FirstOrder ∧ ∀ x,
      SObs (source M start bodies) .callByValuePar (sourceExpr M e) x (some []) ↔
        SObs g .callByValueSeq root x (some []) :=
  ⟨target M start bodies,plain M bodies [] e,target_firstOrder M start bodies,
    plain_firstOrder M bodies [] e,fun x => observations_iff M start bodies safeUsers hSafe hB e he x (some [])⟩

theorem defined_iff {n : Nat} (M : Machine n) (start : Fin n) (bodies : List Arg)
    (safeUsers : Nat) (hSafe : sourceSafe M start bodies safeUsers=true)
    (hB : bodies.all (check M bodies safeUsers)=true) (e : Arg) (he : check M bodies safeUsers e=true)
    (x : List Char) (v : Option Nat) :
    (∃ k, evV (source M start bodies) x .callByValuePar (tblV (source M start bodies) x .callByValuePar k) [] (sourceExpr M e) x.length=some v) ↔
    (∃ k, evV (target M start bodies) x .callByValueSeq (tblV (target M start bodies) x .callByValueSeq k) [] (plain M bodies [] e) x.length=some v) := by
  have hs := RecursiveParserStability.helpers_stable (RecursiveScannerProductHelpers.lexical M)
    (RecursiveScannerProductHelpers.installed M (sourceRules M start bodies)) x .callByValuePar
  have ht := RecursiveParserStability.helpers_stable (RecursiveScannerProductHelpers.lexical M)
    (RecursiveScannerProductHelpers.installed M (targetRules M start bodies)) x .callByValueSeq
  rw [←ClockFreezing.defined_iff (source M start bodies) x .callByValuePar _ _ hs [] (sourceExpr M e) x.length v,
    ←ClockFreezing.defined_iff (target M start bodies) x .callByValueSeq _ _ ht [] (plain M bodies [] e) x.length v]
  have hE : TotalCaptureSafety.Environment M [] := by intro w hw; cases hw
  have heq := fun k => evaluator_eq M start bodies safeUsers hSafe hB x k e he [] []
    (DependentCaptureFilter.environment_accurate (observer M) []) hE x.length (Nat.le_refl _)
  constructor
  · rintro ⟨k,hk⟩; exact ⟨k,(heq k).trans hk⟩
  · rintro ⟨k,hk⟩; exact ⟨k,(heq k).symm.trans hk⟩

theorem undefined_iff {n : Nat} (M : Machine n) (start : Fin n) (bodies : List Arg)
    (safeUsers : Nat) (hSafe : sourceSafe M start bodies safeUsers=true)
    (hB : bodies.all (check M bodies safeUsers)=true) (e : Arg) (he : check M bodies safeUsers e=true)
    (x : List Char) :
    (∀ k, evV (source M start bodies) x .callByValuePar (tblV (source M start bodies) x .callByValuePar k) [] (sourceExpr M e) x.length=none) ↔
    (∀ k, evV (target M start bodies) x .callByValueSeq (tblV (target M start bodies) x .callByValueSeq k) [] (plain M bodies [] e) x.length=none) := by
  have hdef := defined_iff M start bodies safeUsers hSafe hB e he x
  constructor
  · intro hs k
    cases hv : evV (target M start bodies) x .callByValueSeq (tblV (target M start bodies) x .callByValueSeq k) [] (plain M bodies [] e) x.length with
    | none => rfl
    | some v =>
      obtain ⟨j,hj⟩ := (hdef v).mpr ⟨k,hv⟩
      rw [hs j] at hj; cases hj
  · intro ht k
    cases hv : evV (source M start bodies) x .callByValuePar (tblV (source M start bodies) x .callByValuePar k) [] (sourceExpr M e) x.length with
    | none => rfl
    | some v =>
      obtain ⟨j,hj⟩ := (hdef v).mp ⟨k,hv⟩
      rw [ht j] at hj; cases hj

end Shallot.MacroPeg.CBV.RecursiveScannerProductCorrespondence
