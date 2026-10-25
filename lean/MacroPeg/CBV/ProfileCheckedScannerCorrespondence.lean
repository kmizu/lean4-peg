import MacroPeg.CBV.RecursiveCaptureProfiles
import MacroPeg.CBV.IndependentCaptureControl
import MacroPeg.CBV.ControlFilter

namespace Shallot.MacroPeg.CBV.ProfileCheckedScannerCorrespondence
open RecursiveScannerProductCompiler
open StatefulScanner (Machine)
open DynamicScannerCapture (observer)
open CaptureTransitionProfile (profile profiles profile_mem)
open RegularCaptureProduct (filtered run)
open RecursiveScannerProductCorrespondence (source_sound target_sound source_ok target_ok selected_call
  source_zero target_zero source_step target_step)

open RecursiveCaptureProfiles (Summary ScannerSummary effects scopeCheck scope_sound)

abbrev Inputs := Nat → List (List Nat)

def inputCheck {n : Nat} (entries : Entries n) (A : Inputs) (i : Nat) (P : List Nat) : Bool :=
  (A i).contains P && RecursiveScannerProductHeader.entryCheck (entries i) P

def check {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg)
    (C : Summary) (A : Inputs) (S : List (List Nat)) : Arg → Bool
  | .user i a => decide (i<bodies.length) &&
      ((effects M C S a).all (inputCheck entries A i) && check M entries bodies C A S a)
  | .seq a b | .alt a b => check M entries bodies C A S a && check M entries bodies C A S b
  | .notP a | .star a => check M entries bodies C A S a
  | _ => true

def Valid {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg)
    (C : Summary) (A : Inputs) (S : List (List Nat)) : Arg → Prop
  | .user i a => i<bodies.length ∧
      (effects M C S a).all (inputCheck entries A i)=true ∧ Valid M entries bodies C A S a
  | .seq a b | .alt a b => Valid M entries bodies C A S a ∧ Valid M entries bodies C A S b
  | .notP a | .star a => Valid M entries bodies C A S a
  | _ => True

theorem check_sound {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg)
    (C : Summary) (A : Inputs) (S : List (List Nat)) : ∀ e, check M entries bodies C A S e=true → Valid M entries bodies C A S e
  | .user i a,h => ⟨of_decide_eq_true (Bool.and_eq_true_iff.mp h).1,
      (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).2).1,
      check_sound M entries bodies C A S a (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).2).2⟩
  | .seq a b,h | .alt a b,h => ⟨check_sound M entries bodies C A S a (Bool.and_eq_true_iff.mp h).1,
      check_sound M entries bodies C A S b (Bool.and_eq_true_iff.mp h).2⟩
  | .notP a,h | .star a,h => check_sound M entries bodies C A S a h
  | .lit _,_ | .param _,_ => True.intro

theorem valid_scoped {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg)
    (C : Summary) (A : Inputs) (S : List (List Nat)) : ∀ e, Valid M entries bodies C A S e → RecursiveCaptureProfiles.Scoped bodies e
  | .user i a,h => ⟨h.1,valid_scoped M entries bodies C A S a h.2.2⟩
  | .seq a b,h | .alt a b,h => ⟨valid_scoped M entries bodies C A S a h.1,valid_scoped M entries bodies C A S b h.2⟩
  | .notP a,h | .star a,h => valid_scoped M entries bodies C A S a h
  | .lit _,_ | .param _,_ => True.intro

def bodiesCheck {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg) (C : Summary) (A : Inputs) : Bool :=
  entriesCheck M entries bodies && bodies.zipIdx.all (fun (b,i) => (profiles (observer M)).all (fun P =>
    !inputCheck entries A i P || check M entries bodies C A [P] b))

theorem body_checked {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg)
    (C : Summary) (A : Inputs) (h : bodiesCheck M entries bodies C A=true) (i : Nat) (b : Arg)
    (hi : bodies[i]?=some b) (P : List Nat) (hP : P∈profiles (observer M))
    (hp : inputCheck entries A i P=true) : check M entries bodies C A [P] b=true := by
  have hm : (b,i)∈bodies.zipIdx := List.mem_of_getElem? (show bodies.zipIdx[i]?=some (b,i) from by
    simp [List.getElem?_zipIdx,hi])
  have hh := (List.all_eq_true.mp ((List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).2) (b,i) hm)) P hP
  simpa [hp] using hh

def Rows {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg) (A : Inputs) (x : List Char) (k : Nat) : Prop :=
  ∀ i b, bodies[i]?=some b → ∀ w p j, p≤x.length → j≤x.length → sfx x p=w++sfx x j →
    (inputCheck entries A i (profile (observer M) w)=true) →
    (valAt (sourceTable M entries bodies x k (offset M+i) [w]) p=
      valAt (targetTable M entries bodies x k (address M bodies i (profile (observer M) w) none) [w]) j) ∧
    (∀ q t, q<(observer M).width → t<(observer M).width →
      valAt (targetTable M entries bodies x k (address M bodies i (profile (observer M) w) (some (q,t))) [w]) j=
        filtered (observer M) x q t p (valAt (sourceTable M entries bodies x k (offset M+i) [w]) p))

theorem user_correct {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg)
    (H : ScannerSummary n) (C : Summary) (A : Inputs)
    (hH : RecursiveCaptureProfiles.scannerCheck M H=true)
    (hC : RecursiveCaptureProfiles.grammarCheck M entries bodies H C=true)
    (x : List Char) (k : Nat) (hRows : Rows M entries bodies A x k) (i : Nat) (b : Arg) (hi : bodies[i]?=some b)
    (a : Arg) (S : List (List Nat)) (E : List (List Char))
    (hS : DependentCaptureFilter.Accurate (observer M) S E)
    (hScoped : RecursiveCaptureProfiles.Scoped bodies a)
    (ha : (effects M C S a).all (inputCheck entries A i)=true) (p : Nat) (hp : p≤x.length)
    (hplain : evV (target M entries bodies) x .callByValueSeq (targetTable M entries bodies x k) E (plain M bodies S a) p=
      evV (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) E (sourceExpr M a) p)
    (hfilter : ∀ q r, q<(observer M).width → r<(observer M).width →
      evV (target M entries bodies) x .callByValueSeq (targetTable M entries bodies x k) E (filter M bodies S a q r) p=
        filtered (observer M) x q r p (evV (target M entries bodies) x .callByValueSeq (targetTable M entries bodies x k) E (plain M bodies S a) p)) :
    (evV (target M entries bodies) x .callByValueSeq (targetTable M entries bodies x k) E (plain M bodies S (.user i a)) p=
      evV (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) E (sourceExpr M (.user i a)) p) ∧
    (∀ q r, q<(observer M).width → r<(observer M).width →
      evV (target M entries bodies) x .callByValueSeq (targetTable M entries bodies x k) E (filter M bodies S (.user i a) q r) p=
        filtered (observer M) x q r p (evV (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) E (sourceExpr M (.user i a)) p)) := by
  have harg := DependentCaptureFilter.success_prefix (g := source M entries bodies) (x := x)
    (by decide) (source_sound M entries bodies x k) E (sourceExpr M a) (sourceExpr_firstOrder M a) p
  constructor
  · simp only [plain,sourceExpr]
    rw [selected_call M entries bodies x k i b hi a S E p none (mode_plain_mem M) hplain hfilter,
      evV_call_par (source_rule M entries bodies i b hi) rfl (by decide)]
    simp only [evParArgs]
    cases hv : evV (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) E (sourceExpr M a) p with
    | none => rfl
    | some result => cases result with
      | none => rfl
      | some j =>
        obtain ⟨hj,hcap⟩ := harg j hp hv
        have hShape := RecursiveCaptureProfiles.output_shape M entries bodies C x _
          (RecursiveCaptureProfiles.frozen_rows M entries bodies H C hH hC x k) S E hS a hScoped p j hp hv
        obtain ⟨hjp,w,hwprofile,hs⟩ := hShape
        have hpre : pre x p j=w := by
          simpa only [length_sfx x hp,length_sfx x (Nat.le_trans hjp hp)] using pre_eq (sfx_is_suffix x p) hs
        have hw : inputCheck entries A i (profile (observer M) (pre x p j))=true :=
          (List.all_eq_true.mp ha) _ (hpre.symm ▸ hwprofile)
        exact (hRows i b hi _ p j hp hj hcap hw).1.symm
  · intro q r hq hr
    simp only [filter,sourceExpr]
    rw [selected_call M entries bodies x k i b hi a S E p (some (q,r)) (mode_filter_mem M q r hq hr) hplain hfilter,
      evV_call_par (source_rule M entries bodies i b hi) rfl (by decide)]
    simp only [evParArgs]
    cases hv : evV (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) E (sourceExpr M a) p with
    | none => rfl
    | some result => cases result with
      | none => rfl
      | some j =>
        obtain ⟨hj,hcap⟩ := harg j hp hv
        have hShape := RecursiveCaptureProfiles.output_shape M entries bodies C x _
          (RecursiveCaptureProfiles.frozen_rows M entries bodies H C hH hC x k) S E hS a hScoped p j hp hv
        obtain ⟨hjp,w,hwprofile,hs⟩ := hShape
        have hpre : pre x p j=w := by
          simpa only [length_sfx x hp,length_sfx x (Nat.le_trans hjp hp)] using pre_eq (sfx_is_suffix x p) hs
        have hw : inputCheck entries A i (profile (observer M) (pre x p j))=true :=
          (List.all_eq_true.mp ha) _ (hpre.symm ▸ hwprofile)
        exact (hRows i b hi _ p j hp hj hcap hw).2 q r hq hr

/-- The source argument syntax and recursive user rows are separate
inductions. Captures are certified from the actual source component. -/
theorem evaluator_of_rows {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg)
    (H : ScannerSummary n) (C : Summary) (A : Inputs)
    (hH : RecursiveCaptureProfiles.scannerCheck M H=true)
    (hC : RecursiveCaptureProfiles.grammarCheck M entries bodies H C=true)
    (x : List Char) (k : Nat) (hRows : Rows M entries bodies A x k)
    (S : List (List Nat)) (E : List (List Char))
    (hS : DependentCaptureFilter.Accurate (observer M) S E) :
    ∀ e, Valid M entries bodies C A S e → ∀ p, p≤x.length →
    (evV (target M entries bodies) x .callByValueSeq (targetTable M entries bodies x k) E (plain M bodies S e) p=
      evV (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) E (sourceExpr M e) p) ∧
    (∀ q r, q<(observer M).width → r<(observer M).width →
      evV (target M entries bodies) x .callByValueSeq (targetTable M entries bodies x k) E (filter M bodies S e q r) p=
        filtered (observer M) x q r p
          (evV (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) E (sourceExpr M e) p))
  | .lit w, _, p, hp => by
    refine ⟨rfl,?_⟩
    intro q r hq hr
    exact IndependentCaptureControl.filter_correct (observer M) (valid M) _ _ x _ _
      (source_ok M entries bodies x k) (target_ok M entries bodies x k) S E hS (.lit w) True.intro p hp q r hq hr
  | .param i, _, p, hp => by
    refine ⟨rfl,?_⟩
    intro q r hq hr
    exact IndependentCaptureControl.filter_correct (observer M) (valid M) _ _ x _ _
      (source_ok M entries bodies x k) (target_ok M entries bodies x k) S E hS (.param i) True.intro p hp q r hq hr
  | .user i a, ha, p, hp => by
    have hib : i<bodies.length := ha.1
    have hr : bodies[i]?=some bodies[i] := List.getElem?_eq_getElem hib
    have ih := evaluator_of_rows M entries bodies H C A hH hC x k hRows S E hS a ha.2.2 p hp
    apply user_correct M entries bodies H C A hH hC x k hRows i bodies[i] hr a S E hS (valid_scoped M entries bodies C A S a ha.2.2) ha.2.1 p hp ih.1
    intro q t hq ht
    rw [ih.1]
    exact ih.2 q t hq ht
  | .seq a b, ha, p, hp => by
    have hA := evaluator_of_rows M entries bodies H C A hH hC x k hRows S E hS a ha.1 p hp
    have he : evV (target M entries bodies) x .callByValueSeq (targetTable M entries bodies x k) E (plain M bodies S (.seq a b)) p =
        evV (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) E (sourceExpr M (.seq a b)) p := by
      change (match evV _ _ _ _ E (plain M bodies S a) p with
        | some (some z) => evV _ _ _ _ E (plain M bodies S b) z | other => other)=
        (match evV _ _ _ _ E (sourceExpr M a) p with
        | some (some z) => evV _ _ _ _ E (sourceExpr M b) z | other => other)
      rw [hA.1]
      cases hv : evV (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) E (sourceExpr M a) p with
      | none => rfl
      | some result => cases result with
        | none => rfl
        | some z =>
          exact (evaluator_of_rows M entries bodies H C A hH hC x k hRows S E hS b ha.2 z
            (evV_ok (source_ok M entries bodies x k) _ p hp z hv)).1
    refine ⟨he,?_⟩
    intro q t hq ht
    rw [←he]
    exact ControlFilter.seq_correct (observer M) (valid M) _ x .callByValueSeq (by decide) _
      (target_sound M entries bodies x k)
      E (plain M bodies S a) (plain M bodies S b) (plain_firstOrder M bodies S a) (plain_firstOrder M bodies S b)
      _ _ p hp (by intro q t hq ht; rw [hA.1]; exact hA.2 q t hq ht)
      (by
        intro z hz q t hq ht
        have hB := evaluator_of_rows M entries bodies H C A hH hC x k hRows S E hS b ha.2 z hz
        rw [hB.1]
        exact hB.2 q t hq ht) q t hq ht
  | .alt a b, ha, p, hp => by
    have hA := evaluator_of_rows M entries bodies H C A hH hC x k hRows S E hS a ha.1 p hp
    have hB := evaluator_of_rows M entries bodies H C A hH hC x k hRows S E hS b ha.2 p hp
    have he : evV (target M entries bodies) x .callByValueSeq (targetTable M entries bodies x k) E (plain M bodies S (.alt a b)) p =
        evV (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) E (sourceExpr M (.alt a b)) p := by
      change (match evV _ _ _ _ E (plain M bodies S a) p with
        | some none => evV _ _ _ _ E (plain M bodies S b) p | other => other)=
        (match evV _ _ _ _ E (sourceExpr M a) p with
        | some none => evV _ _ _ _ E (sourceExpr M b) p | other => other)
      rw [hA.1]
      cases hv : evV (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) E (sourceExpr M a) p with
      | none => rfl
      | some result => cases result with
        | none => exact hB.1
        | some z => rfl
    refine ⟨he,?_⟩
    intro q t hq ht
    change evV _ _ _ _ E (RootObservation.branch (.andP (plain M bodies S a)) _ _) p=_
    rw [ChoiceArguments.branch_eval]
    cases hv : evV (target M entries bodies) x .callByValueSeq (targetTable M entries bodies x k) E (plain M bodies S a) p with
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
  | .star a, ha, p, hp => by
    have he : evV (target M entries bodies) x .callByValueSeq (targetTable M entries bodies x k) E (plain M bodies S (.star a)) p =
        evV (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) E (sourceExpr M (.star a)) p :=
      evStar_congr p (fun z hz => (evaluator_of_rows M entries bodies H C A hH hC x k hRows S E hS a ha z (by omega)).1)
    refine ⟨he,?_⟩
    intro q t hq ht
    rw [←he]
    exact GeneralStarFilter.correct (observer M) (valid M) _ x .callByValueSeq (by decide) _
      (target_sound M entries bodies x k)
      E _ (plain_firstOrder M bodies S a) _
      (by
        intro q t z hq ht hz
        have hA := evaluator_of_rows M entries bodies H C A hH hC x k hRows S E hS a ha z hz
        rw [hA.1]
        exact hA.2 q t hq ht) q t p hq hp
  | .notP a, ha, p, hp => by
    have hA := evaluator_of_rows M entries bodies H C A hH hC x k hRows S E hS a ha p hp
    have he : evV (target M entries bodies) x .callByValueSeq (targetTable M entries bodies x k) E (plain M bodies S (.notP a)) p =
        evV (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) E (sourceExpr M (.notP a)) p := by
      simp only [plain,sourceExpr,evV,hA.1]
    refine ⟨he,?_⟩
    intro q t hq ht
    rw [←he]
    apply DependentCaptureFilter.atom_correct (state := some q)
    intro j hv
    cases hz : evV (target M entries bodies) x .callByValueSeq (targetTable M entries bodies x k) E (plain M bodies S a) p with
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

/-- Simultaneous recursion closes both actual target row modes. Only
finite syntax checks and the finite certified source prefix remain. -/
theorem tables_rows {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg)
    (H : ScannerSummary n) (C : Summary) (A : Inputs)
    (hH : RecursiveCaptureProfiles.scannerCheck M H=true)
    (hC : RecursiveCaptureProfiles.grammarCheck M entries bodies H C=true)
    (hB : bodiesCheck M entries bodies C A=true) (x : List Char) (k : Nat) :
    Rows M entries bodies A x k := by
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
    have hP := profile_mem (observer M) (valid M) w
    have hvalid := check_sound M entries bodies C A [profile (observer M) w] b
      (body_checked M entries bodies C A hB i b hi _ hP hw)
    have hBody := fun z hz => evaluator_of_rows M entries bodies H C A hH hC x k ih
      [profile (observer M) w] [w] (DependentCaptureFilter.environment_accurate (observer M) [w]) b hvalid z hz
    constructor
    · rw [source_step M entries bodies x k i b hi [w] p hp,
        target_step M entries bodies x k i b hi _ (CaptureTransitionProfile.profile_mem (observer M) (valid M) w)
          none (mode_plain_mem M) [w] j hj]
      exact (RecursiveScannerProductHeader.entry_plain_body M entries bodies (entries i)
        (entry_checked M entries bodies (Bool.and_eq_true_iff.mp hB).1 i b hi) b w x p j k k hp hj hcap
        (Bool.and_eq_true_iff.mp hw).2
        (fun z hz => (hBody z hz).1)).symm
    · intro q t hq ht
      rw [target_step M entries bodies x k i b hi _ (CaptureTransitionProfile.profile_mem (observer M) (valid M) w)
          (some (q,t)) (mode_filter_mem M q t hq ht) [w] j hj,
        source_step M entries bodies x k i b hi [w] p hp]
      exact RecursiveScannerProductHeader.entry_product_body M entries bodies (entries i)
        (entry_checked M entries bodies (Bool.and_eq_true_iff.mp hB).1 i b hi) b w x p j k k hp hj hcap
        (Bool.and_eq_true_iff.mp hw).2 ⟨q,hq⟩ t ht
        (fun z hz u hu => (hBody z hz).2 u t hu ht)

theorem evaluator_eq {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg)
    (H : ScannerSummary n) (C : Summary) (A : Inputs)
    (hH : RecursiveCaptureProfiles.scannerCheck M H=true)
    (hC : RecursiveCaptureProfiles.grammarCheck M entries bodies H C=true)
    (hB : bodiesCheck M entries bodies C A=true) (x : List Char) (k : Nat)
    (e : Arg) (S : List (List Nat)) (E : List (List Char))
    (he : check M entries bodies C A S e=true)
    (hS : DependentCaptureFilter.Accurate (observer M) S E)
    (p : Nat) (hp : p≤x.length) :
    evV (target M entries bodies) x .callByValueSeq (targetTable M entries bodies x k) E (plain M bodies S e) p=
      evV (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) E (sourceExpr M e) p :=
  (evaluator_of_rows M entries bodies H C A hH hC x k (tables_rows M entries bodies H C A hH hC hB x k)
    S E hS e (check_sound M entries bodies C A S e he) p hp).1

theorem filter_eq {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg)
    (H : ScannerSummary n) (C : Summary) (A : Inputs)
    (hH : RecursiveCaptureProfiles.scannerCheck M H=true)
    (hC : RecursiveCaptureProfiles.grammarCheck M entries bodies H C=true)
    (hB : bodiesCheck M entries bodies C A=true) (x : List Char) (k : Nat)
    (e : Arg) (S : List (List Nat)) (E : List (List Char))
    (he : check M entries bodies C A S e=true)
    (hS : DependentCaptureFilter.Accurate (observer M) S E)
    (p : Nat) (hp : p≤x.length) (q t : Nat) (hq : q<(observer M).width) (ht : t<(observer M).width) :
    evV (target M entries bodies) x .callByValueSeq (targetTable M entries bodies x k) E (filter M bodies S e q t) p=
      filtered (observer M) x q t p
        (evV (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) E (sourceExpr M e) p) :=
  (evaluator_of_rows M entries bodies H C A hH hC x k (tables_rows M entries bodies H C A hH hC hB x k)
    S E hS e (check_sound M entries bodies C A S e he) p hp).2 q t hq ht

/-- The fixed generated Seq grammar preserves all finite observations on
the same unchanged original strings. Actual helper stabilization removes
the frozen analysis clock; no recursive row oracle is an input. -/
theorem observations_iff {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg)
    (H : ScannerSummary n) (C : Summary) (A : Inputs)
    (hH : RecursiveCaptureProfiles.scannerCheck M H=true)
    (hC : RecursiveCaptureProfiles.grammarCheck M entries bodies H C=true)
    (hB : bodiesCheck M entries bodies C A=true) (e : Arg) (he : check M entries bodies C A [] e=true)
    (x : List Char) (rest : Option (List Char)) :
    SObs (source M entries bodies) .callByValuePar (sourceExpr M e) x rest ↔
      SObs (target M entries bodies) .callByValueSeq (plain M bodies [] e) x rest := by
  have hs := RecursiveParserStability.helpers_stable (RecursiveScannerProductHelpers.lexical M)
    (RecursiveScannerProductHelpers.installed M (sourceRules M entries bodies)) x .callByValuePar
  have ht := RecursiveParserStability.helpers_stable (RecursiveScannerProductHelpers.lexical M)
    (RecursiveScannerProductHelpers.installed M (targetRules M entries bodies)) x .callByValueSeq
  rw [ClockFreezing.observations_iff (source_firstOrder M entries bodies) x .callByValuePar (by decide)
      (RecursiveParserStability.pick (helperBodies M)) (RecursiveParserStability.floor (helperBodies M) x) hs
      (sourceExpr M e) (sourceExpr_firstOrder M e) rest,
    ClockFreezing.observations_iff (target_firstOrder M entries bodies) x .callByValueSeq (by decide)
      (RecursiveParserStability.pick (helperBodies M)) (RecursiveParserStability.floor (helperBodies M) x) ht
      (plain M bodies [] e) (plain_firstOrder M bodies [] e) rest]
  have hEq := fun k => evaluator_eq M entries bodies H C A hH hC hB x k e [] [] he
    (DependentCaptureFilter.environment_accurate (observer M) []) x.length (Nat.le_refl _)
  constructor
  · rintro ⟨k,v,hv,hr⟩
    exact ⟨k,v,(hEq k).trans hv,hr⟩
  · rintro ⟨k,v,hv,hr⟩
    exact ⟨k,v,(hEq k).symm.trans hv,hr⟩

theorem language_translation {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg)
    (H : ScannerSummary n) (C : Summary) (A : Inputs)
    (hH : RecursiveCaptureProfiles.scannerCheck M H=true)
    (hC : RecursiveCaptureProfiles.grammarCheck M entries bodies H C=true)
    (hB : bodiesCheck M entries bodies C A=true) (e : Arg) (he : check M entries bodies C A [] e=true) :
    ∃ (g : MGrammar) (root : MExp), g.FirstOrder ∧ root.FirstOrder ∧ ∀ x,
      SObs (source M entries bodies) .callByValuePar (sourceExpr M e) x (some []) ↔
        SObs g .callByValueSeq root x (some []) :=
  ⟨target M entries bodies,plain M bodies [] e,target_firstOrder M entries bodies,
    plain_firstOrder M bodies [] e,fun x => observations_iff M entries bodies H C A hH hC hB e he x (some [])⟩

theorem defined_iff {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg)
    (H : ScannerSummary n) (C : Summary) (A : Inputs)
    (hH : RecursiveCaptureProfiles.scannerCheck M H=true)
    (hC : RecursiveCaptureProfiles.grammarCheck M entries bodies H C=true)
    (hB : bodiesCheck M entries bodies C A=true) (e : Arg) (he : check M entries bodies C A [] e=true)
    (x : List Char) (v : Option Nat) :
    (∃ k, evV (source M entries bodies) x .callByValuePar (tblV (source M entries bodies) x .callByValuePar k) [] (sourceExpr M e) x.length=some v) ↔
    (∃ k, evV (target M entries bodies) x .callByValueSeq (tblV (target M entries bodies) x .callByValueSeq k) [] (plain M bodies [] e) x.length=some v) := by
  have hs := RecursiveParserStability.helpers_stable (RecursiveScannerProductHelpers.lexical M)
    (RecursiveScannerProductHelpers.installed M (sourceRules M entries bodies)) x .callByValuePar
  have ht := RecursiveParserStability.helpers_stable (RecursiveScannerProductHelpers.lexical M)
    (RecursiveScannerProductHelpers.installed M (targetRules M entries bodies)) x .callByValueSeq
  rw [←ClockFreezing.defined_iff (source M entries bodies) x .callByValuePar _ _ hs [] (sourceExpr M e) x.length v,
    ←ClockFreezing.defined_iff (target M entries bodies) x .callByValueSeq _ _ ht [] (plain M bodies [] e) x.length v]
  have heq := fun k => evaluator_eq M entries bodies H C A hH hC hB x k e [] [] he
    (DependentCaptureFilter.environment_accurate (observer M) []) x.length (Nat.le_refl _)
  constructor
  · rintro ⟨k,hk⟩; exact ⟨k,(heq k).trans hk⟩
  · rintro ⟨k,hk⟩; exact ⟨k,(heq k).symm.trans hk⟩

theorem undefined_iff {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg)
    (H : ScannerSummary n) (C : Summary) (A : Inputs)
    (hH : RecursiveCaptureProfiles.scannerCheck M H=true)
    (hC : RecursiveCaptureProfiles.grammarCheck M entries bodies H C=true)
    (hB : bodiesCheck M entries bodies C A=true) (e : Arg) (he : check M entries bodies C A [] e=true)
    (x : List Char) :
    (∀ k, evV (source M entries bodies) x .callByValuePar (tblV (source M entries bodies) x .callByValuePar k) [] (sourceExpr M e) x.length=none) ↔
    (∀ k, evV (target M entries bodies) x .callByValueSeq (tblV (target M entries bodies) x .callByValueSeq k) [] (plain M bodies [] e) x.length=none) := by
  have hdef := defined_iff M entries bodies H C A hH hC hB e he x
  constructor
  · intro hs k
    cases hv : evV (target M entries bodies) x .callByValueSeq (tblV (target M entries bodies) x .callByValueSeq k) [] (plain M bodies [] e) x.length with
    | none => rfl
    | some v =>
      obtain ⟨j,hj⟩ := (hdef v).mpr ⟨k,hv⟩
      rw [hs j] at hj; cases hj
  · intro ht k
    cases hv : evV (source M entries bodies) x .callByValuePar (tblV (source M entries bodies) x .callByValuePar k) [] (sourceExpr M e) x.length with
    | none => rfl
    | some v =>
      obtain ⟨j,hj⟩ := (hdef v).mp ⟨k,hv⟩
      rw [ht j] at hj; cases hj

end Shallot.MacroPeg.CBV.ProfileCheckedScannerCorrespondence
