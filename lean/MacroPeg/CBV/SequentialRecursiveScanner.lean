import MacroPeg.CBV.SequentialRecursiveObserver
import MacroPeg.CBV.ParameterizedCaptureSafety
import MacroPeg.CBV.DynamicScannerBinding

namespace Shallot.MacroPeg.CBV.SequentialRecursiveScanner
open SequentialRecursiveObserver (render filter source)
abbrev Arg := SequentialRecursiveObserver.Expr
open CaptureTransitionProfile (profile)
open DynamicScannerCapture (observer)
open ObservedScannerDispatch (dispatch)
open StatefulScanner (Machine)

abbrev D {n : Nat} (M : Machine n) := observer M
abbrev valid {n : Nat} (M : Machine n) := DynamicScannerCapture.observer_valid M

def before {n : Nat} (M : Machine n) (bodies : List Arg) : List MRule :=
  (SequentialRecursiveObserver.grammar (D M) bodies).rules

def grammar {n : Nat} (M : Machine n) (bodies : List Arg) (extra : List MRule) : MGrammar :=
  ObservedScannerDispatch.grammar M (D M) (valid M) (before M bodies) extra

theorem installed {n : Nat} (M : Machine n) (bodies : List Arg) (extra : List MRule) :
    SequentialRecursiveObserver.Installed (D M) bodies (grammar M bodies extra) := by
  constructor
  · intro i b hi
    exact SequentialRecursiveObserver.rule_append _ extra i _
      (SequentialRecursiveObserver.rule_append _ _ i _ (SequentialRecursiveObserver.original_rule (D M) bodies i b hi))
  · intro i b hi P hP q r hq hr
    exact SequentialRecursiveObserver.rule_append _ extra _ _
      (SequentialRecursiveObserver.rule_append _ _ _ _ (SequentialRecursiveObserver.product_rule (D M) bodies i b hi P hP q r hq hr))

theorem firstOrder {n : Nat} (M : Machine n) (bodies : List Arg) (extra : List MRule)
    (hExtra : ∀ r∈extra, r.body.FirstOrder) : (grammar M bodies extra).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · rcases List.mem_append.mp hr with hr | hr
    · exact SequentialRecursiveObserver.firstOrder (D M) bodies r hr
    · exact ObservedScannerDispatch.firstOrder M (D M) (valid M) (before M bodies).length r hr
  · exact hExtra r hr

/-- Finite profile indexing also covers the observer's absorbing sink. -/
def state {n : Nat} (M : Machine n) (P : List Nat) (a : Fin (D M).width) : Fin (D M).width :=
  ⟨(P[a.val]?.getD 0) % (D M).width,Nat.mod_lt _ (valid M).1⟩

theorem state_actual {n : Nat} (M : Machine n) (w : List Char) (a : Fin (D M).width) :
    state M (profile (D M) w) a=ObservedScanner.finish (D M) (valid M) a w := by
  apply Fin.ext
  simp only [state,CaptureTransitionProfile.profile_get (D M) w a.val a.isLt,Option.getD_some,
    Nat.mod_eq_of_lt (RegularCaptureProduct.run_bound (valid M) a.val a.isLt w),ObservedScanner.finish]

def residual {n : Nat} (M : Machine n) (bodies : List Arg) (q : Fin n) (a : Fin (D M).width)
    (K : Fin (n*(D M).width) → MExp) (P : List Nat) : MExp :=
  match DynamicScannerBinding.resume P q with
  | none => MExp.failAlways
  | some r => dispatch (before M bodies).length r (state M P a) K

def origin {n : Nat} (M : Machine n) (bodies : List Arg) (e : Arg) (q : Fin n) (a : Fin (D M).width)
    (K : Fin (n*(D M).width) → MExp) : MExp :=
  .seq (.andP (render e)) (dispatch (before M bodies).length q a K)

def fused {n : Nat} (M : Machine n) (bodies : List Arg) (S : List (List Nat)) (e : Arg)
    (q : Fin n) (a : Fin (D M).width) (K : Fin (n*(D M).width) → MExp) : MExp :=
  ProfileControl.select (D M) (render e) (fun q r => filter (D M) bodies S e q r)
    (fun P => .seq (render e) (residual M bodies q a K P))

theorem residual_firstOrder {n : Nat} (M : Machine n) (bodies : List Arg) (q : Fin n) (a : Fin (D M).width)
    (K : Fin (n*(D M).width) → MExp) (hK : ∀ t, (K t).FirstOrder) (P : List Nat) :
    (residual M bodies q a K P).FirstOrder := by
  unfold residual
  cases DynamicScannerBinding.resume P q with
  | none => trivial
  | some r => exact ObservedScannerDispatch.dispatch_firstOrder _ r _ K hK

theorem fused_firstOrder {n : Nat} (M : Machine n) (bodies : List Arg) (S : List (List Nat)) (e : Arg)
    (q : Fin n) (a : Fin (D M).width) (K : Fin (n*(D M).width) → MExp)
    (hK : ∀ t, (K t).FirstOrder) : (fused M bodies S e q a K).FirstOrder :=
  ProfileControl.select_firstOrder _ _ _ (SequentialRecursiveObserver.render_firstOrder e)
    (fun q r => SequentialRecursiveObserver.filter_firstOrder (D M) bodies S e q r) _
    (fun P _ => ⟨SequentialRecursiveObserver.render_firstOrder e,residual_firstOrder M bodies q a K hK P⟩)

/-- A fresh capture may contain positive mutually recursive Seq calls.
Its generated whole-call observer, actual safety and real residual scanner
compose on every input. Failure, undefinedness and later continuation results
are preserved; no successful-capture or recursive-row oracle is supplied. -/
theorem fusion_correct {n : Nat} (M : Machine n) (bodies : List Arg) (extra : List MRule)
    (hExtra : ∀ r∈extra, r.body.FirstOrder)
    (hB : bodies.all (SequentialRecursiveObserver.check bodies.length)=true)
    (hSafe : ParameterizedCaptureSafety.grammarCheck M (source bodies)=true)
    (e : Arg) (he : SequentialRecursiveObserver.check bodies.length e=true)
    (hSafeE : ParameterizedCaptureSafety.check M (source bodies).rules.length (render e)=true)
    (x : List Char) (clock : Nat) (E : List (List Char)) (hE : TotalCaptureSafety.Environment M E)
    (p : Nat) (hp : p≤x.length) (hclock : p+1≤clock) (q : Fin n) (a : Fin (D M).width)
    (K : Fin (n*(D M).width) → MExp) :
    evV (grammar M bodies extra) x .callByValueSeq (tblV (grammar M bodies extra) x .callByValueSeq clock) E
      (fused M bodies (E.map (profile (D M))) e q a K) p=
    evV (grammar M bodies extra) x .callByValueSeq (tblV (grammar M bodies extra) x .callByValueSeq clock) E
      (origin M bodies e q a K) p := by
  let g := grammar M bodies extra
  have hg := installed M bodies extra
  have hFO := firstOrder M bodies extra hExtra
  have ho := SequentialRecursiveObserver.ambient_original_eval (D M) bodies g hg hB x clock e he E p hp
  change evV g x .callByValueSeq (tblV g x .callByValueSeq clock) E
      (fused M bodies (E.map (profile (D M))) e q a K) p=
    evV g x .callByValueSeq (tblV g x .callByValueSeq clock) E (origin M bodies e q a K) p
  rw [fused,SequentialRecursiveObserver.ambient_select_result (D M) (valid M) bodies g hg hFO hB x clock e he E p hp]
  cases hv : evV g x .callByValueSeq (tblV g x .callByValueSeq clock) E (render e) p with
  | none => simp only [origin,MExp.andP,evV,hv]
  | some result => cases result with
    | none => simp only [origin,MExp.andP,evV,hv]
    | some j =>
      dsimp only []
      have hvSource := ho.trans hv
      have hj := DependentCaptureFilter.success_prefix (by decide)
        (tblV_sound hFO (by decide) clock) E (render e) (SequentialRecursiveObserver.render_firstOrder e) p j hp hv
      obtain ⟨hw,hs⟩ := ParameterizedCaptureSafety.capture M (source bodies)
        (ParameterizedCaptureSafety.grammarCheck_sound M _ hSafe) x .callByValueSeq clock E hE
        (render e) hSafeE p j hp hvSource
      cases ht : StatefulScanner.advance M q (pre x p j) with
      | none => exact False.elim (hw q ht)
      | some r =>
        have hh := ObservedScannerDispatch.dispatch_handoff M (D M) (valid M) (before M bodies) extra q r a
          (pre x p j) x p j clock hp hj.1 hs ht hclock .callByValueSeq E K
        have hr : DynamicScannerBinding.resume (profile (D M) (pre x p j)) q=some r := by
          rw [DynamicScannerBinding.resume_actual,ht]
        rw [evV_seq_ok hv]
        simp only [residual,hr,state_actual]
        have horigin : evV g x .callByValueSeq (tblV g x .callByValueSeq clock) E (origin M bodies e q a K) p=
            evV g x .callByValueSeq (tblV g x .callByValueSeq clock) E (dispatch (before M bodies).length q a K) p := by
          simp only [origin,MExp.andP,evV,hv]
        exact hh.symm.trans horigin.symm

end Shallot.MacroPeg.CBV.SequentialRecursiveScanner
