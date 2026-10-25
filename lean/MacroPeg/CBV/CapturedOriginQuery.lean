import MacroPeg.CBV.GuardedPairCorrespondence

namespace Shallot.MacroPeg.CBV.CapturedOriginQuery
open GuardedPairSyntax (render)
open GuardedPairSimulation (values)
open MixedScannerPairFusion (Entry)
open NestedScannerArguments (scan scan_eval choice)
open ClockFreezing (Table)

inductive Plan where
  | test (tail : MExp)
  | after (second : Bool) (tail : MExp)
  | seq (a b : Plan)
  | alt (a b : Plan)
  | notP (a : Plan)
  | star (a : Plan)

def compile (A B : List Char) (canonical : Bool) : Plan → MExp
  | .test e => .andP e
  | .after second e => .andP (.seq (if canonical then scan (if second then B else A)
      else .param (if second then 1 else 0)) e)
  | .seq a b => .seq (compile A B canonical a) (compile A B canonical b)
  | .alt a b => .alt (compile A B canonical a) (compile A B canonical b)
  | .notP a => .notP (compile A B canonical a)
  | .star a => .star (compile A B canonical a)

def tailCheck (es : List Entry) (e : MExp) := ZeroResetOrigin.closedCheck (render es true e) &&
  ZeroResetOrigin.closedCheck (render es false e)
def check (es : List Entry) : Plan → Bool
  | .test e | .after _ e => tailCheck es e
  | .seq a b | .alt a b => check es a && check es b
  | .notP a | .star a => check es a

theorem render_choice (es : List Entry) (parallel : Bool) (A : List Char) : render es parallel (choice A)=choice A := by
  induction A <;> simp_all [choice,render,MExp.failAlways]
theorem render_scan (es : List Entry) (parallel : Bool) (A : List Char) : render es parallel (scan A)=scan A := by
  simp [scan,render,render_choice]

theorem values_eq (g : MGrammar) (x : List Char) (T : Table) (r : Entry) (A B : List Char)
    (hr : r.pairing=some (A,B)) (p : Nat) (hp : p≤x.length) :
    values r x p=[pre x p ((x.drop (x.length-p)).dropWhile (NestedScannerArguments.accepts A)).length,
      pre x p ((x.drop (x.length-p)).dropWhile (NestedScannerArguments.accepts B)).length] := by
  have hh := ScannerFrontier.parallel_arguments g x .callByValuePar T [] A B p hp
  rw [evPar_cons_ok (scan_eval g x .callByValuePar T [] A p hp),
    evPar_cons_ok (scan_eval g x .callByValuePar T [] B p hp),evPar_nil] at hh
  simpa only [values,hr,Option.some.injEq,sfx] using hh.symm

/-- The actual two scanner arguments supply the retained words. Parameter
replay at their common origin therefore reaches the corresponding scanner end. -/
theorem replay_eq_scan (g : MGrammar) (x : List Char) (T : Table) (hs : SoundTV g x .callByValuePar T)
    (r : Entry) (A B : List Char) (hr : r.pairing=some (A,B)) (second : Bool) (p : Nat) (hp : p≤x.length) :
    evV g x .callByValuePar T (values r x p) (.param (if second then 1 else 0)) p=
      evV g x .callByValuePar T [] (scan (if second then B else A)) p := by
  let C := if second then B else A
  let q := ((sfx x p).dropWhile (NestedScannerArguments.accepts C)).length
  have he : evV g x .callByValuePar T [] (scan C) p=some (some q) := scan_eval _ _ _ _ _ C p hp
  have hprefix := ReplayFusion.success_prefix hs [] (scan C) (NestedScannerArguments.scan_firstOrder C) p q hp he
  have hget : (values r x p)[if second then 1 else 0]?=some (pre x p q) := by
    rw [values_eq g x T r A B hr p hp]
    cases second <;> rfl
  change evV g x .callByValuePar T (values r x p) (.param (if second then 1 else 0)) p=evV g x .callByValuePar T [] (scan C) p
  rw [he]
  simp only [evV,hget,(CBVtoCBN.stripPrefix_exact _ _ _).mpr hprefix.2,length_sfx x hprefix.1]

/-- Every compiled plan is a zero-width test, including partial repetition. -/
theorem returns_origin (es : List Entry) (g : MGrammar) (x : List Char) (T : Table) (E : List (List Char))
    (A B : List Char) (canonical : Bool) : ∀ plan p q,
    evV g x .callByValuePar T E (render es true (compile A B canonical plan)) p=some (some q) → q=p
  | .test e,p,q,h => by
    change evV g x .callByValuePar T E (.andP (render es true e)) p=some (some q) at h
    rw [CallLookahead.evV_peek] at h
    cases he : evV g x .callByValuePar T E (render es true e) p with
    | none => simp [he,CallLookahead.peek] at h
    | some v => cases v <;> simp_all [CallLookahead.peek]
  | .after second e,p,q,h => by
    change evV g x .callByValuePar T E (.andP (render es true (.seq (if canonical then scan (if second then B else A)
      else .param (if second then 1 else 0)) e))) p=some (some q) at h
    rw [CallLookahead.evV_peek] at h
    cases he : evV g x .callByValuePar T E (render es true (.seq (if canonical then scan (if second then B else A)
      else .param (if second then 1 else 0)) e)) p with
    | none => simp [he,CallLookahead.peek] at h
    | some v => cases v <;> simp_all [CallLookahead.peek]
  | .seq a b,p,q,h => by
    cases ha : evV g x .callByValuePar T E (render es true (compile A B canonical a)) p with
    | none => rw [compile,render,evV_seq_none ha] at h; cases h
    | some v => cases v with
      | none => rw [compile,render,evV_seq_fail ha] at h; cases h
      | some j =>
        have hj := returns_origin es g x T E A B canonical a p j ha
        subst j
        rw [compile,render,evV_seq_ok ha] at h
        exact returns_origin es g x T E A B canonical b p q h
  | .alt a b,p,q,h => by
    cases ha : evV g x .callByValuePar T E (render es true (compile A B canonical a)) p with
    | none => rw [compile,render,evV_alt_none ha] at h; cases h
    | some v => cases v with
      | none => rw [compile,render,evV_alt_fail ha] at h; exact returns_origin es g x T E A B canonical b p q h
      | some j =>
        rw [compile,render,evV_alt_ok ha] at h
        have he : j=q := by simpa only [Option.some.injEq] using h
        exact he.symm.trans (returns_origin es g x T E A B canonical a p j ha)
  | .notP a,p,q,h => by
    simp only [compile,render] at h
    cases ha : evV g x .callByValuePar T E (render es true (compile A B canonical a)) p with
    | none => simp [evV,ha] at h
    | some v => cases v <;> simp_all [evV]
  | .star a,p,q,h => by
    rw [compile,render,evV_star] at h
    cases ha : evV g x .callByValuePar T E (render es true (compile A B canonical a)) p with
    | none => rw [evStar_none ha] at h; cases h
    | some v => cases v with
      | none => rw [evStar_fail ha] at h; simpa only [Option.some.injEq] using h.symm
      | some j =>
        have hj := returns_origin es g x T E A B canonical a p j ha
        rw [evStar_stuck ha (by omega)] at h; cases h

theorem aligned (es : List Entry) (g : MGrammar) (x : List Char) (T : Table) (hs : SoundTV g x .callByValuePar T)
    (r : Entry) (A B : List Char) (hr : r.pairing=some (A,B)) : ∀ plan, check es plan=true → ∀ p, p≤x.length →
    evV g x .callByValuePar T (values r x p) (render es true (compile A B false plan)) p=
      evV g x .callByValuePar T [] (render es true (compile A B true plan)) p
  | .test e,hc,p,hp => by
    have hclosed := ZeroResetOrigin.closed_checked _ (Bool.and_eq_true_iff.mp hc).1
    change evV g x .callByValuePar T (values r x p) (.andP (render es true e)) p=
      evV g x .callByValuePar T [] (.andP (render es true e)) p
    exact ReplayFallbackFusion.closed_env g x .callByValuePar T (.andP (render es true e)) hclosed (values r x p) p
  | .after second e,hc,p,hp => by
    have hclosed := ZeroResetOrigin.closed_checked _ (Bool.and_eq_true_iff.mp hc).1
    change evV g x .callByValuePar T (values r x p) (.andP (.seq (.param (if second then 1 else 0)) (render es true e))) p=
      evV g x .callByValuePar T [] (.andP (.seq (render es true (scan (if second then B else A))) (render es true e))) p
    rw [render_scan,CallLookahead.evV_peek,CallLookahead.evV_peek]
    have he := replay_eq_scan g x T hs r A B hr second p hp
    have hscan := scan_eval g x .callByValuePar T [] (if second then B else A) p hp
    rw [hscan] at he
    rw [evV_seq_ok he,evV_seq_ok hscan]
    rw [ReplayFallbackFusion.closed_env g x .callByValuePar T _ hclosed (values r x p)]
  | .seq a b,hc,p,hp => by
    have ha := aligned es g x T hs r A B hr a (Bool.and_eq_true_iff.mp hc).1 p hp
    cases he : evV g x .callByValuePar T (values r x p) (render es true (compile A B false a)) p with
    | none => simp only [compile,render,evV_seq_none he,evV_seq_none (ha.symm.trans he)]
    | some v => cases v with
      | none => simp only [compile,render,evV_seq_fail he,evV_seq_fail (ha.symm.trans he)]
      | some j =>
        have hj := returns_origin es g x T (values r x p) A B false a p j he
        subst j
        simp only [compile,render,evV_seq_ok he,evV_seq_ok (ha.symm.trans he)]
        exact aligned es g x T hs r A B hr b (Bool.and_eq_true_iff.mp hc).2 p hp
  | .alt a b,hc,p,hp => by
    have ha := aligned es g x T hs r A B hr a (Bool.and_eq_true_iff.mp hc).1 p hp
    cases he : evV g x .callByValuePar T (values r x p) (render es true (compile A B false a)) p with
    | none => simp only [compile,render,evV_alt_none he,evV_alt_none (ha.symm.trans he)]
    | some v => cases v with
      | none =>
        simp only [compile,render,evV_alt_fail he,evV_alt_fail (ha.symm.trans he)]
        exact aligned es g x T hs r A B hr b (Bool.and_eq_true_iff.mp hc).2 p hp
      | some j => simp only [compile,render,evV_alt_ok he,evV_alt_ok (ha.symm.trans he)]
  | .notP a,hc,p,hp => by
    simp only [compile,render,evV]
    rw [aligned es g x T hs r A B hr a hc p hp]
  | .star a,hc,p,hp => by
    have ha := aligned es g x T hs r A B hr a hc p hp
    simp only [compile,render,evV_star]
    cases he : evV g x .callByValuePar T (values r x p) (render es true (compile A B false a)) p with
    | none => rw [evStar_none he,evStar_none (ha.symm.trans he)]
    | some v => cases v with
      | none => rw [evStar_fail he,evStar_fail (ha.symm.trans he)]
      | some j =>
        have hj := returns_origin es g x T (values r x p) A B false a p j he
        rw [evStar_stuck he (by omega),evStar_stuck (ha.symm.trans he) (by omega)]

end Shallot.MacroPeg.CBV.CapturedOriginQuery
