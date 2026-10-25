import MacroPeg.CBV.GuardedPairCorrespondence
import MacroPeg.CBV.ScannerFrontierValues

namespace Shallot.MacroPeg.CBV.CapturedOriginQuery
open GuardedPairSyntax (render)
open GuardedPairSimulation (values)
open MixedScannerPairFusion (Entry)
open NestedScannerArguments (scan scan_eval choice)
open ClockFreezing (Table)

inductive Plan where
  | test (tail : MExp)
  | after (second : Bool) (tail : MExp)
  | follow (second : Bool) (tail : Plan)
  | seq (a b : Plan)
  | alt (a b : Plan)
  | notP (a : Plan)
  | star (a : Plan)

/-- At a positive stateless scanner frontier, nonempty old values cannot replay.
Only their two emptiness bits are needed by the remaining query plan. -/
def frontier (nonemptyA nonemptyB : Bool) : Plan → MExp
  | .test e => .andP e
  | .after second e => if (if second then nonemptyB else nonemptyA) then MExp.failAlways else .andP e
  | .follow second a => if (if second then nonemptyB else nonemptyA) then MExp.failAlways else .andP (frontier nonemptyA nonemptyB a)
  | .seq a b => .seq (frontier nonemptyA nonemptyB a) (frontier nonemptyA nonemptyB b)
  | .alt a b => .alt (frontier nonemptyA nonemptyB a) (frontier nonemptyA nonemptyB b)
  | .notP a => .notP (frontier nonemptyA nonemptyB a)
  | .star a => .star (frontier nonemptyA nonemptyB a)

def choose (A B : List Char) (f : Bool → Bool → MExp) : MExp :=
  RootObservation.branch (.andP (choice A))
    (RootObservation.branch (.andP (choice B)) (f true true) (f true false))
    (RootObservation.branch (.andP (choice B)) (f false true) (f false false))

def compile (A B : List Char) (canonical : Bool) : Plan → MExp
  | .test e => .andP e
  | .after second e => .andP (.seq (if canonical then scan (if second then B else A)
      else .param (if second then 1 else 0)) e)
  | .follow second a => .andP (if canonical then choose A B (fun fa fb =>
      if (if second then fb else fa) then .seq (scan (if second then B else A)) (frontier fa fb a)
      else compile A B true a) else .seq (.param (if second then 1 else 0)) (compile A B false a))
  | .seq a b => .seq (compile A B canonical a) (compile A B canonical b)
  | .alt a b => .alt (compile A B canonical a) (compile A B canonical b)
  | .notP a => .notP (compile A B canonical a)
  | .star a => .star (compile A B canonical a)

def tailCheck (es : List Entry) (e : MExp) := ZeroResetOrigin.closedCheck (render es true e) &&
  ZeroResetOrigin.closedCheck (render es false e)
def check (es : List Entry) : Plan → Bool
  | .test e | .after _ e => tailCheck es e
  | .seq a b | .alt a b => check es a && check es b
  | .notP a | .star a | .follow _ a => check es a

theorem render_choice (es : List Entry) (parallel : Bool) (A : List Char) : render es parallel (choice A)=choice A := by
  induction A <;> simp_all [choice,render,MExp.failAlways]
theorem render_scan (es : List Entry) (parallel : Bool) (A : List Char) : render es parallel (scan A)=scan A := by
  simp [scan,render,render_choice]

theorem render_choose (es : List Entry) (parallel : Bool) (A B : List Char) (f : Bool → Bool → MExp) :
    render es parallel (choose A B f)=choose A B (fun a b => render es parallel (f a b)) := by
  simp only [choose,RootObservation.branch,MExp.andP,render,render_choice]

theorem choose_eval (es : List Entry) (g : MGrammar) (x : List Char) (T : Table) (E : List (List Char))
    (A B : List Char) (f : Bool → Bool → MExp) (p : Nat) (hp : p≤x.length) :
    evV g x .callByValuePar T E (render es true (choose A B f)) p=
      evV g x .callByValuePar T E (render es true (f (ScannerFrontierValues.starts A (sfx x p))
        (ScannerFrontierValues.starts B (sfx x p)))) p := by
  rw [render_choose,choose,ScannerFrontier.branch_eval _ _ _ p _ (ScannerFrontierValues.probe_eval g x .callByValuePar T E A p hp)]
  cases ha : ScannerFrontierValues.starts A (sfx x p) <;> simp only [if_true,Bool.false_eq_true,if_false]
  all_goals
    rw [ScannerFrontier.branch_eval _ _ _ p _ (ScannerFrontierValues.probe_eval g x .callByValuePar T E B p hp)]
    cases hb : ScannerFrontierValues.starts B (sfx x p) <;> rfl

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

theorem render_andP_origin (es : List Entry) (g : MGrammar) (x : List Char) (T : Table) (E : List (List Char))
    (e : MExp) (p q : Nat) (h : evV g x .callByValuePar T E (render es true (.andP e)) p=some (some q)) : q=p := by
  change evV g x .callByValuePar T E (.andP (render es true e)) p=some (some q) at h
  rw [CallLookahead.evV_peek] at h
  cases he : evV g x .callByValuePar T E (render es true e) p with
  | none => simp [he,CallLookahead.peek] at h
  | some v => cases v <;> simp_all [CallLookahead.peek]

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
  | .follow second a,p,q,h => render_andP_origin es g x T E _ p q h
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

theorem frontier_aligned (es : List Entry) (g : MGrammar) (x : List Char) (T : Table) (E : List (List Char))
    (A B : List Char) (fa fb : Bool) (p : Nat)
    (hparam : ∀ (second : Bool), evV g x .callByValuePar T E (.param (if second then 1 else 0)) p=
      if (if second then fb else fa) then some none else some (some p)) :
    ∀ plan, check es plan=true → evV g x .callByValuePar T E (render es true (compile A B false plan)) p=
      evV g x .callByValuePar T [] (render es true (frontier fa fb plan)) p
  | .test e,hc => by
    have hclosed := ZeroResetOrigin.closed_checked _ (Bool.and_eq_true_iff.mp hc).1
    exact ReplayFallbackFusion.closed_env g x .callByValuePar T (.andP (render es true e)) hclosed E p
  | .after second e,hc => by
    have hclosed := ZeroResetOrigin.closed_checked _ (Bool.and_eq_true_iff.mp hc).1
    have hh := hparam second
    cases hf : (if second then fb else fa) with
    | true =>
      rw [hf] at hh
      change evV g x .callByValuePar T E (.andP (.seq (.param (if second then 1 else 0)) (render es true e))) p=
        evV g x .callByValuePar T [] (render es true (if (if second then fb else fa) then MExp.failAlways else .andP e)) p
      rw [hf,CallLookahead.evV_peek,evV_seq_fail hh]
      rfl
    | false =>
      rw [hf] at hh
      change evV g x .callByValuePar T E (.andP (.seq (.param (if second then 1 else 0)) (render es true e))) p=
        evV g x .callByValuePar T [] (render es true (if (if second then fb else fa) then MExp.failAlways else .andP e)) p
      rw [hf,CallLookahead.evV_peek,evV_seq_ok hh]
      change CallLookahead.peek p (evV g x .callByValuePar T E (render es true e) p)=
        evV g x .callByValuePar T [] (.andP (render es true e)) p
      rw [CallLookahead.evV_peek,ReplayFallbackFusion.closed_env g x .callByValuePar T _ hclosed E p]
  | .follow second a,hc => by
    have hh := hparam second
    cases hf : (if second then fb else fa) with
    | true =>
      rw [hf] at hh
      change evV g x .callByValuePar T E (.andP (.seq (.param (if second then 1 else 0)) (render es true (compile A B false a)))) p=
        evV g x .callByValuePar T [] (render es true (if (if second then fb else fa) then MExp.failAlways else .andP (frontier fa fb a))) p
      rw [hf,CallLookahead.evV_peek,evV_seq_fail hh]; rfl
    | false =>
      rw [hf] at hh
      change evV g x .callByValuePar T E (.andP (.seq (.param (if second then 1 else 0)) (render es true (compile A B false a)))) p=
        evV g x .callByValuePar T [] (render es true (if (if second then fb else fa) then MExp.failAlways else .andP (frontier fa fb a))) p
      rw [hf,CallLookahead.evV_peek,evV_seq_ok hh]
      change CallLookahead.peek p (evV g x .callByValuePar T E (render es true (compile A B false a)) p)=
        evV g x .callByValuePar T [] (.andP (render es true (frontier fa fb a))) p
      rw [CallLookahead.evV_peek,frontier_aligned es g x T E A B fa fb p hparam a hc]
  | .seq a b,hc => by
    have ha := frontier_aligned es g x T E A B fa fb p hparam a (Bool.and_eq_true_iff.mp hc).1
    cases he : evV g x .callByValuePar T E (render es true (compile A B false a)) p with
    | none => simp only [compile,frontier,render,evV_seq_none he,evV_seq_none (ha.symm.trans he)]
    | some v => cases v with
      | none => simp only [compile,frontier,render,evV_seq_fail he,evV_seq_fail (ha.symm.trans he)]
      | some q =>
        have hq := returns_origin es g x T E A B false a p q he
        subst q
        simp only [compile,frontier,render,evV_seq_ok he,evV_seq_ok (ha.symm.trans he)]
        exact frontier_aligned es g x T E A B fa fb p hparam b (Bool.and_eq_true_iff.mp hc).2
  | .alt a b,hc => by
    have ha := frontier_aligned es g x T E A B fa fb p hparam a (Bool.and_eq_true_iff.mp hc).1
    cases he : evV g x .callByValuePar T E (render es true (compile A B false a)) p with
    | none => simp only [compile,frontier,render,evV_alt_none he,evV_alt_none (ha.symm.trans he)]
    | some v => cases v with
      | none =>
        simp only [compile,frontier,render,evV_alt_fail he,evV_alt_fail (ha.symm.trans he)]
        exact frontier_aligned es g x T E A B fa fb p hparam b (Bool.and_eq_true_iff.mp hc).2
      | some q => simp only [compile,frontier,render,evV_alt_ok he,evV_alt_ok (ha.symm.trans he)]
  | .notP a,hc => by
    simp only [compile,frontier,render,evV]
    rw [frontier_aligned es g x T E A B fa fb p hparam a hc]
  | .star a,hc => by
    have ha := frontier_aligned es g x T E A B fa fb p hparam a hc
    simp only [compile,frontier,render,evV_star]
    cases he : evV g x .callByValuePar T E (render es true (compile A B false a)) p with
    | none => rw [evStar_none he,evStar_none (ha.symm.trans he)]
    | some v => cases v with
      | none => rw [evStar_fail he,evStar_fail (ha.symm.trans he)]
      | some q =>
        have hq := returns_origin es g x T E A B false a p q he
        rw [evStar_stuck he (by omega),evStar_stuck (ha.symm.trans he) (by omega)]

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
  | .follow second a,hc,p,hp => by
    let C := if second then B else A
    let q := ((sfx x p).dropWhile (NestedScannerArguments.accepts C)).length
    have hrep := replay_eq_scan g x T hs r A B hr second p hp
    have hscan : evV g x .callByValuePar T [] (scan C) p=some (some q) := scan_eval _ _ _ _ _ C p hp
    rw [hscan] at hrep
    change evV g x .callByValuePar T (values r x p) (.andP (.seq (.param (if second then 1 else 0)) (render es true (compile A B false a)))) p=
      evV g x .callByValuePar T [] (.andP (render es true (choose A B (fun fa fb =>
        if (if second then fb else fa) then .seq (scan C) (frontier fa fb a) else compile A B true a)))) p
    rw [CallLookahead.evV_peek,CallLookahead.evV_peek,choose_eval es g x T [] A B _ p hp]
    have hflag : (if second then ScannerFrontierValues.starts B (sfx x p) else ScannerFrontierValues.starts A (sfx x p))=
        ScannerFrontierValues.starts C (sfx x p) := by cases second <;> rfl
    rw [hflag]
    by_cases hpos : ScannerFrontierValues.starts C (sfx x p)=true
    · rw [if_pos hpos]
      simp only [render,render_scan]
      rw [evV_seq_ok hrep,evV_seq_ok hscan]
      apply congrArg (CallLookahead.peek p)
      apply frontier_aligned es g x T (values r x p) A B _ _ q _ a hc
      intro j
      have hh := ScannerFrontierValues.frontier_parameter g x T r A B hr second j p hp hpos
      cases j <;> exact hh
    · rw [if_neg hpos]
      have hrest := ScannerFrontierValues.empty_remainder C (sfx x p) (Bool.eq_false_iff.mpr hpos)
      have hq : q=p := by change (ScannerFrontier.remainder C (sfx x p)).length=p; rw [hrest,length_sfx x hp]
      rw [hq] at hrep
      rw [evV_seq_ok hrep]
      exact congrArg (CallLookahead.peek p) (aligned es g x T hs r A B hr a hc p hp)
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
