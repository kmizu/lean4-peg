import MacroPeg.CBV.TupleFieldTransfer

/-! A local call transfer retaining an arbitrary invariant of the actual
captured tuple. This lets the recursive compiler use per-slot alphabets,
rather than assuming body equivalence for every delimiter-free tuple. -/
namespace Shallot.MacroPeg.CBV.TypedFieldTransfer
open TupleFieldTransfer DelimiterTemplate DelimitedWordPattern DelimitedCopyProjection
open DelimitedPatternEvaluation

theorem physical_retaining (g h : MGrammar) (sourceIndex base : Nat) (d : Char)
    (j : Nat) (js : List Nat) (e : MExp)
    (emittedBody : MExp) (Q : List (List Char) → Prop)
    (args emitted : List MExp) (hlen : emitted.length=args.length) (hn : 0<args.length)
    (hscope : ∀ i∈j::js, i<args.length)
    (used : ParameterSupport.Supports (UsedFieldCapture.Allowed args.length (j::js)) emittedBody)
    (hsource : ruleAtM g.rules sourceIndex=some ⟨args.length,sourceBody d (j::js) e⟩)
    (hi : Installed h base args.length d (j::js) emittedBody)
    (hg : g.FirstOrder) (hfo : MExp.FirstOrderArgs args)
    (x : List Char) (E : List (List Char)) (k p : Nat) (hp : p≤x.length)
    (hbody : ∀ m, m<k → ∀ W : List (List Char), W.length=args.length →
      (∀ i, (hii : i<W.length) → Free d W[i]) → Q W → ∀ q, q≤x.length →
      evV g x .callByValuePar (tblV g x .callByValuePar m) W e q=
        evV h x .callByValueSeq (tblV h x .callByValueSeq m) W emittedBody q)
    (he : ∀ i, (hii : i<args.length) → evV g x .callByValuePar (tblV g x .callByValuePar k) E args[i] p=
      evV h x .callByValueSeq (tblV h x .callByValueSeq k) E (emitted[i]'(by omega)) p)
    (hQ : ∀ W, evParArgs g x .callByValuePar (tblV g x .callByValuePar k) E args p=some (some W) → Q W)
    (hfree : ∀ i, (hii : i<args.length) → ∀ q,
      evV g x .callByValuePar (tblV g x .callByValuePar k) E args[i] p=some (some q) → Free d (pre x p q)) :
    evV g x .callByValuePar (tblV g x .callByValuePar k) E (.call sourceIndex args) p=
      evV h x .callByValueSeq (tblV h x .callByValueSeq k) E (head base args.length d (j::js) emitted) p := by
  rw [evV_call_par hsource rfl (by decide)]
  have heargs := ParentPatternTransfer.arguments_congr g h x (tblV g x .callByValuePar k) (tblV h x .callByValueSeq k) E p args emitted hlen he
  unfold head
  change _=(match evV h x .callByValueSeq (tblV h x .callByValueSeq k) E (preflight emitted) p with
    | some (some q) => evV h x .callByValueSeq (tblV h x .callByValueSeq k) E
      (.seq (.andP (targetHead base emitted)) (.call (base+args.length) (CopyFieldCapture.scanArgs d (j::js)))) q
    | other => other)
  rw [preflight_eval,←heargs]
  cases hs : evParArgs g x .callByValuePar (tblV g x .callByValuePar k) E args p with
  | none => rfl
  | some v => cases v with
    | none => rfl
    | some W =>
      have hquery := CopyBodyProjections.query_physical g h base d j js args emitted hlen hn hscope hi.projections
        hg hfo x E k p hp he hfree W hs
      change valAt (tblV g x .callByValuePar k sourceIndex W) p=
        evV h x .callByValueSeq (tblV h x .callByValueSeq k) E
          (.seq (.andP (targetHead base emitted)) (.call (base+args.length) (CopyFieldCapture.scanArgs d (j::js)))) p
      cases k with
      | zero =>
        have hguard : evV h x .callByValueSeq (tblV h x .callByValueSeq 0) E (.andP (targetHead base emitted)) p=none := by
          rw [CallLookahead.evV_peek,hquery]; rfl
        rw [evV_seq_none hguard]; rfl
      | succ k =>
        obtain ⟨qs,hl,hw,hq⟩ := endpoints g x .callByValuePar (tblV g x .callByValuePar (k+1)) E p args W hs
        have hwl : W.length=args.length := by simp [hw,hl]
        have hwfree (i : Nat) (hii : i<W.length) : Free d W[i] := by
          have hh : W[i]=pre x p (qs[i]'(by omega)) := by simp [hw]
          rw [hh]
          exact hfree i (by omega) _ (hq i (by omega))
        have hsc : ∀ i∈j::js, i<W.length := fun i hii => by have := hscope i hii; omega
        rw [valAt_tblV_succ hsource W hp]
        cases hfirst : run d W (sourceParts d (j::js)) (sfx x p) with
        | none =>
          have hguard : evV h x .callByValueSeq (tblV h x .callByValueSeq (k+1)) E (.andP (targetHead base emitted)) p=some none := by
            rw [CallLookahead.evV_peek,hquery]
            change CallLookahead.peek p (some ((run d W (sourceParts d (j::js)) (sfx x p)).map List.length))=_
            rw [hfirst]; rfl
          rw [evV_seq_fail hguard,sourceBody,evV_seq_fail (by rw [compile_eval g x .callByValuePar _ W d _ p hp,hfirst]; rfl)]
        | some rest =>
          have hguard : evV h x .callByValueSeq (tblV h x .callByValueSeq (k+1)) E (.andP (targetHead base emitted)) p=some (some p) := by
            rw [CallLookahead.evV_peek,hquery]
            change CallLookahead.peek p (some ((run d W (sourceParts d (j::js)) (sfx x p)).map List.length))=_
            rw [hfirst]; rfl
          rw [evV_seq_ok hguard,UsedFieldCapture.entry h
            (base+args.length) args.length d (j::js) emittedBody used hi.entry x E W hwl hsc hwfree k p hp rest hfirst]
          have hstep : evV g x .callByValuePar (tblV g x .callByValuePar k) W
              (compile d (sourceParts d (j::js))) p=some (some rest.length) := by
            rw [compile_eval g x .callByValuePar _ W d _ p hp,hfirst]; rfl
          rw [sourceBody,evV_seq_ok hstep]
          exact hbody k (by omega) W hwl hwfree (hQ W hs) rest.length
            (evV_ok (tblV_ok _ _ _ k) _ p hp _ hstep)

/-- When no parameter is read, preflight the actuals and enter a nullary
continuation at the original position. No delimiter anchor is consumed. -/
theorem physical_empty_retaining (g h : MGrammar) (sourceIndex base : Nat) (d : Char)
    (e emittedBody : MExp) (Q : List (List Char) → Prop) (args emitted : List MExp) (hlen : emitted.length=args.length)
    (used : ParameterSupport.Supports (UsedFieldCapture.Allowed args.length []) emittedBody)
    (hsource : ruleAtM g.rules sourceIndex=some ⟨args.length,sourceBody d [] e⟩)
    (hi : Installed h base args.length d [] emittedBody)
    (x : List Char) (E : List (List Char)) (k p : Nat) (hp : p≤x.length)
    (hbody : ∀ m, m<k → ∀ W : List (List Char), W.length=args.length →
      (∀ i, (hii : i<W.length) → Free d W[i]) → Q W → ∀ q, q≤x.length →
      evV g x .callByValuePar (tblV g x .callByValuePar m) W e q=
        evV h x .callByValueSeq (tblV h x .callByValueSeq m) W emittedBody q)
    (he : ∀ i, (hii : i<args.length) → evV g x .callByValuePar (tblV g x .callByValuePar k) E args[i] p=
      evV h x .callByValueSeq (tblV h x .callByValueSeq k) E (emitted[i]'(by omega)) p)
    (hQ : ∀ W, evParArgs g x .callByValuePar (tblV g x .callByValuePar k) E args p=some (some W) → Q W)
    (hfree : ∀ i, (hii : i<args.length) → ∀ q,
      evV g x .callByValuePar (tblV g x .callByValuePar k) E args[i] p=some (some q) → Free d (pre x p q)) :
    evV g x .callByValuePar (tblV g x .callByValuePar k) E (.call sourceIndex args) p=
      evV h x .callByValueSeq (tblV h x .callByValueSeq k) E (head base args.length d [] emitted) p := by
  rw [evV_call_par hsource rfl (by decide)]
  have heargs := ParentPatternTransfer.arguments_congr g h x (tblV g x .callByValuePar k) (tblV h x .callByValueSeq k) E p args emitted hlen he
  unfold head
  change _=(match evV h x .callByValueSeq (tblV h x .callByValueSeq k) E (preflight emitted) p with
    | some (some q) => evV h x .callByValueSeq (tblV h x .callByValueSeq k) E (.call (base+args.length) []) q
    | other => other)
  rw [preflight_eval,←heargs]
  cases hs : evParArgs g x .callByValuePar (tblV g x .callByValuePar k) E args p with
  | none => rfl
  | some v => cases v with
    | none => rfl
    | some W =>
      change valAt (tblV g x .callByValuePar k sourceIndex W) p=
        evV h x .callByValueSeq (tblV h x .callByValueSeq k) E (.call (base+args.length) []) p
      cases k with
      | zero => rw [evV_call_seq hi.entry rfl,evSeq_nil]; rfl
      | succ k =>
        obtain ⟨qs,hl,hw,hq⟩ := endpoints g x .callByValuePar (tblV g x .callByValuePar (k+1)) E p args W hs
        have hwl : W.length=args.length := by simp [hw,hl]
        have hwfree (i : Nat) (hii : i<W.length) : Free d W[i] := by
          have hh : W[i]=pre x p (qs[i]'(by omega)) := by simp [hw]
          rw [hh]
          exact hfree i (by omega) _ (hq i (by omega))
        rw [valAt_tblV_succ hsource W hp,sourceBody,evV_seq_ok (show
          evV g x .callByValuePar (tblV g x .callByValuePar k) W (compile d (sourceParts d [])) p=some (some p) from rfl)]
        have ht := UsedFieldCapture.entry h (base+args.length) args.length d [] emittedBody used hi.entry
          x E W hwl (by intro i hi; cases hi) hwfree k p hp (sfx x p) rfl
        simp only [CopyFieldCapture.scanArgs,length_sfx x hp] at ht
        rw [ht]
        exact hbody k (by omega) W hwl hwfree (hQ W hs) p hp

end Shallot.MacroPeg.CBV.TypedFieldTransfer
