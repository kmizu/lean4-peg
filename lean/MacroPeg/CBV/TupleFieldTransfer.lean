import MacroPeg.CBV.TupleFieldControl
import MacroPeg.CBV.CopyBodyEmission

/-! Translate a checked delimited anchor followed by ordinary control that
can independently replay any of the original Par arguments. The anchor is
mandatory and must cover the source tuple; this is not a general Par compiler. -/
namespace Shallot.MacroPeg.CBV.TupleFieldTransfer
open DelimiterTemplate DelimitedWordPattern DelimitedCopyProjection
open DelimitedPatternEvaluation

def sourceBody (d : Char) (js : List Nat) (e : MExp) : MExp :=
  .seq (compile d (sourceParts d js)) e

def rules (arity : Nat) (d : Char) (js : List Nat) (e : MExp) : List MRule :=
  (List.range arity).map (fun i => ⟨1,compile d (afterParts d i js)⟩)++
    [⟨2*js.length,MExp.subst (CopyFieldCapture.views arity js) e⟩]

def head (base arity : Nat) (d : Char) (js : List Nat) (args : List MExp) : MExp :=
  .seq (preflight args) (.seq (.andP (targetHead base args))
    (.call (base+arity) (CopyFieldCapture.scanArgs d js)))

structure Installed (h : MGrammar) (base arity : Nat) (d : Char) (js : List Nat) (e : MExp) : Prop where
  projections : ∀ i, i<arity → ruleAtM h.rules (base+i)=some ⟨1,compile d (afterParts d i js)⟩
  entry : ruleAtM h.rules (base+arity)=some ⟨2*js.length,MExp.subst (CopyFieldCapture.views arity js) e⟩

theorem rules_projection (arity : Nat) (d : Char) (js : List Nat) (e : MExp) (i : Nat) (hi : i<arity) :
    ruleAtM (rules arity d js e) i=some ⟨1,compile d (afterParts d i js)⟩ := by
  simp only [rules,ruleAtM_eq_getElem?]
  rw [List.getElem?_append_left (by simpa using hi)]
  simp [List.getElem?_map,List.getElem?_range hi]

theorem rules_entry (arity : Nat) (d : Char) (js : List Nat) (e : MExp) :
    ruleAtM (rules arity d js e) arity=some ⟨2*js.length,MExp.subst (CopyFieldCapture.views arity js) e⟩ := by
  simp [rules,ruleAtM_eq_getElem?,List.length_map]

theorem rules_firstOrder (arity : Nat) (d : Char) (js : List Nat) (e : MExp)
    (he : e.FirstOrder) : ∀ r∈rules arity d js e, r.body.FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr|hr
  · obtain ⟨i,_,rfl⟩ := List.mem_map.mp hr
    exact compile_firstOrder _ _
  · have hr : r=⟨2*js.length,MExp.subst (CopyFieldCapture.views arity js) e⟩ := by simpa using hr
    subst r
    exact firstOrder_subst (CopyFieldCapture.views_firstOrder arity js) e he

theorem head_firstOrder (base arity : Nat) (d : Char) (js : List Nat) (args : List MExp)
    (ha : MExp.FirstOrderArgs args) : (head base arity d js args).FirstOrder := by
  have hquery : (targetHead base args).FirstOrder :=
    ⟨DelimitedPatternCompiler.preflight_firstOrder args ha,
      DelimitedPatternCompiler.passes_firstOrder base args ha _ (fun i hi => List.mem_range.mp hi)⟩
  exact ⟨DelimitedPatternCompiler.preflight_firstOrder args ha,hquery,CopyFieldCapture.scanArgs_firstOrder d js⟩

/-- The original actuals may overlap or contain calls. Their local evaluation
correspondence and delimiter freedom are the interface to the caller compiler.
The body after the anchor can use the tuple components separately. -/
theorem physical_of_body (g h : MGrammar) (base : Nat) (d : Char)
    (j : Nat) (js : List Nat) (e : MExp)
    (emittedBody : MExp) (hem : emittedBody.FirstOrder)
    (args emitted : List MExp) (hlen : emitted.length=args.length) (hn : 0<args.length)
    (hscope : ∀ i∈j::js, i<args.length)
    (cover : ∀ i, i<args.length → i∈j::js)
    (hsource : ruleAtM g.rules base=some ⟨args.length,sourceBody d (j::js) e⟩)
    (hi : Installed h base args.length d (j::js) emittedBody)
    (hg : g.FirstOrder) (hfo : MExp.FirstOrderArgs args)
    (x : List Char) (E : List (List Char)) (k p : Nat) (hp : p≤x.length)
    (hbody : ∀ m, m<k → ∀ W : List (List Char), W.length=args.length →
      (∀ i, (hii : i<W.length) → Free d W[i]) → ∀ q, q≤x.length →
      evV g x .callByValuePar (tblV g x .callByValuePar m) W e q=
        evV h x .callByValueSeq (tblV h x .callByValueSeq m) W emittedBody q)
    (he : ∀ i, (hii : i<args.length) → evV g x .callByValuePar (tblV g x .callByValuePar k) E args[i] p=
      evV h x .callByValueSeq (tblV h x .callByValueSeq k) E (emitted[i]'(by omega)) p)
    (hfree : ∀ i, (hii : i<args.length) → ∀ q,
      evV g x .callByValuePar (tblV g x .callByValuePar k) E args[i] p=some (some q) → Free d (pre x p q)) :
    evV g x .callByValuePar (tblV g x .callByValuePar k) E (.call base args) p=
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
      change valAt (tblV g x .callByValuePar k base W) p=
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
          rw [evV_seq_ok hguard,CopyFieldCapture.entry h
            (base+args.length) args.length d (j::js) emittedBody hem hi.entry x E W hwl cover hsc hwfree k p hp rest hfirst]
          have hstep : evV g x .callByValuePar (tblV g x .callByValuePar k) W
              (compile d (sourceParts d (j::js))) p=some (some rest.length) := by
            rw [compile_eval g x .callByValuePar _ W d _ p hp,hfirst]; rfl
          rw [sourceBody,evV_seq_ok hstep]
          exact hbody k (by omega) W hwl hwfree rest.length
            (evV_ok (tblV_ok _ _ _ k) _ p hp _ hstep)

theorem physical (bodies : List MExp) (g h : MGrammar) (base : Nat) (d : Char)
    (j : Nat) (js : List Nat) (e : MExp)
    (hb : RecursiveParserStability.Valid bodies)
    (hgs : RecursiveParserStability.Installed bodies g)
    (hhs : RecursiveParserStability.Installed bodies h)
    (args emitted : List MExp) (hlen : emitted.length=args.length) (hn : 0<args.length)
    (hc : TupleFieldControl.check bodies.length args.length e=true)
    (hscope : ∀ i∈j::js, i<args.length)
    (cover : ∀ i, i<args.length → i∈j::js)
    (hsource : ruleAtM g.rules base=some ⟨args.length,sourceBody d (j::js) e⟩)
    (hi : Installed h base args.length d (j::js) e)
    (hg : g.FirstOrder) (hfo : MExp.FirstOrderArgs args)
    (x : List Char) (E : List (List Char)) (k p : Nat) (hp : p≤x.length)
    (he : ∀ i, (hii : i<args.length) → evV g x .callByValuePar (tblV g x .callByValuePar k) E args[i] p=
      evV h x .callByValueSeq (tblV h x .callByValueSeq k) E (emitted[i]'(by omega)) p)
    (hfree : ∀ i, (hii : i<args.length) → ∀ q,
      evV g x .callByValuePar (tblV g x .callByValuePar k) E args[i] p=some (some q) → Free d (pre x p q)) :
    evV g x .callByValuePar (tblV g x .callByValuePar k) E (.call base args) p=
      evV h x .callByValueSeq (tblV h x .callByValueSeq k) E (head base args.length d (j::js) emitted) p := by
  apply physical_of_body g h base d j js e e (TupleFieldControl.firstOrder _ _ e hc)
    args emitted hlen hn hscope cover hsource hi hg hfo x E k p hp
  · intro m hm W hl hf q hq
    exact TupleFieldControl.physical bodies g h hb hgs hhs x m W args.length e hc q hq
  · exact he
  · exact hfree

end Shallot.MacroPeg.CBV.TupleFieldTransfer
