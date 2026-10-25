import MacroPeg.CBV.CopyPeriodControl
import MacroPeg.CBV.CopyBodyEmission

namespace Shallot.MacroPeg.CBV.ControlledPeriodTransfer
open DelimiterTemplate DelimitedWordPattern DelimitedCopyProjection
open DelimitedPatternEvaluation ClockFreezing
open CopyPeriodControl (Tail probeBody runBody)

def recapture (address : Nat) (d : Char) (js : List Nat) : MExp :=
  .call address [compile d (RecapturedCopyBlock.skeleton d js)]

def rules (arity : Nat) (d : Char) (js : List Nat) (tail : Tail) : List MRule :=
  (List.range arity).map (fun i => ⟨1,compile d (afterParts d i js)⟩)++[⟨1,probeBody tail⟩,⟨1,runBody tail⟩]

def head (base arity : Nat) (d : Char) (js : List Nat) (tail : Tail) (args : List MExp) : MExp :=
  .seq (preflight args) (RootObservation.branch (.andP (targetHead base args))
    (RootObservation.branch (.andP (recapture (base+arity) d js)) (recapture (base+arity+1) d js) .eps) .eps)

structure Installed (h : MGrammar) (base arity : Nat) (d : Char) (js : List Nat) (tail : Tail) : Prop where
  projections : ∀ i, i<arity → ruleAtM h.rules (base+i)=some ⟨1,compile d (afterParts d i js)⟩
  probe : ruleAtM h.rules (base+arity)=some ⟨1,probeBody tail⟩
  run : ruleAtM h.rules (base+arity+1)=some ⟨1,runBody tail⟩

theorem rules_projection (arity : Nat) (d : Char) (js : List Nat) (tail : Tail) (i : Nat) (hi : i<arity) :
    ruleAtM (rules arity d js tail) i=some ⟨1,compile d (afterParts d i js)⟩ := by
  simp only [rules,ruleAtM_eq_getElem?]
  rw [List.getElem?_append_left (by simpa using hi)]
  simp [List.getElem?_map,List.getElem?_range hi]

theorem rules_probe (arity : Nat) (d : Char) (js : List Nat) (tail : Tail) :
    ruleAtM (rules arity d js tail) arity=some ⟨1,probeBody tail⟩ := by
  simp [rules,ruleAtM_eq_getElem?,List.getElem?_append_right,List.length_map]

theorem rules_run (arity : Nat) (d : Char) (js : List Nat) (tail : Tail) :
    ruleAtM (rules arity d js tail) (arity+1)=some ⟨1,runBody tail⟩ := by
  simp [rules,ruleAtM_eq_getElem?,List.getElem?_append_right,List.length_map]

theorem source_firstOrder (d : Char) (js : List Nat) (tail : Tail) : (CopyPeriodControl.sourceBody d js tail).FirstOrder :=
  ⟨compile_firstOrder _ _,CopyPeriodControl.firstOrder _ (compile_firstOrder _ _) tail⟩

theorem rules_firstOrder (arity : Nat) (d : Char) (js : List Nat) (tail : Tail) : ∀ r∈rules arity d js tail, r.body.FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr|hr
  · obtain ⟨i,_,rfl⟩ := List.mem_map.mp hr
    exact compile_firstOrder _ _
  · have hp : (probeBody tail).FirstOrder := CopyPeriodControl.firstOrder (.param 0) True.intro tail
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · exact hp
    · exact ⟨hp,⟨True.intro,hp⟩⟩

theorem head_firstOrder (base arity : Nat) (d : Char) (js : List Nat) (tail : Tail) (args : List MExp)
    (ha : MExp.FirstOrderArgs args) : (head base arity d js tail args).FirstOrder := by
  have hquery : (targetHead base args).FirstOrder :=
    ⟨DelimitedPatternCompiler.preflight_firstOrder args ha,
      DelimitedPatternCompiler.passes_firstOrder base args ha _ (fun i hi => List.mem_range.mp hi)⟩
  have hcap (address : Nat) : (recapture address d js).FirstOrder := ⟨compile_firstOrder _ _,True.intro⟩
  exact ⟨DelimitedPatternCompiler.preflight_firstOrder args ha,
    ⟨⟨hquery,⟨⟨hcap (base+arity),hcap (base+arity+1)⟩,⟨hcap (base+arity),True.intro⟩⟩⟩,⟨hquery,True.intro⟩⟩⟩

theorem physical (bodies : List MExp) (g h : MGrammar) (base : Nat) (d : Char) (j : Nat) (js : List Nat) (tail : Tail)
    (hb : RecursiveParserStability.Valid bodies)
    (hgs : RecursiveParserStability.Installed bodies g) (hhs : RecursiveParserStability.Installed bodies h)
    (ht : CopyPeriodControl.check bodies.length tail=true)
    (args emitted : List MExp) (hlen : emitted.length=args.length) (hn : 0<args.length)
    (hscope : ∀ i∈j::js, i<args.length)
    (hsource : ruleAtM g.rules base=some ⟨args.length,CopyPeriodControl.sourceBody d (j::js) tail⟩)
    (hi : Installed h base args.length d (j::js) tail)
    (hg : g.FirstOrder) (hfo : MExp.FirstOrderArgs args)
    (x : List Char) (E : List (List Char)) (k p : Nat) (hp : p≤x.length)
    (he : ∀ i, (hii : i<args.length) → evV g x .callByValuePar (tblV g x .callByValuePar k) E args[i] p=
      evV h x .callByValueSeq (tblV h x .callByValueSeq k) E (emitted[i]'(by omega)) p)
    (hfree : ∀ i, (hii : i<args.length) → ∀ q,
      evV g x .callByValuePar (tblV g x .callByValuePar k) E args[i] p=some (some q) → Free d (pre x p q)) :
    evV g x .callByValuePar (tblV g x .callByValuePar k) E (.call base args) p=
      evV h x .callByValueSeq (tblV h x .callByValueSeq k) E (head base args.length d (j::js) tail emitted) p := by
  rw [evV_call_par hsource rfl (by decide)]
  have heargs := ParentPatternTransfer.arguments_congr g h x (tblV g x .callByValuePar k) (tblV h x .callByValueSeq k) E p args emitted hlen he
  unfold head
  change _=(match evV h x .callByValueSeq (tblV h x .callByValueSeq k) E (preflight emitted) p with
    | some (some q) => evV h x .callByValueSeq (tblV h x .callByValueSeq k) E
      (RootObservation.branch (.andP (targetHead base emitted))
        (RootObservation.branch (.andP (recapture (base+args.length) d (j::js))) (recapture (base+args.length+1) d (j::js)) .eps) .eps) q
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
          (RootObservation.branch (.andP (targetHead base emitted))
            (RootObservation.branch (.andP (recapture (base+args.length) d (j::js))) (recapture (base+args.length+1) d (j::js)) .eps) .eps) p
      cases k with
      | zero =>
        have hguard : evV h x .callByValueSeq (tblV h x .callByValueSeq 0) E (.andP (targetHead base emitted)) p=none := by
          rw [CallLookahead.evV_peek,hquery]; rfl
        rw [RootObservation.branch,evV_alt_none (evV_seq_none hguard)]
        rfl
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
          rw [ScannerFrontier.branch_eval _ _ _ p false (by simpa using hguard)]
          rw [CopyPeriodControl.sourceBody,evV_star,evStar_fail (evV_seq_fail (by rw [compile_eval g x .callByValuePar _ W d _ p hp,hfirst]; rfl))]
          rfl
        | some rest =>
          have hguard : evV h x .callByValueSeq (tblV h x .callByValueSeq (k+1)) E (.andP (targetHead base emitted)) p=some (some p) := by
            rw [CallLookahead.evV_peek,hquery]
            change CallLookahead.peek p (some ((run d W (sourceParts d (j::js)) (sfx x p)).map List.length))=_
            rw [hfirst]; rfl
          rw [ScannerFrontier.branch_eval _ _ _ p true (by simpa using hguard)]
          simp only [↓reduceIte]
          let B := encode d W (j::js)
          let R := probeBody tail
          let I := MExp.seq (.param 0) R
          have hentry := CopyPeriodControl.entry h (base+args.length) R hi.probe x E W k p hp d (j::js) hsc hwfree rest hfirst
          have hrun := CopyPeriodControl.entry h (base+args.length+1) (runBody tail) hi.run x E W k p hp d (j::js) hsc hwfree rest hfirst
          have hx : sfx x p=B++rest := (CBVtoCBN.stripPrefix_exact _ _ _).mp
            ((RecapturedCopyBlock.source_run d W (j::js) hsc _).symm.trans hfirst)
          have hhead : evV h x .callByValueSeq (tblV h x .callByValueSeq k) [B] (.param 0) p=some (some rest.length) := by
            simp only [evV,List.getElem?_cons_zero,(CBVtoCBN.stripPrefix_exact _ _ _).mpr hx]
          have hq := evV_ok (tblV_ok h x .callByValueSeq k) _ p hp _ hhead
          have hlt : rest.length<p := by
            simpa only [length_sfx x hp] using RepeatedWordEvaluation.source_progress d W j js _ rest hfirst
          rw [CopyPeriodControl.iteration bodies g h hb hgs hhs x k W d (j::js) hsc tail ht p hp]
          have htest : evV h x .callByValueSeq (tblV h x .callByValueSeq (k+1)) E
              (.andP (recapture (base+args.length) d (j::js))) p=
                CallLookahead.peek p (evV h x .callByValueSeq (tblV h x .callByValueSeq k) [B] R rest.length) := by
            rw [CallLookahead.evV_peek]
            exact congrArg (CallLookahead.peek p) hentry
          cases hv : evV h x .callByValueSeq (tblV h x .callByValueSeq k) [B] R rest.length with
          | none =>
            have hn : evV h x .callByValueSeq (tblV h x .callByValueSeq (k+1)) E
                (.andP (recapture (base+args.length) d (j::js))) p=none := by rw [htest,hv]; rfl
            rw [RootObservation.branch,evV_alt_none (evV_seq_none hn)]
            rw [evV_star,evStar_none (by rw [evV_seq_ok hhead]; exact hv)]
          | some v => cases v with
            | none =>
              rw [ScannerFrontier.branch_eval _ _ _ p false (by rw [htest,hv]; rfl)]
              rw [evV_star,evStar_fail (by rw [evV_seq_ok hhead]; exact hv)]
              rfl
            | some r =>
              rw [ScannerFrontier.branch_eval _ _ _ p true (by rw [htest,hv]; rfl)]
              simp only [↓reduceIte,recapture]
              rw [hrun]
              have htail := CopyPeriodControl.physical bodies g h hb hgs hhs x k W d (j::js) hsc tail ht rest.length hq
              have hpref := ReplayFusion.success_prefix (tblV_sound hg (by decide) k) W
                (CopyPeriodControl.render (compile d (sourceParts d (j::js))) tail)
                (CopyPeriodControl.firstOrder _ (compile_firstOrder _ _) tail) rest.length r hq (htail.trans hv)
              have hrbound := congrArg List.length hpref.2
              simp only [length_sfx x hq,length_sfx x hpref.1,List.length_append] at hrbound
              rw [CopyPeriodControl.runBody,evV_seq_ok hv]
              rw [evV_star,evStar_ok (by rw [evV_seq_ok hhead]; exact hv) (show r<p by omega)]
              rfl

end Shallot.MacroPeg.CBV.ControlledPeriodTransfer
