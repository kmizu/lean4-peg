import MacroPeg.CBV.RecapturedCopyBlock
import MacroPeg.CBV.CopyBodyEmission

namespace Shallot.MacroPeg.CBV.RecapturedCopyTransfer
open DelimiterTemplate DelimitedWordPattern DelimitedCopyProjection
open DelimitedPatternEvaluation ClockFreezing

def rules (arity : Nat) (d : Char) (js : List Nat) : List MRule :=
  (List.range arity).map (fun i => ⟨1,compile d (afterParts d i js)⟩)++[⟨1,.star (.param 0)⟩]

def head (base arity : Nat) (d : Char) (js : List Nat) (args : List MExp) : MExp :=
  .seq (preflight args) (RootObservation.branch (.andP (targetHead base args))
    (.call (base+arity) [compile d (RecapturedCopyBlock.skeleton d js)]) .eps)

structure Installed (h : MGrammar) (base arity : Nat) (d : Char) (js : List Nat) : Prop where
  projections : ∀ i, i<arity → ruleAtM h.rules (base+i)=some ⟨1,compile d (afterParts d i js)⟩
  loop : ruleAtM h.rules (base+arity)=some ⟨1,.star (.param 0)⟩

theorem rules_projection (arity : Nat) (d : Char) (js : List Nat) (i : Nat) (hi : i<arity) :
    ruleAtM (rules arity d js) i=some ⟨1,compile d (afterParts d i js)⟩ := by
  simp only [rules,ruleAtM_eq_getElem?]
  rw [List.getElem?_append_left (by simpa using hi)]
  simp [List.getElem?_map,List.getElem?_range hi]

theorem rules_loop (arity : Nat) (d : Char) (js : List Nat) :
    ruleAtM (rules arity d js) arity=some ⟨1,.star (.param 0)⟩ := by
  simp [rules,ruleAtM_eq_getElem?,List.getElem?_append_right,List.length_map]

theorem rules_firstOrder (arity : Nat) (d : Char) (js : List Nat) : ∀ r∈rules arity d js, r.body.FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr|hr
  · obtain ⟨i,_,rfl⟩ := List.mem_map.mp hr
    exact compile_firstOrder _ _
  · have he : r=⟨1,.star (.param 0)⟩ := by simpa using hr
    subst r; trivial

theorem head_firstOrder (base arity : Nat) (d : Char) (js : List Nat) (args : List MExp)
    (ha : MExp.FirstOrderArgs args) : (head base arity d js args).FirstOrder := by
  have hquery : (targetHead base args).FirstOrder :=
    ⟨DelimitedPatternCompiler.preflight_firstOrder args ha,
      DelimitedPatternCompiler.passes_firstOrder base args ha _ (fun i hi => List.mem_range.mp hi)⟩
  have hloop : (MExp.call (base+arity) [compile d (RecapturedCopyBlock.skeleton d js)]).FirstOrder :=
    ⟨compile_firstOrder _ _,True.intro⟩
  exact ⟨DelimitedPatternCompiler.preflight_firstOrder args ha,⟨⟨hquery,hloop⟩,⟨hquery,True.intro⟩⟩⟩

theorem physical (g h : MGrammar) (base : Nat) (d : Char) (j : Nat) (js : List Nat)
    (args emitted : List MExp) (hlen : emitted.length=args.length) (hn : 0<args.length)
    (hscope : ∀ i∈j::js, i<args.length)
    (hsource : ruleAtM g.rules base=some ⟨args.length,.star (compile d (sourceParts d (j::js)))⟩)
    (hi : Installed h base args.length d (j::js))
    (hg : g.FirstOrder) (hfo : MExp.FirstOrderArgs args)
    (x : List Char) (E : List (List Char)) (k p : Nat) (hp : p≤x.length)
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
      (RootObservation.branch (.andP (targetHead base emitted))
        (.call (base+args.length) [compile d (RecapturedCopyBlock.skeleton d (j::js))]) .eps) q
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
            (.call (base+args.length) [compile d (RecapturedCopyBlock.skeleton d (j::js))]) .eps) p
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
          rw [evV_star,evStar_fail (by rw [compile_eval g x .callByValuePar _ W d _ p hp,hfirst]; rfl)]
          rfl
        | some rest =>
          have hguard : evV h x .callByValueSeq (tblV h x .callByValueSeq (k+1)) E (.andP (targetHead base emitted)) p=some (some p) := by
            rw [CallLookahead.evV_peek,hquery]
            change CallLookahead.peek p (some ((run d W (sourceParts d (j::js)) (sfx x p)).map List.length))=_
            rw [hfirst]; rfl
          rw [ScannerFrontier.branch_eval _ _ _ p true (by simpa using hguard)]
          exact (RecapturedCopyBlock.recapture_call g h (base+args.length) d j js hi.loop x E W k p hp hsc hwfree rest hfirst).symm

end Shallot.MacroPeg.CBV.RecapturedCopyTransfer
