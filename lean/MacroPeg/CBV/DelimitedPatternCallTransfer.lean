import MacroPeg.CBV.DelimitedPatternEvaluation

namespace Shallot.MacroPeg.CBV.DelimitedPatternCallTransfer
open DelimiterTemplate DelimitedWordPattern DelimitedPatternPasses DelimitedPatternEvaluation
open DelimitedCopyProjection
open ClockFreezing (Table)

theorem arguments_congr (g h : MGrammar) (x : List Char) (T U : Table) (p : Nat) :
    ∀ (args emitted : List MExp), (hlen : emitted.length=args.length) →
      (∀ i, (hi : i<args.length) → evV g x .callByValuePar T [] args[i] p=evV h x .callByValueSeq U [] (emitted[i]'(by omega)) p) →
      evParArgs g x .callByValuePar T [] args p=evParArgs h x .callByValueSeq U [] emitted p
  | [],[],_,_ => rfl
  | [],_::_,hl,_ | _::_,[],hl,_ => by simp at hl
  | a::args,b::bs,hl,he => by
    have ha : evV g x .callByValuePar T [] a p=evV h x .callByValueSeq U [] b p := he 0 (by simp)
    have ht := arguments_congr g h x T U p args bs (by simpa using hl) (fun i hi => he (i+1) (by simpa using hi))
    simp only [evParArgs,ha,ht]

theorem physical (g h : MGrammar) (n : Nat) (d : Char) (j : Nat) (js : List Nat)
    (args emitted : List MExp) (hlen : emitted.length=args.length) (hn : 0<args.length) (hscope : ∀ i∈j::js, i<args.length)
    (hsrc : ruleAtM g.rules n=some ⟨args.length,compile d (sourceParts d (j::js))⟩)
    (hrows : ∀ i, i<args.length → ruleAtM h.rules (n+i)=some ⟨1,compile d (afterParts d i (j::js))⟩)
    (hg : g.FirstOrder) (hfo : MExp.FirstOrderArgs args)
    (x : List Char) (k p : Nat) (hp : p≤x.length)
    (he : ∀ i, (hi : i<args.length) → evV g x .callByValuePar (tblV g x .callByValuePar k) [] args[i] p=
      evV h x .callByValueSeq (tblV h x .callByValueSeq k) [] (emitted[i]'(by omega)) p)
    (hfree : ∀ i, (hi : i<args.length) → ∀ q,
      evV g x .callByValuePar (tblV g x .callByValuePar k) [] args[i] p=some (some q) → Free d (pre x p q)) :
    evV g x .callByValuePar (tblV g x .callByValuePar k) [] (.call n args) p=
      evV h x .callByValueSeq (tblV h x .callByValueSeq k) [] (targetHead n emitted) p := by
  rw [evV_call_par hsrc rfl (by decide)]
  have heargs := arguments_congr g h x (tblV g x .callByValuePar k) (tblV h x .callByValueSeq k) p args emitted hlen he
  unfold targetHead
  change _=(match evV h x .callByValueSeq (tblV h x .callByValueSeq k) [] (preflight emitted) p with
    | some (some q) => evV h x .callByValueSeq (tblV h x .callByValueSeq k) [] (passes n emitted (List.range emitted.length)) q | other => other)
  rw [preflight_eval,←heargs]
  cases hs : evParArgs g x .callByValuePar (tblV g x .callByValuePar k) [] args p with
  | none => rfl
  | some v => cases v with
    | none => rfl
    | some W =>
      obtain ⟨qs,hl,hw,hq⟩ := endpoints g x .callByValuePar (tblV g x .callByValuePar k) [] p args W hs
      have hwl : W.length=args.length := by simp [hw,hl]
      have hqbound (i : Nat) (hi : i<args.length) : qs[i]'(by omega)≤x.length :=
        evV_ok (tblV_ok _ _ _ k) _ p hp _ (hq i hi)
      have hwi (i : Nat) (hi : i<args.length) : W[i]'(by omega)=pre x p (qs[i]'(by omega)) := by simp [hw]
      let tails := qs.map (sfx x)
      have htl : tails.length=W.length := by simp [tails,hwl,hl]
      have hwfree (i : Nat) (hi : i<W.length) : Free d W[i] := by
        rw [hwi i (by omega)]
        exact hfree i (by omega) _ (hq i (by omega))
      have hprefix (i : Nat) (hi : i<W.length) : sfx x p=W[i]++(tails[i]'(by omega)) := by
        rw [hwi i (by omega)]
        have heFO : args[i].FirstOrder := firstOrder_get args hfo i (by omega)
        simpa [tails] using (ReplayFusion.success_prefix (tblV_sound hg (by decide) k) [] args[i] heFO p _ hp (hq i (by omega))).2
      have hr := run_eq d W tails (by omega) hwfree htl (sfx x p) hprefix j js (fun i hi => by have hh := hscope i hi; omega)
      have hc (i : Nat) (hi : i∈List.range emitted.length) :
          evV h x .callByValueSeq (tblV h x .callByValueSeq k) [] (.call (n+i) [argument emitted i]) p=
            result k (pass d W tails (j::js) i) := by
        have hi : i<args.length := by have hh := List.mem_range.mp hi; omega
        rw [argument_eq emitted i (by omega),unary_call h n i d (j::js) (hrows i hi) x k p _ (hqbound i hi) (emitted[i]'(by omega))
          ((he i hi).symm.trans (hq i hi))]
        simp only [pass,getElem!_pos W i (show i<W.length by omega),getElem!_pos tails i (show i<tails.length by omega),hwi i hi]
        simp [tails]
      have hne : List.range emitted.length≠[] := by simpa only [hlen] using (show List.range args.length≠[] from by simpa using (Nat.ne_of_gt hn))
      have hpass := passes_clock h x (tblV h x .callByValueSeq k) n emitted p k (pass d W tails (j::js)) _ hne hc
      change valAt (tblV g x .callByValuePar k n W) p=evV h x .callByValueSeq (tblV h x .callByValueSeq k) [] (passes n emitted (List.range emitted.length)) p
      rw [source_row g n args.length d (j::js) hsrc x k W p hp]
      change result k (run d W (sourceParts d (j::js)) (sfx x p))=evV h x .callByValueSeq (tblV h x .callByValueSeq k) [] (passes n emitted (List.range emitted.length)) p
      rw [hpass,hlen,←hwl,←hr]

end Shallot.MacroPeg.CBV.DelimitedPatternCallTransfer
