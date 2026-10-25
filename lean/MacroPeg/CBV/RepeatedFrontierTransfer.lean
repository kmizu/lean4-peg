import MacroPeg.CBV.RepeatedWordFrontier
import MacroPeg.CBV.CopyBodyProjections

/-! The exact maximum-frontier calculation uses genuine Seq calls at
their actual capture endpoints. `maximum` remains an evaluator-level
operation; no Seq expression implementing it is asserted here. -/
namespace Shallot.MacroPeg.CBV.RepeatedFrontierTransfer
open DelimiterTemplate DelimitedWordPattern DelimitedCopyProjection
open DelimitedPatternEvaluation ClockFreezing SynchronizedStarFrontier

def afterLoop (d : Char) (i : Nat) (js : List Nat) : MExp :=
  .seq (compile d (afterParts d i js)) (.star (compile d (viewParts d i js)))

theorem afterLoop_firstOrder (d : Char) (i : Nat) (js : List Nat) : (afterLoop d i js).FirstOrder :=
  ⟨compile_firstOrder d _,compile_firstOrder d _⟩

theorem adjusted_loop (h : MGrammar) (x : List Char) (t : Strategy) (U : Table)
    (hU : OkTV x.length U) (w : List Char) (d : Char) (hw : Free d w)
    (i j : Nat) (js : List Nat) (p q : Nat) (hp : p≤x.length) (hq : q≤x.length)
    (hprefix : sfx x p=w++sfx x q) (rest : List Char)
    (hfirst : run d [w] (viewParts d i (j::js)) (sfx x p)=some rest) :
    evV h x t U [w] (afterLoop d i (j::js)) q=
      evV h x t U [w] (.star (compile d (viewParts d i (j::js)))) p := by
  have hadjust : run d [w] (afterParts d i (j::js)) (sfx x q)=some rest := by
    rw [after_eq_view d w hw i j js,←hprefix]
    exact hfirst
  have hview : evV h x t U [w] (compile d (viewParts d i (j::js))) p=some (some rest.length) := by
    simp only [compile_eval h x t U [w] d _ p hp,hfirst,Option.map_some]
  have hafter : evV h x t U [w] (compile d (afterParts d i (j::js))) q=some (some rest.length) := by
    simp only [compile_eval h x t U [w] d _ q hq,hadjust,Option.map_some]
  have hlt : rest.length<p := by
    have hh := RepeatedWordEvaluation.view_progress d w hw i j js (sfx x p) rest hfirst
    simpa only [length_sfx x hp] using hh
  rw [afterLoop,evV_seq_ok hafter,evV_star,evV_star,evStar_ok hview hlt]

theorem unary_call (h : MGrammar) (base i : Nat) (d : Char) (j : Nat) (js : List Nat)
    (hrow : ruleAtM h.rules (base+i)=some ⟨1,afterLoop d i (j::js)⟩)
    (x : List Char) (E : List (List Char)) (k p q : Nat) (hp : p≤x.length) (hq : q≤x.length)
    (a : MExp) (ha : evV h x .callByValueSeq (tblV h x .callByValueSeq (k+1)) E a p=some (some q))
    (hw : Free d (pre x p q)) (hprefix : sfx x p=pre x p q++sfx x q)
    (rest : List Char)
    (hfirst : run d [pre x p q] (viewParts d i (j::js)) (sfx x p)=some rest) :
    evV h x .callByValueSeq (tblV h x .callByValueSeq (k+1)) E (.call (base+i) [a]) p=
      evV h x .callByValueSeq (tblV h x .callByValueSeq k) [pre x p q]
        (.star (compile d (viewParts d i (j::js)))) p := by
  rw [evV_call_seq hrow rfl,evSeq_cons_ok ha,evSeq_nil]
  change valAt (tblV h x .callByValueSeq (k+1) (base+i) [pre x p q]) q=_
  rw [valAt_tblV_succ hrow _ hq]
  exact adjusted_loop h x .callByValueSeq _ (tblV_ok _ _ _ k) _ d hw i j js p q hp hq hprefix rest hfirst

/-- If the first full source iteration succeeds, its entire bare-star
call returns the earliest of the actual unary Seq call frontiers. This
statement retains arbitrary following input and arbitrary caller values. -/
theorem positive_iterations (g h : MGrammar) (base : Nat) (d : Char) (j : Nat) (js : List Nat)
    (args emitted : List MExp) (hlen : emitted.length=args.length) (hn : 0<args.length)
    (hscope : ∀ i∈j::js, i<args.length)
    (hsource : ruleAtM g.rules base=some ⟨args.length,.star (compile d (sourceParts d (j::js)))⟩)
    (hrows : ∀ i, i<args.length → ruleAtM h.rules (base+1+i)=some ⟨1,afterLoop d i (j::js)⟩)
    (hg : g.FirstOrder) (hfo : MExp.FirstOrderArgs args)
    (x : List Char) (E : List (List Char)) (k p : Nat) (hp : p≤x.length)
    (he : ∀ i, (hi : i<args.length) →
      evV g x .callByValuePar (tblV g x .callByValuePar (k+1)) E args[i] p=
      evV h x .callByValueSeq (tblV h x .callByValueSeq (k+1)) E (emitted[i]'(by omega)) p)
    (hfree : ∀ i, (hi : i<args.length) → ∀ q,
      evV g x .callByValuePar (tblV g x .callByValuePar (k+1)) E args[i] p=some (some q) → Free d (pre x p q))
    (W : List (List Char))
    (hs : evParArgs g x .callByValuePar (tblV g x .callByValuePar (k+1)) E args p=some (some W))
    (rest : List Char) (hfirst : run d W (sourceParts d (j::js)) (sfx x p)=some rest) :
    evV g x .callByValuePar (tblV g x .callByValuePar (k+1)) E (.call base args) p=
      maximum ((List.range args.length).map (fun i =>
        evV h x .callByValueSeq (tblV h x .callByValueSeq (k+1)) E
          (.call (base+1+i) [argument emitted i]) p)) := by
  obtain ⟨qs,hl,hw,hq⟩ := endpoints g x .callByValuePar (tblV g x .callByValuePar (k+1)) E p args W hs
  have hwl : W.length=args.length := by simp [hw,hl]
  have hwi (i : Nat) (hi : i<args.length) : W[i]'(by omega)=pre x p (qs[i]'(by omega)) := by simp [hw]
  have hqbound (i : Nat) (hi : i<args.length) : qs[i]'(by omega)≤x.length :=
    evV_ok (tblV_ok _ _ _ (k+1)) _ p hp _ (hq i hi)
  have hwfree (i : Nat) (hi : i<W.length) : Free d W[i] := by
    rw [hwi i (by omega)]
    exact hfree i (by omega) _ (hq i (by omega))
  have hprefix (i : Nat) (hi : i<args.length) : sfx x p=pre x p (qs[i]'(by omega))++sfx x (qs[i]'(by omega)) :=
    (ReplayFusion.success_prefix (tblV_sound hg (by decide) (k+1)) E args[i]
      (firstOrder_get args hfo i hi) p _ hp (hq i hi)).2
  have hmatch := (DelimitedWordPattern.source_iff_views d W (by omega) hwfree (j::js)
    (fun i hi => by have := hscope i hi; omega) _ rest).mp hfirst
  have hc (i : Nat) (hi : i<args.length) :
      evV h x .callByValueSeq (tblV h x .callByValueSeq (k+1)) E (.call (base+1+i) [argument emitted i]) p=
        evV h x .callByValueSeq (tblV h x .callByValueSeq k) [W[i]'(by omega)]
          (.star (compile d (viewParts d i (j::js)))) p := by
    rw [argument_eq emitted i (by omega)]
    have hm : run d [pre x p (qs[i]'(by omega))] (viewParts d i (j::js)) (sfx x p)=some rest := by
      rw [←hwi i hi]
      exact (view_iff d W[i] (hwfree i (by omega)) i _ _ _).mpr (hmatch i (by omega))
    simpa only [hwi i hi] using unary_call h (base+1) i d j js (hrows i hi) x E k p _ hp
      (hqbound i hi) (emitted[i]'(by omega)) ((he i hi).symm.trans (hq i hi))
      (hfree i hi _ (hq i hi)) (hprefix i hi) rest hm
  rw [evV_call_par hsource rfl (by decide),hs]
  change valAt (tblV g x .callByValuePar (k+1) base W) p=_
  rw [valAt_tblV_succ hsource W hp,
    RepeatedWordFrontier.physical g h x .callByValuePar .callByValueSeq
      (tblV g x .callByValuePar k) (tblV h x .callByValueSeq k)
      (tblV_ok g x .callByValuePar k) (tblV_ok h x .callByValueSeq k) W d (by omega) hwfree j js
      (fun i hi => by have := hscope i hi; omega) p hp]
  unfold loops RepeatedWordFrontier.components
  simp only [List.map_map,hwl]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi := List.mem_range.mp hi
  simpa only [Function.comp_apply,RepeatedWordFrontier.viewStep,getElem!_pos W i (show i<W.length by omega),evV_star] using (hc i hi).symm

theorem zero_iterations (g : MGrammar) (base : Nat) (d : Char) (j : Nat) (js : List Nat)
    (args : List MExp)
    (hsource : ruleAtM g.rules base=some ⟨args.length,.star (compile d (sourceParts d (j::js)))⟩)
    (x : List Char) (E : List (List Char)) (k p : Nat) (hp : p≤x.length)
    (W : List (List Char))
    (hs : evParArgs g x .callByValuePar (tblV g x .callByValuePar (k+1)) E args p=some (some W))
    (hfirst : run d W (sourceParts d (j::js)) (sfx x p)=none) :
    evV g x .callByValuePar (tblV g x .callByValuePar (k+1)) E (.call base args) p=some (some p) := by
  rw [evV_call_par hsource rfl (by decide),hs]
  change valAt (tblV g x .callByValuePar (k+1) base W) p=_
  rw [valAt_tblV_succ hsource W hp,evV_star]
  apply evStar_fail
  simp only [compile_eval g x .callByValuePar _ W d _ p hp,hfirst,Option.map_none]

end Shallot.MacroPeg.CBV.RepeatedFrontierTransfer
